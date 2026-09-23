"""
engine2.py -- независимая (клин-рум) исполняемая модель боя H3-det-melee по homm3/MODEL.md.

Написана deriver-2 с нуля, только по тексту MODEL.md / §2 статьи. Не использует
homm3/scripts/homm3_model.py.

Реализовано:
  * гекс-сетка в offset-координатах (чётные ряды сдвинуты вправо), 6 соседей;
  * непроходимые гексы; гекс живого юнита не входим, мёртвого -- входим;
  * стек (fullUnits, firstHPleft), count, применение урона, kills;
  * формула урона с точной рациональной арифметикой (Fraction);
  * раунд: NORMAL-фаза по убыванию spd (ничьи: сторона, потом индекс), WAIT-фаза по возрастанию spd;
  * действия игрока: DEFEND (стоять), WAIT, MOVE(hex), ATTACK(target, from_hex);
  * политика (‡): враг в NORMAL-фазе WAIT, в WAIT-фазе DEFEND (+max(1, floor(0.2*def)) к def до его
    следующего хода);
  * ретал: один заряд в раунд, после удара, только если оба живы;
  * полный перебор действий игрока при R = 1 (с мемоизацией), максимизация value убитых.
"""
from fractions import Fraction
from collections import deque
import itertools

# ---------------------------------------------------------------- grid

def neighbours(x, y, n_rows, n_cols):
    if y % 2 == 0:
        cand = [(x-1, y), (x+1, y), (x, y-1), (x+1, y-1), (x, y+1), (x+1, y+1)]
    else:
        cand = [(x-1, y), (x+1, y), (x-1, y-1), (x, y-1), (x-1, y+1), (x, y+1)]
    return [(a, b) for (a, b) in cand if 0 <= a < n_cols and 0 <= b < n_rows]


def adjacent(h1, h2):
    (x, y) = h1
    if y % 2 == 0:
        cand = [(x-1, y), (x+1, y), (x, y-1), (x+1, y-1), (x, y+1), (x+1, y+1)]
    else:
        cand = [(x-1, y), (x+1, y), (x-1, y-1), (x, y-1), (x-1, y+1), (x, y+1)]
    return h2 in cand


class Board:
    def __init__(self, n_rows, n_cols, obstacles=()):
        self.n_rows = n_rows
        self.n_cols = n_cols
        self.obstacles = frozenset(obstacles)
        self._nb = {}
        for y in range(n_rows):
            for x in range(n_cols):
                self._nb[(x, y)] = tuple(neighbours(x, y, n_rows, n_cols))

    def nb(self, h):
        return self._nb[h]

    def passable(self, h):
        return h not in self.obstacles

    def bfs(self, start, blocked, limit):
        """Гексы, достижимые из start за <= limit шагов по проходимым и не занятым (blocked) гексам.
        Возвращает dict hex -> dist. start включён с dist 0."""
        dist = {start: 0}
        dq = deque([start])
        while dq:
            h = dq.popleft()
            d = dist[h]
            if d == limit:
                continue
            for g in self._nb[h]:
                if g in dist or g in self.obstacles or g in blocked:
                    continue
                dist[g] = d + 1
                dq.append(g)
        return dist

    def hex_count(self):
        return self.n_rows * self.n_cols


# ---------------------------------------------------------------- units

class CType:
    __slots__ = ("name", "att", "dfn", "dmg", "hp", "spd", "value")

    def __init__(self, name, att, dfn, dmg, hp, spd, value=0):
        assert att > 0 and dfn > 0 and dmg >= 1 and hp > 0 and spd > 0 and value >= 0
        self.name, self.att, self.dfn, self.dmg, self.hp, self.spd, self.value = \
            name, att, dfn, dmg, hp, spd, value


def damage(att_type, att_count, def_type, def_bonus):
    """Definition 4.1 MODEL.md, точная арифметика. def_bonus -- прибавка от DEFEND."""
    delta = att_type.att - (def_type.dfn + def_bonus)
    if delta > 0:
        f_att = 1 + min(Fraction(delta, 20), Fraction(4))
    else:
        f_att = Fraction(1)
    if delta < 0:
        f_def = 1 - min(Fraction(-delta, 40), Fraction(7, 10))
    else:
        f_def = Fraction(1)
    raw = att_count * att_type.dmg * f_att * f_def
    return max(1, raw.numerator // raw.denominator)


def defend_bonus(dfn):
    """+20 % защиты, целое, минимум +1 (R13). Читается как max(1, floor(0.2*def))."""
    return max(1, (dfn * 2) // 10)


class StackState:
    """Неизменяемое состояние стека."""
    __slots__ = ("full", "first", "hex", "retal", "bonus", "acted", "waiting")

    def __init__(self, full, first, hex_, retal=True, bonus=0, acted=False, waiting=False):
        self.full, self.first, self.hex, self.retal, self.bonus, self.acted, self.waiting = \
            full, first, hex_, retal, bonus, acted, waiting

    def key(self):
        return (self.full, self.first, self.hex, self.retal, self.bonus, self.acted, self.waiting)

    def alive(self):
        return self.full > 0 or self.first > 0

    def count(self):
        return self.full + (1 if self.first > 0 else 0)

    def avail(self, hp):
        return self.first + hp * self.full

    def replace(self, **kw):
        d = dict(full=self.full, first=self.first, hex_=self.hex, retal=self.retal,
                 bonus=self.bonus, acted=self.acted, waiting=self.waiting)
        for k, v in kw.items():
            d["hex_" if k == "hex" else k] = v
        return StackState(**d)


def apply_damage(st, hp, D):
    """Возвращает (новое состояние, число убитых существ)."""
    c0 = st.count()
    if D < st.first:
        new = st.replace(first=st.first - D)
    else:
        total = max(0, st.avail(hp) - D)
        full = total // hp
        first = total % hp
        if first == 0 and full >= 1:
            first = hp
            full -= 1
        new = st.replace(full=full, first=first)
    return new, c0 - new.count()


def kills_formula(st, hp, D):
    if D < st.first:
        return 0
    return min(1 + (D - st.first) // hp, st.count())


# ---------------------------------------------------------------- game

class Game:
    """Один раунд (R = 1) H3-det-melee против (‡). Игрок -- сторона 0, враг -- сторона 1.

    player_stacks: список (CType, count, hex) -- уже РАЗВЁРНУТЫЕ стеки (count >= 1); пустые слоты
    просто не включаются.
    enemy_stacks: список (CType, count, hex).
    """

    def __init__(self, board, player_stacks, enemy_stacks, allow_moves=True, allow_wait=True, objective="kills"):
        self.board = board
        self.objective = objective  # "kills": value убитых; "hp": поглощённый урон (оверкилл отброшен)
        self.ptypes = [t for (t, c, h) in player_stacks]
        self.etypes = [t for (t, c, h) in enemy_stacks]
        self.p0 = [StackState(c - 1, t.hp, h) for (t, c, h) in player_stacks]
        self.e0 = [StackState(c - 1, t.hp, h) for (t, c, h) in enemy_stacks]
        self.allow_moves = allow_moves
        self.allow_wait = allow_wait
        hexes = set(h for (_, _, h) in player_stacks) | set(h for (_, _, h) in enemy_stacks)
        assert len(hexes) == len(player_stacks) + len(enemy_stacks), "два стека на одном гексе"
        for h in hexes:
            assert board.passable(h), "стек на непроходимом гексе"
        self.memo = {}

    # порядок NORMAL-фазы: (-spd, side, index)
    def normal_order(self):
        order = [(-self.ptypes[i].spd, 0, i) for i in range(len(self.ptypes))] + \
                [(-self.etypes[i].spd, 1, i) for i in range(len(self.etypes))]
        order.sort()
        return [(side, i) for (_, side, i) in order]

    def occupied(self, P, E, except_idx=None):
        occ = set()
        for j, s in enumerate(P):
            if s.alive() and (except_idx is None or except_idx != (0, j)):
                occ.add(s.hex)
        for j, s in enumerate(E):
            if s.alive() and (except_idx is None or except_idx != (1, j)):
                occ.add(s.hex)
        return occ

    def player_options(self, P, E, i):
        """Все варианты завершающего действия стека игрока i: список (kind, data)."""
        st = P[i]
        t = self.ptypes[i]
        occ = self.occupied(P, E, except_idx=(0, i))
        reach = self.board.bfs(st.hex, occ, t.spd)
        opts = [("defend", None)]
        if self.allow_moves is True:
            for h in reach:
                if h != st.hex:
                    opts.append(("move", h))
        elif self.allow_moves == "docking":
            # только ходы на гексы, смежные с живым врагом (единственные, что могут кого-то заблокировать
            # на открытом поле)
            for h in reach:
                if h != st.hex and any(es.alive() and adjacent(h, es.hex) for es in E):
                    opts.append(("move", h))
        for j, es in enumerate(E):
            if not es.alive():
                continue
            for h in reach:
                if adjacent(h, es.hex):
                    opts.append(("attack", (j, h)))
        return opts

    def do_attack(self, P, E, i, j, h):
        """Стек игрока i идёт на h и бьёт врага j. Возвращает (P, E, value_killed)."""
        P = list(P)
        E = list(E)
        t = self.ptypes[i]
        et = self.etypes[j]
        P[i] = P[i].replace(hex=h)
        # удар (оба живы по построению)
        D = damage(t, P[i].count(), et, E[j].bonus)
        before = E[j].avail(et.hp)
        E[j], k = apply_damage(E[j], et.hp, D)
        if self.objective == "hp":
            val = before - E[j].avail(et.hp)
        else:
            val = k * et.value
        # ретал
        if E[j].alive() and P[i].alive() and E[j].retal:
            Dr = damage(et, E[j].count(), t, P[i].bonus)
            P[i], _ = apply_damage(P[i], t.hp, Dr)
            E[j] = E[j].replace(retal=False)
        return P, E, val

    def best_value(self):
        """Максимальная суммарная value убитых врагов за раунд 1 при полном переборе игрока."""
        order = self.normal_order()
        return self._normal(tuple(self.p0), tuple(self.e0), order, 0, 0)

    def _key(self, P, E, phase, pos):
        return (phase, pos, tuple(s.key() for s in P), tuple(s.key() for s in E))

    def _normal(self, P, E, order, pos, acc):
        key = self._key(P, E, "N", pos)
        if key in self.memo:
            return acc + self.memo[key]
        if pos == len(order):
            best = self._wait_phase(P, E)
        else:
            side, i = order[pos]
            if side == 1:
                # враг: WAIT (если жив)
                E2 = list(E)
                if E2[i].alive():
                    E2[i] = E2[i].replace(waiting=True)
                best = self._normal(P, tuple(E2), order, pos + 1, 0)
            else:
                if not P[i].alive():
                    best = self._normal(P, E, order, pos + 1, 0)
                else:
                    best = -1
                    # WAIT
                    if self.allow_wait:
                        P2 = list(P)
                        P2[i] = P2[i].replace(waiting=True)
                        best = max(best, self._normal(tuple(P2), E, order, pos + 1, 0))
                    for kind, data in self.player_options(P, E, i):
                        if kind == "defend":
                            P2 = list(P); P2[i] = P2[i].replace(acted=True, bonus=defend_bonus(self.ptypes[i].dfn))
                            v = self._normal(tuple(P2), E, order, pos + 1, 0)
                        elif kind == "move":
                            P2 = list(P); P2[i] = P2[i].replace(hex=data, acted=True)
                            v = self._normal(tuple(P2), E, order, pos + 1, 0)
                        else:
                            j, h = data
                            P2, E2, val = self.do_attack(P, E, i, j, h)
                            P2[i] = P2[i].replace(acted=True)
                            v = val + self._normal(tuple(P2), tuple(E2), order, pos + 1, 0)
                        best = max(best, v)
        self.memo[key] = best
        return acc + best

    def _wait_phase(self, P, E):
        # WAIT-фаза: по возрастанию spd, ничьи: сторона, индекс
        order = [(self.ptypes[i].spd, 0, i) for i in range(len(P)) if P[i].waiting and P[i].alive()] + \
                [(self.etypes[i].spd, 1, i) for i in range(len(E)) if E[i].waiting and E[i].alive()]
        order.sort()
        order = [(side, i) for (_, side, i) in order]
        return self._wait(P, E, order, 0)

    def _wait(self, P, E, order, pos):
        key = self._key(P, E, "W", pos)
        if key in self.memo:
            return self.memo[key]
        if pos == len(order):
            best = 0
        else:
            side, i = order[pos]
            if side == 1:
                E2 = list(E)
                if E2[i].alive():
                    E2[i] = E2[i].replace(waiting=False, bonus=defend_bonus(self.etypes[i].dfn))
                best = self._wait(P, tuple(E2), order, pos + 1)
            else:
                if not P[i].alive():
                    best = self._wait(P, E, order, pos + 1)
                else:
                    best = -1
                    for kind, data in self.player_options(P, E, i):
                        if kind == "defend":
                            P2 = list(P); P2[i] = P2[i].replace(waiting=False, acted=True, bonus=defend_bonus(self.ptypes[i].dfn))
                            v = self._wait(tuple(P2), E, order, pos + 1)
                        elif kind == "move":
                            P2 = list(P); P2[i] = P2[i].replace(hex=data, waiting=False, acted=True)
                            v = self._wait(tuple(P2), E, order, pos + 1)
                        else:
                            j, h = data
                            P2, E2, val = self.do_attack(P, E, i, j, h)
                            P2[i] = P2[i].replace(waiting=False, acted=True)
                            v = val + self._wait(tuple(P2), tuple(E2), order, pos + 1)
                        best = max(best, v)
        self.memo[key] = best
        return best


# ---------------------------------------------------------------- helpers

def static_reach(board, player_hexes, enemy_hexes, spd):
    """Для каждого слота: множество индексов врагов, которых он может ударить в стартовой позиции
    при всех занятых слотах (BFS по свободным гексам <= spd, затем смежность)."""
    occ = set(player_hexes) | set(enemy_hexes)
    res = []
    for p in player_hexes:
        reach = board.bfs(p, occ - {p}, spd)
        hit = set()
        for j, e in enumerate(enemy_hexes):
            if any(adjacent(h, e) for h in reach):
                hit.add(j)
        res.append(hit)
    return res


def all_allocations(k, stock):
    """Все векторы (c_1..c_k) с c_i >= 0 и суммой <= stock."""
    def rec(i, left):
        if i == k:
            yield ()
            return
        for c in range(left + 1):
            for rest in rec(i + 1, left - c):
                yield (c,) + rest
    return rec(0, stock)


def solve_allocation(board, slots, ptype, stock, enemy_stacks, W, allow_moves=True, allow_wait=True):
    """ARMY-ALLOCATION для одного типа игрока: перебор распределений + перебор игры.
    Возвращает (best_value, best_alloc)."""
    best = (-1, None)
    for alloc in all_allocations(len(slots), stock):
        ps = [(ptype, c, slots[i]) for i, c in enumerate(alloc) if c > 0]
        g = Game(board, ps, enemy_stacks, allow_moves=allow_moves, allow_wait=allow_wait)
        v = g.best_value()
        if v > best[0]:
            best = (v, alloc)
        if v >= W:
            return best
    return best


if __name__ == "__main__":
    # мини-самопроверка формулы урона и применения урона
    P = CType("P", 1, 1, 1, 4, 5)
    Q = CType("Q", 1, 27, 1, 3, 1, 1)
    tab = [damage(P, c, Q, 0) for c in range(1, 13)]
    print("D(1..12) при def 27:", tab)
    Q2 = CType("Q2", 1, 21, 1, 3, 1, 1)
    print("D(1..12) при def 21:", [damage(P, c, Q2, 0) for c in range(1, 13)])
    print("bonus(27) =", defend_bonus(27), " D' =", [damage(P, c, Q, defend_bonus(27)) for c in range(1, 13)])
    st = StackState(2, 5, (0, 0))
    print("stack 3x hp5 hit 7:", apply_damage(st, 5, 7)[0].key(), "kills", apply_damage(st, 5, 7)[1], kills_formula(st, 5, 7))
    print("stack 3x hp5 hit 3:", apply_damage(st, 5, 3)[0].key(), "kills", apply_damage(st, 5, 3)[1])
    print("stack 3x hp5 hit 10:", apply_damage(st, 5, 10)[0].key(), "kills", apply_damage(st, 5, 10)[1])
    print("stack 3x hp5 hit 99:", apply_damage(st, 5, 99)[0].key(), "kills", apply_damage(st, 5, 99)[1])
