#!/usr/bin/env python3
"""Клин-рум самопроверка для deriver-1.md.

Собственная транскрипция механики из MODEL.md (не использует scripts/homm3_model.py):
  * гексы в offset-координатах, чётные строки сдвинуты вправо (BattleHex.h:147-178);
  * урон  max(1, floor(count * d * f_att * f_def)) в точной рациональной арифметике;
  * пул здоровья (fullUnits, firstHPleft), overkill отбрасывается;
  * порядок ходов: NORMAL по убыванию spd (сторона, слот), WAIT по возрастанию spd;
  * политика (‡): враг WAIT, затем DEFEND (+max(1, floor(def/5)) к защите);
  * ответный удар: один заряд за раунд, только если обороняющийся жив после удара.

Проверяет:
  A. факты о соседстве гексов (сдвиги <= 1, вертикальная смежность, чередующиеся тройки);
  B. адаптеры теоремы 3 (все 6 конфигураций) — попарная несмежность трёх дорожек;
  C. брутфорс: конструкция теоремы 1 (PARTITION) на всех малых экземплярах;
  D. брутфорс: конструкция теоремы 4 (3-PARTITION, 6 x (4m+2), полная достижимость);
  E. брутфорс: ручная вложенная крошечная планарная X3C для теоремы 3 и следствия 3.1.
"""
from fractions import Fraction
from itertools import product, combinations
import sys

# ----------------------------------------------------------------------------- гексы

def neighbours(x, y):
    if y % 2:   # нечётная строка
        return [(x - 1, y - 1), (x, y - 1), (x + 1, y), (x, y + 1), (x - 1, y + 1), (x - 1, y)]
    return [(x, y - 1), (x + 1, y - 1), (x + 1, y), (x + 1, y + 1), (x, y + 1), (x - 1, y)]


def adjacent(a, b):
    return b in neighbours(*a)


def hexdist(a, b):
    x1 = a[0] + a[1] // 2
    x2 = b[0] + b[1] // 2
    dx, dy = x2 - x1, b[1] - a[1]
    if (dx >= 0 and dy >= 0) or (dx < 0 and dy < 0):
        return max(abs(dx), abs(dy))
    return abs(dx) + abs(dy)


def check_hex_facts():
    for y in range(-4, 5):
        for x in range(-4, 5):
            for (nx, ny) in neighbours(x, y):
                assert abs(nx - x) <= 1 and abs(ny - y) <= 1
                assert adjacent((nx, ny), (x, y)), "симметрия"
                assert hexdist((x, y), (nx, ny)) == 1
            assert adjacent((x, y), (x, y + 1)) and adjacent((x, y), (x + 1, y))
            # чередующиеся тройки для чётной строки
            if y % 2 == 0:
                tl, r, bl = (x, y - 1), (x + 1, y), (x, y + 1)
                tr, l, br = (x + 1, y - 1), (x - 1, y), (x + 1, y + 1)
                for trip in ((tl, r, bl), (tr, l, br)):
                    for a, b in combinations(trip, 2):
                        assert not adjacent(a, b), (trip, a, b)
                    for c in trip:
                        assert adjacent(c, (x, y))
            # соседи (a,b) с одинаковым x и |dy|=2 не смежны, |dx|>=2 не смежны
            for (ax, ay) in [(x + 2, y), (x - 2, y), (x, y + 2), (x, y - 2), (x + 2, y + 1)]:
                assert not adjacent((x, y), (ax, ay))
    print("A. факты о гексах: OK")

# ----------------------------------------------------------------------------- механика

class Type:
    def __init__(self, att, deff, dmg, hp, spd, value=0):
        self.att, self.deff, self.dmg, self.hp, self.spd, self.value = att, deff, dmg, hp, spd, value


class Stack:
    def __init__(self, side, slot, typ, count, pos):
        self.side, self.slot, self.typ, self.pos = side, slot, typ, pos
        self.full, self.first = count - 1, typ.hp
        self.retal = 1
        self.acted = False       # терминальное действие сделано
        self.waited = False
        self.defbonus = 0
        self.killed = 0          # сколько существ в этом стеке убито

    def alive(self):
        return self.full > 0 or self.first > 0

    def count(self):
        return self.full + (1 if self.first > 0 else 0)

    def avail(self):
        return self.first + self.typ.hp * self.full

    def clone(self):
        s = Stack.__new__(Stack)
        s.__dict__.update(self.__dict__)
        return s


def damage(att_stack, def_stack):
    a = att_stack.typ.att
    d = def_stack.typ.deff + def_stack.defbonus
    delta = a - d
    f_att = Fraction(1)
    f_def = Fraction(1)
    if delta > 0:
        f_att = 1 + min(Fraction(delta, 20), Fraction(4))
    if delta < 0:
        f_def = 1 - min(Fraction(-delta, 40), Fraction(7, 10))
    raw = att_stack.count() * att_stack.typ.dmg * f_att * f_def
    return max(1, raw.numerator // raw.denominator)


def apply_damage(st, D):
    """Возвращает число убитых существ."""
    before = st.count()
    if D < st.first:
        st.first -= D
    else:
        total = max(0, st.avail() - D)
        hp = st.typ.hp
        st.first, st.full = total % hp, total // hp
        if st.first == 0 and st.full >= 1:
            st.first, st.full = hp, st.full - 1
    return before - st.count()


class Battle:
    def __init__(self, n, m, impassable, stacks):
        self.n, self.m = n, m
        self.imp = set(impassable)
        self.stacks = stacks

    def occupied(self):
        return {s.pos: s for s in self.stacks if s.alive()}

    def reachable(self, st):
        """BFS по проходимым незанятым гексам, не более spd шагов; включает исходный гекс."""
        occ = self.occupied()
        occ.pop(st.pos, None)
        seen = {st.pos: 0}
        frontier = [st.pos]
        for step in range(st.typ.spd):
            nxt = []
            for p in frontier:
                for q in neighbours(*p):
                    if not (0 <= q[0] < self.m and 0 <= q[1] < self.n):
                        continue
                    if q in self.imp or q in occ or q in seen:
                        continue
                    seen[q] = step + 1
                    nxt.append(q)
            frontier = nxt
        return set(seen)

    def player_options(self, st):
        opts = [("defend",)]
        if not st.waited:
            opts.append(("wait",))
        reach = self.reachable(st)
        flt = getattr(self, "move_filter", None)
        for h in reach:
            if h != st.pos and (flt is None or flt(h)):
                opts.append(("move", h))
        lim = getattr(self, "attack_hex_limit", None)
        for e in self.stacks:
            if e.side == st.side or not e.alive():
                continue
            hs = sorted(h for h in reach if adjacent(h, e.pos))
            if lim is not None:
                hs = hs[:lim]
            for h in hs:
                opts.append(("attack", e, h))
        return opts

    def strike(self, a, b):
        """Удар a по b с ответным ударом. Возвращает ценность убитых у b."""
        D = damage(a, b)
        killed = apply_damage(b, D)
        b.killed += killed
        value = killed * b.typ.value
        if b.alive() and a.alive() and b.retal > 0:
            b.retal -= 1
            apply_damage(a, damage(b, a))
        return value

    def do(self, st, act):
        st.acted = True
        if act[0] == "defend":
            st.defbonus = max(1, st.typ.deff // 5)
            return 0
        if act[0] == "move":
            st.pos = act[1]
            return 0
        if act[0] == "attack":
            _, e, h = act
            st.pos = h
            return self.strike(st, e)
        raise ValueError(act)


def best_play(battle):
    """Максимальная ценность убитых врагов за один раунд против (‡), полный перебор."""
    order = sorted([s for s in battle.stacks if s.alive()],
                   key=lambda s: (-s.typ.spd, s.side, s.slot))
    return _search(battle, order, 0, 0)


def _snapshot(battle):
    return [s.clone() for s in battle.stacks]


def _restore(battle, snap):
    for s, c in zip(battle.stacks, snap):
        s.__dict__.update(c.__dict__)


def _search(battle, order, idx, phase):
    # phase 0: NORMAL; phase 1: WAIT
    while idx < len(order) and (not order[idx].alive() or order[idx].acted):
        idx += 1
    if idx == len(order):
        if phase == 0:
            waiters = sorted([s for s in battle.stacks if s.alive() and s.waited and not s.acted],
                             key=lambda s: (s.typ.spd, s.side, s.slot))
            return _search(battle, waiters, 0, 1)
        return 0
    st = order[idx]
    if st.side == 1:        # враг: (‡)
        if phase == 0:
            st.waited = True
            return _search(battle, order, idx + 1, phase)
        st.acted = True
        st.defbonus = max(1, st.typ.deff // 5)
        return _search(battle, order, idx + 1, phase)
    best = 0
    for act in battle.player_options(st):
        snap = _snapshot(battle)
        if act[0] == "wait":
            st.waited = True
            v = _search(battle, order, idx + 1, phase)
        else:
            v = battle.do(st, act) + _search(battle, order, idx + 1, phase)
        best = max(best, v)
        _restore(battle, snap)
    return best


def compositions(total_max, k):
    """Все векторы (c_1..c_k) >= 0 с суммой <= total_max."""
    def rec(i, left):
        if i == k:
            yield ()
            return
        for c in range(left + 1):
            for rest in rec(i + 1, left - c):
                yield (c,) + rest
    return rec(0, total_max)

# ----------------------------------------------------------------------------- C. теорема 1

def theorem1_instance(a):
    """PARTITION a_1..a_k -> экземпляр: одна строка, p_j = 5(j-1), E_j = 5(j-1)+1."""
    k = len(a)
    T2 = sum(a)
    assert T2 % 2 == 0
    T = T2 // 2
    m = 5 * (k - 1) + 2
    ptype = Type(att=1, deff=1, dmg=1, hp=1, spd=2)
    etypes = [Type(att=1, deff=1, dmg=1, hp=aj, spd=1, value=aj) for aj in a]
    return k, m, T, ptype, etypes


def check_theorem1():
    cases = []
    for k in (1, 2, 3):
        for a in product(range(1, 5), repeat=k):
            if sum(a) % 2 == 0:
                cases.append(a)
    for a in cases:
        k, m, T, ptype, etypes = theorem1_instance(a)
        partition_yes = any(sum(a[i] for i in S) == T
                            for r in range(k + 1) for S in combinations(range(k), r))
        best = 0
        for c in compositions(T, k):
            stacks = []
            for j in range(k):
                if c[j] > 0:
                    stacks.append(Stack(0, j, ptype, c[j], (5 * j, 0)))
            for j in range(k):
                stacks.append(Stack(1, j, etypes[j], 1, (5 * j + 1, 0)))
            best = max(best, best_play(Battle(1, m, [], stacks)))
        assert (best >= T) == partition_yes, (a, best, T, partition_yes)
    print(f"C. теорема 1: {len(cases)} экземпляров PARTITION, брутфорс совпал с ответом: OK")

# ----------------------------------------------------------------------------- D. теорема 4

def theorem4_instance(a, T):
    m3 = len(a)
    m = m3 // 3
    cols = 4 * m + 2
    spd = 4 * m + 12
    ptypes = [Type(att=1, deff=1, dmg=ai, hp=1, spd=spd) for ai in a]
    etype = Type(att=1, deff=1, dmg=1, hp=T, spd=1, value=1)
    enemies = [(4 * l + 2, 4) for l in range(m)]
    return m, cols, ptypes, etype, enemies


def three_partition_yes(a, T):
    m = len(a) // 3
    idx = list(range(len(a)))

    def rec(remaining):
        if not remaining:
            return True
        first = remaining[0]
        rest = remaining[1:]
        for pair in combinations(rest, 2):
            if a[first] + a[pair[0]] + a[pair[1]] == T:
                nxt = [i for i in rest if i not in pair]
                if rec(nxt):
                    return True
        return False
    return rec(idx)


def check_theorem4():
    # m = 1 и m = 2, малые числа; условие T/4 < a_i < T/2 соблюдено
    cases = []
    for T in range(5, 14):
        lo, hi = T // 4 + 1, (T - 1) // 2
        vals = list(range(lo, hi + 1))
        for a in product(vals, repeat=3):
            if sum(a) == T:
                cases.append((a, T))
    for T in range(6, 14):
        lo, hi = T // 4 + 1, (T - 1) // 2
        vals = list(range(lo, hi + 1))
        for a in product(vals, repeat=6):
            if sum(a) == 2 * T:
                cases.append((a, T))
    seen = set()
    n_checked = 0
    for a, T in cases:
        key = (tuple(sorted(a)), T)
        if key in seen:
            continue
        seen.add(key)
        m, cols, ptypes, etype, enemies = theorem4_instance(a, T)
        want = three_partition_yes(list(a), T)
        # распределение фиксировано (следствие 4.1): существо i в слот i; свободное — перестановки
        # не меняют множество достижимых исходов (все слоты достигают всех врагов), поэтому
        # для скорости перебираем только фиксированное распределение плюс одну перестановку.
        results = []
        for perm in (list(range(len(a))), list(reversed(range(len(a))))):
            stacks = [Stack(0, j, ptypes[perm[j]], 1, (j, 0)) for j in range(len(a))]
            for l, e in enumerate(enemies):
                stacks.append(Stack(1, l, etype, 1, e))
            b = Battle(6, cols, [], stacks)
            b.move_filter = lambda h: False      # чистые перемещения отключены (см. отчёт)
            b.attack_hex_limit = 2               # атака не более чем с двух гексов на цель
            # полная достижимость в стартовой позиции
            for s in stacks:
                if s.side == 0:
                    reach = b.reachable(s)
                    for e in stacks:
                        if e.side == 1:
                            assert any(adjacent(h, e.pos) for h in reach), "нет полной достижимости"
            results.append(best_play(b))
        got = max(results) >= m
        assert got == want, (a, T, results, want)
        n_checked += 1
        if not want:
            n_no = globals().setdefault("_n_no", 0) + 1
            globals()["_n_no"] = n_no
    print(f"D. теорема 4: {n_checked} экземпляров 3-PARTITION (m<=2, T<=13), из них "
          f"{globals().get('_n_no', 0)} без 3-разбиения; брутфорс совпал: OK")

# ----------------------------------------------------------------------------- B/E. теорема 3

def adapter(cfg, Y=2):
    """Три дорожки к чередующимся соседям E_S по моим шаблонам.

    cfg: список (column, side) для трёх заглушек, side in {'A','B'} (сверху/снизу),
    колонки кратны 6; возвращает (E_pos, [path1, path2, path3]) — path_i начинается в
    ячейке заглушки на строке 6Y-5 (A) или 6Y+5 (B).
    """
    r = 6 * Y
    cols = sorted(set(c for c, _ in cfg))

    def vert(c, y0, y1):
        step = 1 if y1 >= y0 else -1
        return [(c, y) for y in range(y0, y1 + step, step)]

    def horiz(y, x0, x1):
        step = 1 if x1 >= x0 else -1
        return [(x, y) for x in range(x0, x1 + step, step)]

    def refl(path):      # отражение относительно строки r (симметрия сетки)
        return [(x, 2 * r - y) for x, y in path]

    if len(cols) == 2:   # совпадающие колонки: (c, A), (c, B) и (c', s')
        c = [col for col in cols if sum(1 for cc, _ in cfg if cc == col) == 2][0]
        c2, s2 = [(cc, ss) for cc, ss in cfg if cc != c][0]
        pA = vert(c, r - 5, r - 1)
        pB = vert(c, r + 5, r + 1)
        if c2 > c:
            E = (c, r)
            p3 = (vert(c2, r - 5, r) if s2 == 'A' else vert(c2, r + 5, r)) + horiz(r, c2 - 1, c + 1)
        else:
            E = (c - 1, r)
            p3 = (vert(c2, r - 5, r) if s2 == 'A' else vert(c2, r + 5, r)) + horiz(r, c2 + 1, c - 2)
        return E, [pA, pB, p3]
    (c1, s1), (c2, s2), (c3, s3) = sorted(cfg)
    if s2 == 'B':        # отразить, решить, отразить обратно
        flipped = [(c1, 'B' if s1 == 'A' else 'A'), (c2, 'A'), (c3, 'B' if s3 == 'A' else 'A')]
        E, paths = adapter(flipped, Y)
        return E, [refl(p) for p in paths]
    # s2 == 'A': заглушка 2 -> рукав N в колонке c2
    p2 = vert(c2, r - 5, r - 1)
    if s1 == 'B':
        E = (c2, r)
        p1 = vert(c1, r + 5, r + 3) + horiz(r + 3, c1 + 1, c2) + vert(c2, r + 2, r + 1)
        p3 = (vert(c3, r - 5, r) if s3 == 'A' else vert(c3, r + 5, r)) + horiz(r, c3 - 1, c2 + 1)
    elif s3 == 'B':      # s1 == 'A', s3 == 'B': T смотрит на запад, E = (c2-1, r)
        E = (c2 - 1, r)
        p3 = vert(c3, r + 5, r + 3) + horiz(r + 3, c3 - 1, c2) + vert(c2, r + 2, r + 1)
        p1 = vert(c1, r - 5, r) + horiz(r, c1 + 1, c2 - 2)
    else:                # AAA
        E = (c2, r)
        p1 = (vert(c1, r - 5, r - 3) + horiz(r - 3, c1 - 1, c1 - 2) + vert(c1 - 2, r - 2, r + 3)
              + horiz(r + 3, c1 - 1, c2) + vert(c2, r + 2, r + 1))
        p3 = vert(c3, r - 5, r) + horiz(r, c3 - 1, c2 + 1)
    return E, [p1, p2, p3]


def check_adapter(cfg):
    E, paths = adapter(cfg)
    ends = [p[-1] for p in paths]
    # концы — три попарно несмежных соседа E
    for e in ends:
        assert adjacent(e, E), (cfg, e, E)
    for a, b in combinations(ends, 2):
        assert not adjacent(a, b), (cfg, a, b)
    # дорожки связны
    for p in paths:
        for a, b in zip(p, p[1:]):
            assert adjacent(a, b), (cfg, a, b)
    # попарная несмежность дорожек; E не смежен ни с чем, кроме концов
    for p, q in combinations(paths, 2):
        for a in p:
            for b in q:
                assert not adjacent(a, b) and a != b, (cfg, a, b)
    for p in paths:
        for a in p[:-1]:
            assert not adjacent(a, E), (cfg, a)
    # всё внутри приватной зоны: строки [6Y-5, 6Y+5], колонки [c_min-2, c_max]
    cmin = min(c for c, _ in cfg)
    cmax = max(c for c, _ in cfg)
    for p in paths:
        for (x, y) in p:
            assert 12 - 5 <= y <= 12 + 5 and cmin - 2 <= x <= cmax, (cfg, x, y)
    return E, paths


def check_adapters():
    n = 0
    for sides in product('AB', repeat=3):
        cfg = [(6, sides[0]), (12, sides[1]), (18, sides[2])]
        check_adapter(cfg)
        n += 1
    for s3 in 'AB':
        check_adapter([(12, 'A'), (12, 'B'), (18, s3)])
        check_adapter([(12, 'A'), (12, 'B'), (6, s3)])
        n += 2
    print(f"B. адаптеры теоремы 3: {n} конфигураций, несмежность и чередование: OK")


def _vline(x, y0, y1):
    return {(x, y) for y in range(min(y0, y1), max(y0, y1) + 1)}


def _hline(y, x0, x1):
    return {(x, y) for x in range(min(x0, x1), max(x0, x1) + 1)}


def theorem3_instances():
    """Две крошечные планарные X3C с явной ручной укладкой (масштаб 6, см. отчёт §T3.4).

    yes: X={0..5}, C=[S0={0,1,2}, S1={3,4,5}, S2={2,3,4}]  -> покрытие {S0,S1}.
    no : X={0..5}, C=[S0={0,1,2}, S2={2,3,4}, S3={1,2,5}]  -> покрытия нет.
    Возвращает список (tag, X, C, trees, E, deploy).
    """
    out = []
    # ---------------- yes
    X = list(range(6))
    C = [(0, 1, 2), (3, 4, 5), (2, 3, 4)]
    tr = {x: set() for x in X}
    tr[0] |= _vline(6, 0, 1)
    tr[1] |= _vline(12, 0, 1)
    tr[2] |= _hline(0, 18, 24) | _vline(18, 0, 1) | _vline(24, 0, 13)
    tr[3] |= _hline(36, 30, 48) | _vline(30, 23, 36) | _vline(48, 23, 36)
    tr[4] |= _hline(42, 24, 54) | _vline(24, 23, 42) | _vline(54, 23, 42)
    tr[5] |= _vline(60, 23, 36)
    sets = {0: ([(6, 'A'), (12, 'A'), (18, 'A')], 1, {(6, 'A'): 0, (12, 'A'): 1, (18, 'A'): 2}),
            2: ([(24, 'A'), (24, 'B'), (30, 'B')], 3, {(24, 'A'): 2, (24, 'B'): 4, (30, 'B'): 3}),
            1: ([(48, 'B'), (54, 'B'), (60, 'B')], 3, {(48, 'B'): 3, (54, 'B'): 4, (60, 'B'): 5})}
    E = {}
    for S, (cfg, Y, owner) in sets.items():
        Epos, paths = adapter(cfg, Y)
        E[S] = Epos
        for p in paths:
            c0, y0 = p[0]
            side = 'A' if y0 == 6 * Y - 5 else 'B'
            tr[owner[(c0, side)]].update(p)
    deploy = {0: (6, 0), 1: (12, 0), 2: (21, 0), 3: (39, 36), 4: (40, 42), 5: (60, 36)}
    out.append(("yes", X, C, tr, E, deploy))
    # ---------------- no
    X = list(range(6))
    C = [(0, 1, 2), (2, 3, 4), (1, 2, 5)]
    tr = {x: set() for x in X}
    tr[0] |= _vline(6, 6, 7)
    tr[1] |= _hline(0, 12, 84) | _vline(12, 0, 7) | _vline(84, 0, 19)
    tr[2] |= _hline(6, 18, 30) | _vline(18, 6, 7) | _vline(24, 6, 19) | _vline(30, 6, 19)
    tr[3] |= _vline(12, 29, 36)
    tr[4] |= _vline(18, 29, 36)
    tr[5] |= _vline(60, 29, 36)
    sets = {0: ([(6, 'A'), (12, 'A'), (18, 'A')], 2, {(6, 'A'): 0, (12, 'A'): 1, (18, 'A'): 2}),
            1: ([(12, 'B'), (18, 'B'), (24, 'A')], 4, {(12, 'B'): 3, (18, 'B'): 4, (24, 'A'): 2}),
            2: ([(30, 'A'), (60, 'B'), (84, 'A')], 4, {(30, 'A'): 2, (60, 'B'): 5, (84, 'A'): 1})}
    E = {}
    for S, (cfg, Y, owner) in sets.items():
        Epos, paths = adapter(cfg, Y)
        E[S] = Epos
        for p in paths:
            c0, y0 = p[0]
            side = 'A' if y0 == 6 * Y - 5 else 'B'
            tr[owner[(c0, side)]].update(p)
    deploy = {0: (6, 6), 1: (48, 0), 2: (27, 6), 3: (12, 36), 4: (18, 36), 5: (60, 36)}
    out.append(("no", X, C, tr, E, deploy))
    return out


def check_theorem3():
    for tag, X, C, trees, E, deploy in theorem3_instances():
        passable = set()
        for x in X:
            passable |= trees[x]
        for x, y in combinations(X, 2):
            for a in trees[x]:
                for b in trees[y]:
                    assert a != b and not adjacent(a, b), (tag, x, y, a, b)
        for S, Epos in E.items():
            assert Epos not in passable
            nb = [q for q in neighbours(*Epos) if q in passable]
            assert len(nb) == 3, (tag, S, nb)
            owners = set()
            for q in nb:
                for x in X:
                    if q in trees[x]:
                        owners.add(x)
            assert owners == set(C[S]), (tag, S, owners, C[S])
            for a, b in combinations(nb, 2):
                assert not adjacent(a, b)
        for S1, S2 in combinations(E, 2):
            assert not adjacent(E[S1], E[S2])
        maxx = max(p[0] for p in passable) + 2
        maxy = max(p[1] for p in passable) + 2
        allhex = {(x, y) for x in range(maxx) for y in range(maxy)}
        impassable = allhex - passable - set(E.values())
        q = len(X) // 3
        ptype = Type(att=1, deff=1, dmg=1, hp=2, spd=maxx * maxy)
        etype = Type(att=1, deff=29, dmg=1, hp=3, spd=1, value=1)
        cover = any(sorted(sum((list(C[S]) for S in comb), [])) == X
                    for comb in combinations(range(len(C)), q))
        enemy_hexes = set(E.values())

        def battle_for(c):
            stacks = [Stack(0, j, ptype, c[j], deploy[x]) for j, x in enumerate(X) if c[j] > 0]
            for S, Epos in E.items():
                stacks.append(Stack(1, S, etype, 1, Epos))
            b = Battle(maxy, maxx, impassable, stacks)
            b.move_filter = lambda h: any(adjacent(h, e) for e in enemy_hexes)
            return b
        best_fixed = best_play(battle_for((1,) * 6))
        assert (best_fixed >= q) == cover, (tag, best_fixed, cover)
        for c in [(6, 0, 0, 0, 0, 0), (3, 3, 0, 0, 0, 0), (2, 1, 1, 1, 1, 0), (2, 2, 2, 0, 0, 0),
                  (0, 1, 1, 1, 1, 1), (1, 1, 1, 0, 1, 1), (1, 1, 2, 1, 1, 0)]:
            v = best_play(battle_for(c))
            assert v < q, (tag, c, v)
        print(f"E. теорема 3 / следствие 3.1, экземпляр '{tag}' ({maxx}x{maxy}): cover={cover}, "
              f"оптимум при (1,...,1)={best_fixed}, все пробные неравномерные распределения < q: OK")


def check_lemma32():
    mu = Fraction(3, 10)

    def D(c):
        return max(1, (mu * c).numerator // (mu * c).denominator)
    for r in range(1, 5):
        for cs in product(range(1, 12), repeat=r):
            if sum(D(c) for c in cs) >= 3:
                assert sum(cs) >= 3
                if sum(cs) == 3:
                    assert r == 3 and cs == (1, 1, 1)
    print("Lemma 3.2 (mu=0.3, c<=11, r<=4): OK")


if __name__ == "__main__":
    check_hex_facts()
    check_lemma32()
    check_adapters()
    check_theorem1()
    check_theorem4()
    check_theorem3()
