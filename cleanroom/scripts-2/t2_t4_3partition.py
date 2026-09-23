"""
Теоремы 2 и 4, Corollary 4.1 / 4.2 (клин-рум проверка deriver-2) на малых инстансах 3-PARTITION.

Теорема 2 (конструкция статьи, увиденная в скетче): 3 ряда × (8m+2) столбцов, E_g в (8(g-1)+1, 1),
hp T, value 1, spd 1; три слота группы на трёх соседях E_g; тип C_i: dmg a_i, hp 5, spd 2, запас 1.
Здесь для каждого g я перебираю ВСЕ 20 троек соседей как деплой-гексы (адверсариально: любая тройка
должна работать, иначе формулировка "три из шести соседей" неточна).

Теорема 4 (моя конструкция): 6 рядов × (4m+2) столбцов, без препятствий; p_j = (j-1, 0), j=1..3m;
E_g = (4(g-1)+1, 5), hp T, value 1, spd 1; тип C_i: dmg a_i, hp 5, spd = число гексов, запас 1;
R = 1, W = m. Проверяется полная досягаемость при всех занятых слотах и ответ игры == 3-PARTITION;
Cor 4.2: hp-objective с порогом mT.

Перебор ходов: m = 1 -- все ходы; m = 2 -- ходы только на докинг-гексы (+WAIT, DEFEND, все атаки).
"""
import itertools, sys, math
from engine2 import Board, CType, Game, static_reach, adjacent

def three_partition_yes(a, m, T):
    idx = list(range(3 * m))
    def rec(rem):
        if not rem:
            return True
        first = rem[0]
        for pair in itertools.combinations(rem[1:], 2):
            if a[first] + a[pair[0]] + a[pair[1]] == T:
                rest = [i for i in rem if i != first and i not in pair]
                if rec(rest):
                    return True
        return False
    return rec(idx)

def gen_instances(m, T):
    lo = T // 4 + 1; hi = (T - 1) // 2
    vals = range(lo, hi + 1)
    for a in itertools.combinations_with_replacement(vals, 3 * m):
        if sum(a) == m * T:
            yield list(a)

# ---------------- Theorem 2
def t2_board(a, m, T, triple_choice):
    board = Board(3, 8 * m + 2)
    types = [CType("C%d" % i, 1, 1, a[i], 5, 2) for i in range(3 * m)]
    enemies = []; slots = []
    for g in range(m):
        X = 8 * g + 1
        eh = (X, 1)
        E = CType("E%d" % g, 1, 1, 1, T, 1, value=1)
        enemies.append((E, 1, eh))
        nbs = board.nb(eh)
        assert len(nbs) == 6
        tri = triple_choice[g]
        slots += [nbs[t] for t in tri]
    return board, types, slots, enemies

def check_t2(m, T, allow_moves):
    n_inst = 0
    triples = list(itertools.combinations(range(6), 3))
    for a in gen_instances(m, T):
        want = three_partition_yes(a, m, T)
        # геометрия: для всех выборов троек (при m=1 -- 20, при m=2 -- 20^2=400; ограничим)
        choices = itertools.product(triples, repeat=m) if m == 1 else [(t, t) for t in triples]
        for tc in choices:
            board, types, slots, enemies = t2_board(a, m, T, tc)
            reach = static_reach(board, slots, [e[2] for e in enemies], 2)
            for j, r in enumerate(reach):
                assert r == {j // 3}, ("T2 reach", a, tc, j, r)
        # игра: перебор распределений типов по слотам (стек 1 или пусто) -- все инъекции типов в слоты
        board, types, slots, enemies = t2_board(a, m, T, [(0, 2, 4)] * m)
        got = False
        for perm in itertools.permutations(range(3 * m)):
            ps = [(types[perm[s]], 1, slots[s]) for s in range(3 * m)]
            g = Game(board, ps, enemies, allow_moves=allow_moves)
            if g.best_value() >= m:
                got = True; break
        # частичные распределения (некоторые слоты пусты) не могут дать больше: не проверяем при m=2
        if m == 1:
            for sub in range(1, 3):
                for perm in itertools.permutations(range(3), sub):
                    ps = [(types[perm[s]], 1, slots[s]) for s in range(sub)]
                    if Game(board, ps, enemies, allow_moves=allow_moves).best_value() >= m:
                        got = True
        assert got == want, ("T2 MISMATCH", a, got, want)
        n_inst += 1
    return n_inst

# ---------------- Theorem 4
def t4_board(a, m, T):
    rows, cols = 6, 4 * m + 2
    board = Board(rows, cols)
    spd = rows * cols
    types = [CType("C%d" % i, 1, 1, a[i], 5, spd) for i in range(3 * m)]
    slots = [(j, 0) for j in range(3 * m)]
    enemies = [(CType("E%d" % g, 1, 1, 1, T, 1, value=1), 1, (4 * g + 1, 5)) for g in range(m)]
    return board, types, slots, enemies, spd

def check_t4(m, T, allow_moves):
    n_inst = 0
    for a in gen_instances(m, T):
        want = three_partition_yes(a, m, T)
        board, types, slots, enemies, spd = t4_board(a, m, T)
        reach = static_reach(board, slots, [e[2] for e in enemies], spd)
        assert all(r == set(range(m)) for r in reach), ("T4 complete reach", a, reach)
        got = False; got_hp = False
        for perm in itertools.permutations(range(3 * m)):
            ps = [(types[perm[s]], 1, slots[s]) for s in range(3 * m)]
            if not got and Game(board, ps, enemies, allow_moves=allow_moves).best_value() >= m:
                got = True
            if not got_hp and Game(board, ps, enemies, allow_moves=allow_moves, objective="hp").best_value() >= m * T:
                got_hp = True
            if got and got_hp:
                break
        assert got == want, ("T4 MISMATCH", a, got, want)
        assert got_hp == want, ("T4-hp MISMATCH", a, got_hp, want)
        n_inst += 1
    return n_inst

if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    if which in ("t2", "all"):
        for (m, T) in [(1, 7), (1, 9), (1, 11), (1, 13)]:
            print("T2 m=%d T=%d: %d инстансов OK (все ходы)" % (m, T, check_t2(m, T, True)))
        for (m, T) in [(2, 7), (2, 9)]:
            print("T2 m=%d T=%d: %d инстансов OK (ходы только на докинги)" % (m, T, check_t2(m, T, "docking")))
    if which in ("t4", "all"):
        for (m, T) in [(1, 7), (1, 9)]:
            print("T4 m=%d T=%d: %d инстансов OK (все ходы, kills + hp objective)" % (m, T, check_t4(m, T, True)), flush=True)
        for (m, T) in [(2, 7), (2, 9)]:
            print("T4 m=%d T=%d: %d инстансов OK (без ходов-без-атаки, kills + hp objective)" % (m, T, check_t4(m, T, False)), flush=True)
