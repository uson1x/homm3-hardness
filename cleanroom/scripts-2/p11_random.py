"""
Proposition 1.1 (адверсариальный рандом-тест deriver-2).

Гипотезы утверждения читаю максимально широко: ЛЮБОЕ поле (с препятствиями, несколько рядов), один тип
у игрока, (★) (att игрока = def врага), R = 1, (‡), одно существо на вражеский стек, и паросочетательная
структура досягаемости (статическая, при всех занятых слотах). Скорости врагов -- любые (медленнее,
равные, быстрее игрока), их урон -- любой (ретал может убивать существ игрока).

Проверяется: optimum игры (полный перебор распределений и ходов, включая WAIT и ходы без атаки)
== knapsack по врагам с весом w_j = ceil(hp_j / d) и ёмкостью B.
"""
import random, sys, math
from engine2 import Board, CType, Game, static_reach, all_allocations

def knapsack(weights, values, B):
    best = [0] * (B + 1)
    for w, v in zip(weights, values):
        if w > B:
            continue
        for b in range(B, w - 1, -1):
            best[b] = max(best[b], best[b - w] + v)
    return best[B]

KMAX = 3

def random_instance(rng):
    rows = rng.randint(1, 3); cols = rng.randint(3, 7 if KMAX > 3 else 6)
    cells = [(x, y) for y in range(rows) for x in range(cols)]
    k = rng.randint(1, KMAX)
    if len(cells) < 2 * k + 1:
        return None
    rng.shuffle(cells)
    slots = cells[:k]; ehex = cells[k:2 * k]
    rest = cells[2 * k:]
    obst = [h for h in rest if rng.random() < rng.choice([0.0, 0.2, 0.4, 0.6])]
    board = Board(rows, cols, obst)
    alpha = rng.randint(1, 30)
    d = rng.randint(1, 2)
    P = CType("P", alpha, rng.randint(1, 5), d, rng.randint(1, 4), rng.randint(1, 3))
    enemies = []
    for j in range(k):
        E = CType("E%d" % j, rng.randint(1, 30), alpha, rng.randint(1, 6), rng.randint(1, 5),
                  rng.randint(1, 4), value=rng.randint(0, 5))
        enemies.append((E, 1, ehex[j]))
    B = rng.randint(1, 6)
    return board, P, slots, enemies, B, d

def main():
    global KMAX
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    KMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    rng = random.Random(seed)
    tested = 0; skipped = 0; nontrivial = 0
    while tested < N:
        inst = random_instance(rng)
        if inst is None:
            continue
        board, P, slots, enemies, B, d = inst
        reach = static_reach(board, slots, [e[2] for e in enemies], P.spd)
        # паросочетание: каждый слот ровно один враг, каждый враг ровно один слот
        if any(len(r) != 1 for r in reach):
            skipped += 1; continue
        hit = [next(iter(r)) for r in reach]
        if len(set(hit)) != len(hit):
            skipped += 1; continue
        # перенумеруем врагов так, что слот j -> E_j
        enemies = [enemies[hit[j]] for j in range(len(slots))]
        weights = [math.ceil(e[0].hp / d) for e in enemies]
        values = [e[0].value for e in enemies]
        dp = knapsack(weights, values, B)
        best = 0
        for alloc in all_allocations(len(slots), B):
            ps = [(P, c, slots[i]) for i, c in enumerate(alloc) if c > 0]
            g = Game(board, ps, enemies)
            best = max(best, g.best_value())
        if best != dp:
            print("COUNTEREXAMPLE", board.n_rows, board.n_cols, sorted(board.obstacles), slots,
                  [(e[0].__dict__ if hasattr(e[0], '__dict__') else (e[0].att, e[0].dfn, e[0].dmg, e[0].hp, e[0].spd, e[0].value), e[2]) for e in enemies],
                  "P", (P.att, P.dfn, P.dmg, P.hp, P.spd), "B", B, "game", best, "dp", dp)
            return
        tested += 1
        if dp > 0 and any(w > 1 for w in weights):
            nontrivial += 1
    print("Prop 1.1: %d matching-инстансов (seed %d) -- game == knapsack везде; нетривиальных %d; отброшено (не паросочетание) %d"
          % (tested, seed, nontrivial, skipped))

if __name__ == "__main__":
    main()
