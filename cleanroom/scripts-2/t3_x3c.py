"""
Теорема 3 (клин-рум, deriver-2): собственная конструкция сведения PLANAR-X3C -> ARMY-ALLOCATION с
одним типом, и её брутфорс-проверка на малых инстансах.

Конструкция G_3(X, C):
  * инцидентный граф (элементы e ∈ X, множества S ∈ C, рёбра e–S при e ∈ S); ортогональное рисование
    на целочисленной сетке (здесь -- рандомизированным поиском, в доказательстве -- цитируемый алгоритм
    для планарных графов степени <= 4);
  * масштаб λ = 12: точка (X, Y) -> гекс (12X + 10, 12Y + 10) (ряды центров чётные);
  * рёбра -> коридоры ширины 1 вдоль рядов/столбцов гекс-сетки;
  * set-вершина S -> коробка 9x9 с врагом z_S в центре и адаптером (adapters2.json) от портов к трём
    чередующимся докингам;
  * element-вершина e -> гекс p_e в центре, прямые рукава от портов к центру;
  * всё остальное -- препятствия.
  * Игрок: один тип P (att 1, def 1, dmg 1, hp 2, spd = число гексов), запас 3q; враг Q (att 1,
    def 21, dmg 1, hp 3, spd 1, value 1) по одному существу в каждом z_S; R = 1, W = q.
    D(c) = max(1, floor(c/2)): 1,1,1,2,2,3,...

Проверки: инварианты I1/I2, гиперграф досягаемости == инцидентность, игра == X3C.
"""
import sys, random, json, itertools
from collections import deque
from engine2 import Board, CType, Game, static_reach, adjacent, all_allocations

LAM = 12; OFF = 10; RB = 4
DIRS = {"U": (0, -1), "D": (0, 1), "L": (-1, 0), "R": (1, 0)}
ADAPTERS = json.load(open(__file__.rsplit("/", 1)[0] + "/adapters2.json"))

# ------------------------------------------------------------ ортогональное рисование (поиск)
def draw(vertices, edges, W, H, rng, attempts=400):
    """Пытается разместить вершины в точках сетки WxH и провести рёбра как внутренне непересекающиеся
    ортогональные пути, по одному ребру на порт. Возвращает (pos, paths) или None."""
    for _ in range(attempts):
        pts = [(x, y) for x in range(W) for y in range(H)]
        rng.shuffle(pts)
        pos = {v: pts[i] for i, v in enumerate(vertices)}
        used = {p: "v" for p in pos.values()}
        ports = {v: set() for v in vertices}
        paths = {}
        order = list(edges); rng.shuffle(order)
        ok = True
        for (a, b) in order:
            pa, pb = pos[a], pos[b]
            # BFS по состояниям (точка, направление прихода)
            start = []
            for dn, (dx, dy) in DIRS.items():
                if dn in ports[a]:
                    continue
                q = (pa[0] + dx, pa[1] + dy)
                if 0 <= q[0] < W and 0 <= q[1] < H:
                    start.append((q, dn))
            rng.shuffle(start)
            prev = {}
            dq = deque()
            found = None
            for q, dn in start:
                if q == pb:
                    opp = {"U": "D", "D": "U", "L": "R", "R": "L"}[dn]
                    if opp in ports[b]:
                        continue
                    found = (q, dn); prev[(q, dn)] = None; break
                if q in used:
                    continue
                prev[(q, dn)] = None; dq.append((q, dn))
            while dq and found is None:
                q, dn = dq.popleft()
                dirs = list(DIRS.items()); rng.shuffle(dirs)
                for dn2, (dx, dy) in dirs:
                    q2 = (q[0] + dx, q[1] + dy)
                    if not (0 <= q2[0] < W and 0 <= q2[1] < H):
                        continue
                    if (q2, dn2) in prev:
                        continue
                    if q2 == pb:
                        opp = {"U": "D", "D": "U", "L": "R", "R": "L"}[dn2]
                        if opp in ports[b]:
                            continue
                        prev[(q2, dn2)] = (q, dn); found = (q2, dn2); break
                    if q2 in used:
                        continue
                    prev[(q2, dn2)] = (q, dn); dq.append((q2, dn2))
            if found is None:
                ok = False; break
            # восстановить путь
            path = []
            cur = found
            while cur is not None:
                path.append(cur[0]); cur = prev[cur]
            path.append(pa); path.reverse()
            for p in path[1:-1]:
                used[p] = "e"
            d0 = (path[1][0] - pa[0], path[1][1] - pa[1])
            d1 = (path[-2][0] - pb[0], path[-2][1] - pb[1])
            ports[a].add([k for k, v in DIRS.items() if v == d0][0])
            ports[b].add([k for k, v in DIRS.items() if v == d1][0])
            paths[(a, b)] = path
        if ok:
            return pos, paths
    return None

# ------------------------------------------------------------ сборка гекс-поля
def hex_of(pt):
    return (LAM * pt[0] + OFF, LAM * pt[1] + OFF)

def segment_hexes(h1, h2):
    (x1, y1), (x2, y2) = h1, h2
    assert x1 == x2 or y1 == y2
    if x1 == x2:
        return [(x1, y) for y in range(min(y1, y2), max(y1, y2) + 1)]
    return [(x, y1) for x in range(min(x1, x2), max(x1, x2) + 1)]

def build(X, C, pos, paths):
    """Возвращает (board, p_hex: e->hex, z_hex: S->hex, dock: (S,e)->hex)."""
    sets = list(C)
    passable = set()
    p_hex = {}; z_hex = {}; dock = {}
    for e in X:
        p_hex[e] = hex_of(pos[("e", e)])
    for i, S in enumerate(sets):
        z_hex[("s", i)] = hex_of(pos[("s", i)])
    # направления рёбер у set-вершин
    set_dirs = {("s", i): {} for i in range(len(sets))}
    for (a, b), path in paths.items():
        for v, other in ((a, b), (b, a)):
            if v[0] == "s":
                pv = pos[v]
                nxt = path[1] if path[0] == pv else path[-2]
                d = (nxt[0] - pv[0], nxt[1] - pv[1])
                dn = [k for k, vv in DIRS.items() if vv == d][0]
                set_dirs[v][dn] = other[1]  # элемент, приходящий с этой стороны
    # коридоры
    for (a, b), path in paths.items():
        hp = [hex_of(p) for p in path]
        for h1, h2 in zip(hp, hp[1:]):
            for h in segment_hexes(h1, h2):
                passable.add(h)
    # set-коробки: удалить внутренность, положить адаптер
    for v, dirs in set_dirs.items():
        cz = z_hex[v]
        assert len(dirs) == 3, ("set-вершина степени != 3", v, dirs)
        missing = [d for d in DIRS if d not in dirs][0]
        for dx in range(-RB, RB + 1):
            for dy in range(-RB, RB + 1):
                passable.discard((cz[0] + dx, cz[1] + dy))
        adp = ADAPTERS[missing]
        for port, ph in adp.items():
            e = dirs[port]
            for (dx, dy) in ph:
                passable.add((cz[0] + dx, cz[1] + dy))
            dock[(v, e)] = (cz[0] + ph[-1][0], cz[1] + ph[-1][1])
        passable.add(cz)
    for e in X:
        passable.add(p_hex[e])
    maxx = max(h[0] for h in passable) + 2; maxy = max(h[1] for h in passable) + 2
    obstacles = [(x, y) for y in range(maxy) for x in range(maxx) if (x, y) not in passable]
    board = Board(maxy, maxx, obstacles)
    return board, p_hex, z_hex, dock

def verify_invariants(board, X, C, p_hex, z_hex, dock):
    sets = list(C)
    zs = set(z_hex.values())
    # I1: проходимые соседи z_S -- ровно три докинга, попарно несмежные; z попарно несмежны
    for v, cz in z_hex.items():
        S = sets[v[1]]
        nb = [h for h in board.nb(cz) if board.passable(h)]
        docks = [dock[(v, e)] for e in S]
        assert sorted(nb) == sorted(docks), ("I1", v, nb, docks)
        for a, b in itertools.combinations(docks, 2):
            assert not adjacent(a, b), ("I1 докинги смежны", v)
        for v2, cz2 in z_hex.items():
            assert v2 == v or not adjacent(cz, cz2)
    # I2: компоненты проходимых гексов без z: ровно один p_e в каждой, смежные враги = {S ∋ e}
    seen = set()
    comp_of = {}
    for y in range(board.n_rows):
        for x in range(board.n_cols):
            h = (x, y)
            if not board.passable(h) or h in zs or h in seen:
                continue
            comp = set([h]); dq = deque([h]); seen.add(h)
            while dq:
                g = dq.popleft()
                for f in board.nb(g):
                    if board.passable(f) and f not in zs and f not in seen:
                        seen.add(f); comp.add(f); dq.append(f)
            ps = [e for e in X if p_hex[e] in comp]
            assert len(ps) == 1, ("I2: компонента с %d деплой-гексами" % len(ps))
            e = ps[0]
            adj_z = {}
            for g in comp:
                for f in board.nb(g):
                    if f in zs:
                        adj_z.setdefault(f, set()).add(g)
            want = {z_hex[("s", i)] for i, S in enumerate(sets) if e in S}
            assert set(adj_z) == want, ("I2: смежные враги", e, adj_z, want)
            for zh, gs in adj_z.items():
                assert len(gs) == 1, ("I2: два гекса подхода", e, zh, gs)
            comp_of[e] = comp
    return comp_of

def x3c_yes(X, C, q):
    sets = list(C)
    for combo in itertools.combinations(range(len(sets)), q):
        u = set()
        okk = True
        for i in combo:
            if u & sets[i]:
                okk = False; break
            u |= sets[i]
        if okk and len(u) == len(X):
            return True
    return False

def game_answer(board, X, C, p_hex, z_hex, allow_moves, allow_wait=True, alloc_filter=None):
    q = len(X) // 3
    nh = board.hex_count()
    P = CType("P", 1, 1, 1, 2, nh)
    Q = CType("Q", 1, 21, 1, 3, 1, value=1)
    sets = list(C)
    enemies = [(Q, 1, z_hex[("s", i)]) for i in range(len(sets))]
    slots = [p_hex[e] for e in X]
    best = 0; n_alloc = 0
    for alloc in all_allocations(len(X), 3 * q):
        if alloc_filter and not alloc_filter(alloc):
            continue
        ps = [(P, c, slots[i]) for i, c in enumerate(alloc) if c > 0]
        if not ps:
            continue
        n_alloc += 1
        g = Game(board, ps, enemies, allow_moves=allow_moves, allow_wait=allow_wait)
        v = g.best_value()
        best = max(best, v)
        if best >= q:
            return True, n_alloc
    return best >= q, n_alloc

def random_x3c(q, rng, nsets):
    X = list(range(3 * q))
    all3 = [frozenset(c) for c in itertools.combinations(X, 3)]
    rng.shuffle(all3)
    return X, all3[:nsets]

def random_x3c_no(q, rng, nsets):
    """no-инстансы: множества попарно пересекаются (при q=2 -- точного покрытия нет)."""
    X = list(range(3 * q))
    all3 = [frozenset(c) for c in itertools.combinations(X, 3)]
    for _ in range(1000):
        rng.shuffle(all3)
        C = []
        for S in all3:
            if all(S & T for T in C):
                C.append(S)
            if len(C) == nsets:
                break
        if len(C) == nsets and all(any(e in S for S in C) for e in X):
            return X, C
    return None

def run(q, nsets_choices, n_inst, seed, allow_moves, allow_wait=True, W=5, H=5, only_no=False):
    rng = random.Random(seed)
    done = 0; skipped = 0; yes = 0
    while done < n_inst:
        if only_no:
            r = random_x3c_no(q, rng, rng.choice(nsets_choices))
            if r is None:
                continue
            X, C = r
        else:
            X, C = random_x3c(q, rng, rng.choice(nsets_choices))
        # каждый элемент хотя бы в одном множестве и степени <= 4 (иначе тривиально/не рисуется)
        deg = {e: sum(e in S for S in C) for e in X}
        if any(d == 0 or d > 4 for d in deg.values()):
            continue
        vertices = [("e", e) for e in X] + [("s", i) for i in range(len(C))]
        edges = [(("e", e), ("s", i)) for i, S in enumerate(C) for e in S]
        dr = draw(vertices, edges, W, H, rng)
        if dr is None:
            skipped += 1; continue
        pos, paths = dr
        board, p_hex, z_hex, dock = build(X, C, pos, paths)
        verify_invariants(board, X, C, p_hex, z_hex, dock)
        reach = static_reach(board, [p_hex[e] for e in X], [z_hex[("s", i)] for i in range(len(C))], board.hex_count())
        want = [{i for i, S in enumerate(C) if e in S} for e in X]
        assert reach == want, ("reach != incidence", reach, want)
        gy, na = game_answer(board, X, C, p_hex, z_hex, allow_moves, allow_wait)
        xy = x3c_yes(X, C, q)
        assert gy == xy, ("T3 MISMATCH", X, [sorted(S) for S in C], gy, xy)
        done += 1; yes += xy
        print("  q=%d |C|=%d поле %dx%d ответ %s (распределений просмотрено %d)" % (q, len(C), board.n_rows, board.n_cols, xy, na), flush=True)
    print("T3: q=%d, %d инстансов OK (yes=%d), пропущено (рисование не найдено) %d; moves=%s wait=%s" % (q, done, yes, skipped, allow_moves, allow_wait), flush=True)

if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "q1"
    if which == "q1":
        run(1, [1], 3, 1, True, True, W=3, H=3)
    elif which == "q2":
        run(2, [2, 3, 4], int(sys.argv[2]) if len(sys.argv) > 2 else 6, int(sys.argv[3]) if len(sys.argv) > 3 else 2, False, True, W=5, H=5)
    elif which == "q2moves":
        run(2, [2, 3], 2, 3, "docking", True, W=5, H=5)
    elif which == "q2no":
        run(2, [3, 4], int(sys.argv[2]) if len(sys.argv) > 2 else 6, int(sys.argv[3]) if len(sys.argv) > 3 else 5, False, True, W=5, H=5, only_no=True)
    elif which == "q2nomoves":
        run(2, [3], 2, 6, "docking", True, W=5, H=5, only_no=True)
    elif which == "q2spec":
        # конкретные инстансы: 4 попарно пересекающихся множества (no) и 4 множества с покрытием (yes),
        # элемент степени 3-4
        specs = [
            ([0, 1, 2], [{0, 1, 2}, {0, 1, 3}, {0, 2, 4}, {1, 2, 5}], False),
            ([0, 1, 2], [{0, 1, 2}, {3, 4, 5}, {0, 3, 4}, {1, 2, 5}], True),
            ([0, 1, 2], [{0, 1, 3}, {0, 2, 4}, {1, 2, 5}, {3, 4, 5}], False),
        ]
        rng = random.Random(11)
        for _, Cs, want in specs:
            X = list(range(6)); C = [frozenset(S) for S in Cs]
            vertices = [("e", e) for e in X] + [("s", i) for i in range(len(C))]
            edges = [(("e", e), ("s", i)) for i, S in enumerate(C) for e in S]
            dr = None
            for (W, H, att) in [(6, 6, 2000), (8, 8, 4000), (10, 10, 8000)]:
                dr = draw(vertices, edges, W, H, rng, attempts=att)
                if dr:
                    break
            if dr is None:
                print("  рисование не найдено для", Cs, flush=True); continue
            pos, paths = dr
            board, p_hex, z_hex, dock = build(X, C, pos, paths)
            verify_invariants(board, X, C, p_hex, z_hex, dock)
            reach = static_reach(board, [p_hex[e] for e in X], [z_hex[("s", i)] for i in range(len(C))], board.hex_count())
            assert reach == [{i for i, S in enumerate(C) if e in S} for e in X]
            gy, na = game_answer(board, X, C, p_hex, z_hex, False, True)
            assert gy == want == x3c_yes(X, C, 2), ("SPEC MISMATCH", Cs, gy, want)
            print("  spec %s: поле %dx%d ответ %s (распределений %d) OK" % (Cs, board.n_rows, board.n_cols, gy, na), flush=True)
