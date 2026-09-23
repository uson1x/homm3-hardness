"""Рендер одного поля конструкции Теоремы 3 (q=1, C={X}) в ASCII для отчёта."""
import random
from t3_x3c import draw, build, verify_invariants
X = [0, 1, 2]; C = [frozenset(X)]
rng = random.Random(7)
vertices = [("e", e) for e in X] + [("s", 0)]
edges = [(("e", e), ("s", 0)) for e in X]
pos, paths = draw(vertices, edges, 3, 3, rng)
board, p_hex, z_hex, dock = build(X, C, pos, paths)
verify_invariants(board, X, C, p_hex, z_hex, dock)
mark = {}
for e, h in p_hex.items(): mark[h] = "P"
for v, h in z_hex.items(): mark[h] = "Z"
for (v, e), h in dock.items(): mark[h] = "d"
xs = [x for (x, y) in board._nb if board.passable((x, y))]; ys = [y for (x, y) in board._nb if board.passable((x, y))]
x0, x1, y0, y1 = min(xs) - 1, max(xs) + 1, min(ys) - 1, max(ys) + 1
out = []
for y in range(y0, y1 + 1):
    row = (" " if y % 2 == 0 else "") + " ".join(mark.get((x, y), "." if board.passable((x, y)) else "#") for x in range(x0, x1 + 1))
    out.append(row)
print("\n".join(out))
print("pos:", pos)
