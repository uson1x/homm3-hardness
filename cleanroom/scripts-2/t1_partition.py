"""
Теорема 1 (клин-рум проверка deriver-2): сведение PARTITION -> ARMY-ALLOCATION на одном ряду.

Конструкция (моя запись): ряд из 5n гексов, p_j = 5(j-1), E_j на 5(j-1)+1; игрок: один тип,
dmg 1, hp 5, spd 2, att = def = 1, запас B; враг E_j: одно существо, hp = value = a_j, spd 1,
att = def = 1, dmg 1. R = 1, W = B.

Проверяем на ВСЕХ инстансах PARTITION с n <= 4 и a_i <= 6 (Σ чётна):
  * структура досягаемости при всех занятых слотах -- паросочетание j -> E_j;
  * ответ игры (полный перебор распределений и ходов, включая WAIT и пустые ходы) == ответ PARTITION.
"""
import itertools, sys
from engine2 import Board, CType, Game, static_reach, all_allocations

def build(a):
    n = len(a); B = sum(a) // 2
    board = Board(1, 5 * n)
    P = CType("P", 1, 1, 1, 5, 2)
    slots = [(5 * j, 0) for j in range(n)]
    enemies = []
    for j in range(n):
        Ej = CType("E%d" % j, 1, 1, 1, a[j], 1, value=a[j])
        enemies.append((Ej, 1, (5 * j + 1, 0)))
    return board, P, slots, B, enemies

def partition_yes(a):
    B2 = sum(a)
    if B2 % 2:
        return False
    n = len(a)
    for mask in range(1 << n):
        if sum(a[i] for i in range(n) if mask >> i & 1) * 2 == B2:
            return True
    return False

def game_yes(a, allow_moves=True):
    board, P, slots, B, enemies = build(a)
    for alloc in all_allocations(len(a), B):
        ps = [(P, c, slots[i]) for i, c in enumerate(alloc) if c > 0]
        g = Game(board, ps, enemies, allow_moves=allow_moves)
        if g.best_value() >= B:
            return True
    return False

def main():
    maxn = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    maxa = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    tested = 0; yes = 0
    for n in range(1, maxn + 1):
        for a in itertools.product(range(1, maxa + 1), repeat=n):
            if sum(a) % 2:
                continue
            if list(a) != sorted(a):
                continue  # симметрия
            board, P, slots, B, enemies = build(a)
            reach = static_reach(board, slots, [e[2] for e in enemies], P.spd)
            assert reach == [{j} for j in range(n)], (a, reach)
            py = partition_yes(list(a)); gy = game_yes(list(a))
            assert py == gy, ("MISMATCH", a, py, gy)
            tested += 1; yes += py
    print("Theorem 1: %d инстансов PARTITION (n<=%d, a<=%d) -- все совпали; yes=%d" % (tested, maxn, maxa, yes))

if __name__ == "__main__":
    main()
