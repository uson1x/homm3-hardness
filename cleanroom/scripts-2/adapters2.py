"""
Поиск адаптеров для set-вершин в моей конструкции Теоремы 3 (deriver-2).

Коробка (2r+1)x(2r+1) с центром z = (0,0) (ряд центра ЧЁТНЫЙ в абсолютных координатах, поэтому
чётность относительной координаты y совпадает с абсолютной). Порты -- середины сторон: U=(0,-r),
D=(0,r), L=(-r,0), R=(r,0); коридор продолжается наружу ещё на 2 гекса по прямой. Докинги -- одна из
двух чередующихся троек соседей z. Нужны три пути порт -> докинг, такие что:
  * гексы разных путей попарно не смежны и не совпадают;
  * ни один гекс пути, кроме докинга, не смежен с z;
  * пути внутри коробки (кроме внешних продолжений), не проходят через z.
Все остальные гексы коробки -- препятствия. Для каждого из 4 наборов направлений (какой порт не
используется) ищем шаблон; выводим ASCII и словарь pattern[missing] = {port: [hexes]}.
"""
import sys
from engine2 import adjacent

R = 4

def nbrs(h):
    x, y = h
    if y % 2 == 0:
        return [(x-1, y), (x+1, y), (x, y-1), (x+1, y-1), (x, y+1), (x+1, y+1)]
    return [(x-1, y), (x+1, y), (x-1, y-1), (x, y-1), (x-1, y+1), (x, y+1)]

Z = (0, 0)
ZN = set(nbrs(Z))
PORTS = {"U": (0, -R), "D": (0, R), "L": (-R, 0), "R": (R, 0)}
OUTSIDE = {"U": [(0, -R-2), (0, -R-1)], "D": [(0, R+2), (0, R+1)],
           "L": [(-R-2, 0), (-R-1, 0)], "R": [(R+2, 0), (R+1, 0)]}  # от дальнего к ближнему
# соседи z при чётном ряде: L(-1,0), TL(0,-1), TR(1,-1), R(1,0), BR(1,1), BL(0,1)
TRIPLES = [[(-1, 0), (1, -1), (1, 1)], [(0, -1), (1, 0), (0, 1)]]

def in_box(h):
    return abs(h[0]) <= R and abs(h[1]) <= R

def touches(h, S):
    return h in S or any(adjacent(h, s) for s in S)

def find_paths(ports, dock_assign, maxlen):
    """ports: список имён; dock_assign: список докингов в том же порядке. Поиск DFS с ограничением
    суммарной длины. Возвращает список путей (списки гексов: outside + порт ... докинг) или None."""
    best = [None]
    def route(idx, used_hexes, acc):
        if idx == len(ports):
            best[0] = list(acc); return True
        name = ports[idx]; dock = dock_assign[idx]
        start = PORTS[name]
        outside = OUTSIDE[name]
        forbidden = set(used_hexes)  # гексы предыдущих путей и их соседи
        # DFS от порта к докингу
        def dfs(path, visited):
            h = path[-1]
            if len(path) > maxlen:
                return False
            if h == dock:
                full = outside + path
                # проверка: ни один гекс кроме докинга не смежен с z
                if any(g in ZN for g in full[:-1]):
                    return False
                # расширяем used
                new_used = set(used_hexes)
                for g in full:
                    new_used.add(g)
                    new_used.update(nbrs(g))
                acc.append(full)
                if route(idx + 1, new_used, acc):
                    return True
                acc.pop()
                return False
            for g in nbrs(h):
                if g in visited or g == Z or not in_box(g) or g in forbidden:
                    continue
                if g != dock and g in ZN:
                    continue
                if any(adjacent(g, o) for o in outside) and g != start:
                    # не приближаться к внешнему коридору, кроме как через порт
                    pass
                visited.add(g); path.append(g)
                if dfs(path, visited):
                    return True
                path.pop(); visited.discard(g)
            return False
        if start in forbidden:
            return False
        return dfs([start], {start})
    # начальные used: внешние продолжения всех используемых портов + их соседи (кроме самих портов)
    used0 = set()
    for name in ports:
        for o in OUTSIDE[name]:
            used0.add(o)
            for g in nbrs(o):
                if g != PORTS[name]:
                    used0.add(g)
    # но собственный порт должен быть разрешён для своего пути: обрабатываем через forbidden = used0 минус свой порт
    # (проще: убираем порты из used0, и запрещаем чужим путям касаться чужих портов через соседей)
    for name in ports:
        used0.discard(PORTS[name])
    ok = route(0, used0, [])
    return best[0] if ok else None

def check(paths):
    """Независимая проверка инвариантов найденного шаблона."""
    allh = [set(p) for p in paths]
    for i in range(len(paths)):
        for j in range(i + 1, len(paths)):
            for a in allh[i]:
                for b in allh[j]:
                    assert a != b and not adjacent(a, b), ("касание", i, j, a, b)
    for p in paths:
        for g in p[:-1]:
            assert g not in ZN, ("лишний сосед z", g)
        assert p[-1] in ZN
        for a, b in zip(p, p[1:]):
            assert adjacent(a, b), ("разрыв", a, b)
    docks = [p[-1] for p in paths]
    assert sorted(docks) in [sorted(t) for t in TRIPLES]

def render(paths):
    grid = {}
    for y in range(-R-2, R+3):
        for x in range(-R-2, R+3):
            grid[(x, y)] = "#" if in_box((x, y)) else " "
    for k, p in enumerate(paths):
        for g in p:
            grid[g] = str(k + 1)
    grid[Z] = "Z"
    lines = []
    for y in range(-R-2, R+3):
        row = (" " if y % 2 == 0 else "") + " ".join(grid[(x, y)] for x in range(-R-2, R+3))
        lines.append(row)
    return "\n".join(lines)

def main():
    import itertools
    result = {}
    for missing in ["U", "D", "L", "R"]:
        ports = [p for p in ["U", "D", "L", "R"] if p != missing]
        found = None
        for maxlen in range(6, 16):
            for tri in TRIPLES:
                for perm in itertools.permutations(tri):
                    paths = find_paths(ports, list(perm), maxlen)
                    if paths:
                        found = (ports, paths); break
                if found: break
            if found: break
        assert found, "нет адаптера для missing=" + missing
        ports, paths = found
        check(paths)
        result[missing] = {ports[i]: paths[i] for i in range(3)}
        print("=== без порта", missing, "порты", ports, "докинги", [p[-1] for p in paths])
        print(render(paths))
    return result

if __name__ == "__main__":
    res = main()
    import json
    json.dump({k: {p: v for p, v in d.items()} for k, d in res.items()}, open("adapters2.json", "w"))
    print("сохранено adapters2.json")
