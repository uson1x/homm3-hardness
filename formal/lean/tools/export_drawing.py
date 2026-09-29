#!/usr/bin/env python3
"""Export the orthogonal drawings behind Lemma D.4's boards as Lean `OrthoDrawing` literals.

Session 5, targets 1 and 5.  `embed_lemma.build_board_lemma` computes, for each family of
`verify_embedding.corpus()`, the graph `G'` of step 1 and its orthogonal drawing (steps 2-3,
`planar_embed.orthogonal_drawing`), but returns only the board.  This script replays steps 0-3
exactly as `build_board_lemma` does (same deduplication, same `planar_embed.planarity` rotation,
same node and edge order, same drawing call), and asserts that the replayed drawing IS the one
behind the board: the scaled vertex centres equal `inst["features"]["boxes"]` and the scaled route
corner chains equal `inst["features"]["corridors"]`.  Read-only imports; nothing under `homm3/` is
written.

The drawing is shifted so that its bounding box starts at the origin (step 4 subtracts
`i_min, j_min`); `gw, gh` are the bounding-box sides, so the board is `(20 gw - 7) x (20 gh - 7)`,
which the script asserts against the board's `width, height`.  Routes are expanded to unit steps
(`planar_embed._expand`).  Vertex kinds: `("s", si)` -> `.set si`, `("e", e, i)` -> `.elem e i`;
edges keep `build_board_lemma`'s orientation (element vertex first).

For target 5 it also records the board's dockings `(g, e, x, y)` in the order of `sets[g]`.

Output: `CrossCheckDrawingData.lean`, the check modules `CrossCheckDrawingA`-`D.lean` and the
umbrella `CrossCheckDrawing.lean`; a JSON summary on stdout.

Run from formal/lean:  PYTHONDONTWRITEBYTECODE=1 python3 tools/export_drawing.py
"""

from __future__ import annotations

import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN_ROOT = os.path.dirname(HERE)
SCRIPTS = os.path.normpath(os.path.join(LEAN_ROOT, "..", "..", "scripts"))  # artifact root/scripts
sys.path.insert(0, SCRIPTS)
sys.dont_write_bytecode = True

import planar_embed  # noqa: E402
import verify_embedding as VE  # noqa: E402
from embed_lemma import build_board_lemma, LAMBDA, OMEGA  # noqa: E402

PARTS = 4


def replay(n_elements, sets):
    """Steps 0-3 of build_board_lemma, verbatim, returning (sets, meta_of, gp_edges, drawing)."""
    cleaned = [tuple(s) for s in sets]
    seen, dedup = set(), []
    for s in cleaned:
        key = tuple(sorted(s))
        if key not in seen:
            seen.add(key)
            dedup.append(s)
    sets = dedup
    n_g = n_elements + len(sets)
    g_edges = [(e, n_elements + si) for si, s in enumerate(sets) for e in s]
    rotation = planar_embed.planarity(n_g, g_edges)
    assert rotation is not None
    node_of, meta_of = {}, []

    def add(key):
        node_of[key] = len(meta_of)
        meta_of.append(key)

    for si in range(len(sets)):
        add(("s", si))
    inc_order = {e: [nb - n_elements for nb in rotation[e]] for e in range(n_elements)}
    for e in range(n_elements):
        for i in range(len(inc_order[e])):
            add(("e", e, i))
    gp_edges = []
    for e in range(n_elements):
        for i, si in enumerate(inc_order[e]):
            gp_edges.append((node_of[("e", e, i)], node_of[("s", si)]))
        for i in range(len(inc_order[e]) - 1):
            gp_edges.append((node_of[("e", e, i)], node_of[("e", e, i + 1)]))
    drawing = planar_embed.orthogonal_drawing(len(meta_of), gp_edges)
    assert drawing is not None
    assert not planar_embed.validate_drawing(len(meta_of), gp_edges, drawing)
    return sets, meta_of, gp_edges, drawing


def lean_drawing(name, meta_of, gp_edges, drawing):
    pts = list(drawing["pos"].values())
    for r in drawing["routes"].values():
        pts.extend(r)
    i0 = min(p[0] for p in pts)
    j0 = min(p[1] for p in pts)
    gw = max(p[0] for p in pts) - i0 + 1
    gh = max(p[1] for p in pts) - j0 + 1
    kinds = []
    for key in meta_of:
        kinds.append(f".set {key[1]}" if key[0] == "s" else f".elem {key[1]} {key[2]}")
    pos = [(drawing["pos"][v][0] - i0, drawing["pos"][v][1] - j0) for v in range(len(meta_of))]
    edges = []
    for (u, v) in gp_edges:
        r = [(x - i0, y - j0) for (x, y) in planar_embed._expand(drawing["routes"][(u, v)])]
        edges.append(f"⟨{u}, {v}, [" + ", ".join(f"({x}, {y})" for x, y in r) + "]⟩")
    txt = (f"def {name} : OrthoDrawing where\n  gw := {gw}\n  gh := {gh}\n"
           f"  kind := [{', '.join(kinds)}]\n"
           f"  pos := [{', '.join(f'({x}, {y})' for x, y in pos)}]\n"
           f"  edges := [\n    " + ",\n    ".join(edges) + "]\n")
    return txt, gw, gh, (i0, j0)


def main():
    t0 = time.time()
    fams = VE.corpus()
    boards = []
    for fi, (n, sets) in enumerate(fams):
        kind, inst = build_board_lemma(n, sets)
        if kind != "board":
            continue
        sets2, meta_of, gp_edges, drawing = replay(n, sets)
        assert [tuple(s) for s in inst["sets"]] == [tuple(s) for s in sets2]
        # the replayed drawing is the one behind the board
        pts = list(drawing["pos"].values())
        for r in drawing["routes"].values():
            pts.extend(r)
        i_min = min(p[0] for p in pts)
        j_min = min(p[1] for p in pts)

        def phi(p):
            return (LAMBDA * (p[0] - i_min) + OMEGA, LAMBDA * (p[1] - j_min) + OMEGA)

        feats = inst["features"]
        assert {v: phi(p) for v, p in drawing["pos"].items()} == feats["boxes"]
        assert {e: tuple(phi(p) for p in r) for e, r in drawing["routes"].items()} == \
            feats["corridors"]
        i = len(boards)
        txt, gw, gh, off = lean_drawing(f"d{i:02d}", meta_of, gp_edges, drawing)
        W, H = inst["width"], inst["height"]
        assert (W, H) == (20 * gw - 7, 20 * gh - 7), (W, H, gw, gh)
        docks = []
        for g, s in enumerate(inst["sets"]):
            for e in s:
                h = inst["dockings"][(g, e)]
                docks.append((g, e, h % W, h // W))
        boards.append({"i": i, "family": fi, "txt": txt, "gw": gw, "gh": gh, "W": W, "H": H,
                       "V": len(meta_of), "E": len(gp_edges), "docks": docks,
                       "unit": sum(len(planar_embed._expand(r)) - 1
                                   for r in drawing["routes"].values()),
                       "free": len(inst["owner"]), "offset": off})

    data = ["import CrossCheckLemmaData", "import Homm3.EmbedCheck", "import Homm3.Step1", "",
            "/-!", "# Session 5, targets 1 and 5. The drawings behind Lemma D.4's boards, as data", "",
            "Generated by `tools/export_drawing.py`: for the `NN`-th corpus family that yields a",
            "board, `dNN` is the orthogonal drawing of `G'` that `embed_lemma.build_board_lemma`",
            "computes (steps 0-3 replayed and asserted equal to the board's recorded features),",
            "shifted to the origin, routes in unit steps; `kNN` the board's dockings `(g, e, x, y)`.",
            "The instance is `LemmaData.qNN`, `LemmaData.CNN`, the Python board `LemmaData.lNN`.",
            "Do not edit by hand.", "-/", "", "namespace Homm3.DrawingData", "",
            "open Homm3 Homm3.Embed", ""]
    for b in boards:
        data.append(b["txt"])
        data.append(f"def k{b['i']:02d} : List (ℕ × ℕ × ℕ × ℕ) := " + str(b["docks"]).replace(" ", ""))
        data.append("")
    data += ["end Homm3.DrawingData", ""]
    with open(os.path.join(LEAN_ROOT, "CrossCheckDrawingData.lean"), "w") as f:
        f.write("\n".join(data))

    parts = [[] for _ in range(PARTS)]
    load = [0] * PARTS
    for b in sorted(boards, key=lambda b: -(b["free"] + 40 * b["E"] ** 2)):
        m = load.index(min(load))
        parts[m].append(b["i"])
        load[m] += b["free"] + 40 * b["E"] ** 2
    names = []
    for m, part in enumerate(parts):
        name = f"CrossCheckDrawing{'ABCD'[m]}"
        names.append(name)
        chk = ["import CrossCheckDrawingData", "",
               f"/-! Session 5, targets 1 and 5: kernel checks of the drawings, part {m + 1} of "
               f"{PARTS} (generated by `tools/export_drawing.py`; see `CrossCheckDrawing.lean`). -/",
               "", "namespace Homm3.DrawingData", "", "open Homm3 Homm3.Embed Homm3.LemmaData", "",
               "set_option profiler true", "set_option profiler.threshold 50", ""]
        for i in sorted(part):
            chk.append(f"theorem va{i:02d} : d{i:02d}.check q{i:02d} C{i:02d} = true := by decide +kernel")
            chk.append(f"theorem eq{i:02d} : SameBoard d{i:02d} q{i:02d} C{i:02d} l{i:02d} k{i:02d} := by "
                       "decide +kernel")
            chk.append("")
        chk += ["end Homm3.DrawingData", ""]
        with open(os.path.join(LEAN_ROOT, name + ".lean"), "w") as f:
            f.write("\n".join(chk))

    top = [f"import {n}" for n in names] + ["",
           "/-!", "# Session 5, targets 1 and 5. Lemma D.4 on the corpus, through the universal lemma", "",
           "For each of the 44 boards of `CrossCheckLemma*.lean`: `vaNN` — the drawing passes",
           "`OrthoDrawing.check` in the kernel, so it is `Valid` (`check_sound`) and `lemmaD4` gives",
           "(I1)-(I4) for `build`; `eqNN` — the board that `build` computes in Lean from the drawing is",
           "the board of `embed_lemma.build_board_lemma` as data (`SameBoard`: dimensions, the label",
           "of every hex, `p_e`, `z_g`, and every docking).  `invNN` / `verdictNN` below combine them;",
           "`s1NN` — the drawing's `G'` is Lean's step 1 (`Step1.vkinds`, `Step1.pairs`) for the cut",
           "rotation read off the drawing, which lists each element's members once (`OrdOK`).",
           "-/", "", "namespace Homm3.DrawingData", "", "open Homm3 Homm3.Embed Homm3.LemmaData", ""]
    for b in boards:
        i = b["i"]
        top.append(f"theorem inv{i:02d} : (build (BoardData.toX3C q{i:02d} C{i:02d}) d{i:02d}).Inv "
                   f"(BoardData.toX3C q{i:02d} C{i:02d}) := lemmaD4 (OrthoDrawing.check_sound va{i:02d})")
        top.append(f"theorem s1{i:02d} : Step1.ordOKB q{i:02d} C{i:02d} (Step1.ordOf d{i:02d}) = true ∧ "
                   f"d{i:02d}.kind = Step1.vkinds (BoardData.toX3C q{i:02d} C{i:02d}) (Step1.ordOf d{i:02d}) ∧ "
                   f"d{i:02d}.edges.map (fun ε => (ε.u, ε.v)) = "
                   f"Step1.pairs (BoardData.toX3C q{i:02d} C{i:02d}) (Step1.ordOf d{i:02d}) := by decide +kernel")
        top.append(f"theorem verdict{i:02d} : (BoardData.toX3C q{i:02d} C{i:02d}).ExactCover ↔ "
                   f"ArmyAllocation (G3pub (BoardData.toX3C q{i:02d} C{i:02d}) "
                   f"(build (BoardData.toX3C q{i:02d} C{i:02d}) d{i:02d})) := "
                   f"theorem3_drawing (OrthoDrawing.check_sound va{i:02d})")
    top += ["",
            "/-! The checks have teeth: a route that stops short of its target, a route through",
            "another vertex's point, a wrong `q`, two routes leaving a set vertex in the same",
            "direction (an edge of `d00` re-routed round the top to enter its set vertex from the",
            "left, where another route already enters and shares its points),",
            "and the board of another family are all rejected. -/",
            "example : ({ d00 with edges := [⟨1, 0, [(0, 3), (0, 2)]⟩] ++ d00.edges.tail } : "
            "OrthoDrawing).check q00 C00 = false := by decide +kernel",
            "example : ({ d00 with edges := [⟨1, 0, [(0, 3), (0, 2), (0, 1), (0, 0), (1, 0)]⟩, ⟨2, 0, [(2, 2), (1, 2), (1, 1), (1, 0)]⟩, "
            "⟨3, 0, [(1, 1), (1, 0)]⟩] } : OrthoDrawing).check q00 C00 = false := by decide +kernel",
            "example : d00.check 2 C00 = false := by decide +kernel",
            "example : ({ d00 with edges := [⟨1, 0, [(0, 3), (0, 2), (0, 1), (0, 0), (1, 0)]⟩, "
            "⟨2, 0, [(2, 2), (2, 1), (2, 0), (2, -1), (1, -1), (0, -1), (-1, -1), (-1, 0), (0, 0), "
            "(1, 0)]⟩, ⟨3, 0, [(1, 1), (1, 0)]⟩] } : OrthoDrawing).check q00 C00 = false := by decide +kernel",
            "example : ¬ SameBoard d01 q01 C01 l02 k01 := by decide +kernel",
            "",
            "#print axioms inv00", "#print axioms eq00", "#print axioms verdict00", "", "end Homm3.DrawingData", ""]
    with open(os.path.join(LEAN_ROOT, "CrossCheckDrawing.lean"), "w") as f:
        f.write("\n".join(top))

    summary = [{k: b[k] for k in ("i", "family", "gw", "gh", "W", "H", "V", "E", "unit", "free",
                                  "offset")} for b in boards]
    print(json.dumps({"boards": summary, "secs": round(time.time() - t0, 1)}))


if __name__ == "__main__":
    main()
