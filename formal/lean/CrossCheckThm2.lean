import CrossCheck

/-! Runner: Theorem 2 tier, per-bijection sample (session 2, target 4).
`lake build CrossCheck && SLICE=lo:hi lake env lean CrossCheckThm2.lean` (default: all rows).
Rows and Python values from a scratch re-run of `brute_force.py`'s seeded generator. -/

open Homm3 CrossCheck

namespace CrossCheck

/-- Theorem 2 tier, per-bijection sample (the full 720-bijection maximum is out of reach of
the unmemoized search, ~1 min per bijection in the interpreter): for every instance the
first two bijections in `itertools.permutations` order, and for a yes-instance the first
bijection on which Python's search reaches `m = 2` kills (dropped when it is one of the
first two).  `(case, a, T, π, python value)`; slot `s` gets type `π s`. -/
def thm2Sample : List (ℕ × List ℕ × ℕ × List ℕ × ℕ) := [
  (0, [9, 9, 7, 9, 7, 7], 24, [0, 1, 2, 3, 4, 5], 1),
  (0, [9, 9, 7, 9, 7, 7], 24, [0, 1, 2, 3, 5, 4], 1),
  (1, [8, 9, 12, 11, 8, 8], 28, [0, 1, 2, 3, 4, 5], 1),
  (1, [8, 9, 12, 11, 8, 8], 28, [0, 1, 2, 3, 5, 4], 1),
  (1, [8, 9, 12, 11, 8, 8], 28, [0, 1, 3, 2, 4, 5], 2),
  (2, [7, 10, 7, 7, 9, 8], 24, [0, 1, 2, 3, 4, 5], 2),
  (2, [7, 10, 7, 7, 9, 8], 24, [0, 1, 2, 3, 5, 4], 2),
  (3, [10, 9, 12, 9, 8, 8], 28, [0, 1, 2, 3, 4, 5], 1),
  (3, [10, 9, 12, 9, 8, 8], 28, [0, 1, 2, 3, 5, 4], 1),
  (3, [10, 9, 12, 9, 8, 8], 28, [0, 1, 3, 2, 4, 5], 2),
  (4, [6, 7, 6, 8, 6, 7], 20, [0, 1, 2, 3, 4, 5], 1),
  (4, [6, 7, 6, 8, 6, 7], 20, [0, 1, 2, 3, 5, 4], 1),
  (4, [6, 7, 6, 8, 6, 7], 20, [0, 1, 5, 2, 3, 4], 2),
  (5, [7, 7, 8, 8, 10, 8], 24, [0, 1, 2, 3, 4, 5], 1),
  (5, [7, 7, 8, 8, 10, 8], 24, [0, 1, 2, 3, 5, 4], 1),
  (5, [7, 7, 8, 8, 10, 8], 24, [0, 1, 4, 2, 3, 5], 2),
  (6, [11, 10, 8, 9, 9, 9], 28, [0, 1, 2, 3, 4, 5], 1),
  (6, [11, 10, 8, 9, 9, 9], 28, [0, 1, 2, 3, 5, 4], 1),
  (6, [11, 10, 8, 9, 9, 9], 28, [0, 2, 3, 1, 4, 5], 2),
  (7, [6, 6, 8, 6, 6, 8], 20, [0, 1, 2, 3, 4, 5], 2),
  (7, [6, 6, 8, 6, 6, 8], 20, [0, 1, 2, 3, 5, 4], 2),
  (8, [7, 7, 10, 10, 7, 7], 24, [0, 1, 2, 3, 4, 5], 2),
  (8, [7, 7, 10, 10, 7, 7], 24, [0, 1, 2, 3, 5, 4], 2),
  (9, [11, 8, 13, 8, 8, 8], 28, [0, 1, 2, 3, 4, 5], 1),
  (9, [11, 8, 13, 8, 8, 8], 28, [0, 1, 2, 3, 5, 4], 1),
  (10, [10, 8, 10, 9, 11, 8], 28, [0, 1, 2, 3, 4, 5], 2),
  (10, [10, 8, 10, 9, 11, 8], 28, [0, 1, 2, 3, 5, 4], 2),
  (11, [8, 8, 8, 8, 9, 7], 24, [0, 1, 2, 3, 4, 5], 2),
  (11, [8, 8, 8, 8, 9, 7], 24, [0, 1, 2, 3, 5, 4], 2),
  (12, [8, 8, 7, 11, 7, 7], 24, [0, 1, 2, 3, 4, 5], 1),
  (12, [8, 8, 7, 11, 7, 7], 24, [0, 1, 2, 3, 5, 4], 1),
  (13, [7, 7, 7, 7, 6, 6], 20, [0, 1, 2, 3, 4, 5], 1),
  (13, [7, 7, 7, 7, 6, 6], 20, [0, 1, 2, 3, 5, 4], 1),
  (13, [7, 7, 7, 7, 6, 6], 20, [0, 1, 4, 2, 3, 5], 2)]

def runThm2Sample (lo hi : ℕ) : IO Unit := do
  IO.println s!"== Theorem 2 tier, per-bijection sample, rows {lo}..{hi - 1} =="
  IO.println "row | case | a | T | bijection | feasible | python | lean AO | verdict | ms"
  for r in (List.range thm2Sample.length).filter (fun r => lo ≤ r && r < hi) do
    let (c, a, T, π, py) := thm2Sample.getD r (0, [], 0, [], 0)
    let I := threePart a T
    let α : ℕ → SlotAlloc := fun j => ⟨π.getD j 0, 1⟩
    let feas := decide (Feasible I α)
    let (v, t) ← timed fun _ => valueAO I α
    IO.println s!"{r} | {c} | {a} | {T} | {π} | {feas} | {py} | {v} | {okStr (v == py && feas)} | {t}"

end CrossCheck

#eval show IO Unit from do
  let sl := (← IO.getEnv "SLICE").getD "0:100"
  let parts := sl.splitOn ":"
  CrossCheck.runThm2Sample (parts.getD 0 "0").toNat! (parts.getD 1 "100").toNat!
