import CrossCheck

/-! Runner: Theorem 2 tier, one instance, every bijection (session 2, target 4).
`lake build CrossCheck && CASE=0 SLICE=lo:hi lake env lean CrossCheckThm2Full.lean`
prints `π | lean AO value` for the bijections `lo … hi−1` of `(List.range 6).permutations`
(slot `s` gets type `π s`).  ~65 s per bijection in the interpreter; the 720 bijections of
one instance are meant to be split over several processes. -/

open Homm3 CrossCheck

#eval show IO Unit from do
  let c := ((← IO.getEnv "CASE").getD "0").toNat!
  let sl := (← IO.getEnv "SLICE").getD "0:720"
  let parts := sl.splitOn ":"
  let lo := (parts.getD 0 "0").toNat!
  let hi := (parts.getD 1 "720").toNat!
  let (a, T, _, _) := thm2Cases.getD c ([], 0, "", 0)
  let I := threePart a T
  let perms := (List.range 6).permutations
  IO.println s!"== case {c}: a = {a}, T = {T}, bijections {lo}..{hi - 1} of {perms.length} =="
  for r in (List.range perms.length).filter (fun r => lo ≤ r && r < hi) do
    let π := perms.getD r []
    let α : ℕ → SlotAlloc := fun j => ⟨π.getD j 0, 1⟩
    let (v, t) ← timed fun _ => valueAO I α
    IO.println s!"{π} | {v} | {decide (Feasible I α)} | {t}"
