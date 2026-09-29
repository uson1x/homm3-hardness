import CrossCheck

/-! Runner (session 3, target 4): `verify_featureless.py` C6 default tier on `G_F` of
`Theorem4.lean`. Per allocation: the greedy attack-only line `valueG` (a lower bound
attained by a genuine play, `valueG_attained`) and the proof-level upper bound
`min m ⌊Σ nominal / T⌋` (`gf_value_le`). `lake build CrossCheck && lake env lean CrossCheckRun3.lean` -/

open Homm3 CrossCheck

def c6Cases : List (List ℕ × ℕ × List (List (Option ℕ)) × List ℕ) :=
  [([4, 4, 4, 4, 5, 5], 13,
      [[some 0, some 1, some 2, some 3, some 4, some 5],
       [none, some 2, some 1, none, some 3, some 0],
       [some 5, some 0, some 1, some 4, none, some 3]], [2, 1, 1]),
   ([4, 4, 4, 4, 4, 6], 13,
      [[some 0, some 1, some 2, some 3, some 4, some 5],
       [none, some 1, some 3, some 5, some 4, none],
       [some 4, none, some 2, some 0, some 1, some 5]], [1, 1, 1])]

def runC6 : IO Unit := do
  IO.println "a | T | alloc | python best | lean lower (valueG) | Σ nominal | lean upper | python within bounds | exact | ms"
  for (a, T, allocs, py) in c6Cases do
    for (l, b) in allocs.zip py do
      let I := GF a T
      let α := pyAlloc l
      let (v, t) ← timed fun _ => valueG I α
      let nom := (List.range (3 * (a.length / 3))).foldl (fun acc j => acc + nominal I α j) 0
      let ub := min (a.length / 3) (nom / T)
      IO.println s!"{a} | {T} | {l} | {b} | {v} | {nom} | {ub} | {okStr (v ≤ b && b ≤ ub)} | {v == ub} | {t}"

#eval runC6

#print axioms CrossCheck.t2_c0
#print axioms CrossCheck.t2_c1
#print axioms CrossCheck.t4_yes13_id
#print axioms CrossCheck.t4_no13_id
#print axioms CrossCheck.valueG_attained
#print axioms CrossCheck.gf_value_le
