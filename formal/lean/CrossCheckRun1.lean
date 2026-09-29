import CrossCheck

/-! Runner: Theorem 1 tier, attack-only and full model on all 28 instances.
`lake build CrossCheck && lake env lean CrossCheckRun1.lean` -/

#eval CrossCheck.runThm1 (fun _ => true)
