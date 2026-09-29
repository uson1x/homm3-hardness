import Homm3.Certificate
import Homm3.Theorem1

/-!
# Regression checks for the executable semantics (run at every `lake build`)

Small instances only; the full cross-check against the Python scripts is
`CrossCheck.lean` (see `PROGRESS.md`, session 2, target 4).  `#guard` evaluates with the
compiler, so these are executions of the verified search, not kernel proofs (the kernel does
not reduce the decision instance: `mergeSort` and `Finset` block it).
-/

open Homm3 Homm3.Corridor

-- `brute_force.py`, Theorem 1 tier: `a = (1,1)` is a yes-instance with best value 1, and
-- `a = (1,3)` a no-instance (`W = 2`) with best value 1.
#guard optimum (G [1, 1]) == 1
#guard optimum (G [1, 3]) == 1
#guard decide (ArmyAllocation (G [1, 1]))
#guard !decide (ArmyAllocation (G [1, 3]))

-- The certificate of Lemma 2.1 for `G((1,1))`: one creature in slot 0; the player strikes
-- (successor index 3 = after WAIT, DEFEND and the one-hex move), the dead `E_0` is skipped,
-- `E_1` waits, the phase switches, `E_1` defends.
#guard checkCert (G [1, 1]) [⟨0, 1⟩, ⟨0, 0⟩] [3, 0, 0, 0, 0]
#guard !checkCert (G [1, 1]) [⟨0, 1⟩, ⟨0, 0⟩] [2, 0, 0, 0, 0]
