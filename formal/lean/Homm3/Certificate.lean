import Homm3.Exec

/-!
# Session 2, target 5a. Lemma 2.1 (membership in NP), without a complexity framework

Paper §2.3, Lemma 2.1: a certificate is the allocation together with the player's actions,
and checking it is a polynomial simulation.  Formalized here as:

* a certificate is a list of `k` slot choices (`l`, read as the allocation `toAlloc l`) and a
  list of natural numbers `path`, each an index into the list of successors `succs I s` of
  the current position (so the defence's forced steps and the phase/round bookkeeping are
  indices too — `(‡)` has one successor, so its index is `0`);
* `checkCert I l path : Bool` replays the path (`replay`) and checks feasibility,
  completion and the target;
* **`armyAllocation_iff_cert`**: `ArmyAllocation I ↔ ∃ l path, l.length = I.k ∧
  path.length ≤ (I.R + 1) * (2 * I.N + 2) ∧ checkCert I l path = true`.

So the certificate has length linear in `R · (k + n)` (with `R` in unary, polynomial in the
input size), every entry of `l` is bounded by feasibility (a type index below the army length,
a count at most a stock), every entry of `path` is below the length of the successor list it
indexes, and the checker is a computable function of the certificate.  What is *not*
formalized is a cost model: that `checkCert` runs in polynomial time is read off its
definition (`replay` makes `path.length` calls to `succs`, each a BFS over the board plus
linear scans), not proved.
-/

namespace Homm3

open Function

/-- Replay a list of successor indices. -/
def replay (I : Instance) : List ℕ → State → Option State
  | [], s => some s
  | c :: cs, s => match (succs I s)[c]? with
    | some s' => replay I cs s'
    | none => none

/-- The certificate checker. -/
def checkCert (I : Instance) (l : List SlotAlloc) (path : List ℕ) : Bool :=
  decide (Feasible I (toAlloc l)) &&
    match replay I path (initState I (toAlloc l)) with
    | some s => decide (Done s) && decide (I.W ≤ destroyed I s)
    | none => false

variable {I : Instance}

theorem replay_sound : ∀ (path : List ℕ) (s t : State), replay I path s = some t →
    Relation.ReflTransGen (Step I) s t
  | [], s, t, h => by simp only [replay, Option.some.injEq] at h; subst h; exact .refl
  | c :: cs, s, t, h => by
    simp only [replay] at h
    split at h
    · rename_i s' hs'
      have hmem : s' ∈ succs I s := List.mem_of_getElem? hs'
      exact Relation.ReflTransGen.head (step_iff_mem_succs.mpr hmem) (replay_sound cs s' t h)
    · cases h

theorem exists_path {s t : State} (h : Relation.ReflTransGen (Step I) s t) :
    ∃ path, replay I path s = some t ∧ path.length + μ I t ≤ μ I s := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], rfl, by simp⟩
  | head hst _ ih =>
    obtain ⟨path, hp, hl⟩ := ih
    obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp (step_iff_mem_succs.mp hst)
    refine ⟨c :: path, by simp [replay, hc, hp], ?_⟩
    have := hst.μ_lt
    simp only [List.length_cons]; omega

theorem μ_init_le (α : ℕ → SlotAlloc) : μ I (initState I α) ≤ (I.R + 1) * (2 * I.N + 2) := by
  unfold μ phaseCost
  simp only [initState, List.length_nil]
  have hL := length_normalQueue I.N (initUnits I α)
  have : (I.R - 1) * (2 * I.N + 2) ≤ I.R * (2 * I.N + 2) :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  rw [show (I.R + 1) * (2 * I.N + 2) = I.R * (2 * I.N + 2) + (2 * I.N + 2) from Nat.succ_mul _ _]
  omega

theorem length_of_mem_allocs {α : ℕ → SlotAlloc} (h : α ∈ allocs I) :
    ∃ l : List SlotAlloc, l.length = I.k ∧ α = toAlloc l := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp h
  have hs := (List.mem_filter.mp hl).1
  rw [List.mem_sections] at hs
  exact ⟨l, by simpa using hs.length_eq, rfl⟩

/-- **Lemma 2.1, certificate form.** -/
theorem armyAllocation_iff_cert : ArmyAllocation I ↔
    ∃ l : List SlotAlloc, ∃ path : List ℕ, l.length = I.k ∧
      path.length ≤ (I.R + 1) * (2 * I.N + 2) ∧ checkCert I l path = true := by
  constructor
  · rintro ⟨α, hα, s, hs, hd, hW⟩
    obtain ⟨β, hβ, he⟩ := exists_mem_allocs hα
    obtain ⟨l, hl, rfl⟩ := length_of_mem_allocs hβ
    have hs' : Relation.ReflTransGen (Step I) (initState I (toAlloc l)) s := by rw [he]; exact hs
    obtain ⟨path, hp, hlen⟩ := exists_path hs'
    refine ⟨l, path, hl, by have := μ_init_le (I := I) (toAlloc l); omega, ?_⟩
    simp only [checkCert, hp, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨feasible_of_mem_allocs hβ, hd, hW⟩
  · rintro ⟨l, path, -, -, hc⟩
    simp only [checkCert, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hf, hr⟩ := hc
    split at hr
    · rename_i s hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
      exact ⟨toAlloc l, hf, s, replay_sound path _ _ hs, hr.1, hr.2⟩
    · cases hr

end Homm3
