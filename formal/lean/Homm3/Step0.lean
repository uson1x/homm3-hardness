import Homm3.X3C

/-!
# Session 5, target 6 (stretch). Step 0 of Lemma D.4: the degenerate inputs

Paper: D.4 step 0 (`main.md:1432–1444`).  Step 0 deletes repeated members, sends `|X| = 0` to a
fixed yes-board, and sends to `G_no` the inputs failing one of three polynomial-time
no-certificates.  Here, on encodings with a universe `[0, nX)` of any size and members given as a
list of finite sets (`CoverRaw nX C`: pairwise disjoint members whose union is the universe):

* `cover_card`: an exact cover by 3-sets has `nX = 3·|K|`; hence **`no_mod3`** (`nX` not divisible
  by 3), **`no_few`** (`|C| < nX / 3`), **`no_uncovered`** (an element in no member) are sound
  no-certificates, and **`step0_sound`** packages them as one Bool test;
* **`cover_dedup`**: deleting repeated members does not change the answer ("a duplicate 3-set is
  never needed by an exact cover");
* **`cover_zero`**: `|X| = 0` is a yes-instance (the empty cover);
* **`coverRaw_iff`**: for a well-formed `X3C` instance, `CoverRaw (3q) C ↔ ExactCover`.
-/

namespace Homm3

namespace Step0

/-- **Exact cover of the universe `[0, nX)`** by members of the list `C`. -/
def CoverRaw (nX : ℕ) (C : List (Finset ℕ)) : Prop :=
  ∃ K : Finset ℕ, (∀ g ∈ K, g < C.length) ∧
    (∀ g ∈ K, ∀ g' ∈ K, g ≠ g' → Disjoint (C.getD g ∅) (C.getD g' ∅)) ∧
    K.biUnion (fun g => C.getD g ∅) = Finset.range nX

/-- Members are 3-sets (the encoding is well formed). -/
def Threes (C : List (Finset ℕ)) : Prop := ∀ s ∈ C, s.card = 3

theorem getD_mem {C : List (Finset ℕ)} {g : ℕ} (hg : g < C.length) : C.getD g ∅ ∈ C := by
  rw [List.getD_eq_getElem _ _ hg]; exact List.getElem_mem _

/-- An exact cover by 3-sets has exactly `nX / 3` members, and `3 ∣ nX`. -/
theorem cover_card {nX : ℕ} {C : List (Finset ℕ)} (h3 : Threes C) {K : Finset ℕ}
    (hK : ∀ g ∈ K, g < C.length)
    (hdis : ∀ g ∈ K, ∀ g' ∈ K, g ≠ g' → Disjoint (C.getD g ∅) (C.getD g' ∅))
    (hcov : K.biUnion (fun g => C.getD g ∅) = Finset.range nX) : nX = 3 * K.card := by
  have := congrArg Finset.card hcov
  rw [Finset.card_biUnion (fun g hg g' hg' hne => hdis g hg g' hg' hne), Finset.card_range,
    Finset.sum_congr rfl (fun g hg => h3 _ (getD_mem (hK g hg))), Finset.sum_const,
    smul_eq_mul] at this
  omega

/-- **No-certificate: `|X|` not divisible by 3.** -/
theorem no_mod3 {nX : ℕ} {C : List (Finset ℕ)} (h3 : Threes C) (h : nX % 3 ≠ 0) :
    ¬ CoverRaw nX C := by
  rintro ⟨K, hK, hdis, hcov⟩
  have := cover_card h3 hK hdis hcov; omega

/-- **No-certificate: fewer than `q = |X| / 3` members.** -/
theorem no_few {nX : ℕ} {C : List (Finset ℕ)} (h3 : Threes C) (h : C.length < nX / 3) :
    ¬ CoverRaw nX C := by
  rintro ⟨K, hK, hdis, hcov⟩
  have h1 := cover_card h3 hK hdis hcov
  have h2 : K.card ≤ C.length := by
    calc K.card ≤ (Finset.range C.length).card :=
          Finset.card_le_card (fun g hg => Finset.mem_range.mpr (hK g hg))
      _ = C.length := Finset.card_range _
  omega

/-- **No-certificate: an element lies in no member.** -/
theorem no_uncovered {nX : ℕ} {C : List (Finset ℕ)} {e : ℕ} (he : e < nX) (h : ∀ s ∈ C, e ∉ s) :
    ¬ CoverRaw nX C := by
  rintro ⟨K, hK, -, hcov⟩
  have : e ∈ K.biUnion (fun g => C.getD g ∅) := by rw [hcov]; exact Finset.mem_range.mpr he
  obtain ⟨g, hg, heg⟩ := Finset.mem_biUnion.mp this
  exact h _ (getD_mem (hK g hg)) heg

/-- **`|X| = 0` is a yes-instance**: the empty cover. -/
theorem cover_zero (C : List (Finset ℕ)) : CoverRaw 0 C :=
  ⟨∅, by simp, by simp, by simp⟩

/-- Exact cover depends only on the **set** of members. -/
theorem coverRaw_iff_sets {nX : ℕ} {C : List (Finset ℕ)} :
    CoverRaw nX C ↔ ∃ T : Finset (Finset ℕ), (∀ s ∈ T, s ∈ C) ∧
      (∀ s ∈ T, ∀ s' ∈ T, s ≠ s' → Disjoint s s') ∧ T.biUnion id = Finset.range nX := by
  constructor
  · rintro ⟨K, hK, hdis, hcov⟩
    refine ⟨K.image (fun g => C.getD g ∅), ?_, ?_, ?_⟩
    · intro s hs
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hs
      exact getD_mem (hK g hg)
    · intro s hs s' hs' hne
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨g', hg', rfl⟩ := Finset.mem_image.mp hs'
      exact hdis g hg g' hg' (fun h => hne (by rw [h]))
    · rw [← hcov]; ext e; simp [Finset.mem_biUnion]
  · rintro ⟨T, hT, hdis, hcov⟩
    refine ⟨T.image (fun s => C.idxOf s), ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hg
      exact List.idxOf_lt_length_iff.mpr (hT s hs)
    · intro g hg g' hg' hne
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hg'
      have e1 : C.getD (C.idxOf s) ∅ = s := by
        rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.mpr (hT s hs))]
        exact List.getElem_idxOf _
      have e2 : C.getD (C.idxOf s') ∅ = s' := by
        rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.mpr (hT s' hs'))]
        exact List.getElem_idxOf _
      rw [e1, e2]
      exact hdis s hs s' hs' (fun h => hne (by rw [h]))
    · rw [← hcov]
      ext e
      simp only [Finset.mem_biUnion, Finset.mem_image, id]
      constructor
      · rintro ⟨g, ⟨s, hs, rfl⟩, he⟩
        have e1 : C.getD (C.idxOf s) ∅ = s := by
          rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.mpr (hT s hs))]
          exact List.getElem_idxOf _
        exact ⟨s, hs, by rwa [e1] at he⟩
      · rintro ⟨s, hs, he⟩
        refine ⟨_, ⟨s, hs, rfl⟩, ?_⟩
        rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.mpr (hT s hs)), List.getElem_idxOf]
        exact he

/-- **Deleting repeated members does not change the answer.** -/
theorem cover_dedup {nX : ℕ} {C : List (Finset ℕ)} : CoverRaw nX C.dedup ↔ CoverRaw nX C := by
  simp only [coverRaw_iff_sets, List.mem_dedup]

/-- **The step-0 test** (after deduplication): `|X| mod 3 ≠ 0`, `|C| < q`, or an uncovered
element. -/
def reject (nX : ℕ) (CL : List (List ℕ)) : Bool :=
  let C := (CL.map List.toFinset).dedup
  decide (nX % 3 ≠ 0) || decide (C.length < nX / 3) ||
    (List.range nX).any (fun e => C.all (fun s => decide (e ∉ s)))

/-- **Step 0 is sound**: an encoding with 3-element members that the test rejects has no exact
cover — so sending it to `G_no` is correct ("only when", `main.md:1420–1424`). -/
theorem step0_sound {nX : ℕ} {CL : List (List ℕ)} (h3 : Threes (CL.map List.toFinset))
    (hr : reject nX CL = true) : ¬ CoverRaw nX (CL.map List.toFinset) := by
  rw [← cover_dedup]
  have h3' : Threes (CL.map List.toFinset).dedup := fun s hs => h3 s (List.mem_dedup.mp hs)
  simp only [reject, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
    List.all_eq_true] at hr
  rcases hr with (h | h) | ⟨e, he, hn⟩
  · exact no_mod3 h3' h
  · exact no_few h3' h
  · exact no_uncovered he hn

/-- For a well-formed instance, `CoverRaw` on `[0, 3q)` is `ExactCover`. -/
theorem coverRaw_iff (P : X3C) (hP : P.WF) : CoverRaw (3 * P.q) P.C ↔ P.ExactCover := by
  have hset : ∀ g, P.C.getD g ∅ = P.set g := fun g => rfl
  constructor
  · rintro ⟨K, hK, hdis, hcov⟩
    refine ⟨K, hK, fun g hg g' hg' hne => hdis g hg g' hg' hne, fun e he => ?_⟩
    have : e ∈ K.biUnion (fun g => P.C.getD g ∅) := by rw [hcov]; exact Finset.mem_range.mpr he
    obtain ⟨g, hg, heg⟩ := Finset.mem_biUnion.mp this
    exact ⟨g, hg, heg⟩
  · rintro ⟨K, hK, hdis, hcov⟩
    refine ⟨K, hK, fun g hg g' hg' hne => hdis g hg g' hg' hne, ?_⟩
    simp only [hset]
    exact X3C.biUnion_eq hP hK hcov

end Step0

end Homm3
