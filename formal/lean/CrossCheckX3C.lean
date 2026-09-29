import CrossCheckX3CData

/-!
# Session 4, target 4. Theorem 3 cross-check against `verify_x3c.py` (default tier)

The 31 boards of the default suite (`CrossCheckX3CData.lean`, exported by
`tools/export_x3c.py`) and the negative control's board.  For every board, **in the kernel**
(`decide +kernel`, no `native_decide`):

* `ckNN`: the board passes `BoardData.check`, hence satisfies (I1)–(I4) (`check_sound`) — so
  `theorem3` applies to the boards the artifact builds;
* `cvNN`: exact cover decided by `coverCheck` (`exactCover_iff_check`);
* `yesNN` / `noNN`: the game verdict **through `theorem3`**, at the historical constants of
  `verify_x3c.py` (`hp 5`, `def 41`) and at the paper's (`hp 4`, `def 27`), plus Corollary 3.1
  (`BATTLE-PLAY` with the all-ones allocation) and, on yes-boards, uniqueness of the winning
  allocation (`T3.winning_unique`).  No game tree is searched: a yes-verdict is the witness run
  of Lemma D.8 behind `theorem3`, a no-verdict is `¬ ExactCover` pushed through it.
* `negctl`: with `def(Q) = att(P) = 1` the no-instance `{{0,1,2}, {0,1,3}}` becomes a yes-instance
  of the game (two stacks of three creatures, each killing an enemy alone — `T3.witness`), while
  at `def 41` it stays a no-instance.
-/

namespace Homm3.X3CData

open Homm3 BoardData T3

set_option profiler true
set_option profiler.threshold 50

theorem ck00 : b00.check q00 C00 = true := by decide +kernel
theorem cv00 : coverCheck q00 C00 = true := by decide +kernel
theorem yes00 : YesV b00 q00 C00 := yes_of ck00 cv00

theorem ck01 : b01.check q01 C01 = true := by decide +kernel
theorem cv01 : coverCheck q01 C01 = true := by decide +kernel
theorem yes01 : YesV b01 q01 C01 := yes_of ck01 cv01

theorem ck02 : b02.check q02 C02 = true := by decide +kernel
theorem cv02 : coverCheck q02 C02 = true := by decide +kernel
theorem yes02 : YesV b02 q02 C02 := yes_of ck02 cv02

theorem ck03 : b03.check q03 C03 = true := by decide +kernel
theorem cv03 : coverCheck q03 C03 = true := by decide +kernel
theorem yes03 : YesV b03 q03 C03 := yes_of ck03 cv03

theorem ck04 : b04.check q04 C04 = true := by decide +kernel
theorem cv04 : coverCheck q04 C04 = true := by decide +kernel
theorem yes04 : YesV b04 q04 C04 := yes_of ck04 cv04

theorem ck05 : b05.check q05 C05 = true := by decide +kernel
theorem cv05 : coverCheck q05 C05 = true := by decide +kernel
theorem yes05 : YesV b05 q05 C05 := yes_of ck05 cv05

theorem ck06 : b06.check q06 C06 = true := by decide +kernel
theorem cv06 : coverCheck q06 C06 = true := by decide +kernel
theorem yes06 : YesV b06 q06 C06 := yes_of ck06 cv06

theorem ck07 : b07.check q07 C07 = true := by decide +kernel
theorem cv07 : coverCheck q07 C07 = true := by decide +kernel
theorem yes07 : YesV b07 q07 C07 := yes_of ck07 cv07

theorem ck08 : b08.check q08 C08 = true := by decide +kernel
theorem cv08 : coverCheck q08 C08 = true := by decide +kernel
theorem yes08 : YesV b08 q08 C08 := yes_of ck08 cv08

theorem ck09 : b09.check q09 C09 = true := by decide +kernel
theorem cv09 : coverCheck q09 C09 = true := by decide +kernel
theorem yes09 : YesV b09 q09 C09 := yes_of ck09 cv09

theorem ck10 : b10.check q10 C10 = true := by decide +kernel
theorem cv10 : coverCheck q10 C10 = true := by decide +kernel
theorem yes10 : YesV b10 q10 C10 := yes_of ck10 cv10

theorem ck11 : b11.check q11 C11 = true := by decide +kernel
theorem cv11 : coverCheck q11 C11 = true := by decide +kernel
theorem yes11 : YesV b11 q11 C11 := yes_of ck11 cv11

theorem ck12 : b12.check q12 C12 = true := by decide +kernel
theorem cv12 : coverCheck q12 C12 = false := by decide +kernel
theorem no12 : NoV b12 q12 C12 := no_of ck12 cv12

theorem ck13 : b13.check q13 C13 = true := by decide +kernel
theorem cv13 : coverCheck q13 C13 = false := by decide +kernel
theorem no13 : NoV b13 q13 C13 := no_of ck13 cv13

theorem ck14 : b14.check q14 C14 = true := by decide +kernel
theorem cv14 : coverCheck q14 C14 = false := by decide +kernel
theorem no14 : NoV b14 q14 C14 := no_of ck14 cv14

theorem ck15 : b15.check q15 C15 = true := by decide +kernel
theorem cv15 : coverCheck q15 C15 = false := by decide +kernel
theorem no15 : NoV b15 q15 C15 := no_of ck15 cv15

theorem ck16 : b16.check q16 C16 = true := by decide +kernel
theorem cv16 : coverCheck q16 C16 = true := by decide +kernel
theorem yes16 : YesV b16 q16 C16 := yes_of ck16 cv16

theorem ck17 : b17.check q17 C17 = true := by decide +kernel
theorem cv17 : coverCheck q17 C17 = false := by decide +kernel
theorem no17 : NoV b17 q17 C17 := no_of ck17 cv17

theorem ck18 : b18.check q18 C18 = true := by decide +kernel
theorem cv18 : coverCheck q18 C18 = false := by decide +kernel
theorem no18 : NoV b18 q18 C18 := no_of ck18 cv18

theorem ck19 : b19.check q19 C19 = true := by decide +kernel
theorem cv19 : coverCheck q19 C19 = false := by decide +kernel
theorem no19 : NoV b19 q19 C19 := no_of ck19 cv19

theorem ck20 : b20.check q20 C20 = true := by decide +kernel
theorem cv20 : coverCheck q20 C20 = false := by decide +kernel
theorem no20 : NoV b20 q20 C20 := no_of ck20 cv20

theorem ck21 : b21.check q21 C21 = true := by decide +kernel
theorem cv21 : coverCheck q21 C21 = true := by decide +kernel
theorem yes21 : YesV b21 q21 C21 := yes_of ck21 cv21

theorem ck22 : b22.check q22 C22 = true := by decide +kernel
theorem cv22 : coverCheck q22 C22 = true := by decide +kernel
theorem yes22 : YesV b22 q22 C22 := yes_of ck22 cv22

theorem ck23 : b23.check q23 C23 = true := by decide +kernel
theorem cv23 : coverCheck q23 C23 = false := by decide +kernel
theorem no23 : NoV b23 q23 C23 := no_of ck23 cv23

theorem ck24 : b24.check q24 C24 = true := by decide +kernel
theorem cv24 : coverCheck q24 C24 = false := by decide +kernel
theorem no24 : NoV b24 q24 C24 := no_of ck24 cv24

theorem ck25 : b25.check q25 C25 = true := by decide +kernel
theorem cv25 : coverCheck q25 C25 = false := by decide +kernel
theorem no25 : NoV b25 q25 C25 := no_of ck25 cv25

theorem ck26 : b26.check q26 C26 = true := by decide +kernel
theorem cv26 : coverCheck q26 C26 = false := by decide +kernel
theorem no26 : NoV b26 q26 C26 := no_of ck26 cv26

theorem ck27 : b27.check q27 C27 = true := by decide +kernel
theorem cv27 : coverCheck q27 C27 = false := by decide +kernel
theorem no27 : NoV b27 q27 C27 := no_of ck27 cv27

theorem ck28 : b28.check q28 C28 = true := by decide +kernel
theorem cv28 : coverCheck q28 C28 = true := by decide +kernel
theorem yes28 : YesV b28 q28 C28 := yes_of ck28 cv28

theorem ck29 : b29.check q29 C29 = true := by decide +kernel
theorem cv29 : coverCheck q29 C29 = false := by decide +kernel
theorem no29 : NoV b29 q29 C29 := no_of ck29 cv29

theorem ck30 : b30.check q30 C30 = true := by decide +kernel
theorem cv30 : coverCheck q30 C30 = true := by decide +kernel
theorem yes30 : YesV b30 q30 C30 := yes_of ck30 cv30

/-! ## The negative control -/

/-- The plan of the negative control: three creatures in slots `2` and `3`; slot `2` strikes
`E_0 = {0,1,2}`, slot `3` strikes `E_1 = {0,1,3}`. -/
def cNeg (j : ℕ) : ℕ := if j = 2 ∨ j = 3 then 3 else 0
def tNeg (j : ℕ) : ℕ := if j = 2 then 0 else 1

theorem ckNeg : bNeg.check qNeg CNeg = true := by decide +kernel
theorem cvNeg : coverCheck qNeg CNeg = false := by decide +kernel

theorem att_neg (g : ℕ) : ∑ j ∈ att (toX3C qNeg CNeg) cNeg tNeg g, bl 1 (cNeg j) =
    (if g = 0 then 3 else 0) + (if g = 1 then 3 else 0) := by
  have h3 : bl 1 3 = 3 := damage_negctl 3 (by norm_num)
  simp only [att, Finset.sum_filter, show (toX3C qNeg CNeg).q = 2 from rfl, Finset.sum_range_succ,
    Finset.sum_range_zero, cNeg, tNeg]
  rcases Nat.lt_or_ge g 2 with hg | hg
  · interval_cases g <;> simp [h3]
  · have h0 : g ≠ 0 := by omega
    have h1 : g ≠ 1 := by omega
    simp [h0, h1, Ne.symm h0, Ne.symm h1]

theorem planNeg : Plan (toX3C qNeg CNeg) 1 cNeg tNeg := by
  refine ⟨fun j hj hc => ?_, fun j hj hc => ?_, fun g hg => ?_, ?_⟩
  · simp only [cNeg] at hc; simp only [tNeg, toX3C_n]; split_ifs <;> simp [CNeg]
  · have hj' : j = 2 ∨ j = 3 := by simp only [cNeg] at hc; split_ifs at hc with h <;> omega
    rw [toX3C_set (by simp only [tNeg]; split_ifs <;> simp [CNeg])]
    rcases hj' with rfl | rfl <;> simp [tNeg, CNeg]
  · rw [att_neg]; simp only [toX3C_n, show CNeg.length = 2 from rfl] at hg
    interval_cases g <;> simp
  · simp [show (toX3C qNeg CNeg).q = 2 from rfl, Finset.sum_range_succ, cNeg]

/-- **The negative control** (`verify_x3c.py::check_negative_control`, paper D.6): the fixture
`{{0,1,2}, {0,1,3}}` has no exact cover; with `def(Q) = att(P) = 1` the game on its board is a
yes-instance (Lemma 3.2 fails: `D(3) = 3`), while at `def 41` it is a no-instance. -/
theorem negctl : bNeg.toBoard.Inv (toX3C qNeg CNeg) ∧ ¬ (toX3C qNeg CNeg).ExactCover ∧
    ArmyAllocation (G3 5 1 (toX3C qNeg CNeg) bNeg.toBoard) ∧
    ¬ ArmyAllocation (G3 5 41 (toX3C qNeg CNeg) bNeg.toBoard) := by
  obtain ⟨hI, hX, h41, -, -⟩ := no_of ckNeg cvNeg
  refine ⟨hI, hX, ?_, h41⟩
  obtain ⟨s, hs, hd, hpool⟩ := witness (hpP := 5) (B := bNeg.toBoard) (by norm_num) hI.core planNeg
  refine ⟨αc cNeg, αc_feasible planNeg.stock, s, hs, hd, ?_⟩
  rw [destroyed_eq hs]
  have hq : (toX3C qNeg CNeg).q = 2 := rfl
  have hn : (toX3C qNeg CNeg).n = 2 := rfl
  have hdead : dead (toX3C qNeg CNeg) s = Finset.range 2 := by
    ext g
    simp only [dead, Finset.mem_filter, Finset.mem_range, hn, and_iff_left_iff_imp]
    intro hg
    rw [hpool g (by rw [hn]; exact hg), att_neg]
    interval_cases g <;> simp
  simp [hdead, G3.W_eq, hq]

set_option profiler false

#print axioms yes01
#print axioms no12
#print axioms negctl

end Homm3.X3CData
