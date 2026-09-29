import CrossCheckDrawingA
import CrossCheckDrawingB
import CrossCheckDrawingC
import CrossCheckDrawingD

/-!
# Session 5, targets 1 and 5. Lemma D.4 on the corpus, through the universal lemma

For each of the 44 boards of `CrossCheckLemma*.lean`: `vaNN` — the drawing passes
`OrthoDrawing.check` in the kernel, so it is `Valid` (`check_sound`) and `lemmaD4` gives
(I1)-(I4) for `build`; `eqNN` — the board that `build` computes in Lean from the drawing is
the board of `embed_lemma.build_board_lemma` as data (`SameBoard`: dimensions, the label
of every hex, `p_e`, `z_g`, and every docking).  `invNN` / `verdictNN` below combine them;
`s1NN` — the drawing's `G'` is Lean's step 1 (`Step1.vkinds`, `Step1.pairs`) for the cut
rotation read off the drawing, which lists each element's members once (`OrdOK`).
-/

namespace Homm3.DrawingData

open Homm3 Homm3.Embed Homm3.LemmaData

theorem inv00 : (build (BoardData.toX3C q00 C00) d00).Inv (BoardData.toX3C q00 C00) := lemmaD4 (OrthoDrawing.check_sound va00)
theorem s100 : Step1.ordOKB q00 C00 (Step1.ordOf d00) = true ∧ d00.kind = Step1.vkinds (BoardData.toX3C q00 C00) (Step1.ordOf d00) ∧ d00.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q00 C00) (Step1.ordOf d00) := by decide +kernel
theorem verdict00 : (BoardData.toX3C q00 C00).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q00 C00) (build (BoardData.toX3C q00 C00) d00)) := theorem3_drawing (OrthoDrawing.check_sound va00)
theorem inv01 : (build (BoardData.toX3C q01 C01) d01).Inv (BoardData.toX3C q01 C01) := lemmaD4 (OrthoDrawing.check_sound va01)
theorem s101 : Step1.ordOKB q01 C01 (Step1.ordOf d01) = true ∧ d01.kind = Step1.vkinds (BoardData.toX3C q01 C01) (Step1.ordOf d01) ∧ d01.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q01 C01) (Step1.ordOf d01) := by decide +kernel
theorem verdict01 : (BoardData.toX3C q01 C01).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q01 C01) (build (BoardData.toX3C q01 C01) d01)) := theorem3_drawing (OrthoDrawing.check_sound va01)
theorem inv02 : (build (BoardData.toX3C q02 C02) d02).Inv (BoardData.toX3C q02 C02) := lemmaD4 (OrthoDrawing.check_sound va02)
theorem s102 : Step1.ordOKB q02 C02 (Step1.ordOf d02) = true ∧ d02.kind = Step1.vkinds (BoardData.toX3C q02 C02) (Step1.ordOf d02) ∧ d02.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q02 C02) (Step1.ordOf d02) := by decide +kernel
theorem verdict02 : (BoardData.toX3C q02 C02).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q02 C02) (build (BoardData.toX3C q02 C02) d02)) := theorem3_drawing (OrthoDrawing.check_sound va02)
theorem inv03 : (build (BoardData.toX3C q03 C03) d03).Inv (BoardData.toX3C q03 C03) := lemmaD4 (OrthoDrawing.check_sound va03)
theorem s103 : Step1.ordOKB q03 C03 (Step1.ordOf d03) = true ∧ d03.kind = Step1.vkinds (BoardData.toX3C q03 C03) (Step1.ordOf d03) ∧ d03.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q03 C03) (Step1.ordOf d03) := by decide +kernel
theorem verdict03 : (BoardData.toX3C q03 C03).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q03 C03) (build (BoardData.toX3C q03 C03) d03)) := theorem3_drawing (OrthoDrawing.check_sound va03)
theorem inv04 : (build (BoardData.toX3C q04 C04) d04).Inv (BoardData.toX3C q04 C04) := lemmaD4 (OrthoDrawing.check_sound va04)
theorem s104 : Step1.ordOKB q04 C04 (Step1.ordOf d04) = true ∧ d04.kind = Step1.vkinds (BoardData.toX3C q04 C04) (Step1.ordOf d04) ∧ d04.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q04 C04) (Step1.ordOf d04) := by decide +kernel
theorem verdict04 : (BoardData.toX3C q04 C04).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q04 C04) (build (BoardData.toX3C q04 C04) d04)) := theorem3_drawing (OrthoDrawing.check_sound va04)
theorem inv05 : (build (BoardData.toX3C q05 C05) d05).Inv (BoardData.toX3C q05 C05) := lemmaD4 (OrthoDrawing.check_sound va05)
theorem s105 : Step1.ordOKB q05 C05 (Step1.ordOf d05) = true ∧ d05.kind = Step1.vkinds (BoardData.toX3C q05 C05) (Step1.ordOf d05) ∧ d05.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q05 C05) (Step1.ordOf d05) := by decide +kernel
theorem verdict05 : (BoardData.toX3C q05 C05).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q05 C05) (build (BoardData.toX3C q05 C05) d05)) := theorem3_drawing (OrthoDrawing.check_sound va05)
theorem inv06 : (build (BoardData.toX3C q06 C06) d06).Inv (BoardData.toX3C q06 C06) := lemmaD4 (OrthoDrawing.check_sound va06)
theorem s106 : Step1.ordOKB q06 C06 (Step1.ordOf d06) = true ∧ d06.kind = Step1.vkinds (BoardData.toX3C q06 C06) (Step1.ordOf d06) ∧ d06.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q06 C06) (Step1.ordOf d06) := by decide +kernel
theorem verdict06 : (BoardData.toX3C q06 C06).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q06 C06) (build (BoardData.toX3C q06 C06) d06)) := theorem3_drawing (OrthoDrawing.check_sound va06)
theorem inv07 : (build (BoardData.toX3C q07 C07) d07).Inv (BoardData.toX3C q07 C07) := lemmaD4 (OrthoDrawing.check_sound va07)
theorem s107 : Step1.ordOKB q07 C07 (Step1.ordOf d07) = true ∧ d07.kind = Step1.vkinds (BoardData.toX3C q07 C07) (Step1.ordOf d07) ∧ d07.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q07 C07) (Step1.ordOf d07) := by decide +kernel
theorem verdict07 : (BoardData.toX3C q07 C07).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q07 C07) (build (BoardData.toX3C q07 C07) d07)) := theorem3_drawing (OrthoDrawing.check_sound va07)
theorem inv08 : (build (BoardData.toX3C q08 C08) d08).Inv (BoardData.toX3C q08 C08) := lemmaD4 (OrthoDrawing.check_sound va08)
theorem s108 : Step1.ordOKB q08 C08 (Step1.ordOf d08) = true ∧ d08.kind = Step1.vkinds (BoardData.toX3C q08 C08) (Step1.ordOf d08) ∧ d08.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q08 C08) (Step1.ordOf d08) := by decide +kernel
theorem verdict08 : (BoardData.toX3C q08 C08).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q08 C08) (build (BoardData.toX3C q08 C08) d08)) := theorem3_drawing (OrthoDrawing.check_sound va08)
theorem inv09 : (build (BoardData.toX3C q09 C09) d09).Inv (BoardData.toX3C q09 C09) := lemmaD4 (OrthoDrawing.check_sound va09)
theorem s109 : Step1.ordOKB q09 C09 (Step1.ordOf d09) = true ∧ d09.kind = Step1.vkinds (BoardData.toX3C q09 C09) (Step1.ordOf d09) ∧ d09.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q09 C09) (Step1.ordOf d09) := by decide +kernel
theorem verdict09 : (BoardData.toX3C q09 C09).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q09 C09) (build (BoardData.toX3C q09 C09) d09)) := theorem3_drawing (OrthoDrawing.check_sound va09)
theorem inv10 : (build (BoardData.toX3C q10 C10) d10).Inv (BoardData.toX3C q10 C10) := lemmaD4 (OrthoDrawing.check_sound va10)
theorem s110 : Step1.ordOKB q10 C10 (Step1.ordOf d10) = true ∧ d10.kind = Step1.vkinds (BoardData.toX3C q10 C10) (Step1.ordOf d10) ∧ d10.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q10 C10) (Step1.ordOf d10) := by decide +kernel
theorem verdict10 : (BoardData.toX3C q10 C10).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q10 C10) (build (BoardData.toX3C q10 C10) d10)) := theorem3_drawing (OrthoDrawing.check_sound va10)
theorem inv11 : (build (BoardData.toX3C q11 C11) d11).Inv (BoardData.toX3C q11 C11) := lemmaD4 (OrthoDrawing.check_sound va11)
theorem s111 : Step1.ordOKB q11 C11 (Step1.ordOf d11) = true ∧ d11.kind = Step1.vkinds (BoardData.toX3C q11 C11) (Step1.ordOf d11) ∧ d11.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q11 C11) (Step1.ordOf d11) := by decide +kernel
theorem verdict11 : (BoardData.toX3C q11 C11).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q11 C11) (build (BoardData.toX3C q11 C11) d11)) := theorem3_drawing (OrthoDrawing.check_sound va11)
theorem inv12 : (build (BoardData.toX3C q12 C12) d12).Inv (BoardData.toX3C q12 C12) := lemmaD4 (OrthoDrawing.check_sound va12)
theorem s112 : Step1.ordOKB q12 C12 (Step1.ordOf d12) = true ∧ d12.kind = Step1.vkinds (BoardData.toX3C q12 C12) (Step1.ordOf d12) ∧ d12.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q12 C12) (Step1.ordOf d12) := by decide +kernel
theorem verdict12 : (BoardData.toX3C q12 C12).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q12 C12) (build (BoardData.toX3C q12 C12) d12)) := theorem3_drawing (OrthoDrawing.check_sound va12)
theorem inv13 : (build (BoardData.toX3C q13 C13) d13).Inv (BoardData.toX3C q13 C13) := lemmaD4 (OrthoDrawing.check_sound va13)
theorem s113 : Step1.ordOKB q13 C13 (Step1.ordOf d13) = true ∧ d13.kind = Step1.vkinds (BoardData.toX3C q13 C13) (Step1.ordOf d13) ∧ d13.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q13 C13) (Step1.ordOf d13) := by decide +kernel
theorem verdict13 : (BoardData.toX3C q13 C13).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q13 C13) (build (BoardData.toX3C q13 C13) d13)) := theorem3_drawing (OrthoDrawing.check_sound va13)
theorem inv14 : (build (BoardData.toX3C q14 C14) d14).Inv (BoardData.toX3C q14 C14) := lemmaD4 (OrthoDrawing.check_sound va14)
theorem s114 : Step1.ordOKB q14 C14 (Step1.ordOf d14) = true ∧ d14.kind = Step1.vkinds (BoardData.toX3C q14 C14) (Step1.ordOf d14) ∧ d14.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q14 C14) (Step1.ordOf d14) := by decide +kernel
theorem verdict14 : (BoardData.toX3C q14 C14).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q14 C14) (build (BoardData.toX3C q14 C14) d14)) := theorem3_drawing (OrthoDrawing.check_sound va14)
theorem inv15 : (build (BoardData.toX3C q15 C15) d15).Inv (BoardData.toX3C q15 C15) := lemmaD4 (OrthoDrawing.check_sound va15)
theorem s115 : Step1.ordOKB q15 C15 (Step1.ordOf d15) = true ∧ d15.kind = Step1.vkinds (BoardData.toX3C q15 C15) (Step1.ordOf d15) ∧ d15.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q15 C15) (Step1.ordOf d15) := by decide +kernel
theorem verdict15 : (BoardData.toX3C q15 C15).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q15 C15) (build (BoardData.toX3C q15 C15) d15)) := theorem3_drawing (OrthoDrawing.check_sound va15)
theorem inv16 : (build (BoardData.toX3C q16 C16) d16).Inv (BoardData.toX3C q16 C16) := lemmaD4 (OrthoDrawing.check_sound va16)
theorem s116 : Step1.ordOKB q16 C16 (Step1.ordOf d16) = true ∧ d16.kind = Step1.vkinds (BoardData.toX3C q16 C16) (Step1.ordOf d16) ∧ d16.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q16 C16) (Step1.ordOf d16) := by decide +kernel
theorem verdict16 : (BoardData.toX3C q16 C16).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q16 C16) (build (BoardData.toX3C q16 C16) d16)) := theorem3_drawing (OrthoDrawing.check_sound va16)
theorem inv17 : (build (BoardData.toX3C q17 C17) d17).Inv (BoardData.toX3C q17 C17) := lemmaD4 (OrthoDrawing.check_sound va17)
theorem s117 : Step1.ordOKB q17 C17 (Step1.ordOf d17) = true ∧ d17.kind = Step1.vkinds (BoardData.toX3C q17 C17) (Step1.ordOf d17) ∧ d17.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q17 C17) (Step1.ordOf d17) := by decide +kernel
theorem verdict17 : (BoardData.toX3C q17 C17).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q17 C17) (build (BoardData.toX3C q17 C17) d17)) := theorem3_drawing (OrthoDrawing.check_sound va17)
theorem inv18 : (build (BoardData.toX3C q18 C18) d18).Inv (BoardData.toX3C q18 C18) := lemmaD4 (OrthoDrawing.check_sound va18)
theorem s118 : Step1.ordOKB q18 C18 (Step1.ordOf d18) = true ∧ d18.kind = Step1.vkinds (BoardData.toX3C q18 C18) (Step1.ordOf d18) ∧ d18.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q18 C18) (Step1.ordOf d18) := by decide +kernel
theorem verdict18 : (BoardData.toX3C q18 C18).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q18 C18) (build (BoardData.toX3C q18 C18) d18)) := theorem3_drawing (OrthoDrawing.check_sound va18)
theorem inv19 : (build (BoardData.toX3C q19 C19) d19).Inv (BoardData.toX3C q19 C19) := lemmaD4 (OrthoDrawing.check_sound va19)
theorem s119 : Step1.ordOKB q19 C19 (Step1.ordOf d19) = true ∧ d19.kind = Step1.vkinds (BoardData.toX3C q19 C19) (Step1.ordOf d19) ∧ d19.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q19 C19) (Step1.ordOf d19) := by decide +kernel
theorem verdict19 : (BoardData.toX3C q19 C19).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q19 C19) (build (BoardData.toX3C q19 C19) d19)) := theorem3_drawing (OrthoDrawing.check_sound va19)
theorem inv20 : (build (BoardData.toX3C q20 C20) d20).Inv (BoardData.toX3C q20 C20) := lemmaD4 (OrthoDrawing.check_sound va20)
theorem s120 : Step1.ordOKB q20 C20 (Step1.ordOf d20) = true ∧ d20.kind = Step1.vkinds (BoardData.toX3C q20 C20) (Step1.ordOf d20) ∧ d20.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q20 C20) (Step1.ordOf d20) := by decide +kernel
theorem verdict20 : (BoardData.toX3C q20 C20).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q20 C20) (build (BoardData.toX3C q20 C20) d20)) := theorem3_drawing (OrthoDrawing.check_sound va20)
theorem inv21 : (build (BoardData.toX3C q21 C21) d21).Inv (BoardData.toX3C q21 C21) := lemmaD4 (OrthoDrawing.check_sound va21)
theorem s121 : Step1.ordOKB q21 C21 (Step1.ordOf d21) = true ∧ d21.kind = Step1.vkinds (BoardData.toX3C q21 C21) (Step1.ordOf d21) ∧ d21.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q21 C21) (Step1.ordOf d21) := by decide +kernel
theorem verdict21 : (BoardData.toX3C q21 C21).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q21 C21) (build (BoardData.toX3C q21 C21) d21)) := theorem3_drawing (OrthoDrawing.check_sound va21)
theorem inv22 : (build (BoardData.toX3C q22 C22) d22).Inv (BoardData.toX3C q22 C22) := lemmaD4 (OrthoDrawing.check_sound va22)
theorem s122 : Step1.ordOKB q22 C22 (Step1.ordOf d22) = true ∧ d22.kind = Step1.vkinds (BoardData.toX3C q22 C22) (Step1.ordOf d22) ∧ d22.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q22 C22) (Step1.ordOf d22) := by decide +kernel
theorem verdict22 : (BoardData.toX3C q22 C22).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q22 C22) (build (BoardData.toX3C q22 C22) d22)) := theorem3_drawing (OrthoDrawing.check_sound va22)
theorem inv23 : (build (BoardData.toX3C q23 C23) d23).Inv (BoardData.toX3C q23 C23) := lemmaD4 (OrthoDrawing.check_sound va23)
theorem s123 : Step1.ordOKB q23 C23 (Step1.ordOf d23) = true ∧ d23.kind = Step1.vkinds (BoardData.toX3C q23 C23) (Step1.ordOf d23) ∧ d23.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q23 C23) (Step1.ordOf d23) := by decide +kernel
theorem verdict23 : (BoardData.toX3C q23 C23).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q23 C23) (build (BoardData.toX3C q23 C23) d23)) := theorem3_drawing (OrthoDrawing.check_sound va23)
theorem inv24 : (build (BoardData.toX3C q24 C24) d24).Inv (BoardData.toX3C q24 C24) := lemmaD4 (OrthoDrawing.check_sound va24)
theorem s124 : Step1.ordOKB q24 C24 (Step1.ordOf d24) = true ∧ d24.kind = Step1.vkinds (BoardData.toX3C q24 C24) (Step1.ordOf d24) ∧ d24.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q24 C24) (Step1.ordOf d24) := by decide +kernel
theorem verdict24 : (BoardData.toX3C q24 C24).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q24 C24) (build (BoardData.toX3C q24 C24) d24)) := theorem3_drawing (OrthoDrawing.check_sound va24)
theorem inv25 : (build (BoardData.toX3C q25 C25) d25).Inv (BoardData.toX3C q25 C25) := lemmaD4 (OrthoDrawing.check_sound va25)
theorem s125 : Step1.ordOKB q25 C25 (Step1.ordOf d25) = true ∧ d25.kind = Step1.vkinds (BoardData.toX3C q25 C25) (Step1.ordOf d25) ∧ d25.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q25 C25) (Step1.ordOf d25) := by decide +kernel
theorem verdict25 : (BoardData.toX3C q25 C25).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q25 C25) (build (BoardData.toX3C q25 C25) d25)) := theorem3_drawing (OrthoDrawing.check_sound va25)
theorem inv26 : (build (BoardData.toX3C q26 C26) d26).Inv (BoardData.toX3C q26 C26) := lemmaD4 (OrthoDrawing.check_sound va26)
theorem s126 : Step1.ordOKB q26 C26 (Step1.ordOf d26) = true ∧ d26.kind = Step1.vkinds (BoardData.toX3C q26 C26) (Step1.ordOf d26) ∧ d26.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q26 C26) (Step1.ordOf d26) := by decide +kernel
theorem verdict26 : (BoardData.toX3C q26 C26).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q26 C26) (build (BoardData.toX3C q26 C26) d26)) := theorem3_drawing (OrthoDrawing.check_sound va26)
theorem inv27 : (build (BoardData.toX3C q27 C27) d27).Inv (BoardData.toX3C q27 C27) := lemmaD4 (OrthoDrawing.check_sound va27)
theorem s127 : Step1.ordOKB q27 C27 (Step1.ordOf d27) = true ∧ d27.kind = Step1.vkinds (BoardData.toX3C q27 C27) (Step1.ordOf d27) ∧ d27.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q27 C27) (Step1.ordOf d27) := by decide +kernel
theorem verdict27 : (BoardData.toX3C q27 C27).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q27 C27) (build (BoardData.toX3C q27 C27) d27)) := theorem3_drawing (OrthoDrawing.check_sound va27)
theorem inv28 : (build (BoardData.toX3C q28 C28) d28).Inv (BoardData.toX3C q28 C28) := lemmaD4 (OrthoDrawing.check_sound va28)
theorem s128 : Step1.ordOKB q28 C28 (Step1.ordOf d28) = true ∧ d28.kind = Step1.vkinds (BoardData.toX3C q28 C28) (Step1.ordOf d28) ∧ d28.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q28 C28) (Step1.ordOf d28) := by decide +kernel
theorem verdict28 : (BoardData.toX3C q28 C28).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q28 C28) (build (BoardData.toX3C q28 C28) d28)) := theorem3_drawing (OrthoDrawing.check_sound va28)
theorem inv29 : (build (BoardData.toX3C q29 C29) d29).Inv (BoardData.toX3C q29 C29) := lemmaD4 (OrthoDrawing.check_sound va29)
theorem s129 : Step1.ordOKB q29 C29 (Step1.ordOf d29) = true ∧ d29.kind = Step1.vkinds (BoardData.toX3C q29 C29) (Step1.ordOf d29) ∧ d29.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q29 C29) (Step1.ordOf d29) := by decide +kernel
theorem verdict29 : (BoardData.toX3C q29 C29).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q29 C29) (build (BoardData.toX3C q29 C29) d29)) := theorem3_drawing (OrthoDrawing.check_sound va29)
theorem inv30 : (build (BoardData.toX3C q30 C30) d30).Inv (BoardData.toX3C q30 C30) := lemmaD4 (OrthoDrawing.check_sound va30)
theorem s130 : Step1.ordOKB q30 C30 (Step1.ordOf d30) = true ∧ d30.kind = Step1.vkinds (BoardData.toX3C q30 C30) (Step1.ordOf d30) ∧ d30.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q30 C30) (Step1.ordOf d30) := by decide +kernel
theorem verdict30 : (BoardData.toX3C q30 C30).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q30 C30) (build (BoardData.toX3C q30 C30) d30)) := theorem3_drawing (OrthoDrawing.check_sound va30)
theorem inv31 : (build (BoardData.toX3C q31 C31) d31).Inv (BoardData.toX3C q31 C31) := lemmaD4 (OrthoDrawing.check_sound va31)
theorem s131 : Step1.ordOKB q31 C31 (Step1.ordOf d31) = true ∧ d31.kind = Step1.vkinds (BoardData.toX3C q31 C31) (Step1.ordOf d31) ∧ d31.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q31 C31) (Step1.ordOf d31) := by decide +kernel
theorem verdict31 : (BoardData.toX3C q31 C31).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q31 C31) (build (BoardData.toX3C q31 C31) d31)) := theorem3_drawing (OrthoDrawing.check_sound va31)
theorem inv32 : (build (BoardData.toX3C q32 C32) d32).Inv (BoardData.toX3C q32 C32) := lemmaD4 (OrthoDrawing.check_sound va32)
theorem s132 : Step1.ordOKB q32 C32 (Step1.ordOf d32) = true ∧ d32.kind = Step1.vkinds (BoardData.toX3C q32 C32) (Step1.ordOf d32) ∧ d32.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q32 C32) (Step1.ordOf d32) := by decide +kernel
theorem verdict32 : (BoardData.toX3C q32 C32).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q32 C32) (build (BoardData.toX3C q32 C32) d32)) := theorem3_drawing (OrthoDrawing.check_sound va32)
theorem inv33 : (build (BoardData.toX3C q33 C33) d33).Inv (BoardData.toX3C q33 C33) := lemmaD4 (OrthoDrawing.check_sound va33)
theorem s133 : Step1.ordOKB q33 C33 (Step1.ordOf d33) = true ∧ d33.kind = Step1.vkinds (BoardData.toX3C q33 C33) (Step1.ordOf d33) ∧ d33.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q33 C33) (Step1.ordOf d33) := by decide +kernel
theorem verdict33 : (BoardData.toX3C q33 C33).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q33 C33) (build (BoardData.toX3C q33 C33) d33)) := theorem3_drawing (OrthoDrawing.check_sound va33)
theorem inv34 : (build (BoardData.toX3C q34 C34) d34).Inv (BoardData.toX3C q34 C34) := lemmaD4 (OrthoDrawing.check_sound va34)
theorem s134 : Step1.ordOKB q34 C34 (Step1.ordOf d34) = true ∧ d34.kind = Step1.vkinds (BoardData.toX3C q34 C34) (Step1.ordOf d34) ∧ d34.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q34 C34) (Step1.ordOf d34) := by decide +kernel
theorem verdict34 : (BoardData.toX3C q34 C34).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q34 C34) (build (BoardData.toX3C q34 C34) d34)) := theorem3_drawing (OrthoDrawing.check_sound va34)
theorem inv35 : (build (BoardData.toX3C q35 C35) d35).Inv (BoardData.toX3C q35 C35) := lemmaD4 (OrthoDrawing.check_sound va35)
theorem s135 : Step1.ordOKB q35 C35 (Step1.ordOf d35) = true ∧ d35.kind = Step1.vkinds (BoardData.toX3C q35 C35) (Step1.ordOf d35) ∧ d35.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q35 C35) (Step1.ordOf d35) := by decide +kernel
theorem verdict35 : (BoardData.toX3C q35 C35).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q35 C35) (build (BoardData.toX3C q35 C35) d35)) := theorem3_drawing (OrthoDrawing.check_sound va35)
theorem inv36 : (build (BoardData.toX3C q36 C36) d36).Inv (BoardData.toX3C q36 C36) := lemmaD4 (OrthoDrawing.check_sound va36)
theorem s136 : Step1.ordOKB q36 C36 (Step1.ordOf d36) = true ∧ d36.kind = Step1.vkinds (BoardData.toX3C q36 C36) (Step1.ordOf d36) ∧ d36.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q36 C36) (Step1.ordOf d36) := by decide +kernel
theorem verdict36 : (BoardData.toX3C q36 C36).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q36 C36) (build (BoardData.toX3C q36 C36) d36)) := theorem3_drawing (OrthoDrawing.check_sound va36)
theorem inv37 : (build (BoardData.toX3C q37 C37) d37).Inv (BoardData.toX3C q37 C37) := lemmaD4 (OrthoDrawing.check_sound va37)
theorem s137 : Step1.ordOKB q37 C37 (Step1.ordOf d37) = true ∧ d37.kind = Step1.vkinds (BoardData.toX3C q37 C37) (Step1.ordOf d37) ∧ d37.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q37 C37) (Step1.ordOf d37) := by decide +kernel
theorem verdict37 : (BoardData.toX3C q37 C37).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q37 C37) (build (BoardData.toX3C q37 C37) d37)) := theorem3_drawing (OrthoDrawing.check_sound va37)
theorem inv38 : (build (BoardData.toX3C q38 C38) d38).Inv (BoardData.toX3C q38 C38) := lemmaD4 (OrthoDrawing.check_sound va38)
theorem s138 : Step1.ordOKB q38 C38 (Step1.ordOf d38) = true ∧ d38.kind = Step1.vkinds (BoardData.toX3C q38 C38) (Step1.ordOf d38) ∧ d38.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q38 C38) (Step1.ordOf d38) := by decide +kernel
theorem verdict38 : (BoardData.toX3C q38 C38).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q38 C38) (build (BoardData.toX3C q38 C38) d38)) := theorem3_drawing (OrthoDrawing.check_sound va38)
theorem inv39 : (build (BoardData.toX3C q39 C39) d39).Inv (BoardData.toX3C q39 C39) := lemmaD4 (OrthoDrawing.check_sound va39)
theorem s139 : Step1.ordOKB q39 C39 (Step1.ordOf d39) = true ∧ d39.kind = Step1.vkinds (BoardData.toX3C q39 C39) (Step1.ordOf d39) ∧ d39.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q39 C39) (Step1.ordOf d39) := by decide +kernel
theorem verdict39 : (BoardData.toX3C q39 C39).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q39 C39) (build (BoardData.toX3C q39 C39) d39)) := theorem3_drawing (OrthoDrawing.check_sound va39)
theorem inv40 : (build (BoardData.toX3C q40 C40) d40).Inv (BoardData.toX3C q40 C40) := lemmaD4 (OrthoDrawing.check_sound va40)
theorem s140 : Step1.ordOKB q40 C40 (Step1.ordOf d40) = true ∧ d40.kind = Step1.vkinds (BoardData.toX3C q40 C40) (Step1.ordOf d40) ∧ d40.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q40 C40) (Step1.ordOf d40) := by decide +kernel
theorem verdict40 : (BoardData.toX3C q40 C40).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q40 C40) (build (BoardData.toX3C q40 C40) d40)) := theorem3_drawing (OrthoDrawing.check_sound va40)
theorem inv41 : (build (BoardData.toX3C q41 C41) d41).Inv (BoardData.toX3C q41 C41) := lemmaD4 (OrthoDrawing.check_sound va41)
theorem s141 : Step1.ordOKB q41 C41 (Step1.ordOf d41) = true ∧ d41.kind = Step1.vkinds (BoardData.toX3C q41 C41) (Step1.ordOf d41) ∧ d41.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q41 C41) (Step1.ordOf d41) := by decide +kernel
theorem verdict41 : (BoardData.toX3C q41 C41).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q41 C41) (build (BoardData.toX3C q41 C41) d41)) := theorem3_drawing (OrthoDrawing.check_sound va41)
theorem inv42 : (build (BoardData.toX3C q42 C42) d42).Inv (BoardData.toX3C q42 C42) := lemmaD4 (OrthoDrawing.check_sound va42)
theorem s142 : Step1.ordOKB q42 C42 (Step1.ordOf d42) = true ∧ d42.kind = Step1.vkinds (BoardData.toX3C q42 C42) (Step1.ordOf d42) ∧ d42.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q42 C42) (Step1.ordOf d42) := by decide +kernel
theorem verdict42 : (BoardData.toX3C q42 C42).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q42 C42) (build (BoardData.toX3C q42 C42) d42)) := theorem3_drawing (OrthoDrawing.check_sound va42)
theorem inv43 : (build (BoardData.toX3C q43 C43) d43).Inv (BoardData.toX3C q43 C43) := lemmaD4 (OrthoDrawing.check_sound va43)
theorem s143 : Step1.ordOKB q43 C43 (Step1.ordOf d43) = true ∧ d43.kind = Step1.vkinds (BoardData.toX3C q43 C43) (Step1.ordOf d43) ∧ d43.edges.map (fun ε => (ε.u, ε.v)) = Step1.pairs (BoardData.toX3C q43 C43) (Step1.ordOf d43) := by decide +kernel
theorem verdict43 : (BoardData.toX3C q43 C43).ExactCover ↔ ArmyAllocation (G3pub (BoardData.toX3C q43 C43) (build (BoardData.toX3C q43 C43) d43)) := theorem3_drawing (OrthoDrawing.check_sound va43)

/-! The checks have teeth: a route that stops short of its target, a route through
another vertex's point, a wrong `q`, two routes leaving a set vertex in the same
direction (an edge of `d00` re-routed round the top to enter its set vertex from the
left, where another route already enters and shares its points),
and the board of another family are all rejected. -/
example : ({ d00 with edges := [⟨1, 0, [(0, 3), (0, 2)]⟩] ++ d00.edges.tail } : OrthoDrawing).check q00 C00 = false := by decide +kernel
example : ({ d00 with edges := [⟨1, 0, [(0, 3), (0, 2), (0, 1), (0, 0), (1, 0)]⟩, ⟨2, 0, [(2, 2), (1, 2), (1, 1), (1, 0)]⟩, ⟨3, 0, [(1, 1), (1, 0)]⟩] } : OrthoDrawing).check q00 C00 = false := by decide +kernel
example : d00.check 2 C00 = false := by decide +kernel
example : ({ d00 with edges := [⟨1, 0, [(0, 3), (0, 2), (0, 1), (0, 0), (1, 0)]⟩, ⟨2, 0, [(2, 2), (2, 1), (2, 0), (2, -1), (1, -1), (0, -1), (-1, -1), (-1, 0), (0, 0), (1, 0)]⟩, ⟨3, 0, [(1, 1), (1, 0)]⟩] } : OrthoDrawing).check q00 C00 = false := by decide +kernel
example : ¬ SameBoard d01 q01 C01 l02 k01 := by decide +kernel

#print axioms inv00
#print axioms eq00
#print axioms verdict00

end Homm3.DrawingData
