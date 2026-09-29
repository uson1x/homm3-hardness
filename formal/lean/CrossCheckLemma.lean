import CrossCheckLemmaA
import CrossCheckLemmaB
import CrossCheckLemmaC
import CrossCheckLemmaD

/-!
# Session 4, target 5. Theorem 3 on the boards of Lemma D.4's construction

Every board that `embed_lemma.build_board_lemma` builds from the corpus of
`verify_embedding.py` (44 of 61 families; the other 17 are `G_no`: an element lies in
no set), **in the kernel**: `ckNN` — the board passes `BoardData.check`, so (I1)–(I4)
hold (`check_sound`) and `theorem3` applies; `cvNN` — exact cover by `coverCheck`;
`yesNN` / `noNN` — the game verdict through `theorem3` at both constant sets,
Corollary 3.1, and uniqueness of the all-ones allocation on yes-boards.  The Python
artifact plays the game only on the smallest of these boards; here every board gets
its verdict, because the invariants are checked and `theorem3` does the rest.  This is
Lemma D.4 **on this corpus**, not the lemma itself (which is universal over planar
incidence graphs; see PROGRESS.md, session 4).  The checks live in
`CrossCheckLemmaA`, `CrossCheckLemmaB`, `CrossCheckLemmaC`, `CrossCheckLemmaD` (split for parallel builds).
-/

namespace Homm3.LemmaData

open Homm3 BoardData

#print axioms yes00
#print axioms yes01
#print axioms yes02
#print axioms yes03
#print axioms yes04
#print axioms yes05
#print axioms yes06
#print axioms yes07
#print axioms yes08
#print axioms yes09
#print axioms yes10
#print axioms yes11
#print axioms no12
#print axioms yes13
#print axioms no14
#print axioms no15
#print axioms yes16
#print axioms yes17
#print axioms no18
#print axioms no19
#print axioms no20
#print axioms no21
#print axioms yes22
#print axioms no23
#print axioms yes24
#print axioms yes25
#print axioms yes26
#print axioms yes27
#print axioms yes28
#print axioms yes29
#print axioms yes30
#print axioms yes31
#print axioms yes32
#print axioms yes33
#print axioms yes34
#print axioms no35
#print axioms no36
#print axioms no37
#print axioms no38
#print axioms yes39
#print axioms yes40
#print axioms yes41
#print axioms yes42
#print axioms yes43

end Homm3.LemmaData
