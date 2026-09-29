import Homm3.X3CBoard

/-!
# Session 4, target 3. The machine facts of Appendix D: Lemma D.2, Lemma D.3, step 4

Paper: §3.3, Appendix C (the four adapter patterns), Appendix D.2 (Lemma D.2), D.3
(enemy gadget, Lemma D.3), D.4 steps 4–5 (separation, parity), D.6 (scope of the machine
checks).  Everything below is checked by the kernel (`decide` / `decide +kernel`), no
`native_decide`.

* **Translation invariance** (`nbrs_shift`, `adj_shift`): shifting by `(a, 2b)` — any column
  offset, an even row offset — maps neighbour lists to neighbour lists and preserves adjacency.
  This is D.4 step 5's parity argument ("the translation onto the board shifts rows by `Y − 4`
  with `Y` even ... the pattern carries over adjacency for adjacency").
* **Lemma D.2** (`lemmaD2`): for **every** hex, of the `C(6,3) = 20` triples of its neighbours
  (indices into `Hex.nbrs`, which has no repeats: `BoardData.nbrs_nodup`), exactly the two
  alternating triples `{0, 3, 5}` (W, NE, SE) and `{1, 2, 4}` (E, NW, SW) are pairwise
  non-adjacent — both row parities, by `decide` on two base hexes and translation.
  `enemy_gadget`: the gadget's dockings `TOP_LEFT (X, Y−1)`, `RIGHT (X+1, Y)`,
  `BOTTOM_LEFT (X, Y+1)` (`Y` even) are the alternating triple `{1, 2, 4}`.
* **Lemma D.3** (`lemmaD3`): the four `9 × 9` patterns of Appendix C, transcribed by
  `tools/appendix_c.py` from `main.md` (the tool also asserts that the printed pictures are
  `verify_x3c.ADAPTERS`), each pass `adapterOK`: three arms from the three used ports (the
  boundary midpoints), each a path of adjacent hexes inside the box, ending at a distinct
  docking of the alternating triple `U = (4,3)`, `R = (5,4)`, `D = (4,5)`, touching `Z = (4,4)`
  only at its last hex, no two arms sharing or touching a hex, the unused port impassable, the
  picture's free hexes exactly `Z` and the arms, and the arms matched to the dockings in cyclic
  order.
* **Step 4** (`adj_linf`, `not_adj_of_linf`, `sep_ineq`, `sep_constants`, `square_in_hex`,
  `old_draft_touch`): hex adjacency needs `L∞` distance `1`; features `λ` apart with boxes of
  radius `ρ` stay `λ − 2ρ` apart; `λ = 20`, `ρ = 4` give `12 ≥ 2`; the 4-neighbour square grid is
  inside hex adjacency in both parities; at the earlier draft's `λ = 9` (`9 − 8 = 1`) two hexes
  can touch; `ω = 6` keeps boxes at coordinates `≥ 2`, `ω = 2` does not.
-/

namespace Homm3

namespace Gadgets

/-! ## Translations -/

/-- Shift by `a` columns and `2b` rows. -/
def shift (a b : ℤ) (h : Hex) : Hex := ⟨h.x + a, h.y + 2 * b⟩

theorem nbrs_shift (a b : ℤ) (h : Hex) : (shift a b h).nbrs = h.nbrs.map (shift a b) := by
  rcases h with ⟨x, y⟩
  have hp : (y + 2 * b) % 2 = y % 2 := by omega
  simp only [Hex.nbrs, shift, hp, List.map_cons, List.map_nil, List.cons.injEq, Hex.mk.injEq]
  and_intros
  all_goals first | trivial | ring

theorem shift_inj {a b : ℤ} {p q : Hex} (h : shift a b p = shift a b q) : p = q := by
  simp only [shift, Hex.mk.injEq] at h
  ext <;> omega

/-- **Adjacency is invariant under column shifts and even row shifts.** -/
theorem adj_shift {a b : ℤ} {p q : Hex} : Hex.Adj (shift a b p) (shift a b q) ↔ Hex.Adj p q := by
  unfold Hex.Adj
  rw [nbrs_shift, List.mem_map]
  constructor
  · rintro ⟨r, hr, he⟩; exact shift_inj he ▸ hr
  · intro h; exact ⟨q, h, rfl⟩

/-- Every hex is a shift of `(0, 0)` or `(0, 1)`. -/
theorem eq_shift_base (h : Hex) : h = shift h.x (h.y / 2) ⟨0, h.y % 2⟩ := by
  ext <;> simp [shift] <;> omega

/-! ## Lemma D.2 (alternating triples) -/

/-- Neighbours `i, j, k` of `h` (indices into `Hex.nbrs`) are pairwise non-adjacent. -/
def Indep (h : Hex) (i j k : ℕ) : Prop :=
  ¬ Hex.Adj (h.nbrs.getD i h) (h.nbrs.getD j h) ∧ ¬ Hex.Adj (h.nbrs.getD i h) (h.nbrs.getD k h) ∧
    ¬ Hex.Adj (h.nbrs.getD j h) (h.nbrs.getD k h)

instance (h : Hex) (i j k : ℕ) : Decidable (Indep h i j k) := by unfold Indep; infer_instance

/-- The two alternating triples, `{0, 3, 5}` and `{1, 2, 4}`. -/
def IsAlt (i j k : ℕ) : Prop := (i = 0 ∧ j = 3 ∧ k = 5) ∨ (i = 1 ∧ j = 2 ∧ k = 4)

instance (i j k : ℕ) : Decidable (IsAlt i j k) := by unfold IsAlt; infer_instance

/-- The two base cases, one per row parity. -/
theorem lemmaD2_even : ∀ i < 6, ∀ j < 6, ∀ k < 6, (i < j ∧ j < k) →
    (Indep ⟨0, 0⟩ i j k ↔ IsAlt i j k) := by
  decide +kernel

theorem lemmaD2_odd : ∀ i < 6, ∀ j < 6, ∀ k < 6, (i < j ∧ j < k) →
    (Indep ⟨0, 1⟩ i j k ↔ IsAlt i j k) := by
  decide +kernel

theorem getD_shift (a b : ℤ) (h : Hex) (i : ℕ) :
    (shift a b h).nbrs.getD i (shift a b h) = shift a b (h.nbrs.getD i h) := by
  rw [nbrs_shift, List.getD_map]

theorem indep_shift (a b : ℤ) (h : Hex) (i j k : ℕ) :
    Indep (shift a b h) i j k ↔ Indep h i j k := by
  simp only [Indep, getD_shift, adj_shift]

/-- **Lemma D.2 (Alternating triples).** For every hex, the only pairwise non-adjacent triples
of its six neighbours are the two alternating triples `{0, 3, 5}` and `{1, 2, 4}` (in the order
of `Hex.nbrs`: W, E, NW, NE, SW, SE), in both row parities. -/
theorem lemmaD2 (h : Hex) {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < 6) :
    Indep h i j k ↔ (i = 0 ∧ j = 3 ∧ k = 5) ∨ (i = 1 ∧ j = 2 ∧ k = 4) := by
  rw [eq_shift_base h, indep_shift]
  rcases Int.emod_two_eq_zero_or_one h.y with hy | hy <;> rw [hy]
  · exact lemmaD2_even i (by omega) j (by omega) k hk ⟨hij, hjk⟩
  · exact lemmaD2_odd i (by omega) j (by omega) k hk ⟨hij, hjk⟩

/-- **The enemy gadget** (D.3): at `(X, Y)` with `Y` even, the dockings `TOP_LEFT (X, Y−1)`,
`RIGHT (X+1, Y)`, `BOTTOM_LEFT (X, Y+1)` are the neighbours `2, 1, 4` — the alternating triple
`{1, 2, 4}` — so they are pairwise non-adjacent, and each is adjacent to `(X, Y)`. -/
theorem enemy_gadget (X Y : ℤ) (hY : Y % 2 = 0) :
    (⟨X, Y⟩ : Hex).nbrs.getD 2 ⟨X, Y⟩ = ⟨X, Y - 1⟩ ∧ (⟨X, Y⟩ : Hex).nbrs.getD 1 ⟨X, Y⟩ = ⟨X + 1, Y⟩ ∧
    (⟨X, Y⟩ : Hex).nbrs.getD 4 ⟨X, Y⟩ = ⟨X, Y + 1⟩ ∧ Indep ⟨X, Y⟩ 1 2 4 ∧
    Hex.Adj ⟨X, Y - 1⟩ ⟨X, Y⟩ ∧ Hex.Adj ⟨X + 1, Y⟩ ⟨X, Y⟩ ∧ Hex.Adj ⟨X, Y + 1⟩ ⟨X, Y⟩ := by
  refine ⟨?_, ?_, ?_, (lemmaD2 _ (by norm_num) (by norm_num) (by norm_num)).mpr (Or.inr ⟨rfl, rfl, rfl⟩),
    ?_, ?_, ?_⟩
  · simp [Hex.nbrs, hY]
  · simp [Hex.nbrs]
  · simp [Hex.nbrs, hY]
  all_goals
    apply Hex.adj_symm
    simp [Hex.Adj, Hex.nbrs, hY]

/-! ## Lemma D.3 (the four adapters of Appendix C) -/

/-- A cell of the `9 × 9` local frame as a hex (row `4` even, as on the board). -/
def cell (c : ℕ × ℕ) : Hex := ⟨c.1, c.2⟩

def adjC (c d : ℕ × ℕ) : Bool := decide (Hex.Adj (cell c) (cell d))

/-- The enemy `Z`, the dockings `U, R, D` (clockwise), the ports top, right, bottom, left
(clockwise). -/
def cZ : ℕ × ℕ := (4, 4)
def docks : List (ℕ × ℕ) := [(4, 3), (5, 4), (4, 5)]
def ports : List (ℕ × ℕ) := [(4, 0), (8, 4), (4, 8), (0, 4)]

/-- The code of a cell in a printed picture: `0` `#`, `1` `.`, `2` `Z`, `3` a docking. -/
def gridAt (G : List (List ℕ)) (c : ℕ × ℕ) : ℕ := (G.getD c.2 []).getD c.1 0

/-- One arm: a path from its port to a docking, inside the box, touching `Z` only at its end. -/
def armOK (a : ℕ × List (ℕ × ℕ)) : Bool :=
  a.2.head? == some (ports.getD a.1 (0, 0)) &&
  (a.2.getLast?).any (fun c => docks.contains c && adjC c cZ) &&
  a.2.all (fun c => decide (c.1 < 9) && decide (c.2 < 9)) &&
  (a.2.zip a.2.tail).all (fun p => adjC p.1 p.2) &&
  a.2.dropLast.all (fun c => !adjC c cZ && c != cZ) &&
  decide a.2.Nodup

/-- The docking index (`U 0`, `R 1`, `D 2`) an arm ends at. -/
def dockIdx (a : ℕ × List (ℕ × ℕ)) : ℕ := docks.idxOf (a.2.getLastD (0, 0))

/-- **The adapter check** for the pattern `G` with arms `A` and the unused port `m`. -/
def adapterOK (G : List (List ℕ)) (A : List (ℕ × List (ℕ × ℕ))) (m : ℕ) : Bool :=
  -- three arms, one per used port, in clockwise port order
  A.map Prod.fst == (List.range 4).filter (· != m) &&
  A.all armOK &&
  -- their ends are the three dockings, one each
  docks.all (fun d => (A.filter (fun a => a.2.getLast? == some d)).length == 1) &&
  -- no two arms share or touch a hex
  A.all (fun a => A.all (fun b => a.1 == b.1 ||
    a.2.all (fun c => b.2.all (fun d => c != d && !adjC c d)))) &&
  -- the unused port is impassable
  gridAt G (ports.getD m (0, 0)) == 0 &&
  -- the printed picture is exactly `Z` and the arms, with `Z` and the dockings marked
  (List.range 9).all (fun y => (List.range 9).all (fun x =>
    (gridAt G (x, y) != 0) == ((x, y) == cZ || A.any (fun a => a.2.contains (x, y))))) &&
  gridAt G cZ == 2 && docks.all (fun d => gridAt G d == 3) &&
  -- cyclic order: clockwise ports go to clockwise dockings
  (match A with
   | [a, b, c] => (dockIdx b + 3 - dockIdx a) % 3 == 1 && (dockIdx c + 3 - dockIdx b) % 3 == 1
   | _ => false)

-- Transcribed by `tools/appendix_c.py` from Appendix C of `main.md` (pictures) and
-- `verify_x3c.ADAPTERS` (arms); ports `0` top, `1` right, `2` bottom, `3` left.

-- missing LEFT (TRB)
def gridLeft : List (List ℕ) :=
  [[0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 3, 0, 0, 0, 0],
   [0, 0, 0, 0, 2, 3, 1, 1, 1],
   [0, 0, 0, 0, 3, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0]]
def armsLeft : List (ℕ × List (ℕ × ℕ)) := [(0, [(4, 0), (4, 1), (4, 2), (4, 3)]),
  (1, [(8, 4), (7, 4), (6, 4), (5, 4)]), (2, [(4, 8), (4, 7), (4, 6), (4, 5)])]

-- missing RIGHT (TBL)
def gridRight : List (List ℕ) :=
  [[0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 3, 0, 0, 0, 0],
   [1, 1, 1, 0, 2, 3, 1, 0, 0],
   [0, 0, 1, 1, 3, 0, 1, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 1, 1, 1, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0]]
def armsRight : List (ℕ × List (ℕ × ℕ)) := [(0, [(4, 0), (4, 1), (4, 2), (4, 3)]),
  (2, [(4, 8), (4, 7), (5, 7), (6, 7), (6, 6), (6, 5), (6, 4), (5, 4)]),
  (3, [(0, 4), (1, 4), (2, 4), (2, 5), (3, 5), (4, 5)])]

-- missing BOTTOM (TRL)
def gridBottom : List (List ℕ) :=
  [[0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 3, 0, 0, 0, 0],
   [1, 1, 1, 0, 2, 3, 1, 1, 1],
   [0, 0, 1, 1, 3, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0]]
def armsBottom : List (ℕ × List (ℕ × ℕ)) := [(0, [(4, 0), (4, 1), (4, 2), (4, 3)]),
  (1, [(8, 4), (7, 4), (6, 4), (5, 4)]), (3, [(0, 4), (1, 4), (2, 4), (2, 5), (3, 5), (4, 5)])]

-- missing TOP (RBL)
def gridTop : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 1, 3, 0, 0, 0, 0],
   [1, 1, 1, 0, 2, 3, 1, 1, 1],
   [0, 0, 0, 0, 3, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 0]]
def armsTop : List (ℕ × List (ℕ × ℕ)) := [(1, [(8, 4), (7, 4), (6, 4), (5, 4)]),
  (2, [(4, 8), (4, 7), (4, 6), (4, 5)]), (3, [(0, 4), (1, 4), (2, 4), (2, 3), (3, 3), (4, 3)])]

/-- **Lemma D.3 (Adapters)**, checked hex by hex in the kernel: for each of the four missing
axis directions, the printed pattern of Appendix C passes `adapterOK`. -/
theorem lemmaD3 : adapterOK gridLeft armsLeft 3 = true ∧ adapterOK gridRight armsRight 1 = true ∧
    adapterOK gridBottom armsBottom 2 = true ∧ adapterOK gridTop armsTop 0 = true := by
  decide +kernel

/-- The checker has teeth: a wrong unused port, a picture that is not the arms', and a
fourth arm are rejected. -/
example : adapterOK gridLeft armsLeft 0 = false ∧ adapterOK gridRight armsLeft 3 = false ∧
    adapterOK gridBottom [(0, [(4, 0), (4, 1), (4, 2), (4, 3)]),
      (1, [(8, 4), (7, 4), (6, 4), (5, 4)]), (3, [(0, 4), (1, 4), (2, 4), (2, 5), (3, 5), (4, 5)]),
      (3, [(0, 4)])] 2 = false := by
  decide +kernel

/-- The alternating triple of the adapter frame is the enemy gadget's (`Z = (4, 4)`, row even):
`U, R, D` are the neighbours `2, 1, 4` of `Z`. -/
theorem docks_alt : docks.map cell = [(cell cZ).nbrs.getD 2 (cell cZ), (cell cZ).nbrs.getD 1 (cell cZ),
    (cell cZ).nbrs.getD 4 (cell cZ)] := by decide +kernel

/-! ## Step 4: separation -/

/-- `L∞` distance in offset coordinates. -/
def linf (p q : Hex) : ℤ := max |p.x - q.x| |p.y - q.y|

/-- **Hex adjacency needs `L∞` distance `1`.** -/
theorem adj_linf {p q : Hex} (h : Hex.Adj p q) : linf p q = 1 := by
  simp only [Hex.Adj, Hex.nbrs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases p with ⟨x, y⟩
  unfold linf
  rcases Int.emod_two_eq_zero_or_one y with hy | hy <;>
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hy]

theorem not_adj_of_linf {p q : Hex} (h : 2 ≤ linf p q) : ¬ Hex.Adj p q := fun ha => by
  rw [adj_linf ha] at h; omega

theorem linf_triangle (p q r : Hex) : linf p r ≤ linf p q + linf q r := by
  unfold linf
  have h1 := abs_sub_le p.x q.x r.x
  have h2 := abs_sub_le p.y q.y r.y
  refine max_le ?_ ?_
  · exact h1.trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact h2.trans (add_le_add (le_max_right _ _) (le_max_right _ _))

theorem linf_comm (p q : Hex) : linf p q = linf q p := by
  unfold linf; rw [abs_sub_comm p.x, abs_sub_comm p.y]

/-- **The separation inequality (SEP′)**: images of features `λ` apart, boxes of radius `ρ`
around them, leave their hexes `λ − 2ρ` apart. -/
theorem sep_ineq {lam ρ : ℤ} {p p' q q' : Hex} (h : lam ≤ linf p' q') (hp : linf p p' ≤ ρ)
    (hq : linf q q' ≤ ρ) : lam - 2 * ρ ≤ linf p q := by
  have h1 := linf_triangle p' p q'
  have h2 := linf_triangle p q q'
  rw [linf_comm] at hp
  linarith

/-- `λ = 20`, `ρ = 4`: non-incident features end `≥ 12 ≥ 2` apart, hence never adjacent. -/
theorem sep_constants {p p' q q' : Hex} (h : 20 ≤ linf p' q') (hp : linf p p' ≤ 4)
    (hq : linf q q' ≤ 4) : 12 ≤ linf p q ∧ ¬ Hex.Adj p q := by
  have := sep_ineq h hp hq
  exact ⟨by linarith, not_adj_of_linf (by linarith)⟩

/-- **The 4-neighbour square grid is a subgraph of hex adjacency**, in both row parities. -/
theorem square_in_hex (x y : ℤ) : Hex.Adj ⟨x, y⟩ ⟨x + 1, y⟩ ∧ Hex.Adj ⟨x, y⟩ ⟨x - 1, y⟩ ∧
    Hex.Adj ⟨x, y⟩ ⟨x, y + 1⟩ ∧ Hex.Adj ⟨x, y⟩ ⟨x, y - 1⟩ := by
  rcases Int.emod_two_eq_zero_or_one y with hy | hy <;>
  simp [Hex.Adj, Hex.nbrs, hy]

/-- The earlier draft's `λ = 9`, `ρ = 4` leaves `9 − 8 = 1`, and hexes at `L∞` distance `1` can
be adjacent — the failure the repair `λ = 20` removes. -/
theorem old_draft_touch : (9 : ℤ) - 2 * 4 = 1 ∧ ∃ p q : Hex, linf p q = 1 ∧ Hex.Adj p q :=
  ⟨by norm_num, ⟨0, 0⟩, ⟨1, 0⟩, by decide, by decide⟩

/-- The offset `ω = 6 > ρ = 4` keeps every box at coordinates `≥ 2`; the earlier `ω = 2` put a
corner box at `−2`. -/
theorem offset_constants : (6 : ℤ) - 4 = 2 ∧ (2 : ℤ) - 4 < 0 := by norm_num

end Gadgets

end Homm3
