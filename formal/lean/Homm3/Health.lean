import Homm3.Battle

/-!
# Session 2, target 3. The engine's health representation `(fullUnits, firstHPleft)`
# and the pool of the Lean model

Source of truth: `homm3/MODEL.md` §3 (Definitions 3.2, 3.3, "Damage application", "Kill
count"), rules R5, R6, R8; `homm3/scripts/homm3_model.py` (`Stack.__init__`, `count`,
`available`, `_set_from_total`, `apply_damage`, `kills_for_damage`).

The engine stores a stack's health as `(fullUnits, firstHPleft)` with `firstHPleft ∈ (0, hp]`
for a living stack and `(0, 0)` for a dead one (`Valid`).  The Lean model (`Battle.lean`)
stores only the pool `avail = firstHPleft + hp · fullUnits`.  With `hp ≥ 1`:

* `equivPool`: valid engine states are in bijection with pools (`avail`, inverse `ofPool`);
* `count_eq_pool`: the engine's `count = fullUnits + [firstHPleft > 0]` equals the model's
  `⌈avail / hp⌉` (`Stack.count`); `alive_iff`: alive iff `avail > 0`;
* `avail_applyDamage`: the engine's damage application (both branches, the overkill clamp,
  the `firstHPleft = 0 ∧ fullUnits ≥ 1` correction) acts on `avail` as truncated
  subtraction — the model's `Stack.hit`; `ofPool_sub` states it as a commuting square;
* `kills_eq`: the engine's kill-count formula `kills(D)` equals the drop in `count`;
* `fresh`: a fresh stack of `c` creatures (`fullUnits = c − 1`, `firstHPleft = hp`) has pool
  `c · hp`, as `initUnits` sets it;
* `Stack.*_engine`: the same facts phrased for the model's `Stack`.
-/

namespace Homm3

/-- The engine's health pair (MODEL.md Def. 3.2). -/
@[ext] structure EHealth where
  full : ℕ
  first : ℕ
  deriving DecidableEq, Repr

namespace EHealth

variable (hp : ℕ)

/-- The engine's invariant: `firstHPleft ∈ (0, hp]`, or the stack is empty `(0, 0)`. -/
def Valid (e : EHealth) : Prop := (e.full = 0 ∧ e.first = 0) ∨ (0 < e.first ∧ e.first ≤ hp)

/-- R5: `avail = firstHPleft + hp · fullUnits`. -/
def avail (e : EHealth) : ℕ := e.first + hp * e.full

/-- R6: `count = fullUnits + [firstHPleft > 0]`. -/
def count (e : EHealth) : ℕ := e.full + if 0 < e.first then 1 else 0

/-- A fresh stack of `c` creatures (`homm3_model.Stack.__init__`). -/
def fresh (c : ℕ) : EHealth := if 0 < c then ⟨c - 1, hp⟩ else ⟨0, 0⟩

/-- `_set_from_total` (MODEL.md: `CUnitState.cpp:262-273`), literally. -/
def setFromTotal (total : ℕ) : EHealth :=
  if total % hp = 0 ∧ 1 ≤ total / hp then ⟨total / hp - 1, hp⟩ else ⟨total / hp, total % hp⟩

/-- R8, `apply_damage` (MODEL.md: `CUnitState.cpp:193-218`), literally: below `firstHPleft`
only the top creature is hurt; otherwise the total is recomputed, clamped at `0`
(`max(0, avail − D)` is truncated subtraction). -/
def applyDamage (e : EHealth) (D : ℕ) : EHealth :=
  if D < e.first then ⟨e.full, e.first - D⟩
  else if avail hp e - D = 0 then ⟨0, 0⟩ else setFromTotal hp (avail hp e - D)

/-- R8, the kill count (MODEL.md: `DamageCalculator.cpp:522-531`), literally. -/
def kills (e : EHealth) (D : ℕ) : ℕ :=
  if D < e.first then 0 else min (1 + (D - e.first) / hp) (count e)

/-- The engine state of a pool. -/
def ofPool (p : ℕ) : EHealth := if p = 0 then ⟨0, 0⟩ else ⟨(p - 1) / hp, (p - 1) % hp + 1⟩

/-- The model's count of a pool, `⌈p / hp⌉` (`Stack.count`). -/
def poolCount (p : ℕ) : ℕ := (p + hp - 1) / hp

variable {hp}

theorem valid_ofPool (h : 1 ≤ hp) (p : ℕ) : Valid hp (ofPool hp p) := by
  unfold ofPool Valid
  split_ifs
  · exact Or.inl ⟨rfl, rfl⟩
  · right; have := Nat.mod_lt (p - 1) (show 0 < hp by omega); simp only; omega

theorem avail_ofPool (p : ℕ) : avail hp (ofPool hp p) = p := by
  unfold ofPool avail
  split_ifs with hp0
  · simp [hp0]
  · have := Nat.mod_add_div (p - 1) hp
    simp only
    omega

/-- Division with remainder, packaged: `x = r + hp·q` with `r < hp` determines `q, r`. -/
theorem divmod_of (h : 1 ≤ hp) {x q r : ℕ} (hx : x = r + hp * q) (hr : r < hp) :
    x / hp = q ∧ x % hp = r :=
  (Nat.div_mod_unique (by omega)).mpr ⟨hx.symm, hr⟩

theorem ofPool_avail (h : 1 ≤ hp) {e : EHealth} (hv : Valid hp e) : ofPool hp (avail hp e) = e := by
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · ext <;> simp [ofPool, avail, h1, h2]
  · have hpos : avail hp e ≠ 0 := by unfold avail; omega
    obtain ⟨hq, hr⟩ := divmod_of h (x := avail hp e - 1) (q := e.full) (r := e.first - 1)
      (by unfold avail; omega) (by omega)
    ext <;> simp only [ofPool, hpos, ↓reduceIte, hq, hr] <;> omega

/-- **Health pool ≡ engine representation**: valid engine states and pools are in bijection. -/
def equivPool (h : 1 ≤ hp) : {e : EHealth // Valid hp e} ≃ ℕ where
  toFun e := avail hp e.1
  invFun p := ⟨ofPool hp p, valid_ofPool h p⟩
  left_inv e := Subtype.ext (ofPool_avail h e.2)
  right_inv p := avail_ofPool p

/-- R6 agrees: the engine's count is the model's `⌈avail / hp⌉`. -/
theorem count_ofPool (h : 1 ≤ hp) (p : ℕ) : count (ofPool hp p) = poolCount hp p := by
  unfold poolCount
  by_cases hp0 : p = 0
  · subst hp0; simp [ofPool, count, Nat.div_eq_of_lt (show hp - 1 < hp by omega)]
  · have := Nat.div_add_mod (p - 1) hp
    obtain ⟨hq, -⟩ := divmod_of h (x := p + hp - 1) (q := (p - 1) / hp + 1)
      (r := (p - 1) % hp) (by rw [Nat.mul_succ]; omega) (Nat.mod_lt _ (by omega))
    rw [hq]; simp [ofPool, count, hp0]

theorem count_eq_pool (h : 1 ≤ hp) {e : EHealth} (hv : Valid hp e) :
    count e = poolCount hp (avail hp e) := by
  rw [← count_ofPool h, ofPool_avail h hv]

theorem alive_iff (h : 1 ≤ hp) {e : EHealth} (hv : Valid hp e) : 0 < count e ↔ 0 < avail hp e := by
  rw [count_eq_pool h hv, poolCount]
  constructor
  · intro hc; by_contra h0; rw [show avail hp e = 0 by omega, zero_add,
      Nat.div_eq_of_lt (by omega)] at hc; omega
  · intro ha; exact Nat.div_pos (by omega) (by omega)

theorem valid_fresh (h : 1 ≤ hp) (c : ℕ) : Valid hp (fresh hp c) := by
  unfold fresh Valid; split_ifs
  · right; simp only; omega
  · left; simp

theorem avail_fresh (c : ℕ) : avail hp (fresh hp c) = c * hp := by
  unfold fresh avail; split_ifs with hc
  · simp only
    obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  · simp [show c = 0 by omega]

theorem count_fresh (h : 1 ≤ hp) (c : ℕ) : count (fresh hp c) = c := by
  unfold fresh count; split_ifs <;> simp_all <;> omega

theorem setFromTotal_eq (h : 1 ≤ hp) {t : ℕ} (ht : 0 < t) : setFromTotal hp t = ofPool hp t := by
  have hdm := Nat.div_add_mod t hp
  have hlt := Nat.mod_lt t (show 0 < hp by omega)
  unfold setFromTotal ofPool
  rw [if_neg (show t ≠ 0 by omega)]
  split_ifs with hc
  · -- `hp ∣ t`: the correction branch
    obtain ⟨hq, hr⟩ := divmod_of h (x := t - 1) (q := t / hp - 1) (r := hp - 1)
      (by
        have : hp * (t / hp) = hp * (t / hp - 1) + hp := by
          rw [← Nat.mul_succ]; congr 1; omega
        omega) (by omega)
    ext <;> simp only [hq, hr] <;> omega
  · have hr0 : t % hp ≠ 0 := by
      intro h0; apply hc; refine ⟨h0, ?_⟩
      by_contra hq
      have : t / hp = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_le hq)
      rw [this, h0] at hdm; omega
    obtain ⟨hq, hr⟩ := divmod_of h (x := t - 1) (q := t / hp) (r := t % hp - 1)
      (by omega) (by omega)
    ext <;> simp only [hq, hr] <;> omega

/-- **R8 agrees**: the engine's damage application acts on `avail` as truncated
subtraction, i.e. as the model's `Stack.hit`. -/
theorem avail_applyDamage (h : 1 ≤ hp) {e : EHealth} (hv : Valid hp e) (D : ℕ) :
    avail hp (applyDamage hp e D) = avail hp e - D := by
  unfold applyDamage
  split_ifs with h1 h2
  · simp only [avail]; generalize hp * e.full = m; omega
  · rw [h2]; simp [avail]
  · rw [setFromTotal_eq h (by omega), avail_ofPool]

theorem valid_applyDamage (h : 1 ≤ hp) {e : EHealth} (hv : Valid hp e) (D : ℕ) :
    Valid hp (applyDamage hp e D) := by
  unfold applyDamage
  split_ifs with h1 h2
  · right; rcases hv with ⟨-, h3⟩ | ⟨-, h3⟩ <;> simp only <;> omega
  · left; simp
  · rw [setFromTotal_eq h (by omega)]; exact valid_ofPool h _

/-- The commuting square: damaging the engine state of pool `p` gives the engine state of
pool `p − D`. -/
theorem ofPool_sub (h : 1 ≤ hp) (p D : ℕ) : applyDamage hp (ofPool hp p) D = ofPool hp (p - D) := by
  have hv := valid_applyDamage h (valid_ofPool h p) D
  rw [← ofPool_avail h hv, avail_applyDamage h (valid_ofPool h p), avail_ofPool]

/-- `⌈(hp·q − r)/hp⌉ = q − ⌊r/hp⌋` in truncated arithmetic. -/
theorem poolCount_sub (h : 1 ≤ hp) (q r : ℕ) : poolCount hp (hp * q - r) = q - r / hp := by
  have hdm := Nat.div_add_mod r hp
  have hlt := Nat.mod_lt r (show 0 < hp by omega)
  unfold poolCount
  generalize r / hp = a at hdm ⊢
  generalize r % hp = b at hdm hlt
  by_cases hqa : q ≤ a
  · have : hp * q ≤ hp * a := Nat.mul_le_mul_left hp hqa
    rw [show hp * q - r = 0 by omega, zero_add, Nat.div_eq_of_lt (by omega)]; omega
  · obtain ⟨m, rfl⟩ : ∃ m, q = a + (m + 1) := ⟨q - a - 1, by omega⟩
    have e1 : hp * (a + (m + 1)) = hp * a + hp * m + hp := by ring
    have e2 : (m + 1 + 1) * hp = hp * m + hp + hp := by ring
    have e3 : (m + 1) * hp = hp * m + hp := by ring
    rw [show a + (m + 1) - a = m + 1 by omega]
    apply Nat.div_eq_of_lt_le
    · rw [e3]; rw [e1]; omega
    · rw [e2]; rw [e1]; omega

/-- **The kill count agrees**: the engine's `kills(D)` is exactly the drop in `count`
caused by `applyDamage`, for every valid state and every `D`. -/
theorem kills_eq (h : 1 ≤ hp) {e : EHealth} (hv : Valid hp e) (D : ℕ) :
    kills hp e D = count e - count (applyDamage hp e D) := by
  have hc := count_eq_pool h hv
  rw [← ofPool_avail h hv, ofPool_sub h, ofPool_avail h hv, count_ofPool h]
  unfold kills
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- the empty stack
    rw [if_neg (by omega), hc, show avail hp e = 0 by simp [avail, h1, h2]]
    simp [poolCount, Nat.div_eq_of_lt (show hp - 1 < hp by omega)]
  · rw [hc]
    have hA : avail hp e = e.first + hp * e.full := rfl
    have hcA : poolCount hp (avail hp e) = e.full + 1 := by
      rw [← hc]; simp [count, h1]
    rw [hcA]
    split_ifs with hD
    · -- only the top creature is hurt
      have : poolCount hp (avail hp e - D) = e.full + 1 := by
        unfold poolCount
        apply Nat.div_eq_of_lt_le
        · rw [hA, show (e.full + 1) * hp = hp * e.full + hp by ring]
          generalize hp * e.full = m; omega
        · rw [hA, show (e.full + 1 + 1) * hp = hp * e.full + hp + hp by ring]
          generalize hp * e.full = m; omega
      omega
    · have hsub : avail hp e - D = hp * e.full - (D - e.first) := by rw [hA]; omega
      rw [hsub, poolCount_sub h]
      have hdm := Nat.div_add_mod (D - e.first) hp
      generalize (D - e.first) / hp = a at hdm ⊢
      omega

/-- Hand-checked against `homm3_model.Stack.apply_damage` / `kills_for_damage` (`hp = 5`,
three fresh creatures): 7 damage takes the top creature and 2 of the next — `(1, 3)`, one
kill; 5 damage hits the correction branch (`total = 10`, `10 mod 5 = 0`) — `(1, 5)`. -/
example : applyDamage 5 (fresh 5 3) 7 = ⟨1, 3⟩ ∧ kills 5 (fresh 5 3) 7 = 1 ∧
    applyDamage 5 (fresh 5 3) 5 = ⟨1, 5⟩ ∧ kills 5 (fresh 5 3) 5 = 1 ∧
    applyDamage 5 (fresh 5 3) 16 = ⟨0, 0⟩ ∧ kills 5 (fresh 5 3) 16 = 3 := by decide

end EHealth

/-! ## The model's `Stack` is the engine's, read through `ofPool` -/

namespace Stack

theorem count_engine (u : Stack) (h : 1 ≤ u.type.hp) :
    u.count = EHealth.count (EHealth.ofPool u.type.hp u.pool) := by
  rw [EHealth.count_ofPool h]; rfl

theorem alive_engine (u : Stack) (h : 1 ≤ u.type.hp) :
    u.alive ↔ 0 < EHealth.count (EHealth.ofPool u.type.hp u.pool) := by
  rw [EHealth.alive_iff h (EHealth.valid_ofPool h _), EHealth.avail_ofPool]; rfl

theorem hit_engine (u : Stack) (h : 1 ≤ u.type.hp) (D : ℕ) :
    EHealth.ofPool u.type.hp (u.hit D).pool =
      EHealth.applyDamage u.type.hp (EHealth.ofPool u.type.hp u.pool) D := by
  rw [EHealth.ofPool_sub h]; rfl

/-- The model's kills (drop in `count`) are the engine's `kills(D)`. -/
theorem kills_engine (u : Stack) (h : 1 ≤ u.type.hp) (D : ℕ) :
    u.count - (u.hit D).count = EHealth.kills u.type.hp (EHealth.ofPool u.type.hp u.pool) D := by
  rw [EHealth.kills_eq h (EHealth.valid_ofPool h _), ← hit_engine u h, count_engine u h]
  congr 1
  exact count_engine (u.hit D) h

/-- The model's starting pool `c · hp` is the engine's fresh stack. -/
theorem fresh_engine (hp c : ℕ) (h : 1 ≤ hp) :
    EHealth.ofPool hp (c * hp) = EHealth.fresh hp c := by
  rw [← EHealth.avail_fresh (hp := hp) c, EHealth.ofPool_avail h (EHealth.valid_fresh h c)]

end Stack

end Homm3
