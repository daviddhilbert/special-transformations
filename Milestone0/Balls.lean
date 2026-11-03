/-
Self-contained `import Mathlib` file, milestone 0 of formalizing
Yimu Yin, "Special transformations in algebraically closed valued fields"
(APAL 2010, arXiv:1006.2467), Sections 2-3.

# Ball geometry and the C-relation (paper: Definitions 2.6, 2.7)

Order convention.  The paper orders `Γ` so that `𝒪 = rv⁻¹(RV^{≥1})` and
`ℳ = rv⁻¹(RV^{>1})`, i.e. "deeper into `ℳ` is bigger".  Mathlib orders the
value group the other way (`Valuation.valuationSubring = {x | v x ≤ 1}`, and
`v 0 = 0` is the *bottom*).  We keep Mathlib's convention.  Consequently the
paper's open ball `{b | v (b-a) > γ}` (with `γ` in the paper's order) is
`openBall v a γ⁻¹` below, and:

* the paper's radius `∞` ("each point is a closed ball of radius ∞") is `0` in
  Mathlib's `Γ₀`: see `closedBall_zero_eq_singleton`;
* the paper's radius `-∞` ("`VF` is a clopen ball of radius -∞") is the top of
  the extended value monoid, which Mathlib's `Γ₀` does not have; the whole
  space is recorded separately as `Set.univ` (`isBall_univ`).

`rad` (Definition 2.6) is *not* a function of a ball: a ball has many radii
(`openBall_eq_of_mem`), so we state everything about radii relationally.
-/
import Mathlib

open Valuation

set_option linter.unusedSectionVars false

namespace SpecialTransformations

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-! ### The RV conventions of `SpecialTransformations/Basic.lean`, copied verbatim -/

section RV

variable (v : Valuation K Γ₀)

/-- `RV× = Kˣ / (1 + M)`, the multiplicative RV sort. -/
abbrev RVUnit : Type _ := Kˣ ⧸ v.valuationSubring.principalUnitGroup

/-- The RV sort with the point at infinity: `RV = RV× ∪ {∞}`.  `none` is `∞`. -/
abbrev RV : Type _ := Option (RVUnit v)

/-- `RV0 = RV ∪ {0}`.  The outer `none` is the added `0`. -/
abbrev RV0 : Type _ := Option (RV v)

/-- The quotient map `rv : K → RV`, with `rv 0 = ∞`. -/
noncomputable def rv (x : K) : RV v := by
  classical
  exact if h : x = 0 then none else some (QuotientGroup.mk (Units.mk0 x h))

@[simp] theorem rv_zero : rv v 0 = none := by
  classical
  simp [rv]

theorem rv_eq_none_iff {a : K} : rv v a = none ↔ a = 0 := by
  classical
  by_cases h : a = 0
  · simp [rv, h]
  · simp [rv, h]

end RV

/-! ### The ultrametric triangle inequality -/

section Ultrametric

variable (v : Valuation K Γ₀)

/-- The ultrametric triangle inequality, in Mathlib's convention. -/
theorem v_sub_le_max (x y z : K) : v (x - z) ≤ max (v (x - y)) (v (y - z)) := by
  have h : x - z = (x - y) + (y - z) := by ring
  rw [h]
  exact v.map_add _ _

/-- `max a b = a` when `b < a`. -/
theorem max_eq_left_of_lt {a b : Γ₀} (h : b < a) : max a b = a := by
  rw [max_def, if_neg (not_le.mpr h)]

/-- From `a ≤ max b c` and `c < a` conclude `a ≤ b`. -/
theorem le_of_le_max_left_lt {a b c : Γ₀} (h : a ≤ max b c) (hc : c < a) : a ≤ b := by
  rw [max_def] at h
  split at h
  · exact absurd h (not_le.mpr hc)
  · exact h

/-- From `a ≤ max b c` and `b < a` conclude `a ≤ c`. -/
theorem le_of_le_max_right_lt {a b c : Γ₀} (h : a ≤ max b c) (hb : b < a) : a ≤ c := by
  rw [max_def] at h
  split at h
  · exact h
  · exact absurd h (not_le.mpr hb)

end Ultrametric

/-! ### Definition 2.6: open balls, closed balls, `rv`-balls -/

section Balls

variable (v : Valuation K Γ₀)

/-- The open ball of radius `γ` centred at `a` (Definition 2.6). -/
def openBall (a : K) (γ : Γ₀) : Set K := {b | v (b - a) < γ}

/-- The closed ball of radius `γ` centred at `a` (Definition 2.6). -/
def closedBall (a : K) (γ : Γ₀) : Set K := {b | v (b - a) ≤ γ}

/-- The `rv`-ball `rv⁻¹(t)` (Definition 2.6). -/
noncomputable def rvBall (t : RV v) : Set K := {a | rv v a = t}

/-- A single point, which Definition 2.6 calls a closed ball of radius `∞`. -/
def pointBall (a : K) : Set K := {a}

@[simp] theorem mem_openBall {a b : K} {γ : Γ₀} :
    b ∈ openBall v a γ ↔ v (b - a) < γ := Iff.rfl

@[simp] theorem mem_closedBall {a b : K} {γ : Γ₀} :
    b ∈ closedBall v a γ ↔ v (b - a) ≤ γ := Iff.rfl

@[simp] theorem mem_rvBall {a : K} {t : RV v} : a ∈ rvBall v t ↔ rv v a = t := Iff.rfl

@[simp] theorem mem_pointBall {a b : K} : b ∈ pointBall a ↔ b = a := Iff.rfl

/-- A point of a ball of radius `γ` that is `γ`-close to a centre is in the ball. -/
theorem mem_openBall_of_lt {a w y : K} {γ : Γ₀} (hw : w ∈ openBall v a γ)
    (h : v (y - w) < γ) : y ∈ openBall v a γ := by
  have h1 : v (y - a) ≤ max (v (y - w)) (v (w - a)) := v_sub_le_max v y w a
  exact lt_of_le_of_lt h1 (max_lt h hw)

/-- The same for closed balls. -/
theorem mem_closedBall_of_le {a w y : K} {γ : Γ₀} (hw : w ∈ closedBall v a γ)
    (h : v (y - w) ≤ γ) : y ∈ closedBall v a γ := by
  have h1 : v (y - a) ≤ max (v (y - w)) (v (w - a)) := v_sub_le_max v y w a
  exact le_trans h1 (max_le h hw)

theorem openBall_subset_closedBall (a : K) (γ : Γ₀) :
    openBall v a γ ⊆ closedBall v a γ := fun _ h => le_of_lt h

theorem openBall_zero (a : K) : openBall v a 0 = ∅ := by
  ext b
  simp [openBall]

theorem closedBall_zero_eq_singleton (a : K) :
    closedBall v a 0 = {a} := by
  ext b
  simp only [mem_closedBall, Set.mem_singleton_iff]
  constructor
  · intro h
    have h' : v (b - a) = 0 := le_antisymm h (by simp)
    exact sub_eq_zero.mp ((v.zero_iff).mp h')
  · rintro rfl
    rw [sub_self, v.map_zero]

theorem closedBall_antitone {a : K} {γ δ : Γ₀} (h : γ ≤ δ) :
    closedBall v a γ ⊆ closedBall v a δ := fun _ hb => le_trans hb h

/-- Any point of an open ball is a centre of that ball. -/
theorem openBall_eq_of_mem {a b : K} {γ : Γ₀} (h : b ∈ openBall v a γ) :
    openBall v b γ = openBall v a γ := by
  ext y
  constructor
  · intro hy
    exact mem_openBall_of_lt v h hy
  · intro hy
    exact mem_openBall_of_lt v (a := b) (w := a) (show v (a - b) < γ from by rwa [v.map_sub_swap a b]) hy

/-- Any point of a closed ball is a centre of that ball. -/
theorem closedBall_eq_of_mem {a b : K} {γ : Γ₀} (h : b ∈ closedBall v a γ) :
    closedBall v b γ = closedBall v a γ := by
  ext y
  constructor
  · intro hy
    exact mem_closedBall_of_le v h hy
  · intro hy
    exact mem_closedBall_of_le v (a := b) (w := a) (show v (a - b) ≤ γ from by rwa [v.map_sub_swap a b]) hy

/-- **Nesting**: two open balls are nested or disjoint. -/
theorem openBall_subset_or_subset {a b : K} {γ δ : Γ₀}
    (h : (openBall v a γ ∩ openBall v b δ).Nonempty) :
    openBall v a γ ⊆ openBall v b δ ∨ openBall v b δ ⊆ openBall v a γ := by
  obtain ⟨w, hwa, hwb⟩ := h
  rcases le_total γ δ with hγδ | hδγ
  · left
    intro y hy
    have h1 : v (y - w) < γ := by
      have := v_sub_le_max v y a w
      rw [v.map_sub_swap a w] at this
      exact lt_of_le_of_lt this (max_lt hy hwa)
    exact mem_openBall_of_lt v hwb (lt_of_lt_of_le h1 hγδ)
  · right
    intro y hy
    have h1 : v (y - w) < δ := by
      have := v_sub_le_max v y b w
      rw [v.map_sub_swap b w] at this
      exact lt_of_le_of_lt this (max_lt hy hwb)
    exact mem_openBall_of_lt v hwa (lt_of_lt_of_le h1 hδγ)

/-- **Nesting** for closed balls. -/
theorem closedBall_subset_or_subset {a b : K} {γ δ : Γ₀}
    (h : (closedBall v a γ ∩ closedBall v b δ).Nonempty) :
    closedBall v a γ ⊆ closedBall v b δ ∨ closedBall v b δ ⊆ closedBall v a γ := by
  obtain ⟨w, hwa, hwb⟩ := h
  rcases le_total γ δ with hγδ | hδγ
  · left
    intro y hy
    have h1 : v (y - w) ≤ γ := by
      have := v_sub_le_max v y a w
      rw [v.map_sub_swap a w] at this
      exact le_trans this (max_le hy hwa)
    exact mem_closedBall_of_le v hwb (le_trans h1 hγδ)
  · right
    intro y hy
    have h1 : v (y - w) ≤ δ := by
      have := v_sub_le_max v y b w
      rw [v.map_sub_swap b w] at this
      exact le_trans this (max_le hy hwb)
    exact mem_closedBall_of_le v hwa (le_trans h1 hδγ)

end Balls

/-! ### Definition 2.6: `rv`-balls are balls (the bridge between the quotient
definition of `RV` and the ball family of the paper) -/

section RVBridge

variable (v : Valuation K Γ₀)

/-- Membership in the principal units, phrased with `v` itself rather than with
the valuation of the associated valuation subring. -/
theorem mem_principalUnitGroup_iff_v (x : Kˣ) :
    x ∈ v.valuationSubring.principalUnitGroup ↔ v ((x : K) - 1) < 1 := by
  rw [ValuationSubring.mem_principalUnitGroup_iff]
  have h := Valuation.isEquiv_valuation_valuationSubring (v := v)
  have hle : v.valuationSubring.valuation ((x : K) - 1) ≤
      v.valuationSubring.valuation (1 : K) ↔ v ((x : K) - 1) ≤ v (1 : K) :=
    (h.le_iff_le (x := (x : K) - 1) (y := (1 : K))).symm
  rw [Valuation.map_one, Valuation.map_one] at hle
  have heq : v.valuationSubring.valuation ((x : K) - 1) = 1 ↔ v ((x : K) - 1) = 1 :=
    (h.eq_one_iff_eq_one (x := (x : K) - 1)).symm
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, hle]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hv => h2 (heq.mpr hv)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun ha => h2 (heq.mp ha)⟩

/-- `v a` is invertible for `a ≠ 0`. -/
theorem pos_map_of_ne_zero {a : K} (ha : a ≠ 0) : 0 < v a := by
  have h0 : v a ≠ 0 := fun h => ha ((v.zero_iff).mp h)
  exact lt_of_le_of_ne' zero_le h0

/-- The key computation: multiplying by `(v a)⁻¹` does not change the ordering
against `1`. -/
theorem mul_inv_lt_one_iff {a : K} (ha : a ≠ 0) (x : Γ₀) :
    x * (v a)⁻¹ < 1 ↔ x < v a := by
  have hv : 0 < v a := pos_map_of_ne_zero v ha
  constructor
  · intro h
    have h2 := mul_lt_mul_of_pos_right h hv
    have h3 : (x * (v a)⁻¹) * v a = x := by
      rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hv), mul_one]
    simpa [h3] using h2
  · intro h
    have h2 := mul_lt_mul_of_pos_right h (inv_pos.mpr hv)
    simpa [mul_inv_cancel₀ (ne_of_gt hv)] using h2

/-- **The bridge**: `rv a = rv b` iff `a` and `b` are within the open ball of
radius `v a` around `a`, i.e. the `rv`-fibres of `RV = Kˣ/(1+M)` are balls in
the sense of Definition 2.6. -/
theorem rv_eq_iff {a b : K} (ha : a ≠ 0) : rv v a = rv v b ↔ v (a - b) < v a := by
  classical
  rcases eq_or_ne b 0 with hb | hb
  · subst hb
    rw [rv_zero, rv_eq_none_iff, sub_zero]
    exact ⟨fun h => absurd h ha, fun h => absurd h (lt_irrefl _)⟩
  · have hrv_a : rv v a = some (QuotientGroup.mk (Units.mk0 a ha)) := by simp [rv, ha]
    have hrv_b : rv v b = some (QuotientGroup.mk (Units.mk0 b hb)) := by simp [rv, hb]
    rw [hrv_a, hrv_b, Option.some_inj, QuotientGroup.eq, mem_principalUnitGroup_iff_v]
    have hval : ((((Units.mk0 a ha)⁻¹ * Units.mk0 b hb : Kˣ) : K)) = a⁻¹ * b := by simp
    have hval2 : a⁻¹ * b - 1 = (b - a) / a := by
      rw [div_eq_mul_inv, sub_mul, mul_inv_cancel₀ ha, mul_comm b, sub_eq_add_neg]
    rw [hval, hval2, div_eq_mul_inv, v.map_mul, v.map_inv, mul_inv_lt_one_iff v ha,
      v.map_sub_swap b a]

/-- Definition 2.6, `rv`-ball form: the `rv`-ball of `rv b` is the open ball of
radius `v b` around `b` (for `b ≠ 0`; for `b = 0` the `rv`-ball is `{0}` and
`v 0 = 0` is not a radius). -/
theorem rvBall_eq_openBall {b : K} (hb : b ≠ 0) :
    rvBall v (rv v b) = openBall v b (v b) := by
  ext a
  rw [mem_rvBall, mem_openBall, eq_comm, rv_eq_iff v hb, v.map_sub_swap b a]

/-- The `rv`-balls partition the field. -/
theorem rvBall_disjoint {t s : RV v} (h : t ≠ s) : Disjoint (rvBall v t) (rvBall v s) := by
  rw [Set.disjoint_left]
  intro a ha hb
  rw [mem_rvBall] at ha hb
  exact h (ha.symm.trans hb)

theorem iUnion_rvBall : (⋃ t : RV v, rvBall v t) = Set.univ := by
  ext a
  simp only [Set.mem_iUnion, mem_rvBall, Set.mem_univ, iff_true]
  exact ⟨rv v a, rfl⟩

end RVBridge

/-! ### The C-relation

The paper never names a C-relation: Definition 2.7 says C-minimality is
"every parametrically definable subset of `VF(M)` is a boolean combination of
balls".  We record the C-relation of the ultrametric (in Mathlib's order:
`C x y z` iff `y` and `z` are closer to each other than `x` and `y`; the
paper's convention is `v (y-z) > v (x-y)`), and check that it satisfies the
C-relation axioms, so that "boolean combination of balls" is exactly
C-minimality in the sense of Macpherson-Steinhorn. -/

section CRelation

variable (v : Valuation K Γ₀)

/-- The C-relation of the valuation: `y` and `z` are closer to each other than
`x` and `y` are. -/
def Crel (x y z : K) : Prop := v (y - z) < v (x - y)

/-- Consequence of `C x y z`: `v (x - z) = v (x - y)`. -/
theorem v_sub_eq_of_Crel {x y z : K} (h : Crel v x y z) : v (x - z) = v (x - y) := by
  have h1 : v ((x - y) + (y - z)) = v (x - y) := v.map_add_eq_of_lt_left h
  rwa [show x - y + (y - z) = x - z by ring] at h1

theorem Crel_swap {x y z : K} (h : Crel v x y z) : Crel v x z y := by
  have h1 : v (x - z) = v (x - y) := v_sub_eq_of_Crel v h
  unfold Crel at *
  rw [h1, v.map_sub_swap z y]
  exact h

theorem Crel_asym {x y z : K} (h : Crel v x y z) : ¬ Crel v y x z := by
  intro h2
  have h1 : v (x - z) = v (x - y) := v_sub_eq_of_Crel v h
  unfold Crel at h2
  rw [h1, v.map_sub_swap y x] at h2
  exact lt_irrefl _ h2

theorem Crel_trans {x y z w : K} (h : Crel v x y z) : Crel v x y w ∨ Crel v w y z := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨h1, h2⟩ := hc
  unfold Crel at h1 h2 h
  rw [not_lt] at h1 h2
  rw [v.map_sub_swap w y] at h2
  exact absurd h (not_lt.mpr (le_trans h1 h2))

theorem Crel_trans' {x y z w : K} (h : Crel v x y z) : Crel v x z w ∨ Crel v w y z := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨h1, h2⟩ := hc
  unfold Crel at h1 h2
  rw [not_lt] at h1 h2
  have h3 : v (x - z) = v (x - y) := v_sub_eq_of_Crel v h
  have h4 : v (z - w) ≤ v (y - z) := by
    have h5 := v_sub_le_max v z y w
    rw [v.map_sub_swap z y, v.map_sub_swap y w] at h5
    exact le_trans h5 (max_le le_rfl h2)
  rw [h3] at h1
  exact absurd h (not_lt.mpr (le_trans h1 h4))

/-- The axioms of a C-relation. -/
structure IsCrelation (C : K → K → K → Prop) : Prop where
  /-- `C x y z → C x z y` -/
  swap : ∀ x y z, C x y z → C x z y
  /-- `C x y z → ¬ C y x z` -/
  asym : ∀ x y z, C x y z → ¬ C y x z
  /-- `C x y z → C x y w ∨ C w y z` -/
  trans : ∀ x y z w, C x y z → C x y w ∨ C w y z
  /-- `C x y z → C x z w ∨ C w y z` -/
  trans' : ∀ x y z w, C x y z → C x z w ∨ C w y z

/-- The valuation C-relation is a C-relation. -/
theorem isCrelation_Crel : IsCrelation (Crel v) where
  swap _ _ _ := Crel_swap v
  asym _ _ _ := Crel_asym v
  trans _ _ _ _ := Crel_trans v
  trans' _ _ _ _ := Crel_trans' v

end CRelation

/-! ### Definition 2.7: `C`-minimality

The paper: "Let `L` be a language expanding `L_RV`.  Let `M` be a structure of
`L` that satisfies the axioms for valued fields.  We say that `M` is
`C`-minimal if every parametrically definable subset of `VF(M)` is a boolean
combination of balls.  An `L`-theory `T` is `C`-minimal if every model of `T`
is `C`-minimal."

We separate the syntactic input (a family `D` of "parametrically definable"
subsets of the field) from the ball structure.  `LRV.lean` supplies `D` from
the actual two-sorted language `L_RV`; see `LRV.theorem_2_8`.
-/

section BoolComb

variable (v : Valuation K Γ₀)

/-- A set is a ball in the sense of Definition 2.6: an open ball, a closed
ball, an `rv`-ball, the whole space (radius `-∞`), or a single point (a closed
ball of radius `∞`). -/
def IsBall (s : Set K) : Prop :=
  (∃ a γ, s = openBall v a γ) ∨ (∃ a γ, s = closedBall v a γ) ∨
    (∃ t, s = rvBall v t) ∨ s = Set.univ ∨ (∃ a, s = pointBall a)

/-- `s` is a finite Boolean combination of balls: there are finitely many balls
`b i` and a Boolean function `t` of their membership pattern that cuts out
`s` exactly. -/
noncomputable def IsBoolCombOfBalls (s : Set K) : Prop := by
  classical
  exact ∃ (ι : Type) (_ : Fintype ι) (b : ι → Set K) (t : (ι → Bool) → Bool),
    (∀ i, IsBall v (b i)) ∧ ∀ x : K, (x ∈ s ↔ t (fun i => decide (x ∈ b i)) = true)

theorem isBoolCombOfBalls_of_isBall {s : Set K} (h : IsBall v s) :
    IsBoolCombOfBalls v s := by
  classical
  refine ⟨PUnit, inferInstance, fun _ => s, fun f => f ⟨⟩, fun _ => h, ?_⟩
  intro x
  simp

theorem isBoolCombOfBalls_empty : IsBoolCombOfBalls v (∅ : Set K) := by
  classical
  refine ⟨Fin 0, inferInstance, fun i => i.elim0, fun _ => false, fun i => i.elim0, ?_⟩
  intro x
  simp

theorem isBoolCombOfBalls_univ : IsBoolCombOfBalls v (Set.univ : Set K) := by
  classical
  refine ⟨Fin 0, inferInstance, fun i => i.elim0, fun _ => true, fun i => i.elim0, ?_⟩
  intro x
  simp

/-- Definition 2.7, with the syntax abstracted into a family `D` of
"parametrically definable" subsets of the field.  `LRV.lean` instantiates `D`
with the sets definable in the two-sorted language `L_RV`; see
`LRV.theorem_2_8`. -/
def IsCMinimal (D : Set (Set K)) : Prop := ∀ s ∈ D, IsBoolCombOfBalls v s

end BoolComb

section BoolCombLemmas

variable {v : Valuation K Γ₀}

theorem IsBoolCombOfBalls.compl {s : Set K} (hs : IsBoolCombOfBalls v s) :
    IsBoolCombOfBalls v sᶜ := by
  classical
  obtain ⟨ι, hι, b, t, hb, ht⟩ := hs
  refine ⟨ι, hι, b, fun f => !(t f), hb, ?_⟩
  intro x
  rw [Set.mem_compl_iff, ht x]
  cases h : t (fun i => decide (x ∈ b i)) <;> simp [h]

theorem IsBoolCombOfBalls.inter {s s' : Set K} (hs : IsBoolCombOfBalls v s)
    (hs' : IsBoolCombOfBalls v s') : IsBoolCombOfBalls v (s ∩ s') := by
  classical
  obtain ⟨ι, hι, b, t, hb, ht⟩ := hs
  obtain ⟨κ, hκ, c, u, hc, hu⟩ := hs'
  refine ⟨ι ⊕ κ, inferInstance,
    (fun i => match i with | Sum.inl i => b i | Sum.inr j => c j),
    (fun f => t (fun i => f (Sum.inl i)) && u (fun j => f (Sum.inr j))),
    ?_, ?_⟩
  · rintro (i | j)
    · exact hb i
    · exact hc j
  · intro x
    rw [Set.mem_inter_iff, ht x, hu x]
    have hpat : (fun i => decide (x ∈ match i with
        | Sum.inl i => b i | Sum.inr j => c j))
        = Sum.elim (fun i => decide (x ∈ b i)) (fun j => decide (x ∈ c j)) := by
      funext i
      cases i <;> rfl
    rw [hpat, Bool.and_eq_true]
    simp only [Sum.elim_inl, Sum.elim_inr]

theorem IsBoolCombOfBalls.union {s s' : Set K} (hs : IsBoolCombOfBalls v s)
    (hs' : IsBoolCombOfBalls v s') : IsBoolCombOfBalls v (s ∪ s') := by
  have h : s ∪ s' = (sᶜ ∩ s'ᶜ)ᶜ := by
    rw [Set.compl_inter, compl_compl, compl_compl, Set.union_eq_compl_compl_inter_compl]
  rw [h]
  exact (hs.compl.inter hs'.compl).compl

theorem IsBoolCombOfBalls.diff {s s' : Set K} (hs : IsBoolCombOfBalls v s)
    (hs' : IsBoolCombOfBalls v s') : IsBoolCombOfBalls v (s \ s') := by
  rw [Set.sdiff_eq]
  exact hs.inter hs'.compl

/-- The combinatorial workhorse behind every use of Definition 2.7 in the paper:
an infinite Boolean combination of balls contains an open ball.  (Provable from
`openBall_subset_or_subset` by choosing, at a point of the combination, the
minimal ball containing it; left as a target here.) -/
theorem infinite_boolComb_contains_openBall {s : Set K}
    (hne : ∀ a : K, ∃ γ, ∃ b : K, v (b - a) < γ)
    (hs : IsBoolCombOfBalls v s) (hinf : s.Infinite) :
    ∃ a γ, openBall v a γ ⊆ s := by
  sorry

end BoolCombLemmas

end SpecialTransformations
