module

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
public import Mathlib

@[expose] public section

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

/- The combinatorial workhorse behind every use of Definition 2.7 in the paper:
an infinite Boolean combination of balls contains an open ball.  Proved below. -/
set_option autoImplicit false
/-! ## 1. Every ball is an open ball, a closed ball, `univ` or a point

`IsBall` also allows `rv`-balls.  At a nonzero point an `rv`-ball *is* an open ball
(`rvBall_eq_openBall`), and an `rv`-ball is either empty or the `rv`-ball of one of its points, so
every `rv`-ball is an open ball or a point.  We therefore work with the four normal forms below. -/

/-- Balls in normal form: open ball, closed ball, the whole space, a point. -/
def IsBallN (s : Set K) : Prop :=
  (∃ a γ, s = openBall v a γ) ∨ (∃ a γ, s = closedBall v a γ) ∨
    s = Set.univ ∨ (∃ a, s = pointBall a)

/-- An `rv`-ball is empty or the open ball of radius `v a` around any of its points, unless that
point is `0`, in which case it is the point `0`. -/
theorem rvBall_normal (t : RV v) :
    (∃ a γ, rvBall v t = openBall v a γ) ∨ (∃ a, rvBall v t = pointBall a) := by
  by_cases h : ∃ a, a ∈ rvBall v t
  · obtain ⟨a, ha⟩ := h
    by_cases h0 : a = 0
    · right
      refine ⟨0, ?_⟩
      have ht : t = rv v 0 := by rw [← ha, h0]
      ext y
      rw [mem_rvBall, mem_pointBall, ht, rv_zero, rv_eq_none_iff]
    · left
      refine ⟨a, v a, ?_⟩
      rw [← rvBall_eq_openBall v h0, ← ha]
  · push_neg at h
    left
    refine ⟨0, 0, ?_⟩
    rw [openBall_zero]
    ext y
    simp only [mem_rvBall, Set.mem_empty_iff_false, iff_false]
    exact h y

/-- Every ball is in normal form. -/
theorem isBallN_of_isBall {s : Set K} (hs : IsBall v s) : IsBallN (v := v) s := by
  rcases hs with ⟨a, γ, rfl⟩ | ⟨a, γ, rfl⟩ | ⟨t, rfl⟩ | rfl | ⟨a, rfl⟩
  · exact Or.inl ⟨a, γ, rfl⟩
  · exact Or.inr (Or.inl ⟨a, γ, rfl⟩)
  · rcases rvBall_normal t with ⟨a, γ, h⟩ | ⟨a, h⟩
    · exact Or.inl ⟨a, γ, h⟩
    · exact Or.inr (Or.inr (Or.inr ⟨a, h⟩))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr ⟨a, rfl⟩))

/-! ## 2. A ball that is not a point contains an open ball at each of its nonzero-vicinity points -/

theorem pos_val_of_ne {x a : K} (h : x ≠ a) : 0 < v (x - a) := by
  rcases eq_or_ne (v (x - a)) 0 with h0 | h0
  · exact absurd (v.zero_iff.mp h0) (sub_ne_zero.mpr h)
  · exact lt_of_le_of_ne zero_le (Ne.symm h0)

/-- If `x` lies in the ball `s` and `s` is not contained in `{x}`, then an open ball around `x` lies
in `s`.  (`s = {x}` is exactly the excluded case: the point balls.) -/
theorem exists_openBall_subset_of_mem {s : Set K} (hs : IsBallN (v := v) s) {x : K} (hx : x ∈ s)
    (hnot : ¬ s ⊆ {x}) : ∃ γ, 0 < γ ∧ openBall v x γ ⊆ s := by
  rcases hs with ⟨a, δ, rfl⟩ | ⟨a, δ, rfl⟩ | rfl | ⟨a, rfl⟩
  · -- open ball
    have hδ : 0 < δ := lt_of_le_of_lt (zero_le : (0 : Γ₀) ≤ v (x - a)) hx
    refine ⟨δ, hδ, fun y hy => ?_⟩
    rw [mem_openBall] at hy hx ⊢
    exact lt_of_le_of_lt (v_sub_le_max v y x a) (max_lt hy hx)
  · -- closed ball
    by_cases hδ : δ = 0
    · exfalso
      apply hnot
      have hxa : x = a := by
        rw [hδ, closedBall_zero_eq_singleton] at hx
        exact hx
      intro y hy
      rw [hδ, closedBall_zero_eq_singleton] at hy
      exact hy.trans hxa.symm
    · have hδpos : 0 < δ := lt_of_le_of_ne zero_le (Ne.symm hδ)
      refine ⟨δ, hδpos, fun y hy => ?_⟩
      rw [mem_openBall] at hy
      rw [mem_closedBall]
      exact le_trans (v_sub_le_max v y x a) (max_le (le_of_lt hy) hx)
  · -- univ
    exact ⟨1, zero_lt_one, fun y _ => Set.mem_univ y⟩
  · -- point
    exfalso
    apply hnot
    intro y hy
    rw [mem_pointBall] at hy hx
    exact hy.trans hx.symm

/-- If `x` lies outside the ball `s`, then an open ball around `x` misses `s`. -/
theorem exists_openBall_disjoint {s : Set K} (hs : IsBallN (v := v) s) {x : K} (hx : x ∉ s) :
    ∃ γ, 0 < γ ∧ ∀ y, y ∈ openBall v x γ → y ∉ s := by
  rcases hs with ⟨a, δ, rfl⟩ | ⟨a, δ, rfl⟩ | rfl | ⟨a, rfl⟩
  · -- open ball
    by_cases hδ : δ = 0
    · refine ⟨1, zero_lt_one, fun y _ => ?_⟩
      rw [hδ, openBall_zero]
      exact Set.notMem_empty y
    · have hδpos : 0 < δ := lt_of_le_of_ne zero_le (Ne.symm hδ)
      have hxa : x ≠ a := by
        rintro rfl
        exact hx (by rw [mem_openBall]; simpa using hδpos)
      have hge : δ ≤ v (x - a) := by
        rw [mem_openBall] at hx
        exact not_lt.mp hx
      have hγpos : 0 < v (x - a) := lt_of_lt_of_le hδpos hge
      refine ⟨v (x - a), hγpos, fun y hy hyb => ?_⟩
      rw [mem_openBall] at hy hyb
      have hle := v_sub_le_max v x y a
      rw [v.map_sub_swap x y] at hle
      exact absurd (max_lt hy (lt_of_lt_of_le hyb hge)) (not_lt.mpr hle)
  · -- closed ball
    have hxa : x ≠ a := by
      rintro rfl
      exact hx (by rw [mem_closedBall]; simpa using (zero_le : (0 : Γ₀) ≤ δ))
    have hgt : δ < v (x - a) := by
      rw [mem_closedBall] at hx
      exact not_le.mp hx
    refine ⟨v (x - a), lt_of_le_of_lt zero_le hgt, fun y hy hyb => ?_⟩
    rw [mem_openBall] at hy
    rw [mem_closedBall] at hyb
    have hle := v_sub_le_max v x y a
    rw [v.map_sub_swap x y] at hle
    exact absurd (max_lt hy (lt_of_le_of_lt hyb hgt)) (not_lt.mpr hle)
  · -- univ
    exact absurd (Set.mem_univ x) hx
  · -- point
    have hxa : x ≠ a := by
      rintro rfl
      exact hx rfl
    refine ⟨v (x - a), pos_val_of_ne hxa, fun y hy hyb => ?_⟩
    rw [mem_pointBall] at hyb
    subst hyb
    rw [mem_openBall, v.map_sub_swap] at hy
    exact lt_irrefl _ hy

/-! ## 3. Atoms

The atom of `x` for a finite family `b` is the set of points with the same membership pattern. -/

/-- The atom of `x`: same membership pattern in the family `b`. -/
def atom {ι : Type} (b : ι → Set K) (x : K) : Set K := {y | ∀ i, (y ∈ b i ↔ x ∈ b i)}

theorem mem_atom_self {ι : Type} (b : ι → Set K) (x : K) : x ∈ atom b x :=
  fun _ => Iff.rfl

/-- **An infinite atom of a finite family of balls contains an open ball around any of its nonzero
points.**  Each ball either contains the point (and is not a point, so it contains a ball there) or
is at positive distance from it.  Finitely many positive radii have a positive minimum. -/
theorem atom_contains_openBall {ι : Type} [Fintype ι] [Nonempty ι] {b : ι → Set K}
    (hb : ∀ i, IsBall v (b i)) {x : K} (hx0 : x ≠ 0) (hinf : (atom b x).Infinite) :
    ∃ γ, 0 < γ ∧ openBall v x γ ⊆ atom b x := by
  classical
  have key : ∀ i, ∃ γ : Γ₀, 0 < γ ∧
      ((x ∈ b i → openBall v x γ ⊆ b i) ∧ (x ∉ b i → ∀ y, y ∈ openBall v x γ → y ∉ b i)) := by
    intro i
    by_cases hxi : x ∈ b i
    · have hnot : ¬ b i ⊆ {x} := by
        intro hsub
        have hsub' : atom b x ⊆ {x} := fun y hy => hsub ((hy i).mpr hxi)
        exact hinf (Set.Finite.subset (Set.finite_singleton x) hsub')
      obtain ⟨γ, hγ0, hγsub⟩ :=
        exists_openBall_subset_of_mem (isBallN_of_isBall (hb i)) hxi hnot
      exact ⟨γ, hγ0, fun _ => hγsub, fun h => absurd hxi h⟩
    · obtain ⟨γ, hγ0, hγ⟩ := exists_openBall_disjoint (isBallN_of_isBall (hb i)) hxi
      exact ⟨γ, hγ0, fun h => absurd h hxi, fun _ => hγ⟩
  let f : ι → Γ₀ := fun i => (key i).choose
  have hf0 : ∀ i, 0 < f i := fun i => (key i).choose_spec.1
  have hfmem : ∀ i, x ∈ b i → openBall v x (f i) ⊆ b i :=
    fun i => (key i).choose_spec.2.1
  have hfdis : ∀ i, x ∉ b i → ∀ y, y ∈ openBall v x (f i) → y ∉ b i :=
    fun i => (key i).choose_spec.2.2
  refine ⟨Finset.univ.inf' Finset.univ_nonempty f, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hf0 i)
  · intro y hy i
    have hyle : y ∈ openBall v x (f i) := by
      rw [mem_openBall] at hy ⊢
      exact lt_of_lt_of_le hy (Finset.inf'_le f (Finset.mem_univ i))
    by_cases hxi : x ∈ b i
    · exact ⟨fun _ => hxi, fun _ => hfmem i hxi hyle⟩
    · exact ⟨fun hyb => absurd hyb (hfdis i hxi y hyle), fun h => absurd h hxi⟩

/-! ## 4. The target: an infinite finite Boolean combination of balls contains an open ball -/

attribute [local instance] Classical.propDecidable

/-- The atom of `x` is the fibre of the membership pattern over the pattern of `x`. -/
theorem mem_atom_iff {ι : Type} (b : ι → Set K) (a y : K) :
    y ∈ atom b a ↔ (fun i => decide (y ∈ b i)) = (fun i => decide (a ∈ b i)) := by
  constructor
  · intro h
    funext i
    exact decide_eq_decide.mpr (h i)
  · intro h i
    exact decide_eq_decide.mp (congrFun h i)

/-- **The frozen target of `Milestone0/Balls.lean`.**  `IsBoolCombOfBalls` is a *finite* Boolean
combination of balls (`Fintype ι`), so the family has finitely many atoms; an infinite union of
finitely many sets has an infinite atom, and an infinite atom contains an open ball (§3).  The
hypothesis `hne` of the frozen statement is *not* used and is not needed. -/
theorem infinite_boolComb_contains_openBall_core {s : Set K}
    (hs : IsBoolCombOfBalls v s) (hinf : s.Infinite) :
    ∃ a γ, openBall v a γ ⊆ s := by
  classical
  obtain ⟨ι, hι, b, t, hb, ht⟩ := hs
  -- adjoin one dumb ball so that the index type is nonempty; the atoms are unchanged
  set b' : Option ι → Set K := fun o => o.elim Set.univ b with hb'
  have hb'ball : ∀ o, IsBall v (b' o) := by
    intro o
    cases o with
    | none => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | some i => exact hb i
  -- some atom meeting `s` is infinite
  have hex : ∃ p : Option ι → Bool, ({y : K | (fun o => decide (y ∈ b' o)) = p} ∩ s).Infinite := by
    by_contra h
    have hf : ∀ p, ({y : K | (fun o => decide (y ∈ b' o)) = p} ∩ s).Finite := by
      intro p
      exact Set.not_infinite.mp (fun hp => h ⟨p, hp⟩)
    have hsub : s ⊆ ⋃ p : (Option ι → Bool),
        ({y : K | (fun o => decide (y ∈ b' o)) = p} ∩ s) := by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨(fun o => decide (x ∈ b' o)), rfl, hx⟩
    have hU : (⋃ p : (Option ι → Bool),
        ({y : K | (fun o => decide (y ∈ b' o)) = p} ∩ s)).Finite := by
      have hfin := Set.Finite.biUnion (s := (Set.univ : Set (Option ι → Bool)))
        (t := fun p => ({y : K | (fun o => decide (y ∈ b' o)) = p} ∩ s))
        Set.finite_univ (fun p _ => hf p)
      simpa using hfin
    exact hinf (hU.subset hsub)
  obtain ⟨p, hp⟩ := hex
  -- an infinite set has a nonzero point
  have hne0 : ∃ x : K, x ∈ ({y : K | (fun o => decide (y ∈ b' o)) = p} ∩ s) ∧ x ≠ 0 := by
    by_contra h
    have hall : ∀ x : K, x ∈ ({y : K | (fun o => decide (y ∈ b' o)) = p} ∩ s) → x = 0 := by
      intro x hx
      by_contra hx0
      exact h ⟨x, hx, hx0⟩
    exact hp (Set.Finite.subset (Set.finite_singleton 0) hall)
  obtain ⟨x, hxF, hx0⟩ := hne0
  -- the atom of `x` is that infinite fibre
  have hatomx : atom b' x = {y : K | (fun o => decide (y ∈ b' o)) = p} := by
    ext y
    rw [mem_atom_iff b' x y, hxF.1]
    exact Iff.rfl
  have hFinf : (atom b' x).Infinite := by
    rw [hatomx]
    exact hp.mono Set.inter_subset_left
  obtain ⟨γ, hγ0, hγsub⟩ := atom_contains_openBall hb'ball hx0 hFinf
  -- the atom of a point of `s` lies in `s`
  have hatoms : atom b' x ⊆ s := by
    intro y hy
    have hy' : (fun o => decide (y ∈ b' o)) = (fun o => decide (x ∈ b' o)) :=
      (mem_atom_iff b' x y).mp hy
    have hxa : t (fun i => decide (x ∈ b i)) = true := ht x |>.mp hxF.2
    have hspec : (fun i => decide (y ∈ b i)) = (fun i => decide (x ∈ b i)) := by
      funext i
      have h := congrFun hy' (some i)
      simpa [hb'] using h
    exact (ht y).mpr (by rw [hspec]; exact hxa)
  exact ⟨x, γ, fun z hz => hatoms (hγsub hz)⟩


/-- **The frozen target of this file** (statement verbatim, proof complete): an infinite Boolean
combination of balls contains an open ball.  The hypothesis `hne` is not needed. -/
theorem infinite_boolComb_contains_openBall {s : Set K}
    (hne : ∀ a : K, ∃ γ, ∃ b : K, v (b - a) < γ)
    (hs : IsBoolCombOfBalls v s) (hinf : s.Infinite) :
    ∃ a γ, openBall v a γ ⊆ s :=
  infinite_boolComb_contains_openBall_core hs hinf

#print axioms infinite_boolComb_contains_openBall

end BoolCombLemmas

end SpecialTransformations
