 /-
**The bridge from a `v x ≤ v y` predicate to a Mathlib `Valuation`.**

For a field `S` with a binary predicate `vle`, `ValuedPredicate S vle` collects the semantic
axioms (total, transitive, `vle x 0 ↔ x = 0`, multiplicative, ultrametric), and
`ValuedPredicate.exists_valuation` produces a genuine Mathlib `Valuation S Γ₀` into a
`LinearOrderedCommGroupWithZero` with `v x ≤ v y ↔ vle x y`; `ofValuation` is the converse.  So
an abstract `Language.val`-structure need only unpack its axioms into `ValuedPredicate` to get a
real valuation, and the value group is `Sˣ / {u | v u = 1}` ordered by the predicate on
representatives.

This is what makes the single-sorted `Language.val` (`QE/PrimeModels_val_partial.lean`) and the
Mathlib `Valuation` framework (`QE/Johnson23_valuation.lean`) interchangeable.  From swarm
`smw0c60wk` member m1; compiled and axiom-checked by the reviewer, not edited.

Only import: Mathlib.
-/

/-
# From the raw predicate `v x ≤ v y` to a Mathlib `Valuation`

The one-sorted language `L_val` of valued fields has, besides the ring operations, a single binary
relation symbol interpreted as `v x ≤ v y`.  Everything that runs Johnson's criterion at
`T₀` = valued fields has to start from an *abstract* `L_val`-structure and recover an honest
Mathlib `Valuation` from the predicate alone.  This file does that.

* `ValuedPredicate S vle` — the relational axioms (totality, transitivity, support
  `v x ≤ v 0 ↔ x = 0`, multiplicativity, ultrametric inequality) on a field `S`;
* `ValuedPredicate.exists_valuation` — **the bridge**: there are `Γ₀` with
  `LinearOrderedCommGroupWithZero Γ₀` and `v : Valuation S Γ₀` with `v x ≤ v y ↔ vle x y`;
* `ValuedPredicate.ofValuation` — **soundness**: the predicate of a genuine valuation satisfies the
  axioms, so the two descriptions agree on the nose.

The value group is the quotient `Sˣ ⧸ {u | v u = 1}` of the unit group, ordered by the predicate on
representatives.  The order is well defined because a factor of value one can be stripped from
either side of `v x ≤ v y`, which is where multiplicativity is used.
-/
import Mathlib

set_option linter.unusedVariables false

namespace ValBridge

variable {S : Type} [Field S] {vle : S → S → Prop}

/-- The relational axioms of a valued field, on a field `S`, for the predicate `vle x y` read as
`v x ≤ v y`.  The ring axioms are supplied by the field structure on `S`. -/
structure ValuedPredicate (S : Type) [Field S] (vle : S → S → Prop) : Prop where
  /-- the relation is total -/
  total : ∀ x y : S, vle x y ∨ vle y x
  /-- the relation is transitive -/
  trans : ∀ x y z : S, vle x y → vle y z → vle x z
  /-- the support is trivial: `v x ≤ v 0` exactly for `x = 0` -/
  eq_zero : ∀ x : S, vle x 0 ↔ x = 0
  /-- multiplicativity -/
  mul : ∀ x y z : S, z ≠ 0 → (vle (x * z) (y * z) ↔ vle x y)
  /-- the ultrametric inequality -/
  add : ∀ x y : S, vle (x + y) x ∨ vle (x + y) y

namespace ValuedPredicate

section Basic

variable (h : ValuedPredicate S vle)

theorem refl (h : ValuedPredicate S vle) (x : S) : vle x x := (h.total x x).elim id id

theorem pred_zero_le (h : ValuedPredicate S vle) (x : S) : vle 0 x := by
  rcases h.total 0 x with hx | hx
  · exact hx
  · rw [h.eq_zero x] at hx
    subst hx
    exact h.refl 0

theorem le_zero_iff (h : ValuedPredicate S vle) (x : S) : vle x 0 ↔ x = 0 := h.eq_zero x

/-- `v y ≤ v (y * c)` and back, when `c` has value one. -/
theorem le_mul_of_value_one (h : ValuedPredicate S vle) {c : S}
    (h1 : vle c 1) (h2 : vle 1 c) (y : S) :
    vle y (y * c) ∧ vle (y * c) y := by
  have hc : c ≠ 0 := by
    rintro rfl
    rw [h.eq_zero] at h2
    exact one_ne_zero h2
  rcases eq_or_ne y 0 with rfl | hy0
  · refine ⟨?_, ?_⟩ <;> simpa using h.refl (0 : S)
  · exact ⟨by simpa [mul_comm] using (h.mul 1 c y hy0).2 h2,
      by simpa [mul_comm] using (h.mul c 1 y hy0).2 h1⟩

/-- A factor of value one can be stripped from the left argument. -/
theorem strip_left (h : ValuedPredicate S vle) {c : S}
    (h1 : vle c 1) (h2 : vle 1 c) (x y : S) : vle (x * c) y ↔ vle x y := by
  obtain ⟨hyc, hcy⟩ := h.le_mul_of_value_one h1 h2 y
  have hc : c ≠ 0 := by
    rintro rfl
    rw [h.eq_zero] at h2
    exact one_ne_zero h2
  exact ⟨fun hxy => (h.mul x y c hc).1 (h.trans _ _ _ hxy hyc),
    fun hxy => h.trans _ _ _ ((h.mul x y c hc).2 hxy) hcy⟩

/-- A factor of value one can be stripped from the right argument. -/
theorem strip_right (h : ValuedPredicate S vle) {c : S}
    (h1 : vle c 1) (h2 : vle 1 c) (x y : S) : vle x (y * c) ↔ vle x y := by
  obtain ⟨hcy, hyc⟩ := h.le_mul_of_value_one h1 h2 y
  exact ⟨fun hxy => h.trans _ _ _ hxy hyc, fun hxy => h.trans _ _ _ hxy hcy⟩

/-- The units of value one: `{u : Sˣ | v u = 1}`. -/
def unitSubgroup (h : ValuedPredicate S vle) : Subgroup Sˣ where
  carrier := {u | vle (u : S) 1 ∧ vle 1 (u : S)}
  one_mem' := ⟨h.refl 1, h.refl 1⟩
  mul_mem' := by
    rintro u w ⟨hu1, hu2⟩ ⟨hw1, hw2⟩
    have huw : ((u * w : Sˣ) : S) = (u : S) * (w : S) := Units.val_mul u w
    refine ⟨?_, ?_⟩
    · rw [huw]
      exact h.trans _ _ _ (by simpa using (h.mul (u : S) 1 (w : S) (Units.ne_zero w)).2 hu1) hw1
    · rw [huw]
      exact h.trans _ _ _ hw2 (by simpa using (h.mul 1 (u : S) (w : S) (Units.ne_zero w)).2 hu2)
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    refine ⟨?_, ?_⟩
    · simpa using (h.mul 1 (u : S) ((u⁻¹ : Sˣ) : S) (Units.ne_zero u⁻¹)).2 hu2
    · simpa using (h.mul (u : S) 1 ((u⁻¹ : Sˣ) : S) (Units.ne_zero u⁻¹)).2 hu1

/-- **The value group** of the predicate: units modulo units of value one. -/
abbrev valueGroup (h : ValuedPredicate S vle) : Type := Sˣ ⧸ h.unitSubgroup

theorem mem_unitSubgroup_iff (h : ValuedPredicate S vle) {u : Sˣ} :
    u ∈ h.unitSubgroup ↔ vle (u : S) 1 ∧ vle 1 (u : S) := Iff.rfl

/-- `v u ≤ v w` depends only on the classes of `u` and `w` in the value group. -/
theorem le_wellDefined (h : ValuedPredicate S vle) {u₁ w₁ u₂ w₂ : Sˣ}
    (h₁ : (QuotientGroup.leftRel h.unitSubgroup) u₁ u₂)
    (h₂ : (QuotientGroup.leftRel h.unitSubgroup) w₁ w₂) :
    vle (u₁ : S) (w₁ : S) = vle (u₂ : S) (w₂ : S) := by
  rw [QuotientGroup.leftRel_apply] at h₁ h₂
  obtain ⟨hc1, hc2⟩ := h₁
  obtain ⟨hd1, hd2⟩ := h₂
  have hu : (u₁ * (u₁⁻¹ * u₂) : Sˣ) = u₂ := by simp
  have hw : (w₁ * (w₁⁻¹ * w₂) : Sˣ) = w₂ := by simp
  have key : vle ((u₁ * (u₁⁻¹ * u₂) : Sˣ) : S) ((w₁ * (w₁⁻¹ * w₂) : Sˣ) : S) ↔
      vle (u₁ : S) (w₁ : S) := by
    rw [Units.val_mul, Units.val_mul]
    exact (h.strip_right hd1 hd2 _ _).trans (h.strip_left hc1 hc2 _ _)
  rw [hu, hw] at key
  exact propext key.symm

/-- The order on the value group: `v u ≤ v w` on representatives. -/
def leOf (h : ValuedPredicate S vle) (a b : h.valueGroup) : Prop :=
  Quotient.liftOn₂ a b (fun u w : Sˣ => vle (u : S) (w : S))
    (fun u₁ w₁ u₂ w₂ h₁ h₂ => h.le_wellDefined h₁ h₂)

theorem leOf_mk (h : ValuedPredicate S vle) (u w : Sˣ) :
    h.leOf (Quotient.mk (QuotientGroup.leftRel h.unitSubgroup) u)
      (Quotient.mk (QuotientGroup.leftRel h.unitSubgroup) w) ↔ vle (u : S) (w : S) :=
  Iff.rfl

/-- The order on the value group. -/
instance instLE (h : ValuedPredicate S vle) : LE h.valueGroup := ⟨h.leOf⟩

theorem mk_le_mk_iff (h : ValuedPredicate S vle) (u w : Sˣ) :
    @LE.le h.valueGroup (instLE h) (Quotient.mk (QuotientGroup.leftRel h.unitSubgroup) u)
      (Quotient.mk (QuotientGroup.leftRel h.unitSubgroup) w) ↔ vle (u : S) (w : S) :=
  Iff.rfl

theorem mk'_le_mk'_iff (h : ValuedPredicate S vle) (u w : Sˣ) :
    @LE.le h.valueGroup (instLE h) (QuotientGroup.mk' h.unitSubgroup u)
      (QuotientGroup.mk' h.unitSubgroup w) ↔ vle (u : S) (w : S) :=
  Iff.rfl

noncomputable instance instLinearOrder (h : ValuedPredicate S vle) : LinearOrder h.valueGroup where
  le := h.leOf
  le_refl := by
    intro a
    induction a using Quotient.inductionOn with
    | h u => exact (h.mk_le_mk_iff u u).2 (h.refl _)
  le_trans := by
    intro a b c
    induction a using Quotient.inductionOn with
    | h u =>
      induction b using Quotient.inductionOn with
      | h w =>
        induction c using Quotient.inductionOn with
        | h x =>
          intro hab hbc
          exact (h.mk_le_mk_iff _ _).2
            (h.trans _ _ _ ((h.mk_le_mk_iff u w).1 hab) ((h.mk_le_mk_iff w x).1 hbc))
  le_antisymm := by
    intro a b hab hba
    induction a using Quotient.inductionOn with
    | h u =>
      induction b using Quotient.inductionOn with
      | h w =>
        refine Quotient.sound ?_
        show (QuotientGroup.leftRel h.unitSubgroup) u w
        rw [QuotientGroup.leftRel_apply, h.mem_unitSubgroup_iff]
        have h2 : vle (u : S) (w : S) := (h.mk_le_mk_iff u w).1 hab
        have h3 : vle (w : S) (u : S) := (h.mk_le_mk_iff w u).1 hba
        constructor
        · simpa [Units.val_mul, mul_comm] using
            (h.mul (w : S) (u : S) ((u⁻¹ : Sˣ) : S) (Units.ne_zero u⁻¹)).2 h3
        · simpa [Units.val_mul, mul_comm] using
            (h.mul (u : S) (w : S) ((u⁻¹ : Sˣ) : S) (Units.ne_zero u⁻¹)).2 h2
  le_total := by
    intro a b
    induction a using Quotient.inductionOn with
    | h u =>
      induction b using Quotient.inductionOn with
      | h w =>
        rcases h.total (u : S) (w : S) with hle | hle
        · exact Or.inl ((h.mk_le_mk_iff u w).2 hle)
        · exact Or.inr ((h.mk_le_mk_iff w u).2 hle)
  toDecidableLE := Classical.decRel _

noncomputable instance instIsOrderedMonoid (h : ValuedPredicate S vle) : IsOrderedMonoid h.valueGroup where
  mul_le_mul_left := by
    intro a b hab c
    induction a using Quotient.inductionOn with
    | h u =>
      induction b using Quotient.inductionOn with
      | h w =>
        induction c using Quotient.inductionOn with
        | h x =>
          have h1 : vle (u : S) (w : S) := (h.mk_le_mk_iff u w).1 hab
          have h2 : vle ((u * x : Sˣ) : S) ((w * x : Sˣ) : S) := by
            rw [Units.val_mul, Units.val_mul]
            exact (h.mul (u : S) (w : S) (x : S) (Units.ne_zero x)).2 h1
          exact (h.mk_le_mk_iff (u * x) (w * x)).2 h2

/-- The value group with zero adjoined is a `LinearOrderedCommGroupWithZero`. -/
abbrev codomain (h : ValuedPredicate S vle) : Type := WithZero h.valueGroup

noncomputable instance instCodomain (h : ValuedPredicate S vle) : LinearOrderedCommGroupWithZero h.codomain :=
  inferInstanceAs (LinearOrderedCommGroupWithZero (WithZero h.valueGroup))

end Basic

section Valuation

attribute [local instance] Classical.propDecidable

variable (h : ValuedPredicate S vle)

/-- The valuation map: `0 ↦ 0`, and a nonzero element maps to its class in the value group. -/
noncomputable def toFun (h : ValuedPredicate S vle) (x : S) : h.codomain :=
  if hx : x = 0 then 0
  else ((QuotientGroup.mk' h.unitSubgroup (Units.mk0 x hx) : h.valueGroup) : h.codomain)

theorem toFun_zero (h : ValuedPredicate S vle) : h.toFun 0 = 0 := by
  simp [toFun]

theorem toFun_of_ne (h : ValuedPredicate S vle) {x : S} (hx : x ≠ 0) :
    h.toFun x = ((QuotientGroup.mk' h.unitSubgroup (Units.mk0 x hx) : h.valueGroup) : h.codomain) := by
  simp only [toFun, dif_neg hx]

theorem toFun_eq_zero_iff (h : ValuedPredicate S vle) (x : S) : h.toFun x = 0 ↔ x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [toFun]
  · rw [h.toFun_of_ne hx]
    exact ⟨fun hc => absurd hc WithZero.coe_ne_zero, fun hc => absurd hc hx⟩

theorem toFun_mul (h : ValuedPredicate S vle) (x y : S) :
    h.toFun (x * y) = h.toFun x * h.toFun y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [toFun]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [toFun]
  rw [h.toFun_of_ne hx, h.toFun_of_ne hy, h.toFun_of_ne (mul_ne_zero hx hy)]
  have hunit : Units.mk0 x hx * Units.mk0 y hy
      = Units.mk0 (x * y) (mul_ne_zero hx hy) := Units.ext rfl
  have h2 : (((QuotientGroup.mk' h.unitSubgroup (Units.mk0 x hx) *
      QuotientGroup.mk' h.unitSubgroup (Units.mk0 y hy) : h.valueGroup)) : h.codomain) =
      ((QuotientGroup.mk' h.unitSubgroup (Units.mk0 (x * y) (mul_ne_zero hx hy)) :
        h.valueGroup) : h.codomain) := by
    rw [← map_mul (QuotientGroup.mk' h.unitSubgroup), hunit]
  rw [← h2]
  exact WithZero.coe_mul _ _

theorem toFun_one (h : ValuedPredicate S vle) : h.toFun 1 = 1 := by
  rw [h.toFun_of_ne one_ne_zero]
  have hone : Units.mk0 (1 : S) one_ne_zero = 1 := Units.ext rfl
  rw [hone, map_one, WithZero.coe_one]

theorem toFun_le_iff (h : ValuedPredicate S vle) {x y : S} :
    h.toFun x ≤ h.toFun y ↔ vle x y := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [h.toFun_zero]
    constructor
    · intro hle
      rw [h.le_zero_iff, ← h.toFun_eq_zero_iff x]
      exact le_antisymm hle (bot_le)
    · intro hle
      rw [(h.le_zero_iff x).1 hle, h.toFun_zero]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [h.toFun_zero, h.toFun_of_ne hy]
    exact ⟨fun _ => h.pred_zero_le (y : S), fun _ => bot_le⟩
  · rw [h.toFun_of_ne hx, h.toFun_of_ne hy, WithZero.coe_le_coe, h.mk'_le_mk'_iff]
    simp

theorem toFun_add_le (h : ValuedPredicate S vle) (x y : S) :
    h.toFun (x + y) ≤ max (h.toFun x) (h.toFun y) := by
  rcases eq_or_ne (x + y) 0 with hxy | hxy
  · rw [hxy, h.toFun_zero]
    exact bot_le
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_add, h.toFun_zero]
    exact (le_max_right _ _)
  rcases eq_or_ne y 0 with rfl | hy
  · rw [add_zero, h.toFun_zero]
    exact (le_max_left _ _)
  have hle : h.toFun (x + y) ≤ h.toFun x ∨ h.toFun (x + y) ≤ h.toFun y := by
    rcases h.add x y with h' | h'
    · exact Or.inl ((h.toFun_le_iff).2 h')
    · exact Or.inr ((h.toFun_le_iff).2 h')
  rcases hle with h' | h'
  · exact h'.trans (le_max_left _ _)
  · exact h'.trans (le_max_right _ _)

/-- **The valuation attached to a valued-field predicate.** -/
noncomputable def toValuation (h : ValuedPredicate S vle) : Valuation S h.codomain where
  toFun := h.toFun
  map_zero' := h.toFun_zero
  map_one' := h.toFun_one
  map_mul' := h.toFun_mul
  map_add_le_max' := h.toFun_add_le

theorem toValuation_le_iff (h : ValuedPredicate S vle) (x y : S) :
    h.toValuation x ≤ h.toValuation y ↔ vle x y := h.toFun_le_iff

/-- **The bridge: every field with a predicate satisfying the axioms of a valuation carries a
Mathlib valuation with exactly that predicate.** -/
theorem exists_valuation (h : ValuedPredicate S vle) :
    ∃ (Γ₀ : Type) (hΓ : LinearOrderedCommGroupWithZero Γ₀),
      letI := hΓ
      ∃ v : Valuation S Γ₀, ∀ x y : S, v x ≤ v y ↔ vle x y :=
  ⟨h.codomain, h.instCodomain, h.toValuation, h.toValuation_le_iff⟩

end Valuation

/-- **Soundness**: the predicate `v x ≤ v y` of a genuine valuation satisfies the axioms. -/
theorem ofValuation {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation S Γ₀) : ValuedPredicate S (fun x y => v x ≤ v y) where
  total _ _ := le_total _ _
  trans _ _ _ := le_trans
  eq_zero x := by
    rw [Valuation.map_zero]
    refine ⟨fun h => ?_, fun h => by rw [h, Valuation.map_zero]⟩
    exact v.zero_iff.1 (le_antisymm h (zero_le : (0 : Γ₀) ≤ v x))
  mul x y z hz := by
    rw [v.map_mul, v.map_mul]
    exact mul_le_mul_iff_left₀ (zero_lt_iff.mpr (v.ne_zero_iff.mpr hz))
  add x y := by
    by_cases h : v (x + y) ≤ v x
    · exact Or.inl h
    · push_neg at h
      by_cases h2 : v (x + y) ≤ v y
      · exact Or.inr h2
      · push_neg at h2
        exact absurd (v.map_add_le_max' x y) (not_le.mpr (max_lt h h2))

end ValuedPredicate

end ValBridge

/-! ## Axiom check -/

#print axioms ValBridge.ValuedPredicate.exists_valuation
#print axioms ValBridge.ValuedPredicate.toValuation_le_iff
#print axioms ValBridge.ValuedPredicate.ofValuation
#print axioms ValBridge.ValuedPredicate.mk_le_mk_iff
