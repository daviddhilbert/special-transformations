import CanonicalRV
import RVValueMap

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace CanonicalRV

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

@[simp] theorem equiv_zero : (equiv v hv none).1 = iRVZero := by
  rw [← _root_.RVCalc.rv_zero (v := v), equiv_rv]
  exact RVCalc.rv_zero_eq hM

@[simp] theorem equiv_one : (equiv v hv (_root_.RVCalc.rv v 1)).1 = iRVOne := by
  rw [equiv_rv]
  exact RVCalc.rv_one hM

/-- The encoding order is the reverse of Mathlib's absolute-value order. -/
theorem le_equiv_iff (a b : _root_.RVCalc.RV v) :
    iLe (equiv v hv a).1 (equiv v hv b).1 ↔
      _root_.RVCalc.vrv v b ≤ _root_.RVCalc.vrv v a := by
  obtain ⟨x, rfl⟩ := rv_surjective v a
  obtain ⟨y, rfl⟩ := rv_surjective v b
  rw [equiv_rv, equiv_rv, _root_.RVCalc.vrv_rv, _root_.RVCalc.vrv_rv]
  exact hv y x

theorem equiv_ne_zero_iff (a : _root_.RVCalc.RV v) :
    (equiv v hv a).1 ≠ iRVZero ↔ a ≠ none := by
  rw [← equiv_zero v hv]
  constructor
  · intro h he
    exact h (congrArg (fun z => (equiv v hv z).1) he)
  · intro h he
    exact h ((equiv v hv).injective (Subtype.ext he))

/-- Away from the absorbing element, the named unit predicate is precisely
valuation one in the quotient presentation. -/
theorem units_equiv_iff (a : _root_.RVCalc.RV v) (ha : a ≠ none) :
    iUnits (equiv v hv a).1 ↔ _root_.RVCalc.vrv v a = 1 := by
  rw [RVCalc.units_iff_le_one hM (equiv v hv a).2 ((equiv_ne_zero_iff v hv a).mpr ha)]
  rw [← equiv_one v hv, le_equiv_iff, le_equiv_iff,
    _root_.RVCalc.vrv_rv, map_one]
  exact le_antisymm_iff.symm

end CanonicalRV

#print axioms CanonicalRV.le_equiv_iff
#print axioms CanonicalRV.units_equiv_iff
