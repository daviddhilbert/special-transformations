import Section6.AngularCodes
import CanonicalRVOrder

/-! Value and residue-domain predicates on the single-zero angular
codes. The final native comparison explicitly reverses the Mathlib
multiplicative valuation order. -/

noncomputable section
open Classical

namespace SpecialTransformations.Section6.AngularComponent

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem value_splitting (v : Valuation K Γ) (a : Data v) (q : RVCalc.RVUnit v) :
    RVCalc.vrvUnit v q = (((splitting v a q).2.val : Γˣ) : Γ) := by
  refine Quotient.inductionOn q (fun x => ?_)
  rfl

theorem value_encode (v : Valuation K Γ) (a : Data v) (r : Residue v) (g : ValueGroup v) :
    RVCalc.vrv v (encode v a r g) = if r = 0 then 0 else ((g.val : Γˣ) : Γ) := by
  by_cases hr : r = 0
  · subst r
    rw [encode_zero, if_pos rfl]
    rfl
  · rw [encode_ne_zero v a r hr, if_neg hr, RVCalc.vrv_some, value_splitting,
      MulEquiv.apply_symm_apply]

theorem encode_nonzero (v : Valuation K Γ) (a : Data v) (r : Residue v) (g : ValueGroup v) :
    encode v a r g ≠ none ↔ r ≠ 0 := by
  by_cases hr : r = 0
  · subst r
    simp [encode_zero]
  · constructor
    · intro _
      exact hr
    · intro _
      rw [encode_ne_zero v a r hr]
      exact Option.some_ne_none _

theorem group_value_one (v : Valuation K Γ) (g : ValueGroup v) :
    ((g.val : Γˣ) : Γ) = 1 ↔ g = 1 := by
  constructor
  · intro h
    exact Subtype.ext (Units.ext h)
  · rintro rfl
    rfl

theorem residue_unit_encode (v : Valuation K Γ) (a : Data v) (r : Residue v) (g : ValueGroup v) :
    (encode v a r g ≠ none ∧ RVCalc.vrv v (encode v a r g) = 1) ↔ r ≠ 0 ∧ g = 1 := by
  rw [encode_nonzero, value_encode]
  by_cases hr : r = 0
  · simp [hr]
  · simp only [hr, if_false, true_and, group_value_one]

theorem residue_domain_encode (v : Valuation K Γ) (a : Data v) (r : Residue v) (g : ValueGroup v) :
    (encode v a r g = none ∨ RVCalc.vrv v (encode v a r g) = 1) ↔ r = 0 ∨ g = 1 := by
  by_cases hr : r = 0
  · subst r
    simp [encode_zero]
  · have hn := (encode_nonzero v a r g).mpr hr
    rw [value_encode, if_neg hr, group_value_one]
    simp only [hn, hr, false_or]

theorem value_order_encode (v : Valuation K Γ) (a : Data v)
    (r s : Residue v) (g h : ValueGroup v) :
    (RVCalc.vrv v (encode v a s h) ≤ RVCalc.vrv v (encode v a r g)) ↔
      s = 0 ∨ (r ≠ 0 ∧ ((h.val : Γˣ) : Γ) ≤ ((g.val : Γˣ) : Γ)) := by
  have hg : 0 < ((g.val : Γˣ) : Γ) := pos_iff_ne_zero.mpr (Units.ne_zero g.val)
  have hh : 0 < ((h.val : Γˣ) : Γ) := pos_iff_ne_zero.mpr (Units.ne_zero h.val)
  rw [value_encode, value_encode]
  by_cases hr : r = 0 <;> by_cases hs : s = 0 <;> simp [hr, hs, hg.le, hh.not_ge]

end SpecialTransformations.Section6.AngularComponent
