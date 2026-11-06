import Section6.RVTermSupport
import ResidueTransportCore

/-! The author's Definition 2.4 clarification in the released quotient
presentation: rv preserves totalized inversion and division. The ordinary
polynomial leaves in RVTermSupport therefore require no new convention. -/

namespace SpecialTransformations.Section6.RVQuotients

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem rv_inverse (v : Valuation K Γ) (x : K) :
    RVCalc.rv v x⁻¹ = (RVCalc.rv v x).map Inv.inv := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [RVCalc.rv_inv (v := v) hx, RVCalc.rv_of_ne hx]
    rfl

theorem rv_division (v : Valuation K Γ) (x y : K) :
    RVCalc.rv v (x / y) = RVCalc.rvMul v (RVCalc.rv v x) ((RVCalc.rv v y).map Inv.inv) := by
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hy : y = 0
  · subst y
    simp
  rw [div_eq_mul_inv, RVCalc.rv_mul (v := v) hx (inv_ne_zero hy), rv_inverse]

end SpecialTransformations.Section6.RVQuotients
