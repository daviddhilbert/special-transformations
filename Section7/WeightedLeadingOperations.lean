module

public import Section7.WeightedLeadingTerms
public import ResidueTranscendentalTransport

@[expose] public section

/-!
# Multiplication and unequal degrees for weighted leading terms

Scaling by a nonzero monomial scales the prescribed degree. Two unequal
nonzero degrees can agree in RV only when both leading terms vanish.
Together with subtraction at equal degrees, this is the case split for
guarded RV equality literals on a fixed value fibre.
-/

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem weightedLeadingTerm_value (v : Valuation K Γ) (α : Γ) (x : K) :
    RVCalc.vrv v (weightedLeadingTerm v α x) = if v x = α then α else 0 := by
  by_cases h : v x = α
  · simp [weightedLeadingTerm, h, RVCalc.vrv_rv]
  · simp [weightedLeadingTerm, h, RVCalc.vrv]

theorem weightedLeadingTerm_eq_iff_of_value_ne (v : Valuation K Γ)
    {α β : Γ} (hα : α ≠ 0) (hβ : β ≠ 0) (hne : α ≠ β)
    {x y : K} (hx : v x ≤ α) (hy : v y ≤ β) :
    weightedLeadingTerm v α x = weightedLeadingTerm v β y ↔ v x < α ∧ v y < β := by
  constructor
  · intro h
    have he := congrArg (RVCalc.vrv v) h
    simp only [weightedLeadingTerm_value] at he
    have hxl : v x ≠ α := by
      intro hxe
      by_cases hye : v y = β
      · exact hne (by simpa only [hxe, hye, if_true] using he)
      · exact hα (by simpa only [hxe, hye, if_true, if_false] using he)
    have hyl : v y ≠ β := by
      intro hye
      exact hβ (by simpa only [hxl, hye, if_true, if_false] using he.symm)
    exact ⟨lt_of_le_of_ne hx hxl, lt_of_le_of_ne hy hyl⟩
  · rintro ⟨hxl, hyl⟩
    rw [(weightedLeadingTerm_eq_zero_iff v hα hx).mpr hxl,
      (weightedLeadingTerm_eq_zero_iff v hβ hy).mpr hyl]

theorem weightedLeadingTerm_mul_of_exact (v : Valuation K Γ) {α : Γ}
    (hα : α ≠ 0) (β : Γ) {c : K} (hc : v c = α) (x : K) :
    weightedLeadingTerm v (α * β) (c * x) =
      RVCalc.rvMul v (RVCalc.rv v c) (weightedLeadingTerm v β x) := by
  have he : v (c * x) = α * β ↔ v x = β := by
    rw [map_mul, hc]
    exact ⟨mul_left_cancel₀ hα, congrArg (fun t => α * t)⟩
  by_cases hx : v x = β
  · rw [weightedLeadingTerm, if_pos (he.mpr hx), weightedLeadingTerm, if_pos hx,
      ResidueTranscendentalTransport.rv_mul_all]
  · rw [weightedLeadingTerm, if_neg (fun h => hx (he.mp h)), weightedLeadingTerm, if_neg hx]
    cases RVCalc.rv v c <;> rfl

end SpecialTransformations.Section7
