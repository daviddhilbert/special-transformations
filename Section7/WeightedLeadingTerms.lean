module

public import Section7.GammaPolynomial

@[expose] public section

/-!
# Leading terms at a prescribed value

The equality case needed to turn an RV equality on a fixed value fibre
into a residue-root test. Both evaluations are bounded by the prescribed
value. If their values drop below that bound, both leading terms are the
single existing RV zero. No new RV quotient or addition is introduced.
-/

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

noncomputable def weightedLeadingTerm (v : Valuation K Γ) (α : Γ) (x : K) : RVCalc.RV v :=
  if v x = α then RVCalc.rv v x else none

theorem weightedLeadingTerm_eq_zero_iff (v : Valuation K Γ) {α : Γ} (hα : α ≠ 0)
    {x : K} (hx : v x ≤ α) : weightedLeadingTerm v α x = none ↔ v x < α := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · simp [weightedLeadingTerm, hlt, ne_of_lt hlt]
  · have h0 : x ≠ 0 := (Valuation.ne_zero_iff v).mp (heq.symm ▸ hα)
    simp [weightedLeadingTerm, heq, RVCalc.rv_ne_none h0]

/-- Equality in the fixed degree is precisely the strict valuation bound
on the difference. Mathlib's strict inequality reverses the paper order. -/
theorem weightedLeadingTerm_eq_iff_sub_lt (v : Valuation K Γ) {α : Γ} (hα : α ≠ 0)
    {x y : K} (hx : v x ≤ α) (hy : v y ≤ α) :
    weightedLeadingTerm v α x = weightedLeadingTerm v α y ↔ v (x - y) < α := by
  rcases lt_or_eq_of_le hx with hxl | hxe <;> rcases lt_or_eq_of_le hy with hyl | hye
  · simp [weightedLeadingTerm, ne_of_lt hxl, ne_of_lt hyl, v.map_sub_lt hxl hyl]
  · have hy0 : y ≠ 0 := (Valuation.ne_zero_iff v).mp (hye.symm ▸ hα)
    have he : v (x - y) = α := (v.map_sub_eq_of_lt_right (hye.symm ▸ hxl)).trans hye
    rw [weightedLeadingTerm, if_neg (ne_of_lt hxl), weightedLeadingTerm, if_pos hye, he]
    exact iff_of_false (fun h => RVCalc.rv_ne_none hy0 h.symm) (lt_irrefl α)
  · have hx0 : x ≠ 0 := (Valuation.ne_zero_iff v).mp (hxe.symm ▸ hα)
    have he : v (x - y) = α := (v.map_sub_eq_of_lt_left (hxe.symm ▸ hyl)).trans hxe
    rw [weightedLeadingTerm, if_pos hxe, weightedLeadingTerm, if_neg (ne_of_lt hyl), he]
    exact iff_of_false (RVCalc.rv_ne_none hx0) (lt_irrefl α)
  · have hx0 : x ≠ 0 := (Valuation.ne_zero_iff v).mp (hxe.symm ▸ hα)
    have hy0 : y ≠ 0 := (Valuation.ne_zero_iff v).mp (hye.symm ▸ hα)
    rw [weightedLeadingTerm, if_pos hxe, weightedLeadingTerm, if_pos hye,
      RVCalc.rv_eq_iff hx0 hy0, hxe]

end SpecialTransformations.Section7
