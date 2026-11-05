import ResidueTransportCore

namespace RVCalc
variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀}
theorem rv_eq_iff {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    rv v x = rv v y ↔ v (x - y) < v x := by
  have hxpos : 0 < v x := zero_lt_iff.2 ((Valuation.ne_zero_iff v).2 hx)
  rw [rv_of_ne hx, rv_of_ne hy, Option.some.injEq,
    QuotientGroup.mk'_eq_mk' (N := principalUnits v)]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hz' : v ((z : K) - 1) < 1 := hz
    have h1 : x * (z : K) = y := by
      simpa using congrArg Units.val hzy
    have hzx : (z : K) = y / x := by
      rw [eq_div_iff hx, mul_comm]
      exact h1
    have h2 : v (y / x - 1) < 1 := by rw [← hzx]; exact hz'
    calc v (x - y) = v (x * (1 - y / x)) := by
            rw [mul_sub, mul_one, mul_div_cancel₀ y hx]
      _ = v x * v (1 - y / x) := map_mul ..
      _ = v x * v (y / x - 1) := by
            rw [show 1 - y / x = -((y / x) - 1) by ring, Valuation.map_neg v]
      _ < v x * 1 := mul_lt_mul_of_pos_left h2 hxpos
      _ = v x := mul_one _
  · intro h
    refine ⟨(Units.mk0 x hx)⁻¹ * Units.mk0 y hy, ?_, ?_⟩
    · rw [mem_principalUnits]
      have hzK : (((Units.mk0 x hx)⁻¹ * Units.mk0 y hy : Kˣ) : K) = y / x := by
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
        ring
      rw [hzK, show y / x - 1 = (y - x) / x by field_simp,
        Valuation.map_div v, show y - x = -(x - y) by ring, Valuation.map_neg v,
        div_lt_one₀ hxpos]
      exact h
    · simp


end RVCalc
