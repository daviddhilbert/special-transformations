import RVClassEquality

/-!
Leading-term helper copied verbatim from QE/RV_henselian.lean at fa3867c:
rv_sum_eq_of_lt. Only the import and namespace frame differ. The rv_eq_iff
dependency is the single shared declaration from RVClassEquality.
-/
namespace RVCalc
variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation K Γ₀}
/-- `rv` of a finite sum whose terms are all strictly smaller in value than one term. -/
theorem rv_sum_eq_of_lt {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → K} {j : ι}
    (hj : j ∈ s) (h0 : v (f j) ≠ 0) (hf : ∀ i ∈ s \ {j}, v (f i) < v (f j)) :
    rv v (∑ i ∈ s, f i) = rv v (f j) := by
  have hfj : f j ≠ 0 := by rintro h; rw [h, Valuation.map_zero] at h0; exact h0 rfl
  have hval : v (∑ i ∈ s, f i) = v (f j) := Valuation.map_sum_eq_of_lt v hj hf
  have hne : (∑ i ∈ s, f i) ≠ 0 := by
    rintro h; rw [h, Valuation.map_zero] at hval; exact h0 hval.symm
  refine (rv_eq_iff hne hfj).2 ?_
  rw [hval, Finset.sum_eq_add_sum_sdiff_singleton_of_mem hj, add_sub_cancel_left]
  exact Valuation.map_sum_lt v h0 hf



end RVCalc
#print axioms RVCalc.rv_sum_eq_of_lt

