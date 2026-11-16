module

public import Section9.GaussDerivative
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

@[expose] public section

/-! A finer valuation can certify the Gauss bound for a coarsening.
Distinct fine monomial values rule out cancellation even when several
of those values coincide after coarsening. -/

open MvPolynomial

namespace SpecialTransformations.Section9

variable {E K Γ Δ ι : Type*} [Field E] [Field K] [Algebra E K]
variable [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

theorem isGaussEvaluation_of_distinct_fine_values
    (v : Valuation K Γ) (w : Valuation K Δ)
    (hcoarse : ∀ a b, v a ≤ v b → w a ≤ w b)
    (x : ι → K) (hx : ∀ i, w (x i) = 1)
    (hsep : ∀ (P : MvPolynomial ι E) d e, d ∈ P.support → e ∈ P.support → d ≠ e →
      v (aeval x (monomial d (P.coeff d))) ≠ v (aeval x (monomial e (P.coeff e)))) :
    IsGaussEvaluation (E := E) w x := by
  classical
  intro P d hd
  let m (i : ι →₀ ℕ) := aeval x (monomial i (P.coeff i))
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image P.support (fun i => v (m i)) ⟨d, hd⟩
  have hsum : aeval x P = ∑ i ∈ P.support, m i := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
  have he : v (aeval x P) = v (m j) := by
    rw [hsum]
    apply v.map_sum_eq_of_lt hj
    intro i hi
    obtain ⟨hiP, hne⟩ := Finset.mem_sdiff.mp hi
    exact lt_of_le_of_ne (hmax i hiP) (hsep P i j hiP hj (by simpa using hne))
  have hm (i : ι →₀ ℕ) : w (m i) = w (algebraMap E K (P.coeff i)) := by
    change w (aeval x (monomial i (P.coeff i))) = _
    rw [aeval_monomial, map_mul, Finsupp.prod, map_prod]
    simp only [map_pow, hx, one_pow, Finset.prod_const_one, mul_one]
  rw [← hm]
  exact (hcoarse _ _ (hmax d hd)).trans (hcoarse _ _ he.ge)

theorem algebraicIndependent_of_isGaussEvaluation
    (v : Valuation K Γ) (x : ι → K) (h : IsGaussEvaluation (E := E) v x) :
    AlgebraicIndependent E x := by
  apply (injective_iff_map_eq_zero (aeval (R := E) x)).mpr
  intro P hP
  apply support_eq_empty.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hv := h P d hd
  rw [hP, map_zero, le_zero_iff] at hv
  exact (mem_support_iff.mp hd) ((algebraMap E K).injective (by
    rw [map_zero]
    exact v.zero_iff.mp hv))

end SpecialTransformations.Section9
