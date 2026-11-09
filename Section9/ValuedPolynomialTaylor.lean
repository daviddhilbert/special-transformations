import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic.Ring

/-! A quadratic first-order error bound for polynomials with integral
coefficients, in arbitrary valuation rank. This is the estimate used
to identify a simple Hensel branch with its implicit derivative. -/

open MvPolynomial
open scoped BigOperators

namespace SpecialTransformations.Section9

variable {K Γ ι : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation K Γ)

local notation "O" => v.valuationSubring

theorem value_aeval_le_one (P : MvPolynomial ι O) (x : ι → K)
    (hx : ∀ i, v (x i) ≤ 1) : v (aeval x P) ≤ 1 := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [aeval_C]
    exact c.property
  | add P Q hP hQ =>
    rw [map_add]
    exact v.map_add_le hP hQ
  | mul_X P i hP =>
    rw [map_mul, aeval_X, map_mul]
    simpa only [mul_one] using mul_le_mul hP (hx i) zero_le zero_le

variable [Fintype ι]

section PolynomialTerms

variable {R : Type*} [CommRing R] [Algebra R K]

noncomputable def polynomialLinearTerm (P : MvPolynomial ι R) (x h : ι → K) : K :=
  ∑ i, aeval x (pderiv i P) * h i

noncomputable def polynomialRemainder (P : MvPolynomial ι R) (x h : ι → K) : K :=
  aeval (x + h) P - aeval x P - polynomialLinearTerm P x h

private theorem polynomialLinearTerm_add (P Q : MvPolynomial ι R) (x h : ι → K) :
    polynomialLinearTerm (P + Q) x h = polynomialLinearTerm P x h + polynomialLinearTerm Q x h := by
  simp only [polynomialLinearTerm, map_add, add_mul, Finset.sum_add_distrib]

private theorem polynomialLinearTerm_mul_X (P : MvPolynomial ι R) (j : ι) (x h : ι → K) :
    polynomialLinearTerm (P * X j) x h =
      polynomialLinearTerm P x h * x j + aeval x P * h j := by
  classical
  simp only [polynomialLinearTerm, pderiv_mul, map_add, map_mul, aeval_X,
    add_mul, Finset.sum_add_distrib]
  have h₁ : (∑ i, aeval x (pderiv i P) * x j * h i) =
      (∑ i, aeval x (pderiv i P) * h i) * x j := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h₂ : (∑ i, aeval x P * aeval x (pderiv i (X j : MvPolynomial ι R)) * h i) =
      aeval x P * h j := by
    calc
      _ = ∑ i, if i = j then aeval x P * h j else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases he : i = j
        · subst i
          simp
        · simp only [he, if_false, pderiv_X_of_ne (Ne.symm he), map_zero, mul_zero, zero_mul]
      _ = _ := by simp
  rw [h₁, h₂]

private theorem polynomialRemainder_add (P Q : MvPolynomial ι R) (x h : ι → K) :
    polynomialRemainder (P + Q) x h = polynomialRemainder P x h + polynomialRemainder Q x h := by
  simp only [polynomialRemainder, map_add, polynomialLinearTerm_add]
  ring

private theorem polynomialRemainder_mul_X (P : MvPolynomial ι R) (j : ι) (x h : ι → K) :
    polynomialRemainder (P * X j) x h =
      polynomialRemainder P x h * (x j + h j) + polynomialLinearTerm P x h * h j := by
  simp only [polynomialRemainder, polynomialLinearTerm_mul_X, map_mul, aeval_X, Pi.add_apply]
  ring

/-- A polynomial at an arbitrary centre has a linear valuation bound
and a quadratic error bound. The constants depend only on the polynomial
and centre, and there is no restriction on the valuation rank. -/
theorem exists_value_polynomialTaylor_bounds (P : MvPolynomial ι R) (x : ι → K) :
    ∃ B C : Γ, 1 ≤ B ∧ 1 ≤ C ∧ ∀ (r : Γ), r ≤ 1 → ∀ h : ι → K, (∀ i, v (h i) ≤ r) →
      v (polynomialLinearTerm P x h) ≤ B * r ∧ v (polynomialRemainder P x h) ≤ C * r ^ 2 := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨1, 1, le_rfl, le_rfl, fun r _ h _ => ?_⟩
    simp [polynomialLinearTerm, polynomialRemainder]
  | add P Q hP hQ =>
    obtain ⟨B, C, hB, hC, hP⟩ := hP
    obtain ⟨D, E, hD, hE, hQ⟩ := hQ
    refine ⟨max B D, max C E, hB.trans (le_max_left _ _), hC.trans (le_max_left _ _),
      fun r hr h hh => ?_⟩
    obtain ⟨hPl, hPr⟩ := hP r hr h hh
    obtain ⟨hQl, hQr⟩ := hQ r hr h hh
    constructor
    · rw [polynomialLinearTerm_add]
      exact v.map_add_le (hPl.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) zero_le))
        (hQl.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) zero_le))
    · rw [polynomialRemainder_add]
      exact v.map_add_le (hPr.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) zero_le))
        (hQr.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) zero_le))
  | mul_X P i hP =>
    obtain ⟨B, C, _, _, hP⟩ := hP
    let B' := max 1 (max (B * v (x i)) (v (aeval x P)))
    let C' := max 1 (max (C * max (v (x i)) 1) B)
    refine ⟨B', C', le_max_left _ _, le_max_left _ _, fun r hr h hh => ?_⟩
    obtain ⟨hPl, hPr⟩ := hP r hr h hh
    constructor
    · rw [polynomialLinearTerm_mul_X]
      apply v.map_add_le
      · rw [map_mul]
        calc
          _ ≤ B * r * v (x i) := mul_le_mul_of_nonneg_right hPl zero_le
          _ = (B * v (x i)) * r := by ac_rfl
          _ ≤ B' * r := mul_le_mul_of_nonneg_right
            ((le_max_left _ _).trans (le_max_right _ _)) zero_le
      · rw [map_mul]
        exact mul_le_mul ((le_max_right _ _).trans (le_max_right _ _)) (hh i) zero_le zero_le
    · rw [polynomialRemainder_mul_X]
      apply v.map_add_le
      · rw [map_mul]
        have hx : v (x i + h i) ≤ max (v (x i)) 1 :=
          (v.map_add (x i) (h i)).trans (max_le_max le_rfl ((hh i).trans hr))
        calc
          _ ≤ C * r ^ 2 * max (v (x i)) 1 := mul_le_mul hPr hx zero_le zero_le
          _ = (C * max (v (x i)) 1) * r ^ 2 := by ac_rfl
          _ ≤ C' * r ^ 2 := mul_le_mul_of_nonneg_right
            ((le_max_left _ _).trans (le_max_right _ _)) zero_le
      · rw [map_mul]
        calc
          _ ≤ B * r * r := mul_le_mul hPl (hh i) zero_le zero_le
          _ = B * r ^ 2 := by rw [pow_two, mul_assoc]
          _ ≤ C' * r ^ 2 := mul_le_mul_of_nonneg_right
            ((le_max_right _ _).trans (le_max_right _ _)) zero_le

end PolynomialTerms

theorem value_polynomialLinearTerm_le (P : MvPolynomial ι O) (x h : ι → K)
    (hx : ∀ i, v (x i) ≤ 1) (r : Γ) (hh : ∀ i, v (h i) ≤ r) :
    v (polynomialLinearTerm P x h) ≤ r := by
  apply v.map_sum_le
  intro i _
  rw [map_mul]
  simpa only [one_mul] using mul_le_mul (value_aeval_le_one v (pderiv i P) x hx)
    (hh i) zero_le zero_le

/-- The valued-field first-order error is at most the square of any
common bound on the increments that is at most one. -/
theorem value_polynomialRemainder_le_sq (P : MvPolynomial ι O) (x h : ι → K)
    (hx : ∀ i, v (x i) ≤ 1) (r : Γ) (hr : r ≤ 1) (hh : ∀ i, v (h i) ≤ r) :
    v (polynomialRemainder P x h) ≤ r ^ 2 := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [polynomialRemainder, polynomialLinearTerm]
  | add P Q hP hQ =>
    rw [polynomialRemainder_add]
    exact v.map_add_le hP hQ
  | mul_X P j hP =>
    rw [polynomialRemainder_mul_X]
    apply v.map_add_le
    · rw [map_mul]
      have hj := v.map_add_le (hx j) ((hh j).trans hr)
      simpa only [mul_one] using mul_le_mul hP hj zero_le zero_le
    · rw [map_mul, pow_two]
      exact mul_le_mul (value_polynomialLinearTerm_le v P x h hx r hh) (hh j) zero_le zero_le

end SpecialTransformations.Section9
