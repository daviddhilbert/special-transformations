import Section7.GammaPolynomialAlgebra
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# The residue polynomial projection in Definition 7.1

Lift exactly the finite support of a residue polynomial. Each nonzero
coefficient has a unit lift in the actual valuation ring, so each monomial
in the resulting presentation has value one at coordinate weights one.
Zero coefficients are omitted, including the empty support of zero.
-/

open MvPolynomial IsLocalRing

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-- Every polynomial over the actual residue field is the coefficientwise
reduction of a valuation-ring polynomial whose image in the valued field
is a gamma-polynomial with all weights and residue value equal to one.
These ones are the paper's zeros under the multiplicative convention. -/
theorem exists_gammaPolynomial_residue_projection (v : Valuation K Γ) {n : ℕ}
    (p : MvPolynomial (Fin n) (ResidueField v.valuationSubring)) :
    ∃ P : MvPolynomial (Fin n) v.valuationSubring,
      P.map (residue v.valuationSubring) = p ∧
      IsGammaPolynomial v (fun _ => 1) 1 (P.map v.valuationSubring.subtype) := by
  classical
  choose a ha using fun d : Fin n →₀ ℕ =>
    (residue_surjective (R := v.valuationSubring)) (p.coeff d)
  let P := ∑ d : p.support, monomial d.val (a d.val)
  have hval (d : p.support) : v (a d.val : K) = 1 := by
    apply (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.valuationSubring.integers v)).mp
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [ha]
    exact MvPolynomial.mem_support_iff.mp d.property
  refine ⟨P, ?_, ?_⟩
  · simp only [P, map_sum, map_monomial, ha]
    exact (Finset.sum_coe_sort p.support (fun d => monomial d (p.coeff d))).trans
      (MvPolynomial.as_sum p).symm
  · have h := isGammaPolynomial_ofFamily v (γ := fun _ : Fin n => 1)
      (α := 1) (fun _ => one_ne_zero) one_ne_zero
      (fun d : p.support => (a d.val : K)) (fun d => d.val) (by
        intro d
        simp [hval d])
    simpa only [P, map_sum, map_monomial, ValuationSubring.coe_subtype] using h

end SpecialTransformations.Section7
