module

public import Section7.SimpleRootNormalization
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

/-!
# The ordinary valuation-ring input supplied by the RV/Jacobian bridge

A normalized finite presentation gives an actual polynomial over the
valuation ring, including all coefficient cancellation. Reduction at the
all-one point vanishes and the evaluated Jacobian is a unit in that ring.
This constructs the input for ordinary multivariate Hensel; root existence
and uniqueness are not hypotheses or conclusions of this module.
-/

open MvPolynomial IsLocalRing

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem normalizedGammaPolynomial_integral (v : Valuation K Γ) {n : ℕ}
    {F : MvPolynomial (Fin n) K} (hF : IsGammaPolynomial v (fun _ => 1) 1 F) :
    ∃ G : MvPolynomial (Fin n) v.valuationSubring, G.map v.valuationSubring.subtype = F := by
  classical
  obtain ⟨_, _, P, rfl, hP⟩ := hF
  have hcoef (j : Fin P.length) : P.coefficient j ∈ v.valuationSubring := by
    apply (Valuation.mem_valuationSubring_iff v _).mpr
    exact (show v (P.coefficient j) = 1 by simpa using hP j).le
  refine ⟨∑ j, monomial (P.exponent j) (⟨P.coefficient j, hcoef j⟩ : v.valuationSubring), ?_⟩
  simp only [map_sum, map_monomial, ValuationSubring.coe_subtype, PolynomialPresentation.polynomial]

theorem normalizedGammaPolynomial_coeff_le (v : Valuation K Γ) {n : ℕ}
    {F : MvPolynomial (Fin n) K} (hF : IsGammaPolynomial v (fun _ => 1) 1 F)
    (d : Fin n →₀ ℕ) : v (F.coeff d) ≤ 1 := by
  obtain ⟨G, rfl⟩ := normalizedGammaPolynomial_integral v hF
  rw [coeff_map]
  exact (Valuation.mem_valuationSubring_iff v _).mp (G.coeff d).property

theorem map_jacobianPolynomial {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {n : ℕ} (F : Fin n → MvPolynomial (Fin n) R) :
    (jacobianPolynomial F).map f = jacobianPolynomial (fun i => (F i).map f) := by
  unfold jacobianPolynomial
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  funext i j
  exact (pderiv_map (φ := f) (f := F i) (i := j)).symm

/-- The output of the RV/Jacobian bridge is a square system over the actual
valuation ring, with zero residue and a unit Jacobian at its all-one point. -/
theorem exists_integral_simpleRoot_normalization (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} {α : Fin n → Γ}
    {F : Fin n → MvPolynomial (Fin n) K} (h : IsSimpleCommonResidueRoot v t α F) :
    ∃ (c e : Fin n → K) (H : Fin n → MvPolynomial (Fin n) v.valuationSubring),
      c ∈ RVFibre v t ∧ (∀ i, v (e i) * α i = 1) ∧
      (∀ i, (H i).map v.valuationSubring.subtype = normalizePolynomial c (e i) (F i)) ∧
      (∀ i, (H i).eval (fun _ => 1) ∈ maximalIdeal v.valuationSubring) ∧
      IsUnit ((jacobianPolynomial H).eval (fun _ => 1)) ∧
      (∀ y, (y ∈ RVFibre v (fun _ => RVCalc.rv v (1 : K)) ∧
          ∀ i, (normalizePolynomial c (e i) (F i)).eval y = 0) ↔
        ((fun i => c i * y i) ∈ RVFibre v t ∧
          ∀ i, (F i).eval (fun j => c j * y j) = 0)) := by
  classical
  obtain ⟨c, e, hc, he, hs, hj, hsol⟩ := exists_simpleRoot_normalization v h
  have hnorm (i : Fin n) :
      IsGammaPolynomial v (fun _ => 1) 1 (normalizePolynomial c (e i) (F i)) := by
    simpa only [RVCalc.vrv_rv, map_one] using hs.2.1 i
  choose H hH using fun i => normalizedGammaPolynomial_integral v (hnorm i)
  let ι : v.valuationSubring →+* K := v.valuationSubring.subtype
  have hH' (i : Fin n) : (H i).map ι = normalizePolynomial c (e i) (F i) := hH i
  have heval (i : Fin n) :
      ι ((H i).eval (fun _ => 1)) = (normalizePolynomial c (e i) (F i)).eval (fun _ => 1) := by
    rw [MvPolynomial.map_eval, hH' i]
    rfl
  have hsmall (i : Fin n) : (H i).eval (fun _ => 1) ∈ maximalIdeal v.valuationSubring := by
    apply (Valuation.mem_maximalIdeal_iff K v).mpr
    change v (ι ((H i).eval (fun _ => 1))) < 1
    rw [heval]
    exact hs.2.2.1 i _ (fun _ => rfl)
  have hunit : IsUnit ((jacobianPolynomial H).eval (fun _ => 1)) := by
    apply (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.valuationSubring.integers v)).mpr
    change v (ι ((jacobianPolynomial H).eval (fun _ => 1))) = 1
    rw [MvPolynomial.map_eval, map_jacobianPolynomial]
    simp only [hH', Function.comp_def, map_one]
    exact hj _ (fun _ => rfl)
  exact ⟨c, e, H, hc, he, hH, hsmall, hunit, hsol⟩

end SpecialTransformations.Section7
