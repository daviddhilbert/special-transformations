import Section7.ResidueFibreEvaluation
import Mathlib.Algebra.CharZero.Infinite

/-!
# The finite weighted-test reduction for Lemma 7.4

Given a finite list of original-field gamma-polynomial tests isolating a
point on a last-coordinate value fibre, extract the required simple
residue-root polynomial over that original field. The guarded-normal-form
construction of this finite test list from RV algebraicity is separate.
-/

open MvPolynomial IsLocalRing

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem exists_simpleResidueRoot_of_finite_RV_pattern (v : Valuation K Γ)
    [CharZero (ResidueField v.valuationSubring)] (E : Subfield K)
    {n : ℕ} (t : Fin n → RVCalc.RV v) (ht : ∀ j, t j ≠ none) (i : Fin n)
    {ι : Type*} [Finite ι] (α : ι → Γ) (F : ι → MvPolynomial (Fin n) E)
    (hF : ∀ j, IsGammaPolynomial v (fun k => RVCalc.vrv v (t k)) (α j) ((F j).map E.subtype))
    (hfin : {u : RVCalc.RV v | RVCalc.vrv v u = RVCalc.vrv v (t i) ∧
      ∀ j, IsResidueRoot v (Function.update t i u) (α j) ((F j).map E.subtype) ↔
        IsResidueRoot v t (α j) ((F j).map E.subtype)}.Finite) :
    ∃ (β : Γ) (P : MvPolynomial (Fin n) E),
      IsGammaPolynomial v (fun j => RVCalc.vrv v (t j)) β (P.map E.subtype) ∧
      IsResidueRoot v t β (P.map E.subtype) ∧
      ¬ IsResidueRoot v t (β / RVCalc.vrv v (t i)) ((pderiv i P).map E.subtype) := by
  classical
  obtain ⟨c, hc⟩ := rvFibre_nonempty v t
  let γ := fun j => RVCalc.vrv v (t j)
  have hcv : ∀ j, v (c j) = γ j := rvFibre_value v hc
  have hc0 (j : Fin n) : c j ≠ 0 := by
    intro h
    exact ht j ((hc j).symm.trans (h ▸ RVCalc.rv_zero))
  have hγ (j : Fin n) : γ j ≠ 0 := by
    rw [← hcv j]
    exact (Valuation.ne_zero_iff v).mpr (hc0 j)
  -- A zero polynomial contributes a constant true test and needs no scalar.
  let J := {j : ι // (F j).map E.subtype ≠ 0}
  have hnorm (j : J) : ∃ (e : K) (H : MvPolynomial (Fin n) v.valuationSubring),
      v e * α j = 1 ∧ H.map v.valuationSubring.subtype =
        normalizePolynomial c e ((F j).map E.subtype) := by
    obtain ⟨e, he⟩ := gammaPolynomial_normalizingScalar_exists v (hF j) j.property c hcv
    obtain ⟨H, hH⟩ := normalizedGammaPolynomial_integral v
      (normalizePolynomial_isGamma v (hF j) c e hcv he)
    exact ⟨e, H, he, hH⟩
  choose e H he hH using hnorm
  let q (j : J) := specializeVariable (residue v.valuationSubring) (fun _ => 1) i (H j)
  have htest_one (j : J) : IsResidueRoot v t (α j) ((F j).map E.subtype) ↔ (q j).IsRoot 1 :=
    (residueRoot_iff_normalized_integral_eval v ht (hF j) hc (e j) (he j) (H j) (hH j)).trans
      (specializeResidue_isRoot_one_iff v i (H j)).symm
  let kappa := ResidueField v.valuationSubring
  choose z hz using fun u : kappa => (residue_surjective (R := v.valuationSubring)) u
  let r (u : kappa) := RVCalc.rv v (c i * (z u : K))
  let s (u : kappa) := Function.update t i (r u)
  let y (u : kappa) := Function.update (fun _ : Fin n => (1 : v.valuationSubring)) i (z u)
  let x (u : kappa) := fun j => c j * (y u j : K)
  have hrv (u : kappa) (hu : u ≠ 0) : RVCalc.vrv v (r u) = γ i := by
    change RVCalc.vrv v (RVCalc.rv v (c i * (z u : K))) = γ i
    have hzu : residue v.valuationSubring (z u) ≠ 0 := by rwa [hz u]
    rw [RVCalc.vrv_rv, map_mul, valuationRing_value_one_of_residue_ne_zero v _ hzu, mul_one, hcv]
  have hsval (u : kappa) (hu : u ≠ 0) (j : Fin n) : RVCalc.vrv v (s u j) = γ j := by
    by_cases hj : j = i
    · subst j
      simpa [s] using hrv u hu
    · simp [s, hj, γ]
  have hs0 (u : kappa) (hu : u ≠ 0) (j : Fin n) : s u j ≠ none := by
    intro hj
    have hv := hsval u hu j
    rw [hj] at hv
    exact hγ j hv.symm
  have hx (u : kappa) : x u ∈ RVFibre v (s u) := by
    intro j
    by_cases hj : j = i
    · subst j
      simp [x, y, s, r]
    · simpa [x, y, s, hj] using hc j
  have htest (u : kappa) (hu : u ≠ 0) (j : J) :
      IsResidueRoot v (s u) (α j) ((F j).map E.subtype) ↔ (q j).IsRoot u := by
    have hp : IsGammaPolynomial v (fun k => RVCalc.vrv v (s u k)) (α j)
        ((F j).map E.subtype) := by
      rw [funext (hsval u hu)]
      exact hF j
    have hr : IsResidueRoot v (s u) (α j) ((F j).map E.subtype) ↔
        v (((F j).map E.subtype).eval (x u)) < α j :=
      ⟨fun h => h (x u) (hx u), fun h =>
        (residueRoot_iff_exists v (hs0 u hu) hp).mpr ⟨x u, hx u, h⟩⟩
    exact hr.trans (by
      simpa only [q, x, y, hz u] using
        (valuation_eval_lt_iff_specialized_residue v c (e j) (he j) ((F j).map E.subtype)
          (H j) (hH j) i (z u)))
  let X : Set kappa := {u | u ≠ 0 ∧ ∀ j, (q j).IsRoot u ↔ (q j).IsRoot 1}
  have hXf : X.Finite := hfin.of_injOn (f := r) (s := X) (by
    intro u hu
    refine ⟨hrv u hu.1, ?_⟩
    intro j
    by_cases hj : (F j).map E.subtype ≠ 0
    · let j' : J := ⟨j, hj⟩
      exact (htest u hu.1 j').trans ((hu.2 j').trans (htest_one j').symm)
    · have hzF : (F j).map E.subtype = 0 := not_ne_iff.mp hj
      have hzRoot (w : Fin n → RVCalc.RV v) : IsResidueRoot v w (α j) 0 := by
        intro b _
        simpa only [map_zero] using (zero_lt_iff).mpr (hF j).2.1
      rw [hzF]
      exact iff_of_true (hzRoot _) (hzRoot _)) (by
    intro u hu w hw heq
    have hzu : residue v.valuationSubring (z u) ≠ 0 := by
      rw [hz u]
      exact hu.1
    have hzw : residue v.valuationSubring (z w) ≠ 0 := by
      rw [hz w]
      exact hw.1
    have he := (scaledRV_eq_iff_residue_eq v (hc0 i) (z u) (z w) hzu hzw).mp heq
    simpa only [hz u, hz w] using he)
  obtain ⟨j, hq, hr⟩ := exists_nonzero_root_of_finite_polynomial_pattern q 1 hXf
  exact exists_simpleResidueRoot_of_specialized_residue v E ht i (F j) (hF j)
    ((htest_one j).mpr hr) hc (e j) (he j) (H j) (hH j) hq

end SpecialTransformations.Section7
