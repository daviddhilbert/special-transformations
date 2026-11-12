module

public import Section7.PolynomialFibreExtraction
public import Section7.ResidueDerivativeNormalization

@[expose] public section

/-!
# Extract a simple last-coordinate residue root

This is the derivative step of Lemma 7.4. A nonzero residue specialization
of a normalized original-base polynomial gives a derivative over the same
original subfield, with the required nonvanishing next derivative. The
existence of the initial polynomial from RV algebraicity remains separate.
-/

open MvPolynomial IsLocalRing

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem specializeResidue_isRoot_one_iff (v : Valuation K Γ) {n : ℕ}
    (i : Fin n) (H : MvPolynomial (Fin n) v.valuationSubring) :
    (specializeVariable (residue v.valuationSubring) (fun _ => 1) i H).IsRoot 1 ↔
      (H.map (residue v.valuationSubring)).eval (fun _ => 1) = 0 := by
  rw [Polynomial.IsRoot, eval_specializeVariable]
  have he : Function.update (fun _ : Fin n => (1 : ResidueField v.valuationSubring)) i 1 =
      fun _ => 1 := by
    funext j
    by_cases h : j = i <;> simp [Function.update, h]
  rw [he, MvPolynomial.eval_map]

theorem exists_simpleResidueRoot_of_specialized_residue (v : Valuation K Γ)
    [CharZero (ResidueField v.valuationSubring)] (E : Subfield K) {n : ℕ}
    {t : Fin n → RVCalc.RV v} (ht : ∀ j, t j ≠ none) (i : Fin n)
    {α : Γ} (F : MvPolynomial (Fin n) E)
    (hF : IsGammaPolynomial v (fun j => RVCalc.vrv v (t j)) α (F.map E.subtype))
    (hroot : IsResidueRoot v t α (F.map E.subtype))
    {c : Fin n → K} (hc : c ∈ RVFibre v t) (e : K) (he : v e * α = 1)
    (H : MvPolynomial (Fin n) v.valuationSubring)
    (hH : H.map v.valuationSubring.subtype = normalizePolynomial c e (F.map E.subtype))
    (hn : specializeVariable (residue v.valuationSubring) (fun _ => 1) i H ≠ 0) :
    ∃ (β : Γ) (P : MvPolynomial (Fin n) E),
      IsGammaPolynomial v (fun j => RVCalc.vrv v (t j)) β (P.map E.subtype) ∧
      IsResidueRoot v t β (P.map E.subtype) ∧
      ¬ IsResidueRoot v t (β / RVCalc.vrv v (t i)) ((pderiv i P).map E.subtype) := by
  let Q := specializeVariable (residue v.valuationSubring) (fun _ => 1) i H
  let γ := fun j => RVCalc.vrv v (t j)
  have hQroot : Q.IsRoot 1 := (specializeResidue_isRoot_one_iff v i H).mpr
    ((residueRoot_iff_normalized_integral_eval v ht hF hc e he H hH).mp hroot)
  obtain ⟨k, hk, hkn⟩ := exists_iterate_derivative_simpleRoot hn hQroot
  have hpoly (l : ℕ) : IsGammaPolynomial v γ (α / γ i ^ l)
      ((((pderiv i)^[l]) F).map E.subtype) := by
    rw [← iterate_pderiv_map]
    exact hF.iterate_pderiv v i l
  have htransport (l : ℕ) : IsResidueRoot v t (α / γ i ^ l)
      ((((pderiv i)^[l]) F).map E.subtype) ↔ ((Polynomial.derivative^[l]) Q).IsRoot 1 := by
    let H' := (pderiv i)^[l] H
    have hH' : H'.map v.valuationSubring.subtype =
        normalizePolynomial c (e * c i ^ l) ((((pderiv i)^[l]) F).map E.subtype) := by
      change (((pderiv i)^[l]) H).map v.valuationSubring.subtype = _
      rw [← iterate_pderiv_map, hH, iterate_pderiv_normalizePolynomial, iterate_pderiv_map]
    have hs := iterate_normalizingScalar_value v c e (rvFibre_value v hc) hF.1 he i l
    rw [residueRoot_iff_normalized_integral_eval v ht (hpoly l) hc _ hs H' hH',
      ← specializeResidue_isRoot_one_iff v i H']
    exact Iff.of_eq (congrArg (fun p : Polynomial (ResidueField v.valuationSubring) => p.IsRoot 1)
      (iterate_derivative_specializeVariable (residue v.valuationSubring) (fun _ => 1) i H l).symm)
  refine ⟨α / γ i ^ k, (pderiv i)^[k] F, hpoly k, (htransport k).mpr hk, ?_⟩
  have hγ : γ i ≠ 0 := hF.1 i
  have hw : α / γ i ^ k / γ i = α / γ i ^ (k + 1) := by
    rw [pow_succ]
    apply (eq_div_iff (mul_ne_zero (pow_ne_zero _ hγ) hγ)).mpr
    change (α / γ i ^ k / γ i) * (γ i ^ k * γ i) = α
    calc
      _ = (α / γ i ^ k / γ i * γ i) * γ i ^ k := by ac_rfl
      _ = α := by rw [div_mul_cancel₀ _ hγ, div_mul_cancel₀ _ (pow_ne_zero _ hγ)]
  change ¬ IsResidueRoot v t (α / γ i ^ k / γ i)
    ((pderiv i ((pderiv i)^[k] F)).map E.subtype)
  rw [hw, ← Function.iterate_succ_apply' (f := (pderiv i : MvPolynomial (Fin n) E →
    MvPolynomial (Fin n) E)) k F, htransport (k + 1), Function.iterate_succ_apply']
  exact hkn

end SpecialTransformations.Section7
