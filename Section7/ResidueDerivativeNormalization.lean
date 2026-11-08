import Section7.IntegralNormalization

/-!
# Iterated partial derivatives and normalized residue evaluation

The derivatives are taken on the original polynomial. Normalization only
changes how they are evaluated: each differentiation multiplies the
normalizing scalar by the corresponding coordinate representative and
divides the residue value by the coordinate weight. Thus normalization
does not enlarge the coefficient field of the polynomial we extract.
-/

open MvPolynomial IsLocalRing

namespace SpecialTransformations.Section7

theorem iterate_pderiv_map {R S σ : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (i : σ) (F : MvPolynomial σ R) (k : ℕ) :
    (pderiv i)^[k] (F.map f) = (((pderiv i)^[k]) F).map f := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, pderiv_map]

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem pderiv_normalizePolynomial {n : ℕ} (c : Fin n → K) (e : K)
    (i : Fin n) (F : MvPolynomial (Fin n) K) :
    pderiv i (normalizePolynomial c e F) = normalizePolynomial c (e * c i) (pderiv i F) := by
  simp only [normalizePolynomial, pderiv_C_mul, pderiv_diagonalScale, map_mul, mul_assoc]

theorem iterate_pderiv_normalizePolynomial {n : ℕ} (c : Fin n → K) (e : K)
    (i : Fin n) (F : MvPolynomial (Fin n) K) (k : ℕ) :
    (pderiv i)^[k] (normalizePolynomial c e F) =
      normalizePolynomial c (e * c i ^ k) ((pderiv i)^[k] F) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply', ih, pderiv_normalizePolynomial, pow_succ, mul_assoc]

theorem IsGammaPolynomial.iterate_pderiv (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α : Γ} {F : MvPolynomial (Fin n) K}
    (hF : IsGammaPolynomial v γ α F) (i : Fin n) (k : ℕ) :
    IsGammaPolynomial v γ (α / γ i ^ k) ((MvPolynomial.pderiv i)^[k] F) := by
  induction k with
  | zero => simpa using hF
  | succ k ih =>
    have hw : α / γ i ^ k / γ i = α / γ i ^ (k + 1) := by
      rw [pow_succ]
      apply (eq_div_iff (mul_ne_zero (pow_ne_zero _ (hF.1 i)) (hF.1 i))).mpr
      calc
        _ = (α / γ i ^ k / γ i * γ i) * γ i ^ k := by ac_rfl
        _ = α := by rw [div_mul_cancel₀ _ (hF.1 i), div_mul_cancel₀ _ (pow_ne_zero _ (hF.1 i))]
    simpa only [Function.iterate_succ_apply', ← hw] using ih.pderiv v i

theorem iterate_normalizingScalar_value (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α : Γ} (c : Fin n → K) (e : K)
    (hc : ∀ i, v (c i) = γ i) (hγ : ∀ i, γ i ≠ 0) (he : v e * α = 1)
    (i : Fin n) (k : ℕ) : v (e * c i ^ k) * (α / γ i ^ k) = 1 := by
  rw [map_mul, map_pow, hc i, div_eq_mul_inv]
  calc
    _ = (v e * α) * (γ i ^ k * (γ i ^ k)⁻¹) := by ac_rfl
    _ = 1 := by rw [mul_inv_cancel₀ (pow_ne_zero _ (hγ i)), mul_one, he]

/-- Residue-root testing after normalization is exactly reduction of the
valuation-ring polynomial at the all-one tuple. -/
theorem residueRoot_iff_normalized_integral_eval (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} (ht : ∀ i, t i ≠ none)
    {α : Γ} {F : MvPolynomial (Fin n) K}
    (hF : IsGammaPolynomial v (fun i => RVCalc.vrv v (t i)) α F)
    {c : Fin n → K} (hc : c ∈ RVFibre v t) (e : K) (he : v e * α = 1)
    (H : MvPolynomial (Fin n) v.valuationSubring)
    (hH : H.map v.valuationSubring.subtype = normalizePolynomial c e F) :
    IsResidueRoot v t α F ↔ (H.map (residue v.valuationSubring)).eval (fun _ => 1) = 0 := by
  have hroot : IsResidueRoot v t α F ↔ v (F.eval c) < α :=
    ⟨fun h => h c hc, fun h => (residueRoot_iff_exists v ht hF).mpr ⟨c, hc, h⟩⟩
  have hred : (H.map (residue v.valuationSubring)).eval (fun _ => 1) =
      residue v.valuationSubring (H.eval (fun _ => 1)) := by
    simpa only [Function.comp_def, map_one] using
      (MvPolynomial.map_eval (residue v.valuationSubring) (fun _ => 1) H).symm
  have heval : v.valuationSubring.subtype (H.eval (fun _ => 1)) = e * F.eval c := by
    rw [MvPolynomial.map_eval, hH]
    simp [eval_normalizePolynomial, Function.comp_def]
  have he0 : v e ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at he
    exact zero_ne_one he
  have hepos : 0 < v e := lt_of_le_of_ne zero_le (Ne.symm he0)
  rw [hroot, hred, residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  change _ ↔ v (v.valuationSubring.subtype (H.eval (fun _ => 1))) < 1
  rw [heval, map_mul, ← he, mul_lt_mul_iff_right₀ hepos]

end SpecialTransformations.Section7
