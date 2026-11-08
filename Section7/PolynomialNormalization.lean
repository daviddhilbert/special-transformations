import Section7.GammaPolynomial

/-!
# The coordinate normalization in the proof of Lemma 7.2

The change `X_i = c_i Y_i` and multiplication by `e` are performed on the
finite presentation, so repeated exponents and cancellation are retained.
This file proves the algebraic and valuation transport. It does not assume
or assert the existence part of multivariate Hensel's lemma.
-/

open MvPolynomial

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

namespace PolynomialPresentation

/-- Multiply the polynomial by `e` after the diagonal substitution. -/
noncomputable def normalize {n : ℕ} (P : PolynomialPresentation n K)
    (c : Fin n → K) (e : K) : PolynomialPresentation n K where
  length := P.length
  coefficient j := e * P.coefficient j * ∏ i, c i ^ P.exponent j i
  exponent := P.exponent

theorem eval_normalize {n : ℕ} (P : PolynomialPresentation n K)
    (c y : Fin n → K) (e : K) :
    (P.normalize c e).polynomial.eval y = e * P.polynomial.eval (fun i => c i * y i) := by
  classical
  rw [eval_polynomial, eval_polynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [normalize, mul_pow, Finset.prod_mul_distrib]
  ring

theorem homogeneous_normalize (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α : Γ} {P : PolynomialPresentation n K}
    (hP : P.Homogeneous v γ α) (c : Fin n → K) (e : K)
    (hc : ∀ i, v (c i) = γ i) (he : v e * α = 1) :
    (P.normalize c e).Homogeneous v (fun _ => 1) 1 := by
  classical
  intro j
  simp only [normalize, one_pow, Finset.prod_const_one, mul_one, map_mul, map_prod,
    map_pow]
  have hp : (∏ i, v (c i) ^ P.exponent j i) = ∏ i, γ i ^ P.exponent j i := by
    apply Finset.prod_congr rfl
    intro i _
    rw [hc i]
  rw [hp, mul_assoc, hP j, he]

end PolynomialPresentation

/-- For a nonzero gamma-polynomial, its residue value is attained in the field.
The normalizing scalar therefore needs no surjectivity assumption on `Γ`. -/
theorem gammaPolynomial_normalizingScalar_exists (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α : Γ} {F : MvPolynomial (Fin n) K}
    (hF : IsGammaPolynomial v γ α F) (hF0 : F ≠ 0)
    (c : Fin n → K) (hc : ∀ i, v (c i) = γ i) :
    ∃ e : K, v e * α = 1 := by
  classical
  obtain ⟨_, hα, P, hPF, hP⟩ := hF
  have hlen : P.length ≠ 0 := by
    intro hz
    have hzero : P.polynomial = 0 := by
      unfold PolynomialPresentation.polynomial
      haveI : IsEmpty (Fin P.length) := by rw [hz]; infer_instance
      simp
    exact hF0 (hPF.symm.trans hzero)
  let j : Fin P.length := ⟨0, Nat.pos_of_ne_zero hlen⟩
  let w : K := P.coefficient j * ∏ i, c i ^ P.exponent j i
  have hw : v w = α := by
    dsimp only [w]
    rw [map_mul, map_prod]
    have hp : (∏ i, v (c i ^ P.exponent j i)) = ∏ i, γ i ^ P.exponent j i := by
      apply Finset.prod_congr rfl
      intro i _
      rw [map_pow, hc i]
    rw [hp, hP j]
  refine ⟨w⁻¹, ?_⟩
  rw [map_inv₀, hw, inv_mul_cancel₀ hα]

/-- Scaling by representatives of `t` identifies its RV fibre with the fibre of one. -/
theorem rv_mul_eq_representative_iff (v : Valuation K Γ) {c y : K} (hc : c ≠ 0) :
    RVCalc.rv v (c * y) = RVCalc.rv v c ↔ RVCalc.rv v y = RVCalc.rv v (1 : K) := by
  by_cases hy : y = 0
  · subst y
    simp only [mul_zero, RVCalc.rv_zero]
    exact iff_of_false (fun h => RVCalc.rv_ne_none hc h.symm)
      (fun h => RVCalc.rv_ne_none (one_ne_zero : (1 : K) ≠ 0) h.symm)
  rw [RVCalc.rv_eq_iff (mul_ne_zero hc hy) hc, RVCalc.rv_eq_iff hy one_ne_zero]
  rw [show c * y - c = c * (y - 1) by ring, map_mul, map_mul,
    mul_lt_mul_iff_right₀ ((zero_lt_iff).mpr ((Valuation.ne_zero_iff v).mpr hc))]

theorem rvFibre_scale_iff (v : Valuation K Γ) {n : ℕ} {t : Fin n → RVCalc.RV v}
    (ht : ∀ i, t i ≠ none) {c : Fin n → K} (hc : c ∈ RVFibre v t) (y : Fin n → K) :
    (fun i => c i * y i) ∈ RVFibre v t ↔
      y ∈ RVFibre v (fun _ => RVCalc.rv v (1 : K)) := by
  apply forall_congr'
  intro i
  rw [← hc i]
  apply rv_mul_eq_representative_iff
  intro hz
  exact ht i ((hc i).symm.trans (hz ▸ RVCalc.rv_zero))

/-- The polynomial and residue-root normalization in Lemma 7.2.
The scalar is a field element, with its exact valuation equation displayed;
no surjectivity of the ambient value-group carrier is required. -/
theorem gammaPolynomial_normalization (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} (ht : ∀ i, t i ≠ none)
    {α : Γ} {F : MvPolynomial (Fin n) K}
    (hF : IsGammaPolynomial v (fun i => RVCalc.vrv v (t i)) α F)
    {c : Fin n → K} (hc : c ∈ RVFibre v t) (e : K) (he : v e * α = 1) :
    ∃ G : MvPolynomial (Fin n) K,
      IsGammaPolynomial v (fun _ => 1) 1 G ∧
      (∀ y, G.eval y = e * F.eval (fun i => c i * y i)) ∧
      (IsResidueRoot v (fun _ => RVCalc.rv v (1 : K)) 1 G ↔
        IsResidueRoot v t α F) := by
  classical
  obtain ⟨hγ, hα, P, hPF, hP⟩ := hF
  let G := (P.normalize c e).polynomial
  have hG (y : Fin n → K) : G.eval y = e * F.eval (fun i => c i * y i) := by
    rw [← hPF]
    exact P.eval_normalize c y e
  have hepos : 0 < v e := by
    apply lt_of_le_of_ne zero_le
    intro hz
    have : (0 : Γ) = 1 := by simpa [← hz] using he
    exact zero_ne_one this
  have hcompare (z : K) : v (e * z) < 1 ↔ v z < α := by
    rw [map_mul, ← he, mul_lt_mul_iff_right₀ hepos]
  refine ⟨G, ⟨fun _ => one_ne_zero, one_ne_zero,
    P.normalize c e, rfl,
      PolynomialPresentation.homogeneous_normalize v hP c e (rvFibre_value v hc) he⟩,
    hG, ?_⟩
  constructor
  · intro h a ha
    let y : Fin n → K := fun i => a i / c i
    have hc0 (i : Fin n) : c i ≠ 0 := by
      intro hz
      exact ht i ((hc i).symm.trans (hz ▸ RVCalc.rv_zero))
    have hcy : (fun i => c i * y i) = a := by
      funext i
      exact mul_div_cancel₀ (a i) (hc0 i)
    have hy : y ∈ RVFibre v (fun _ => RVCalc.rv v (1 : K)) :=
      (rvFibre_scale_iff v ht hc y).mp (by rw [hcy]; exact ha)
    have hh := h y hy
    rw [hG, hcy] at hh
    exact (hcompare _).mp hh
  · intro h y hy
    rw [hG]
    exact (hcompare _).mpr (h _ ((rvFibre_scale_iff v ht hc y).mpr hy))

/-- Every nonzero gamma-polynomial admits the coordinate normalization, with
both representatives and scalar constructed inside the valued field. -/
theorem exists_gammaPolynomial_normalization (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} (ht : ∀ i, t i ≠ none)
    {α : Γ} {F : MvPolynomial (Fin n) K}
    (hF : IsGammaPolynomial v (fun i => RVCalc.vrv v (t i)) α F) (hF0 : F ≠ 0) :
    ∃ (c : Fin n → K) (e : K) (G : MvPolynomial (Fin n) K),
      c ∈ RVFibre v t ∧ v e * α = 1 ∧
      IsGammaPolynomial v (fun _ => 1) 1 G ∧
      (∀ y, G.eval y = e * F.eval (fun i => c i * y i)) ∧
      (IsResidueRoot v (fun _ => RVCalc.rv v (1 : K)) 1 G ↔
        IsResidueRoot v t α F) := by
  obtain ⟨c, hc⟩ := rvFibre_nonempty v t
  obtain ⟨e, he⟩ := gammaPolynomial_normalizingScalar_exists v hF hF0 c (rvFibre_value v hc)
  obtain ⟨G, hG, heval, hroot⟩ := gammaPolynomial_normalization v ht hF hc e he
  exact ⟨c, e, G, hc, he, hG, heval, hroot⟩

end SpecialTransformations.Section7
