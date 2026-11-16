module

public import Section7.GammaPolynomialAlgebra
public import Section7.PolynomialNormalization
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# The RV/Jacobian normalization bridge in Lemma 7.2

The Jacobian is a genuine polynomial. Its gamma-polynomial structure and
exact value at every representative of a simple residue root are proved,
not assumed. The diagonal substitution, chain rule and determinant
calculation adapt the local MIT `Sec7GammaHensel.lean` (Yimu Yin); its RV
copy, collected-coefficient predicate and assumed Hensel theorem are excluded.

These elementary results hold in arbitrary valued fields. They prove the
normalization bridge, not the remaining multivariate root-existence theorem.
-/

open MvPolynomial

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

noncomputable def jacobianMatrix {R : Type*} [CommRing R] {n : ℕ}
    (F : Fin n → MvPolynomial (Fin n) R) (a : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (pderiv j (F i)).eval a

noncomputable def jacobianPolynomial {R : Type*} [CommRing R] {n : ℕ}
    (F : Fin n → MvPolynomial (Fin n) R) :
    MvPolynomial (Fin n) R := Matrix.det (Matrix.of fun i j => pderiv j (F i))

/-- Paper `sum alpha_i - sum gamma_j` in multiplicative valuation notation. -/
def jacobianValue {n : ℕ} (γ α : Fin n → Γ) : Γ := (∏ i, α i) / ∏ j, γ j

theorem isGammaPolynomial_jacobian (v : Valuation K Γ) {n : ℕ}
    {γ α : Fin n → Γ} {F : Fin n → MvPolynomial (Fin n) K}
    (hF : ∀ i, IsGammaPolynomial v γ (α i) (F i)) :
    IsGammaPolynomial v γ (jacobianValue γ α) (jacobianPolynomial F) := by
  classical
  have hγ (i : Fin n) : γ i ≠ 0 := (hF i).1 i
  have hα (i : Fin n) : α i ≠ 0 := (hF i).2.1
  have hδ : jacobianValue γ α ≠ 0 :=
    div_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hα i)
      (Finset.prod_ne_zero_iff.mpr fun i _ => hγ i)
  rw [jacobianPolynomial, Matrix.det_apply]
  apply IsGammaPolynomial.sum v hγ hδ
  intro σ
  have hp := IsGammaPolynomial.prod v hγ Finset.univ
    (fun j _ => (hF (σ j)).pderiv v j)
  have he : (∏ j, α (σ j) / γ j) = jacobianValue γ α := by
    rw [Finset.prod_div_distrib, Equiv.prod_comp σ]
    rfl
  rw [he] at hp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using hp
  · simpa [hs] using hp.neg v

/-- Definition 7.1 on a finite, nonzero RV tuple. Simplicity is the paper's
non-residue-root condition on the Jacobian, not an assumed valuation identity. -/
def IsSimpleCommonResidueRoot (v : Valuation K Γ) {n : ℕ}
    (t : Fin n → RVCalc.RV v) (α : Fin n → Γ)
    (F : Fin n → MvPolynomial (Fin n) K) : Prop :=
  (∀ i, t i ≠ none) ∧
  (∀ i, IsGammaPolynomial v (fun j => RVCalc.vrv v (t j)) (α i) (F i)) ∧
  (∀ i, IsResidueRoot v t (α i) (F i)) ∧
  ¬ IsResidueRoot v t (jacobianValue (fun j => RVCalc.vrv v (t j)) α)
      (jacobianPolynomial F)

theorem not_residueRoot_iff_eval_eq (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} (ht : ∀ i, t i ≠ none)
    {α : Γ} {F : MvPolynomial (Fin n) K}
    (hF : IsGammaPolynomial v (fun i => RVCalc.vrv v (t i)) α F) :
    ¬ IsResidueRoot v t α F ↔ ∀ a ∈ RVFibre v t, v (F.eval a) = α := by
  constructor
  · intro hn a ha
    have hn' : ¬ ∃ b ∈ RVFibre v t, v (F.eval b) < α :=
      (not_congr (residueRoot_iff_exists v ht hF)).mp hn
    exact le_antisymm (gammaPolynomial_eval_le v hF (rvFibre_value v ha))
      (le_of_not_gt fun hlt => hn' ⟨a, ha, hlt⟩)
  · intro he hn
    obtain ⟨a, ha⟩ := rvFibre_nonempty v t
    exact (lt_irrefl α) (by simpa only [he a ha] using hn a ha)

theorem IsSimpleCommonResidueRoot.jacobian_eval_value (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} {α : Fin n → Γ}
    {F : Fin n → MvPolynomial (Fin n) K} (h : IsSimpleCommonResidueRoot v t α F)
    {a : Fin n → K} (ha : a ∈ RVFibre v t) :
    v ((jacobianPolynomial F).eval a) =
      jacobianValue (fun j => RVCalc.vrv v (t j)) α :=
  (not_residueRoot_iff_eval_eq v h.1 (isGammaPolynomial_jacobian v h.2.1)).mp h.2.2.2 a ha

theorem IsSimpleCommonResidueRoot.polynomial_ne_zero (v : Valuation K Γ) {n : ℕ}
    {t : Fin n → RVCalc.RV v} {α : Fin n → Γ}
    {F : Fin n → MvPolynomial (Fin n) K} (h : IsSimpleCommonResidueRoot v t α F)
    (i : Fin n) : F i ≠ 0 := by
  intro hi
  have hzero : jacobianPolynomial F = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    simp [hi]
  obtain ⟨a, ha⟩ := rvFibre_nonempty v t
  have hv := h.jacobian_eval_value v ha
  rw [hzero, map_zero, map_zero] at hv
  exact (isGammaPolynomial_jacobian v h.2.1).2.1 hv.symm

noncomputable def diagonalScale {n : ℕ} (c : Fin n → K) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval fun j => C (c j) * X j

@[simp] theorem diagonalScale_X {n : ℕ} (c : Fin n → K) (j : Fin n) :
    diagonalScale c (X j) = C (c j) * X j := by rw [diagonalScale, aeval_X]

@[simp] theorem diagonalScale_C {n : ℕ} (c : Fin n → K) (a : K) :
    diagonalScale c (C a) = C a := by simp [diagonalScale]

theorem diagonalScale_monomial {n : ℕ} (c : Fin n → K) (d : Fin n →₀ ℕ) (r : K) :
    diagonalScale c (monomial d r) = monomial d (r * d.prod fun j e => c j ^ e) := by
  rw [diagonalScale, aeval_monomial, algebraMap_eq, ← C_mul_monomial]
  congr 1
  rw [Finsupp.prod, Finsupp.prod]
  rw [show (∏ a ∈ d.support, (C (c a) * X a) ^ d a) =
      ∏ a ∈ d.support, C (c a ^ d a) * X a ^ d a from
    Finset.prod_congr rfl fun a _ => by rw [mul_pow, C_pow]]
  rw [Finset.prod_mul_distrib, prod_X_pow_eq_monomial, ← map_prod, C_mul_monomial, mul_one]

theorem eval_diagonalScale {n : ℕ} (c : Fin n → K) (F : MvPolynomial (Fin n) K)
    (y : Fin n → K) : (diagonalScale c F).eval y = F.eval (fun j => c j * y j) := by
  induction F using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [diagonalScale_monomial, eval_monomial, eval_monomial]
    have h : d.prod (fun j e => (c j * y j) ^ e) =
        (d.prod fun j e => c j ^ e) * (d.prod fun j e => y j ^ e) := by
      simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
    rw [h]
    ring
  | add p q hp hq => rw [map_add, eval_add, hp, eval_add, hq]

theorem pderiv_diagonalScale {n : ℕ} (c : Fin n → K) (i : Fin n)
    (F : MvPolynomial (Fin n) K) :
    pderiv i (diagonalScale c F) = C (c i) * diagonalScale c (pderiv i F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]; ring
  | mul_X p j hp =>
    have hX : pderiv i (C (c j) * X j) = if i = j then C (c j) else 0 := by
      rw [pderiv_C_mul]
      by_cases h : i = j
      · subst h; simp
      · rw [pderiv_X_of_ne (Ne.symm h), mul_zero, if_neg h]
    have hdsX : diagonalScale c (pderiv i (X j)) = if i = j then 1 else 0 := by
      by_cases h : i = j
      · subst h; simp
      · rw [pderiv_X_of_ne (Ne.symm h), map_zero, if_neg h]
    simp only [map_mul, diagonalScale_X, pderiv_mul, map_add, hp, hX, hdsX]
    by_cases h : i = j
    · subst h; simp; ring
    · simp only [if_neg h, mul_zero, add_zero]; ring

noncomputable def normalizePolynomial {n : ℕ} (c : Fin n → K) (e : K)
    (F : MvPolynomial (Fin n) K) : MvPolynomial (Fin n) K := C e * diagonalScale c F

theorem eval_normalizePolynomial {n : ℕ} (c : Fin n → K) (e : K)
    (F : MvPolynomial (Fin n) K) (y : Fin n → K) :
    (normalizePolynomial c e F).eval y = e * F.eval (fun j => c j * y j) := by
  rw [normalizePolynomial, eval_mul, eval_C, eval_diagonalScale]

theorem PolynomialPresentation.normalize_polynomial {n : ℕ} (P : PolynomialPresentation n K)
    (c : Fin n → K) (e : K) :
    (P.normalize c e).polynomial = normalizePolynomial c e P.polynomial := by
  classical
  have hterm (j : Fin P.length) :
      C e * diagonalScale c (monomial (P.exponent j) (P.coefficient j)) =
        monomial (P.exponent j) ((P.normalize c e).coefficient j) := by
    have hp : (P.exponent j).prod (fun k m => c k ^ m) = ∏ k, c k ^ P.exponent j k := by
      rw [Finsupp.prod_fintype]
      intro k
      simp
    rw [diagonalScale_monomial, C_mul_monomial, hp]
    simp only [PolynomialPresentation.normalize]
    congr 1
    ring
  simp only [normalizePolynomial, PolynomialPresentation.polynomial, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => (hterm j).symm

theorem normalizePolynomial_isGamma (v : Valuation K Γ) {n : ℕ}
    {γ : Fin n → Γ} {α : Γ} {F : MvPolynomial (Fin n) K}
    (hF : IsGammaPolynomial v γ α F) (c : Fin n → K) (e : K)
    (hc : ∀ i, v (c i) = γ i) (he : v e * α = 1) :
    IsGammaPolynomial v (fun _ => 1) 1 (normalizePolynomial c e F) := by
  obtain ⟨_, _, P, rfl, hP⟩ := hF
  exact ⟨fun _ => one_ne_zero, one_ne_zero, P.normalize c e,
    P.normalize_polynomial c e, PolynomialPresentation.homogeneous_normalize v hP c e hc he⟩

theorem eval_jacobianPolynomial {R : Type*} [CommRing R] {n : ℕ}
    (F : Fin n → MvPolynomial (Fin n) R) (y : Fin n → R) :
    (jacobianPolynomial F).eval y = (jacobianMatrix F y).det := by
  rw [jacobianPolynomial, RingHom.map_det]
  rfl

theorem jacobianMatrix_normalize {n : ℕ} (F : Fin n → MvPolynomial (Fin n) K)
    (c e y : Fin n → K) :
    jacobianMatrix (fun i => normalizePolynomial c (e i) (F i)) y =
      Matrix.diagonal e * jacobianMatrix F (fun j => c j * y j) * Matrix.diagonal c := by
  ext i j
  simp only [jacobianMatrix, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    normalizePolynomial, pderiv_C_mul, pderiv_diagonalScale, eval_mul, eval_C,
    eval_diagonalScale]
  ring

theorem jacobianPolynomial_eval_normalize {n : ℕ}
    (F : Fin n → MvPolynomial (Fin n) K) (c e y : Fin n → K) :
    (jacobianPolynomial (fun i => normalizePolynomial c (e i) (F i))).eval y =
      (∏ i, e i * c i) * (jacobianPolynomial F).eval (fun j => c j * y j) := by
  rw [eval_jacobianPolynomial, jacobianMatrix_normalize, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_diagonal, eval_jacobianPolynomial, Finset.prod_mul_distrib]
  ring

end SpecialTransformations.Section7
