module

public import Section7.LiftingAlgebra
public import Section9.RVJacobianReduction

@[expose] public section

/-! The determinant calculation for the weighted polynomial lift in
Theorem 9.16. The values of the two blocks come from the simplicity
conditions in Section 7. The row weights cancel in the implicit matrix.
The separate local derivative theorem identifies this matrix with the
derivative of the chosen Hensel branch. -/

open MvPolynomial
open SpecialTransformations.Section7
open scoped BigOperators

namespace SpecialTransformations.Section9

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-- The determinant of the implicit matrix has the ratio of the output
and input coordinate weights. The common product of row weights cancels. -/
theorem implicitMatrix_value_of_blocks (v : Valuation K Γ) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) (weight input output : Γ)
    (hw : weight ≠ 0) (ho : output ≠ 0)
    (hA : v A.det = weight / input) (hB : v B.det = weight / output) :
    v (implicitMatrix A B).det = output / input := by
  have hBo : v B.det ≠ 0 := hB.symm ▸ div_ne_zero hw ho
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr (v.ne_zero_iff.mp hBo)
  have hEq : B * implicitMatrix A B = -A :=
    eq_neg_of_add_eq_zero_left (implicitMatrix_equation A B hBu)
  have hdet := congrArg Matrix.det hEq
  rw [Matrix.det_mul, Matrix.det_neg] at hdet
  have hv := congrArg v hdet
  simp only [map_mul, map_pow, v.map_neg, map_one, one_pow, one_mul] at hv
  rw [hA, hB] at hv
  apply mul_left_cancel₀ (div_ne_zero hw ho)
  calc
    (weight / output) * v (implicitMatrix A B).det = weight / input := hv
    _ = (weight / output) * (output / input) := by
      symm
      calc
        (weight / output) * (output / input) =
            (output⁻¹ * output) * (weight * input⁻¹) := by
          simp only [div_eq_mul_inv]
          ac_rfl
        _ = weight / input := by rw [inv_mul_cancel₀ ho, one_mul, div_eq_mul_inv]

/-- The evaluated block of the weighted polynomial system in the same
coordinate order as `partialJacobianPolynomial`. -/
noncomputable def partialJacobianMatrix {n m d : ℕ} (f : Fin n ↪ Fin m)
    (F : Fin d → MvPolynomial (Fin m) K) (a : Fin m → K) : Matrix (Fin d) (Fin n) K :=
  Matrix.of (fun i j => (pderiv (f j) (F i)).eval a)

theorem det_partialJacobianMatrix {n m : ℕ} (f : Fin n ↪ Fin m)
    (F : Fin n → MvPolynomial (Fin m) K) (a : Fin m → K) :
    (partialJacobianMatrix f F a).det = (partialJacobianPolynomial f F).eval a := by
  rw [partialJacobianPolynomial, RingHom.map_det]
  rfl

/-- Multiplying the determinant of a weighted block by its column
weights gives the product of the common row weights. -/
theorem weightedBlock_value_mul_columns (v : Valuation K Γ) {n m : ℕ}
    (u : Fin m → RVCalc.RV v) (hu : ∀ j, u j ≠ none)
    {α : Fin n → Γ} (F : Fin n → MvPolynomial (Fin m) K)
    (hF : ∀ i, IsGammaPolynomial v (fun j => RVCalc.vrv v (u j)) (α i) (F i))
    (f : Fin n ↪ Fin m)
    (hf : ¬ IsResidueRoot v u (jacobianValue (fun j => RVCalc.vrv v (u (f j))) α)
      (partialJacobianPolynomial f F))
    {a : Fin m → K} (ha : a ∈ RVFibre v u) :
    v ((partialJacobianPolynomial f F).eval a * ∏ j, a (f j)) = ∏ i, α i := by
  have hγ (j : Fin m) : RVCalc.vrv v (u j) ≠ 0 := by
    rw [← rvFibre_value v ha j]
    exact v.ne_zero_iff.mpr (fun h => hu j ((ha j).symm.trans (h ▸ RVCalc.rv_zero)))
  have he := (not_residueRoot_iff_eval_eq v hu (isGammaPolynomial_partialJacobian v hγ hF f)).mp
    hf a ha
  rw [map_mul, map_prod, he, jacobianValue]
  simp only [rvFibre_value v ha]
  exact div_mul_cancel₀ _ (Finset.prod_ne_zero_iff.mpr fun j _ => hγ (f j))

/-- The implicit matrix of a Section 7 system simple in both blocks has
the prescribed Gamma value at every point of the product RV fibre. This
calculation is for the chosen system and applies in any valuation rank. -/
theorem weightedImplicitMatrix_value (v : Valuation K Γ) {n : ℕ}
    (t s : Fin n → RVCalc.RV v) (ht : ∀ j, t j ≠ none) (hs : ∀ j, s j ≠ none)
    {α : Fin n → Γ} (F : Fin n → MvPolynomial (Fin (n + n)) K)
    (hF : ∀ i, IsGammaPolynomial v (fun j => RVCalc.vrv v (productTuple t s j)) (α i) (F i))
    (hleft : ¬ IsResidueRoot v (productTuple t s)
      (jacobianValue (fun j => RVCalc.vrv v (t j)) α)
      (partialJacobianPolynomial (productLeft n n) F))
    (hright : ¬ IsResidueRoot v (productTuple t s)
      (jacobianValue (fun j => RVCalc.vrv v (s j)) α)
      (partialJacobianPolynomial (productRight n n) F))
    {x y : Fin n → K} (hx : x ∈ RVFibre v t) (hy : y ∈ RVFibre v s) :
    v (implicitMatrix
      (partialJacobianMatrix (productLeft n n) F (productTuple x y))
      (partialJacobianMatrix (productRight n n) F (productTuple x y))).det =
      (∏ j, RVCalc.vrv v (s j)) / ∏ j, RVCalc.vrv v (t j) := by
  have hts (j : Fin (n + n)) : productTuple t s j ≠ none := by
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective j
    cases i with
    | inl i =>
      change productTuple t s (productLeft n n i) ≠ none
      simpa only [productTuple_left] using ht i
    | inr i =>
      change productTuple t s (productRight n n i) ≠ none
      simpa only [productTuple_right] using hs i
  have hxy := productTuple_mem_RVFibre v hx hy
  have hγ (j : Fin (n + n)) : RVCalc.vrv v (productTuple t s j) ≠ 0 := by
    rw [← rvFibre_value v hxy j]
    exact v.ne_zero_iff.mpr (fun h => hts j ((hxy j).symm.trans (h ▸ RVCalc.rv_zero)))
  have hA := (not_residueRoot_iff_eval_eq v hts
      (isGammaPolynomial_partialJacobian v hγ hF (productLeft n n))).mp
    (by simpa only [jacobianValue, Function.comp_apply, productTuple_left] using hleft) _ hxy
  have hB := (not_residueRoot_iff_eval_eq v hts
      (isGammaPolynomial_partialJacobian v hγ hF (productRight n n))).mp
    (by simpa only [jacobianValue, Function.comp_apply, productTuple_right] using hright) _ hxy
  apply implicitMatrix_value_of_blocks v _ _ (∏ i, α i) _ _
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => (hF i).2.1
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _
    simpa only [productTuple_right] using hγ (productRight n n j)
  · rw [det_partialJacobianMatrix]
    simpa only [jacobianValue, Function.comp_apply, productTuple_left] using hA
  · rw [det_partialJacobianMatrix]
    simpa only [jacobianValue, Function.comp_apply, productTuple_right] using hB

end SpecialTransformations.Section9
