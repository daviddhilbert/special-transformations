module

public import Section9.ResidueChartReducedness
public import Section9.RVJacobianNormalization
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-! On a certified open residue chart the Jacobian is the implicit
matrix obtained from the two square derivative blocks. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "k" => ModelResidue M

theorem residueChart_inputBlock_det_ne_zero [IsAlgClosed k]
    (C : Set (Fin (n + n) → k)) (p : Fin (n + n) → k) (hp : p ∈ C)
    (P : Fin n → MvPolynomial (Fin (n + n)) k) (Q T : MvPolynomial (Fin (n + n)) k)
    (hQ : Q = residueOutputJacobian P * T)
    (hP : ∀ i q, q ∈ C → (P i).eval q = 0) (hQp : Q.eval p ≠ 0)
    (hchart : ∀ q, (∀ i, (P i).eval q = 0) → Q.eval q ≠ 0 → q ∈ C)
    (hhor : ∀ x, IsPolynomialTangent C p (productTuple x 0) → x = 0) :
    (Matrix.of fun i j => (pderiv (productLeft n n j) (P i)).eval p).det ≠ 0 := by
  classical
  let B : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => (pderiv (productLeft n n j) (P i)).eval p
  have hB : Function.Injective B.mulVec := by
    intro x y he
    have hzero : B.mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, he, sub_self]
    apply sub_eq_zero.mp
    apply hhor
    apply (isPolynomialTangent_iff_of_radical_chart C p hp P Q hP hQp hchart
      (residueChartIdeal_isRadical_of_outputJacobian P Q T hQ) _).mpr
    intro i
    rw [← (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).sum_comp, Fintype.sum_sum_type]
    change (∑ j, B i j * productTuple (x - y) 0 (productLeft n n j)) +
      (∑ j, (pderiv (productRight n n j) (P i)).eval p *
        productTuple (x - y) 0 (productRight n n j)) = 0
    simp only [productTuple_left, productTuple_right, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    exact congrFun hzero i
  exact ((Matrix.isUnit_iff_isUnit_det B).mp (Matrix.mulVec_injective_iff_isUnit.mp hB)).ne_zero

theorem isResidueJacobianMap_of_open_chart [IsAlgClosed k]
    (C : Set (Fin (n + n) → k)) (p : Fin (n + n) → k) (hp : p ∈ C)
    (P : Fin n → MvPolynomial (Fin (n + n)) k) (Q T : MvPolynomial (Fin (n + n)) k)
    (hQ : Q = residueOutputJacobian P * T)
    (hP : ∀ i q, q ∈ C → (P i).eval q = 0)
    (hQp : Q.eval p ≠ 0)
    (hchart : ∀ q, (∀ i, (P i).eval q = 0) → Q.eval q ≠ 0 → q ∈ C)
    (hB : (Matrix.of fun i j => (pderiv (productLeft n n j) (P i)).eval p).det ≠ 0) :
    let A : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => (pderiv (productRight n n j) (P i)).eval p
    let B : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => (pderiv (productLeft n n j) (P i)).eval p
    IsResidueJacobianMap (M := M) C p (Matrix.toLin' (A⁻¹ * (-B))) ∧ (A⁻¹ * (-B)).det ≠ 0 := by
  classical
  dsimp only
  let A : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => (pderiv (productRight n n j) (P i)).eval p
  let B : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => (pderiv (productLeft n n j) (P i)).eval p
  change IsResidueJacobianMap (M := M) C p (Matrix.toLin' (A⁻¹ * (-B))) ∧ (A⁻¹ * (-B)).det ≠ 0
  have hA : IsUnit A.det := by
    rw [hQ, map_mul, eval_residueOutputJacobian] at hQp
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hQp)
  have hB' : IsUnit (-B).det := by
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    exact ((Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hB)).neg
  refine ⟨?_, ?_⟩
  · intro x y
    rw [isPolynomialTangent_iff_of_radical_chart C p hp P Q hP hQp hchart
      (residueChartIdeal_isRadical_of_outputJacobian P Q T hQ), Matrix.toLin'_apply]
    have he (i : Fin n) :
        (∑ j, (pderiv j (P i)).eval p * productTuple x y j) = (B.mulVec x + A.mulVec y) i := by
      rw [← (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).sum_comp, Fintype.sum_sum_type]
      change (∑ j, (pderiv (productLeft n n j) (P i)).eval p * productTuple x y (productLeft n n j)) +
        (∑ j, (pderiv (productRight n n j) (P i)).eval p * productTuple x y (productRight n n j)) = _
      simp only [productTuple_left, productTuple_right, Pi.add_apply, Matrix.mulVec, dotProduct, B, A] <;> rfl
    simp only [he]
    have hcancel (z : Fin n → k) : (A⁻¹).mulVec (A.mulVec z) = z := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]
    constructor
    · intro h
      have h₁ : B.mulVec x + A.mulVec y = 0 := funext h
      have h₂ : A.mulVec y = (-B).mulVec x := by
        rw [Matrix.neg_mulVec]
        exact eq_neg_of_add_eq_zero_right h₁
      rw [← Matrix.mulVec_mulVec, ← h₂, hcancel]
    · intro h
      have h₂ : A.mulVec y = (-B).mulVec x := by
        rw [h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_left A _ hA]
      intro i
      simp only [h₂, Matrix.neg_mulVec, add_neg_cancel, Pi.zero_apply]
  · rw [Matrix.det_mul]
    exact mul_ne_zero (A.isUnit_nonsing_inv_det hA).ne_zero hB'.ne_zero

theorem isRVJacobianAt_of_certified_chart [IsAlgClosed k]
    (C : Set (Fin (n + n) → CanonicalRV.RVSort M))
    (a b : Fin n → CanonicalRV.RVSort M) (x y : Fin n → k)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (P : Fin n → MvPolynomial (Fin (n + n)) k) (T : MvPolynomial (Fin (n + n)) k)
    (hp : productTuple x y ∈ normalizedCorrespondence C a b)
    (hP : ∀ i q, q ∈ normalizedCorrespondence C a b → (P i).eval q = 0)
    (hQ : (residueOutputJacobian P * T).eval (productTuple x y) ≠ 0)
    (hchart : ∀ q, (∀ i, (P i).eval q = 0) → (residueOutputJacobian P * T).eval q ≠ 0 →
      q ∈ normalizedCorrespondence C a b)
    (hB : (Matrix.of fun i j => (pderiv (productLeft n n j) (P i)).eval (productTuple x y)).det ≠ 0) :
    let A : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => (pderiv (productRight n n j) (P i)).eval (productTuple x y)
    let B : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => (pderiv (productLeft n n j) (P i)).eval (productTuple x y)
    IsRVJacobianAt C (residueScale a x) (residueScale b y)
      (((∏ i, b i) / ∏ i, a i) * residueRV ((-1 : k)^n * (B.det * A.det⁻¹))) := by
  let p := productTuple x y
  let A : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => (pderiv (productRight n n j) (P i)).eval p
  let B : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => (pderiv (productLeft n n j) (P i)).eval p
  obtain ⟨hJ, hdet⟩ := isResidueJacobianMap_of_open_chart (normalizedCorrespondence C a b) p hp
    P (residueOutputJacobian P * T) T rfl hP hQ hchart hB
  have h := isRVJacobianAt_of_normalized_residue_jacobian C a b x y ha hb hx hy hp (A⁻¹ * (-B)) hJ hdet
  have he : (A⁻¹ * (-B)).det = (-1 : k)^n * (B.det * A.det⁻¹) := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Matrix.det_neg, Fintype.card_fin]
    ac_rfl
  rw [he] at h
  exact h

end SpecialTransformations.Section9
