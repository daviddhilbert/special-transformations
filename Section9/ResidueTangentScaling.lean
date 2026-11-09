import Section9.ResidueTangentMatrix
import Section9.RVJacobianDerivations

/-! Coordinatewise normalization transports the polynomial tangent.
The calculation uses the algebraic derivation chain rule. -/

open MvPolynomial

namespace SpecialTransformations.Section9

variable {K : Type*} [Field K] {d : ℕ}

def coordinateScale (s x : Fin d → K) : Fin d → K := fun i => s i * x i

private noncomputable def scalePolynomial (s : Fin d → K) (P : MvPolynomial (Fin d) K) :
    MvPolynomial (Fin d) K := aeval (fun i => C (s i) * X i) P

private theorem eval_scalePolynomial (s x : Fin d → K) (P : MvPolynomial (Fin d) K) :
    (scalePolynomial s P).eval x = P.eval (coordinateScale s x) := by
  simp only [← aeval_eq_eval, scalePolynomial]
  rw [comp_aeval_apply]
  simp only [map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, aeval_X]
  rfl

private theorem pderiv_scalePolynomial (s : Fin d → K) (P : MvPolynomial (Fin d) K) (i : Fin d) :
    pderiv i (scalePolynomial s P) = scalePolynomial s (pderiv i P) * C (s i) := by
  classical
  let x (j : Fin d) := C (s j) * X j
  change pderiv i (aeval x P) = _
  rw [derivation_aeval_eq_sum (pderiv i) x P, Finset.sum_eq_single i]
  · simp only [x, pderiv_mul, pderiv_C, zero_mul, pderiv_X_self, mul_one, zero_add]
    rfl
  · intro j _ hj
    simp only [x, pderiv_mul, pderiv_C, zero_mul, pderiv_X_of_ne hj, mul_zero, add_zero]
  · simp

private theorem scale_inverse (s x : Fin d → K) (hs : ∀ i, s i ≠ 0) :
    coordinateScale (fun i => (s i)⁻¹) (coordinateScale s x) = x := by
  funext i
  change (s i)⁻¹ * (s i * x i) = x i
  rw [← mul_assoc, inv_mul_cancel₀ (hs i), one_mul]

theorem polynomialTangent_scale_iff (s : Fin d → K) (hs : ∀ i, s i ≠ 0)
    (A : Set (Fin d → K)) (p h : Fin d → K) :
    IsPolynomialTangent (coordinateScale s ⁻¹' A) p h ↔
      IsPolynomialTangent A (coordinateScale s p) (coordinateScale s h) := by
  constructor
  · intro ht P hP
    have hzero := ht (scalePolynomial s P) (fun x hx => by
      rw [eval_scalePolynomial]
      exact hP _ hx)
    simpa only [pderiv_scalePolynomial, map_mul, eval_C, eval_scalePolynomial, coordinateScale,
      mul_assoc] using hzero
  · intro ht P hP
    let t (i : Fin d) := (s i)⁻¹
    have ht₀ (i : Fin d) : t i ≠ 0 := inv_ne_zero (hs i)
    have hP' (x : Fin d → K) (hx : x ∈ A) : (scalePolynomial t P).eval x = 0 := by
      rw [eval_scalePolynomial]
      apply hP
      change coordinateScale s (coordinateScale t x) ∈ A
      have h : coordinateScale s (coordinateScale t x) = x := by
        simpa only [t, inv_inv] using scale_inverse t x ht₀
      exact h.symm ▸ hx
    have hzero := ht (scalePolynomial t P) hP'
    have hp : coordinateScale t (coordinateScale s p) = p := scale_inverse s p hs
    simp only [pderiv_scalePolynomial, map_mul, eval_C, eval_scalePolynomial,
      hp, coordinateScale, mul_assoc] at hzero
    have he (i : Fin d) : t i * (s i * h i) = h i := by
      rw [← mul_assoc, show t i = (s i)⁻¹ from rfl, inv_mul_cancel₀ (hs i), one_mul]
    simpa only [he] using hzero

end SpecialTransformations.Section9
