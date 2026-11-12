module

public import Section9.RVJacobian

@[expose] public section

/-! Tangent columns determine the residue Jacobian once the simple
output equations rule out vertical tangent vectors. -/

open MvPolynomial
open SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {K : Type*} [Field K] {n d : ℕ}

private def polynomialTangentSpace (C : Set (Fin d → K)) (p : Fin d → K) :
    Submodule K (Fin d → K) where
  carrier := {h | IsPolynomialTangent C p h}
  zero_mem' := by
    intro P hP
    simp
  add_mem' := by
    intro x y hx hy P hP
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hx P hP, hy P hP, add_zero]
  smul_mem' := by
    intro r x hx P hP
    simp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm _ r, ← Finset.mul_sum, hx P hP, mul_zero]

theorem polynomialTangent_iff_mulVec
    (C : Set (Fin (n + n) → K)) (p : Fin (n + n) → K)
    (D : Matrix (Fin n) (Fin n) K)
    (hcol : ∀ j, IsPolynomialTangent C p (productTuple (Pi.single j 1) (fun i => D i j)))
    (hvertical : ∀ y, IsPolynomialTangent C p (productTuple 0 y) → y = 0)
    (x y : Fin n → K) :
    IsPolynomialTangent C p (productTuple x y) ↔ y = D.mulVec x := by
  classical
  let T := polynomialTangentSpace C p
  have hx : productTuple x (D.mulVec x) ∈ T := by
    have he : (∑ j, x j • productTuple (Pi.single j 1) (fun i => D i j)) =
        productTuple x (D.mulVec x) := by
      apply productTuple_ext
      · intro i
        simp only [Finset.sum_apply, Pi.smul_apply, productTuple_left, smul_eq_mul]
        rw [Finset.sum_eq_single i]
        · rw [Pi.single_eq_same, mul_one]
        · intro j _ hji
          rw [Pi.single_eq_of_ne hji.symm, mul_zero]
        · simp
      · intro i
        simp only [Finset.sum_apply, Pi.smul_apply, productTuple_right, smul_eq_mul,
          Matrix.mulVec, dotProduct, mul_comm (x _)]
    rw [← he]
    exact T.sum_mem fun j _ => T.smul_mem (x j) (hcol j)
  constructor
  · intro hy
    have hsub := T.sub_mem (show productTuple x y ∈ T from hy) hx
    have he : productTuple x y - productTuple x (D.mulVec x) =
        productTuple 0 (y - D.mulVec x) := by
      apply productTuple_ext
      · intro i
        simp only [Pi.sub_apply, productTuple_left, sub_self, Pi.zero_apply]
      · intro i
        simp only [Pi.sub_apply, productTuple_right]
    rw [he] at hsub
    exact sub_eq_zero.mp (hvertical _ hsub)
  · rintro rfl
    exact hx

theorem polynomialTangent_vertical_eq_zero_of_simple_equations
    (C : Set (Fin (n + n) → K)) (p : Fin (n + n) → K)
    (P : Fin n → MvPolynomial (Fin (n + n)) K)
    (hP : ∀ i q, q ∈ C → (P i).eval q = 0)
    (hoff : ∀ i j, j ≠ i → (pderiv (productRight n n j) (P i)).eval p = 0)
    (hdiag : ∀ i, (pderiv (productRight n n i) (P i)).eval p ≠ 0)
    (y : Fin n → K) (hy : IsPolynomialTangent C p (productTuple 0 y)) : y = 0 := by
  classical
  funext i
  have h := hy (P i) (hP i)
  rw [← (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).sum_comp, Fintype.sum_sum_type] at h
  change (∑ j : Fin n, (pderiv (productLeft n n j) (P i)).eval p *
      productTuple (0 : Fin n → K) y (productLeft n n j)) +
    (∑ j : Fin n, (pderiv (productRight n n j) (P i)).eval p *
      productTuple (0 : Fin n → K) y (productRight n n j)) = 0 at h
  simp only [productTuple_left, productTuple_right, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add] at h
  rw [Finset.sum_eq_single i] at h
  · exact (mul_eq_zero.mp h).resolve_left (hdiag i)
  · intro j _ hj
    rw [hoff i j hj, zero_mul]
  · simp

theorem IsPolynomialTangent.comp_equiv {C : Set (Fin d → K)} {p h : Fin d → K}
    (ht : IsPolynomialTangent C p h) (e : Fin d ≃ Fin d) :
    IsPolynomialTangent {z | z ∘ e.symm ∈ C} (p ∘ e) (h ∘ e) := by
  intro P hP
  have hvanish (x : Fin d → K) (hx : x ∈ C) : (rename e P).eval x = 0 := by
    rw [eval_rename]
    apply hP
    change (x ∘ e) ∘ e.symm ∈ C
    have he : (x ∘ e) ∘ e.symm = x := funext fun i => congrArg x (e.apply_symm_apply i)
    rwa [he]
  have hzero := ht (rename e P) hvanish
  rw [← e.sum_comp] at hzero
  simpa only [pderiv_rename e.injective, eval_rename, Function.comp_apply] using hzero

end SpecialTransformations.Section9
