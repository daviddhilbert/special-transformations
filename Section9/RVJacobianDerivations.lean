module

public import Section9.RVJacobianReduction

@[expose] public section

/-!
# Algebraic derivations of an implicit polynomial graph

This file identifies the implicit matrix from `RVJacobianReduction` with
the values of coordinate derivations on an algebraic graph.  The input
derivations are genuine Mathlib derivations, rather than hypotheses
asserting a Jacobian comparison.  Their existence on the relevant Gauss
field and extension to the actual graph remain separate prerequisites.
-/

open MvPolynomial

namespace SpecialTransformations.Section9

noncomputable section

section PolynomialChainRule

variable {R K ι : Type*} [CommRing R] [CommRing K] [Algebra R K] [Fintype ι]

/-- The chain rule for a derivation applied to multivariate polynomial
evaluation. Coefficients lie in the base ring annihilated by the
derivation. -/
theorem derivation_aeval_eq_sum (D : Derivation R K K) (z : ι → K)
    (P : MvPolynomial ι R) :
    D (aeval z P) = ∑ i, aeval z (pderiv i P) * D (z i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp [D.map_algebraMap]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P j hP =>
      simp only [map_mul, aeval_X, D.leibniz, smul_eq_mul,
        pderiv_mul, map_add, pderiv_X, Pi.single_apply]
      have hX (i : ι) :
          aeval z (if j = i then (1 : MvPolynomial ι R) else 0) =
            if j = i then (1 : K) else 0 := by
        split <;> simp
      simp only [hX, mul_ite, mul_one, mul_zero, add_mul, Finset.sum_add_distrib,
        ite_mul, zero_mul]
      rw [hP, Finset.mul_sum, add_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        ring
      · symm
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hij
          simp [Ne.symm hij]
        · simp

end PolynomialChainRule

section ImplicitDerivations

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
variable {n m : ℕ}

/-- Differentiating the equations of a polynomial graph produces the
linear system with its input and output Jacobian blocks. -/
theorem derivation_implicit_equation
    (P : Fin m → MvPolynomial (Fin n ⊕ Fin m) R)
    (x : Fin n → K) (y : Fin m → K)
    (hP : ∀ i, aeval (Sum.elim x y) (P i) = 0)
    (D : Fin n → Derivation R K K)
    (hx : ∀ j i, D j (x i) = if i = j then 1 else 0) :
    outputJacobian (fun i => (P i).map (algebraMap R K)) x y *
        (Matrix.of fun i j => D j (y i)) +
      inputJacobian (fun i => (P i).map (algebraMap R K)) x y = 0 := by
  classical
  ext i j
  have h := derivation_aeval_eq_sum (D j) (Sum.elim x y) (P i)
  rw [hP i, map_zero] at h
  rw [Fintype.sum_sum_type] at h
  simp only [Sum.elim_inl, Sum.elim_inr, hx, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, outputJacobian, inputJacobian,
    Matrix.zero_apply, pderiv_map, eval_map, ← aeval_def, add_comm] using h.symm

/-- Coordinate derivations on a polynomial graph agree with its implicit
Jacobian wherever the output block is invertible. -/
theorem derivation_eq_implicitJacobian
    (P : Fin m → MvPolynomial (Fin n ⊕ Fin m) R)
    (x : Fin n → K) (y : Fin m → K)
    (hP : ∀ i, aeval (Sum.elim x y) (P i) = 0)
    (D : Fin n → Derivation R K K)
    (hx : ∀ j i, D j (x i) = if i = j then 1 else 0)
    (hB : IsUnit (outputJacobian (fun i => (P i).map (algebraMap R K)) x y).det) :
    (Matrix.of fun i j => D j (y i)) =
      implicitJacobian (fun i => (P i).map (algebraMap R K)) x y :=
  implicitMatrix_unique _ _ hB _ (derivation_implicit_equation P x y hP D hx)

end ImplicitDerivations

end

end SpecialTransformations.Section9
