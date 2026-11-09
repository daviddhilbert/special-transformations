import Section9.RVJacobian

/-! A polynomial chart for a residue correspondence computes its
tangent space when the equations generate the localized vanishing
ideal. A certificate uses one multiplier nonzero at the chart point. -/

open MvPolynomial

namespace SpecialTransformations.Section9

variable {K : Type*} [Field K] {d m : ℕ}

theorem isPolynomialTangent_iff_of_local_equations
    (C : Set (Fin d → K)) (p : Fin d → K) (hp : p ∈ C)
    (P : Fin m → MvPolynomial (Fin d) K)
    (hP : ∀ i q, q ∈ C → (P i).eval q = 0)
    (hgen : ∀ Q : MvPolynomial (Fin d) K, (∀ q ∈ C, Q.eval q = 0) →
      ∃ R : MvPolynomial (Fin d) K, ∃ A : Fin m → MvPolynomial (Fin d) K,
        R.eval p ≠ 0 ∧ R * Q = ∑ i, A i * P i) (h : Fin d → K) :
    IsPolynomialTangent C p h ↔ ∀ i, ∑ j, (pderiv j (P i)).eval p * h j = 0 := by
  classical
  let D (A : MvPolynomial (Fin d) K) := ∑ j, (pderiv j A).eval p * h j
  have hmul (A B : MvPolynomial (Fin d) K) : D (A * B) = A.eval p * D B + B.eval p * D A := by
    simp only [D, Derivation.leibniz, smul_eq_mul, map_add, map_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  have hsum (A : Fin m → MvPolynomial (Fin d) K) : D (∑ i, A i) = ∑ i, D (A i) := by
    simp only [D, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  constructor
  · intro ht i
    exact ht (P i) (hP i)
  · intro ht Q hQ
    change D Q = 0
    obtain ⟨R, A, hR, hEq⟩ := hgen Q hQ
    have hleft : D (R * Q) = R.eval p * D Q := by
      rw [hmul, hQ p hp, zero_mul, add_zero]
    have hright : D (∑ i, A i * P i) = 0 := by
      rw [hsum]
      apply Finset.sum_eq_zero
      intro i _
      rw [hmul, hP i p hp, show D (P i) = 0 from ht i, mul_zero, zero_mul, add_zero]
    rw [hEq, hright] at hleft
    exact (mul_eq_zero.mp hleft.symm).resolve_left hR

end SpecialTransformations.Section9
