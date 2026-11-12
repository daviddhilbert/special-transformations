module

public import Section9.ValuedImplicitDerivative
public import Section9.RVJacobianDerivations

@[expose] public section

/-! Identify the derivative of an arbitrary definable branch with
coordinate derivations using its simple-root equations. This step uses
the equations from generic differentiation and needs no new local
analytic parameterization of the branch. -/

open MvPolynomial

namespace SpecialTransformations.Section9

variable {E K : Type*} [Field E] [Field K] [Algebra E K] {n : ℕ}

theorem implicitScalarSlope_single (P : MvPolynomial (Fin n ⊕ Unit) E)
    (z : Fin n ⊕ Unit → K) (j : Fin n) :
    implicitScalarSlope P z (Pi.single j 1) =
      -aeval z (pderiv (Sum.inl j) P) / aeval z (pderiv (Sum.inr ()) P) := by
  classical
  change -(∑ i : Fin n, aeval z (pderiv (Sum.inl i) P) * (Pi.single j 1 : Fin n → K) i) / _ = _
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, mul_one]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, mul_zero]
  · simp

/-- At a simple root, the coordinate derivation of the output equals
the implicit scalar slope on the corresponding basis vector. -/
theorem implicitScalarSlope_eq_derivation
    (P : MvPolynomial (Fin n ⊕ Unit) E) (x : Fin n → K) (y : K)
    (hroot : aeval (Sum.elim x (fun _ => y)) P = 0)
    (hs : aeval (Sum.elim x (fun _ => y)) (pderiv (Sum.inr ()) P) ≠ 0)
    (j : Fin n) (D : Derivation E K K)
    (hD : ∀ i, D (x i) = if j = i then 1 else 0) :
    implicitScalarSlope P (Sum.elim x (fun _ => y)) (Pi.single j 1) = D y := by
  classical
  let z : Fin n ⊕ Unit → K := Sum.elim x (fun _ => y)
  let A (i : Fin n) := aeval z (pderiv (Sum.inl i) P)
  let d := aeval z (pderiv (Sum.inr ()) P)
  have h := derivation_aeval_eq_sum D z P
  rw [show aeval z P = 0 from hroot, map_zero, Fintype.sum_sum_type] at h
  have hsum : (∑ i : Fin n, A i * D (x i)) = A j := by
    rw [Finset.sum_eq_single j]
    · simp [hD]
    · intro i _ hi
      simp [hD, Ne.symm hi]
    · simp
  have h' : 0 = (∑ i : Fin n, A i * D (x i)) + d * D y := by
    simpa [A, d, z] using h
  rw [hsum] at h'
  rw [implicitScalarSlope_single]
  change -A j / d = D y
  apply (div_eq_iff hs).mpr
  linear_combination h'

end SpecialTransformations.Section9
