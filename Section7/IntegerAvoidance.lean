module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Int.Cast.Field

@[expose] public section

/-!
# Integer choices for the two Jacobians in Theorem 7.6

Pinned Mathlib's `MvPolynomial.funext_set` already proves polynomial
extensionality on a box of infinite subsets. Apply it to the integer image
in a characteristic-zero field, then to the product of the two actual
determinant polynomials. No genericity condition is assumed as a premise.
The valued-field and original-base polynomial bridges are separate.
-/

open MvPolynomial

namespace SpecialTransformations.Section7

variable {K : Type*} [Field K] [CharZero K]

theorem exists_integer_eval_ne_zero {σ : Type*} {P : MvPolynomial σ K} (hP : P ≠ 0) :
    ∃ z : σ → ℤ, P.eval (fun i => (z i : K)) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hP
  apply MvPolynomial.funext_set (fun _ => Set.range (Int.castRingHom K))
    (fun _ => Set.infinite_range_of_injective (Int.cast_injective))
  intro x hx
  choose z hz using fun i => hx i (Set.mem_univ i)
  have he : (fun i => (z i : K)) = x := funext hz
  simpa only [map_zero, he] using h z

noncomputable def rowCombinationDeterminant {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) : MvPolynomial (Fin n ⊕ Fin n) K :=
  Matrix.det (Matrix.of fun i j => X (.inl i) * C (A i j) + X (.inr i) * C (B i j))

theorem eval_rowCombinationDeterminant {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) (p q : Fin n → K) :
    (rowCombinationDeterminant A B).eval (Sum.elim p q) =
      Matrix.det (Matrix.of fun i j => p i * A i j + q i * B i j) := by
  classical
  unfold rowCombinationDeterminant
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  simp

/-- A single pair of integer row coefficients makes both determinant
polynomials nonzero. The first is nonzero at `(p,q)=(1,0)`, the second at
`(0,1)`. This includes the empty square matrix. -/
theorem exists_integer_rowCombinations {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) K)
    (hA : A.det ≠ 0) (hD : D.det ≠ 0) :
    ∃ p q : Fin n → ℤ,
      Matrix.det (Matrix.of fun i j => (p i : K) * A i j + (q i : K) * B i j) ≠ 0 ∧
      Matrix.det (Matrix.of fun i j => (p i : K) * C i j + (q i : K) * D i j) ≠ 0 := by
  classical
  have h₁ : rowCombinationDeterminant A B ≠ 0 := by
    intro he
    have hv := eval_rowCombinationDeterminant A B (fun _ => 1) (fun _ => 0)
    have hm : (Matrix.of fun i j => (1 : K) * A i j + 0 * B i j) = A := by
      ext i j
      simp
    rw [he, map_zero, hm] at hv
    exact hA hv.symm
  have h₂ : rowCombinationDeterminant C D ≠ 0 := by
    intro he
    have hv := eval_rowCombinationDeterminant C D (fun _ => 0) (fun _ => 1)
    have hm : (Matrix.of fun i j => (0 : K) * C i j + 1 * D i j) = D := by
      ext i j
      simp
    rw [he, map_zero, hm] at hv
    exact hD hv.symm
  obtain ⟨z, hz⟩ := exists_integer_eval_ne_zero (mul_ne_zero h₁ h₂)
  have hz' : (rowCombinationDeterminant A B).eval (fun i => (z i : K)) ≠ 0 ∧
      (rowCombinationDeterminant C D).eval (fun i => (z i : K)) ≠ 0 := by
    simpa only [map_mul, ne_eq, mul_eq_zero, not_or] using hz
  have he : (fun i : Fin n ⊕ Fin n => (z i : K)) =
      Sum.elim (fun i => (z (.inl i) : K)) (fun i => (z (.inr i) : K)) := by
    funext i
    cases i <;> rfl
  rw [he, eval_rowCombinationDeterminant, eval_rowCombinationDeterminant] at hz'
  exact ⟨fun i => z (.inl i), fun i => z (.inr i), hz'⟩

end SpecialTransformations.Section7
