module

public import Section7.IntegralNormalization
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# Reduction of the Jacobian of an implicit polynomial graph

This is the algebraic reduction calculation needed in the repaired Lemma
9.15.  A system over a valuation ring with invertible output Jacobian has
an integral implicit derivative matrix, whose reduction is the implicit
derivative matrix of the reduced system.  Both input and output blocks
being invertible after reduction makes its determinant a unit.

This file does not assert that an arbitrary definable lifted graph has
such a polynomial presentation.  Establishing that presentation at a
residue-generic point, and identifying this matrix with the valued-field
derivative, are separate obligations.
-/

open MvPolynomial IsLocalRing

namespace SpecialTransformations.Section9

noncomputable section

section Matrices

variable {R S : Type*} [CommRing R] [CommRing S]
variable {n m : ℕ}

/-- Matrix inversion commutes with a ring map on invertible matrices.
The unit hypothesis is necessary over rings: total matrix inversion does
not commute with an arbitrary quotient on singular matrices. -/
theorem matrix_map_inv_of_isUnit (φ : R →+* S) (B : Matrix (Fin m) (Fin m) R)
    (hB : IsUnit B.det) : (B⁻¹).map φ = (B.map φ)⁻¹ := by
  apply Eq.symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, B.nonsing_inv_mul hB]
  exact Matrix.map_one φ (map_zero φ) (map_one φ)

/-- The derivative determined by the equation `B * J + A = 0`. -/
def implicitMatrix (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin m) (Fin m) R) :
    Matrix (Fin m) (Fin n) R := -(B⁻¹ * A)

theorem implicitMatrix_equation (A : Matrix (Fin m) (Fin n) R)
    (B : Matrix (Fin m) (Fin m) R) (hB : IsUnit B.det) :
    B * implicitMatrix A B + A = 0 := by
  simp [implicitMatrix, Matrix.mul_neg, B.mul_nonsing_inv_cancel_left A hB]

theorem implicitMatrix_unique (A : Matrix (Fin m) (Fin n) R)
    (B : Matrix (Fin m) (Fin m) R) (hB : IsUnit B.det)
    (J : Matrix (Fin m) (Fin n) R) (hJ : B * J + A = 0) :
    J = implicitMatrix A B := by
  have h : B * J = -A := eq_neg_of_add_eq_zero_left hJ
  have hh := congrArg (fun C => B⁻¹ * C) h
  simpa [implicitMatrix, B.nonsing_inv_mul_cancel_left J hB] using hh

theorem map_implicitMatrix (φ : R →+* S) (A : Matrix (Fin m) (Fin n) R)
    (B : Matrix (Fin m) (Fin m) R) (hB : IsUnit B.det) :
    (implicitMatrix A B).map φ = implicitMatrix (A.map φ) (B.map φ) := by
  simp only [implicitMatrix, Matrix.map_neg φ (map_neg φ), Matrix.map_mul,
    matrix_map_inv_of_isUnit φ B hB]

theorem implicitMatrix_det_isUnit (A B : Matrix (Fin n) (Fin n) R)
    (hA : IsUnit A.det) (hB : IsUnit B.det) :
    IsUnit (implicitMatrix A B).det := by
  rw [implicitMatrix, Matrix.det_neg, Matrix.det_mul]
  simpa only [Fintype.card_fin] using
    (isUnit_neg_one.pow n).mul ((B.isUnit_nonsing_inv_det hB).mul hA)

end Matrices

section PolynomialSystems

variable {R S : Type*} [CommRing R] [CommRing S]
variable {n m : ℕ}

/-- The input block of the Jacobian of an implicit polynomial system. -/
def inputJacobian (P : Fin m → MvPolynomial (Fin n ⊕ Fin m) R)
    (x : Fin n → R) (y : Fin m → R) : Matrix (Fin m) (Fin n) R :=
  fun i j => (pderiv (Sum.inl j) (P i)).eval (Sum.elim x y)

/-- The output block, which is required to be invertible for an implicit
graph over the input coordinates. -/
def outputJacobian (P : Fin m → MvPolynomial (Fin n ⊕ Fin m) R)
    (x : Fin n → R) (y : Fin m → R) : Matrix (Fin m) (Fin m) R :=
  fun i j => (pderiv (Sum.inr j) (P i)).eval (Sum.elim x y)

theorem map_inputJacobian (φ : R →+* S)
    (P : Fin m → MvPolynomial (Fin n ⊕ Fin m) R)
    (x : Fin n → R) (y : Fin m → R) :
    (inputJacobian P x y).map φ =
      inputJacobian (fun i => (P i).map φ) (fun i => φ (x i)) (fun i => φ (y i)) := by
  ext i j
  simp only [inputJacobian, Matrix.map_apply, pderiv_map, MvPolynomial.map_eval]
  have he : (φ : R → S) ∘ Sum.elim x y = Sum.elim (fun i => φ (x i)) (fun i => φ (y i)) := by
    funext k
    cases k <;> rfl
  rw [he]

theorem map_outputJacobian (φ : R →+* S)
    (P : Fin m → MvPolynomial (Fin n ⊕ Fin m) R)
    (x : Fin n → R) (y : Fin m → R) :
    (outputJacobian P x y).map φ =
      outputJacobian (fun i => (P i).map φ) (fun i => φ (x i)) (fun i => φ (y i)) := by
  ext i j
  simp only [outputJacobian, Matrix.map_apply, pderiv_map, MvPolynomial.map_eval]
  have he : (φ : R → S) ∘ Sum.elim x y = Sum.elim (fun i => φ (x i)) (fun i => φ (y i)) := by
    funext k
    cases k <;> rfl
  rw [he]

def implicitJacobian (P : Fin m → MvPolynomial (Fin n ⊕ Fin m) R)
    (x : Fin n → R) (y : Fin m → R) : Matrix (Fin m) (Fin n) R :=
  implicitMatrix (inputJacobian P x y) (outputJacobian P x y)

/-- Reduction commutes with the implicit Jacobian when the output block
has unit determinant. This is a ring-theoretic statement, so it applies
to valuation rings of arbitrary rank. -/
theorem map_implicitJacobian (φ : R →+* S)
    (P : Fin m → MvPolynomial (Fin n ⊕ Fin m) R)
    (x : Fin n → R) (y : Fin m → R)
    (h : IsUnit (outputJacobian P x y).det) :
    (implicitJacobian P x y).map φ =
      implicitJacobian (fun i => (P i).map φ) (fun i => φ (x i)) (fun i => φ (y i)) := by
  rw [implicitJacobian, map_implicitMatrix φ _ _ h,
    map_inputJacobian, map_outputJacobian]
  rfl

end PolynomialSystems

section ValuationRing

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation K Γ) {n m : ℕ}

theorem outputJacobian_isUnit_of_residue
    (P : Fin m → MvPolynomial (Fin n ⊕ Fin m) v.valuationSubring)
    (x : Fin n → v.valuationSubring) (y : Fin m → v.valuationSubring)
    (h : (outputJacobian (fun i => (P i).map (residue v.valuationSubring))
      (fun i => residue v.valuationSubring (x i))
      (fun i => residue v.valuationSubring (y i))).det ≠ 0) :
    IsUnit (outputJacobian P x y).det := by
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [RingHom.map_det]
  change ((outputJacobian P x y).map (residue v.valuationSubring)).det ≠ 0
  rw [map_outputJacobian]
  exact h

/-- A polynomial system with invertible output reduction has an integral
matrix whose images in the valued field and residue field are exactly
the two corresponding implicit Jacobians. -/
theorem implicitJacobian_integral_reduction
    (P : Fin m → MvPolynomial (Fin n ⊕ Fin m) v.valuationSubring)
    (x : Fin n → v.valuationSubring) (y : Fin m → v.valuationSubring)
    (h : (outputJacobian (fun i => (P i).map (residue v.valuationSubring))
      (fun i => residue v.valuationSubring (x i))
      (fun i => residue v.valuationSubring (y i))).det ≠ 0) :
    ∃ J : Matrix (Fin m) (Fin n) v.valuationSubring,
      J.map v.valuationSubring.subtype =
        implicitJacobian (fun i => (P i).map v.valuationSubring.subtype)
          (fun i => (x i : K)) (fun i => (y i : K)) ∧
      J.map (residue v.valuationSubring) =
        implicitJacobian (fun i => (P i).map (residue v.valuationSubring))
          (fun i => residue v.valuationSubring (x i))
          (fun i => residue v.valuationSubring (y i)) := by
  have hunit := outputJacobian_isUnit_of_residue v P x y h
  exact ⟨implicitJacobian P x y,
    map_implicitJacobian _ P x y hunit, map_implicitJacobian _ P x y hunit⟩

/-- When both projections of the reduced square correspondence are
étale, its integral implicit Jacobian has determinant of value one.
Here one is the paper's additive valuation zero. -/
theorem implicitJacobian_value_one
    (P : Fin n → MvPolynomial (Fin n ⊕ Fin n) v.valuationSubring)
    (x y : Fin n → v.valuationSubring)
    (hA : (inputJacobian (fun i => (P i).map (residue v.valuationSubring))
      (fun i => residue v.valuationSubring (x i))
      (fun i => residue v.valuationSubring (y i))).det ≠ 0)
    (hB : (outputJacobian (fun i => (P i).map (residue v.valuationSubring))
      (fun i => residue v.valuationSubring (x i))
      (fun i => residue v.valuationSubring (y i))).det ≠ 0) :
    v (implicitJacobian (fun i => (P i).map v.valuationSubring.subtype)
      (fun i => (x i : K)) (fun i => (y i : K))).det = 1 := by
  have ha : IsUnit (inputJacobian P x y).det := by
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [RingHom.map_det]
    change ((inputJacobian P x y).map (residue v.valuationSubring)).det ≠ 0
    rw [map_inputJacobian]
    exact hA
  have hb := outputJacobian_isUnit_of_residue v P x y hB
  have he := map_implicitJacobian v.valuationSubring.subtype P x y hb
  refine (congrArg (fun J : Matrix (Fin n) (Fin n) K => v J.det) he).symm.trans ?_
  change v ((v.valuationSubring.subtype.mapMatrix (implicitJacobian P x y)).det) = 1
  rw [← RingHom.map_det]
  exact (Valuation.Integers.isUnit_iff_valuation_eq_one
    (Valuation.valuationSubring.integers v)).mp (implicitMatrix_det_isUnit _ _ ha hb)

end ValuationRing

end

end SpecialTransformations.Section9
