import Section7.PolynomialSystemEtale
import Section9.EtaleDomainReducedness
import Mathlib.RingTheory.Smooth.Flat

/-! An open chart cut out by a square system with invertible Jacobian
has a reduced coordinate ring over a domain. The equation for the
inverse of the open factor is included in the presentation. -/

set_option backward.isDefEq.respectTransparency false

open Algebra MvPolynomial
open SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {R : Type} [CommRing R] {n : ℕ}

noncomputable def openSquareEquations
    (F : Fin n → MvPolynomial (Fin n) R) (Q : MvPolynomial (Fin n) R) :
    Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) R :=
  Sum.elim (fun i => rename Sum.inl (F i)) (fun _ => X (.inr ()) * rename Sum.inl Q - 1)

private theorem pderiv_rename_inl_inr (Q : MvPolynomial (Fin n) R) :
    pderiv (Sum.inr ()) (rename (Sum.inl : Fin n → Fin n ⊕ Unit) Q) = 0 := by
  induction Q using MvPolynomial.induction_on with
  | C c => rw [rename_C, pderiv_C]
  | add u v hu hv => rw [map_add, map_add, hu, hv, add_zero]
  | mul_X u i hu =>
    rw [map_mul, rename_X, pderiv_mul, hu, pderiv_X_of_ne Sum.inl_ne_inr, zero_mul, mul_zero, add_zero]

private theorem pderiv_openSquareEquations_inverse
    (F : Fin n → MvPolynomial (Fin n) R) (Q : MvPolynomial (Fin n) R) :
    pderiv (Sum.inr ()) (openSquareEquations F Q (.inr ())) =
      rename (Sum.inl : Fin n → Fin n ⊕ Unit) Q := by
  change pderiv (Sum.inr ()) (X (Sum.inr ()) * rename (Sum.inl : Fin n → Fin n ⊕ Unit) Q - 1) = _
  rw [map_sub, pderiv_one, sub_zero, pderiv_mul, pderiv_X_self, pderiv_rename_inl_inr,
    mul_zero, one_mul, add_zero]

set_option maxHeartbeats 600000 in
theorem openSquareSystem_etale
    (F : Fin n → MvPolynomial (Fin n) R) (Q T : MvPolynomial (Fin n) R)
    (hQ : Q = jacobianPolynomial F * T) :
    Algebra.Etale R (MvPolynomial (Fin n ⊕ Unit) R ⧸ Ideal.span (Set.range (openSquareEquations F Q))) := by
  classical
  let I := Ideal.span (Set.range (openSquareEquations F Q))
  let B := MvPolynomial (Fin n ⊕ Unit) R ⧸ I
  let f : MvPolynomial (Fin n ⊕ Unit) R →+* B := Ideal.Quotient.mk I
  let g : MvPolynomial (Fin n) R →+* B := f.comp (rename Sum.inl).toRingHom
  let P : PreSubmersivePresentation R B (Fin n ⊕ Unit) (Fin n ⊕ Unit) :=
    PreSubmersivePresentation.naive (v := openSquareEquations F Q) id Function.injective_id
  have hu : f (X (.inr ())) * g Q = 1 := by
    apply sub_eq_zero.mp
    change f (X (.inr ()) * rename Sum.inl Q - 1) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨.inr (), rfl⟩)
  have hunit : IsUnit (g Q) := isUnit_of_mul_isUnit_right (hu ▸ isUnit_one)
  have hdet : IsUnit (g (jacobianPolynomial F)) := by
    have h := hunit
    rw [hQ, map_mul] at h
    exact isUnit_of_mul_isUnit_left h
  let A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n ⊕ Unit) R) :=
    Matrix.of fun i j => rename Sum.inl (pderiv j (F i))
  let C : Matrix Unit (Fin n) (MvPolynomial (Fin n ⊕ Unit) R) :=
    Matrix.of fun _ j => pderiv (.inl j) (openSquareEquations F Q (.inr ()))
  let D : Matrix Unit Unit (MvPolynomial (Fin n ⊕ Unit) R) := fun _ _ => rename Sum.inl Q
  have hM₀ : P.jacobiMatrix = (Matrix.of fun i j => pderiv j (openSquareEquations F Q i)).transpose := by
    ext i j : 1
    rw [PreSubmersivePresentation.jacobiMatrix_apply]
    rfl
  have hM : (Matrix.of fun i j => pderiv j (openSquareEquations F Q i)) = Matrix.fromBlocks A 0 C D := by
    ext i j : 1
    rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
    · change pderiv (.inl j) (rename Sum.inl (F i)) = rename Sum.inl (pderiv j (F i))
      exact pderiv_rename Sum.inl_injective j (F i)
    · change pderiv (.inr ()) (rename Sum.inl (F i)) = 0
      exact pderiv_rename_inl_inr _
    · rfl
    · exact pderiv_openSquareEquations_inverse F Q
  have hA : A.det = rename Sum.inl (jacobianPolynomial F) := by
    change ((rename Sum.inl).toRingHom.mapMatrix (Matrix.of fun i j => pderiv j (F i))).det = _
    rw [← RingHom.map_det]
    rfl
  have hD : D.det = rename Sum.inl Q := Matrix.det_unique D
  have hJac : P.jacobian = f P.jacobiMatrix.det := by
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    rfl
  have hP : IsUnit P.jacobian := by
    rw [hJac, hM₀, Matrix.det_transpose, hM, Matrix.det_fromBlocks_zero₁₂, hA, hD, map_mul]
    exact hdet.mul hunit
  let P' : SubmersivePresentation R B (Fin n ⊕ Unit) (Fin n ⊕ Unit) :=
    { P with jacobian_isUnit := hP }
  haveI : IsStandardSmoothOfRelativeDimension 0 R B := P'.isStandardSmoothOfRelativeDimension
    (by simp [Presentation.dimension])
  infer_instance

theorem openSquareSystem_reduced [IsDomain R]
    (F : Fin n → MvPolynomial (Fin n) R) (Q T : MvPolynomial (Fin n) R)
    (hQ : Q = jacobianPolynomial F * T) :
    IsReduced (MvPolynomial (Fin n ⊕ Unit) R ⧸ Ideal.span (Set.range (openSquareEquations F Q))) := by
  letI := openSquareSystem_etale F Q T hQ
  exact isReduced_of_flat_formallyUnramified_over_domain R _

end SpecialTransformations.Section9
