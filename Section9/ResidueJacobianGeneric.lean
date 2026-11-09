import Section9.ResidueTangentDescent
import Section9.ResidueTangentMatrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The tangent determinant is the determinant of the coordinate
derivations on the residue field of a graph point. -/

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "k" => ModelResidue M

theorem isResidueJacobianMap_of_coordinate_derivations [IsAlgClosed k]
    (E : Subfield k) [IsAlgClosed E]
    {F : Type*} [Field F] [Algebra E F] (f : F →ₐ[E] k)
    (C : Set (Fin (n + n) → k)) (hC : Relative.Def E C)
    (p : Fin (n + n) → F) (hp : f ∘ p ∈ C)
    (D : Fin n → Derivation E F F)
    (hD : ∀ j i, D j (p (productLeft n n i)) = if i = j then 1 else 0)
    (hvertical : ∀ y, IsPolynomialTangent C (f ∘ p) (productTuple 0 y) → y = 0)
    (hhorizontal : ∀ x, IsPolynomialTangent C (f ∘ p) (productTuple x 0) → x = 0) :
    let A : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => f (D j (p (productRight n n i)))
    IsResidueJacobianMap (M := M) C (f ∘ p) (Matrix.toLin' A) ∧ A.det ≠ 0 := by
  let A : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => f (D j (p (productRight n n i)))
  have hcol (j : Fin n) : IsPolynomialTangent C (f ∘ p)
      (productTuple (Pi.single j 1) (fun i => A i j)) := by
    have h := isPolynomialTangent_of_residue_derivation E f C hC p hp (D j)
    have he : f ∘ D j ∘ p = productTuple (Pi.single j 1) (fun i => A i j) := by
      apply productTuple_ext
      · intro i
        simp only [Function.comp_apply, productTuple_left, hD, Pi.single_apply,
          apply_ite f, map_one, map_zero]
      · intro i
        change A i j = productTuple (Pi.single j 1) (fun i => A i j) (productRight n n i)
        exact (productTuple_right (Pi.single j (1 : k)) (fun i : Fin n => A i j) i).symm
    exact he ▸ h
  have hgraph : IsResidueJacobianMap (M := M) C (f ∘ p) (Matrix.toLin' A) := by
    intro x y
    rw [Matrix.toLin'_apply]
    exact polynomialTangent_iff_mulVec C (f ∘ p) A hcol hvertical x y
  have hInj : Function.Injective (Matrix.toLin' A) := by
    apply (injective_iff_map_eq_zero (Matrix.toLin' A)).mpr
    intro x hx
    exact hhorizontal x ((hgraph x 0).mpr hx.symm)
  have hA : Function.Injective A.mulVec := by
    intro x y he
    apply hInj
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact he
  exact ⟨hgraph, ((Matrix.isUnit_iff_isUnit_det A).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hA)).ne_zero⟩

end SpecialTransformations.Section9
