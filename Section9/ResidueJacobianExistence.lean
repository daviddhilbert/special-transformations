import Section9.GraphCoordinateDerivations
import Section9.ResidueJacobianGeneric
import Section9.ResidueSimpleEquations

/-! Existence of the residue Jacobian at a point whose two projections
are independent over the coefficient field. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "k" => ModelResidue M

private theorem residue_vertical_eq_zero [CharZero k]
    {κ : Cardinal} (hs : Saturated M κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    (C : Set (Fin (n + n) → k)) (hC : Relative.Def (residueParameterField B) C)
    (hfin : ∀ x : Fin n → k, {y | productTuple x y ∈ C}.Finite)
    (x y : Fin n → k) (hxy : productTuple x y ∈ C)
    (hx : AlgebraicIndependent (residueParameterField B) x)
    (z : Fin n → k) (hz : IsPolynomialTangent C (productTuple x y) (productTuple 0 z)) : z = 0 := by
  let E := residueParameterField B
  obtain ⟨P, hP, hoff, hdiag⟩ := exists_residue_simple_equations hs B hB C hC hfin
  let Q (i : Fin n) := (P i).map E.subtype
  have hL : productTuple x y ∘ productLeft n n = x := funext (productTuple_left x y)
  apply polynomialTangent_vertical_eq_zero_of_simple_equations C (productTuple x y) Q _ _ _ z hz
  · intro i p hp
    change ((P i).map E.subtype).eval p = 0
    rw [eval_map]
    exact hP p hp i
  · intro i j hij
    change (pderiv (productRight n n j) ((P i).map E.subtype)).eval (productTuple x y) = 0
    rw [pderiv_map, hoff i j hij, map_zero]
    exact map_zero (eval (productTuple x y))
  · intro i
    change (pderiv (productRight n n i) ((P i).map E.subtype)).eval (productTuple x y) ≠ 0
    rw [pderiv_map, eval_map]
    exact hdiag (productTuple x y) hxy (hL.symm ▸ hx) i

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem residue_tangent_kernels_eq_zero_of_independent_projections [CharZero k]
    {κ : Cardinal} (hs : Saturated M κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    (C : Set (Fin (n + n) → k)) (hC : Relative.Def (residueParameterField B) C)
    (hfinRight : ∀ x : Fin n → k, {y | productTuple x y ∈ C}.Finite)
    (hfinLeft : ∀ y : Fin n → k, {x | productTuple x y ∈ C}.Finite)
    (x y : Fin n → k) (hxy : productTuple x y ∈ C)
    (hx : AlgebraicIndependent (residueParameterField B) x)
    (hy : AlgebraicIndependent (residueParameterField B) y) :
    (∀ z, IsPolynomialTangent C (productTuple x y) (productTuple 0 z) → z = 0) ∧
    (∀ z, IsPolynomialTangent C (productTuple x y) (productTuple z 0) → z = 0) := by
  let E := residueParameterField B
  have hvert := residue_vertical_eq_zero hs B hB C hC hfinRight x y hxy hx
  let q : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  let e := (q.symm.trans (_root_.Equiv.sumComm (Fin n) (Fin n))).trans q
  have hLeft (i : Fin n) : e (productLeft n n i) = productRight n n i :=
    congrArg (fun j => q (_root_.Equiv.sumComm (Fin n) (Fin n) j)) (q.symm_apply_apply (Sum.inl i))
  have hRight (i : Fin n) : e (productRight n n i) = productLeft n n i :=
    congrArg (fun j => q (_root_.Equiv.sumComm (Fin n) (Fin n) j)) (q.symm_apply_apply (Sum.inr i))
  have he (a b : Fin n → k) : productTuple a b ∘ e = productTuple b a := by
    apply productTuple_ext
    · intro i
      change productTuple a b (e (productLeft n n i)) = productTuple b a (productLeft n n i)
      rw [hLeft, productTuple_right, productTuple_left]
    · intro i
      change productTuple a b (e (productRight n n i)) = productTuple b a (productRight n n i)
      rw [hRight, productTuple_left, productTuple_right]
  have he' : e.symm = e := by
    apply _root_.Equiv.ext
    intro j
    apply e.injective
    rw [e.apply_symm_apply]
    obtain ⟨i, rfl⟩ := q.surjective j
    cases i with
    | inl i => exact ((congrArg e (hLeft i)).trans (hRight i)).symm
    | inr i => exact ((congrArg e (hRight i)).trans (hLeft i)).symm
  let C' := {z | z ∘ e.symm ∈ C}
  have hC' : Relative.Def E C' := hC.preimage_comp e.symm
  have hfin' (a : Fin n → k) : {b | productTuple a b ∈ C'}.Finite := by
    convert hfinLeft a using 1
    ext b
    change productTuple a b ∘ e.symm ∈ C ↔ productTuple b a ∈ C
    rw [he', he]
  have hyx : productTuple y x ∈ C' := by
    change productTuple y x ∘ e.symm ∈ C
    rwa [he', he]
  have hhor (z : Fin n → k) (hz : IsPolynomialTangent C (productTuple x y) (productTuple z 0)) : z = 0 := by
    apply residue_vertical_eq_zero hs B hB C' hC' hfin' y x hyx hy z
    simpa only [he] using hz.comp_equiv e
  exact ⟨hvert, hhor⟩

theorem exists_residueJacobianMap_over_coefficients [CharZero k]
    {κ : Cardinal} (hs : Saturated M κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    (E : Subfield k) [IsAlgClosed E] (hBE : residueParameterField B ≤ E)
    (C : Set (Fin (n + n) → k)) (hC : Relative.Def (residueParameterField B) C)
    (hfinRight : ∀ x : Fin n → k, {y | productTuple x y ∈ C}.Finite)
    (hfinLeft : ∀ y : Fin n → k, {x | productTuple x y ∈ C}.Finite)
    (x y : Fin n → k) (hxy : productTuple x y ∈ C)
    (hx : AlgebraicIndependent E x) (hy : AlgebraicIndependent E y) :
    ∃ D : (Fin n → k) →ₗ[k] (Fin n → k),
      IsResidueJacobianMap (M := M) C (productTuple x y) D ∧ (LinearMap.toMatrix' D).det ≠ 0 := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed k := ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  letI : Algebra (residueParameterField B) E := (Subfield.inclusion hBE).toAlgebra
  letI : IsScalarTower (residueParameterField B) E k := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hInj := (algebraMap (residueParameterField B) E).injective
  have hCE : Relative.Def E C := hC.mono hBE
  obtain ⟨hvert, hhor⟩ := residue_tangent_kernels_eq_zero_of_independent_projections
    hs B hB C hC hfinRight hfinLeft x y hxy (hx.restrictScalars hInj) (hy.restrictScalars hInj)
  have hyAlg (i : Fin n) : IsAlgebraic (IntermediateField.adjoin E (Set.range x)) (y i) := by
    have h := finite_residue_row_coordinate_isAlgebraic E C hCE x y hxy (hfinRight x) i
    rwa [tupleField_eq_adjoin] at h
  obtain ⟨A, fA, aA, f, X, Y, d, hX, hY, hd⟩ := exists_graph_coordinate_derivations E x y hx hyAlg
  letI := fA
  letI := aA
  let p := productTuple X Y
  have hp : f ∘ p = productTuple x y := by
    apply productTuple_ext
    · intro i
      simpa only [Function.comp_apply, p, productTuple_left] using hX i
    · intro i
      simpa only [Function.comp_apply, p, productTuple_right] using hY i
  have hdp (j i : Fin n) : d j (p (productLeft n n i)) = if i = j then 1 else 0 := by
    simpa only [p, productTuple_left] using hd j i
  obtain ⟨hJ, hdet⟩ := isResidueJacobianMap_of_coordinate_derivations E f C hCE p
    (hp.symm ▸ hxy) d hdp (hp.symm ▸ hvert) (hp.symm ▸ hhor)
  refine ⟨_, hp ▸ hJ, ?_⟩
  simpa only [LinearMap.toMatrix'_toLin'] using hdet

theorem exists_residueJacobianMap_of_independent_projections [CharZero k]
    {κ : Cardinal} (hs : Saturated M κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    [IsAlgClosed (residueParameterField B)]
    (C : Set (Fin (n + n) → k)) (hC : Relative.Def (residueParameterField B) C)
    (hfinRight : ∀ x : Fin n → k, {y | productTuple x y ∈ C}.Finite)
    (hfinLeft : ∀ y : Fin n → k, {x | productTuple x y ∈ C}.Finite)
    (x y : Fin n → k) (hxy : productTuple x y ∈ C)
    (hx : AlgebraicIndependent (residueParameterField B) x)
    (hy : AlgebraicIndependent (residueParameterField B) y) :
    ∃ D : (Fin n → k) →ₗ[k] (Fin n → k),
      IsResidueJacobianMap (M := M) C (productTuple x y) D ∧ (LinearMap.toMatrix' D).det ≠ 0 :=
  exists_residueJacobianMap_over_coefficients hs B hB (residueParameterField B) le_rfl
    C hC hfinRight hfinLeft x y hxy hx hy

end SpecialTransformations.Section9
