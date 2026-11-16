module

public import Section9.RVJacobianNormalization
public import Section9.RVDeterminantReduction
public import Section4.CanonicalLift

@[expose] public section

/-! The reduced determinant of the graph matrix, transported from
fixed scale representatives to the paper's point normalization. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language IsLocalRing
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "VF" => VFType (M := M)
local notation "RV" => CanonicalRV.RVSort M
local notation "w" => Values.presentationValuation (M := M)
local notation "R" => Valuation.valuationSubring (Values.presentationValuation (M := M))

theorem encodedRv_of_residue_ne_zero (x : R) (hx : residue R x ≠ 0) :
    CanonicalRV.encodedRv (x : VF) = residueRV (residue R x) := by
  have hval : w (x : VF) = 1 := x.property.antisymm
    (le_of_not_gt (fun h => hx ((residue_eq_zero_iff x).mpr
      ((Valuation.mem_maximalIdeal_iff VF w).mpr h))))
  change CanonicalRV.encodedRv (x : VF) =
    CanonicalResidue.toRV w Values.presentation_compatible (residue R x)
  rw [CanonicalResidue.toRV_residue]
  simp only [CanonicalResidue.reduction, hval, if_true]

theorem isRVJacobianAt_of_normalized_determinant
    (C : Set (Fin (n + n) → RV)) (a b : Fin n → VF) (x y : Fin n → R)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hx : ∀ i, residue R (x i) ≠ 0) (hy : ∀ i, residue R (y i) ≠ 0)
    (D : Matrix (Fin n) (Fin n) (ModelResidue M))
    (hD : D.det ≠ 0) (J : VF) (hrep : CanonicalRV.encodedRv J = residueRV D.det)
    (hp : productTuple (residue R ∘ x) (residue R ∘ y) ∈ normalizedCorrespondence C (tupleRV a) (tupleRV b))
    (hJ : IsResidueJacobianMap (M := M) (normalizedCorrespondence C (tupleRV a) (tupleRV b))
      (productTuple (residue R ∘ x) (residue R ∘ y)) (Matrix.toLin' D)) :
    IsRVJacobianAt C (tupleRV (fun i => a i * (x i : VF))) (tupleRV (fun i => b i * (y i : VF)))
      (CanonicalRV.encodedRv (((∏ i, b i) / ∏ i, a i) * J)) := by
  let f : VF →*₀ RV := RVOperations.rvHom
  have hscale (c : Fin n → VF) (z : Fin n → R) (hz : ∀ i, residue R (z i) ≠ 0) :
      tupleRV (fun i => c i * (z i : VF)) = residueScale (tupleRV c) (residue R ∘ z) := by
    funext i
    change f (c i * (z i : VF)) = f (c i) * residueRV (residue R (z i))
    rw [map_mul]
    exact congrArg (fun e => f (c i) * e) (encodedRv_of_residue_ne_zero (z i) (hz i))
  have hzero (c : Fin n → VF) (hc : ∀ i, c i ≠ 0) (i : Fin n) : tupleRV c i ≠ 0 := by
    intro hz
    apply hc i
    apply (CanonicalRV.encodedRv_zero_iff (c i)).mp
    exact (congrArg Subtype.val hz).trans RVOperations.zero_val
  rw [hscale a x hx, hscale b y hy]
  change IsRVJacobianAt C _ _ (f (((∏ i, b i) / ∏ i, a i) * J))
  have he : f J = residueRV D.det := hrep
  rw [map_mul, map_div₀, map_prod, map_prod, he]
  exact isRVJacobianAt_of_normalized_residue_jacobian C (tupleRV a) (tupleRV b)
    (residue R ∘ x) (residue R ∘ y) (hzero a ha) (hzero b hb) hx hy hp _ hJ hD

theorem isRVJacobianAt_of_integral_graph_matrix
    (C : Set (Fin (n + n) → RV)) (a b : Fin n → VF) (x y : Fin n → R)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hx : ∀ i, residue R (x i) ≠ 0) (hy : ∀ i, residue R (y i) ≠ 0)
    (A : Matrix (Fin n) (Fin n) R)
    (hA : (A.map (residue R)).det ≠ 0)
    (hp : productTuple (residue R ∘ x) (residue R ∘ y) ∈ normalizedCorrespondence C (tupleRV a) (tupleRV b))
    (hJ : IsResidueJacobianMap (M := M) (normalizedCorrespondence C (tupleRV a) (tupleRV b))
      (productTuple (residue R ∘ x) (residue R ∘ y)) (Matrix.toLin' (A.map (residue R)))) :
    IsRVJacobianAt C (tupleRV (fun i => a i * (x i : VF))) (tupleRV (fun i => b i * (y i : VF)))
      (CanonicalRV.encodedRv (((∏ i, b i) / ∏ i, a i) * (A.map (R).subtype).det)) :=
  isRVJacobianAt_of_normalized_determinant C a b x y ha hb hx hy _ hA _
    (encodedRv_det_of_integral_matrix w Values.presentation_compatible A hA) hp hJ

end SpecialTransformations.Section9
