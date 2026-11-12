module

public import Section7.GuardedResidueSums
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-! When the reduced derivative is nonsingular, the RV class of the
VF determinant is the residue determinant. -/

open FirstOrder FirstOrder.Language IsLocalRing
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace SpecialTransformations.Section9

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ] {n : ℕ}
local notation "VF" => VFType (M := M)

theorem encodedRv_det_of_integral_matrix
    (v : Valuation VF Γ) (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    (A : Matrix (Fin n) (Fin n) v.valuationSubring)
    (hA : (A.map (residue v.valuationSubring)).det ≠ 0) :
    CanonicalRV.encodedRv (A.map v.valuationSubring.subtype).det =
      ResidueRVAlgebra.residueRVHom v hv (A.map (residue v.valuationSubring)).det := by
  have hr : residue v.valuationSubring A.det ≠ 0 := by
    rw [RingHom.map_det]
    exact hA
  have hmax : A.det ∉ maximalIdeal v.valuationSubring := by
    rwa [← residue_eq_zero_iff]
  have hvA : v ((A.det : v.valuationSubring) : VF) = 1 :=
    ((Valuation.mem_valuationSubring_iff v _).mp A.det.property).antisymm
      (le_of_not_gt (fun h => hmax ((Valuation.mem_maximalIdeal_iff VF v).mpr h)))
  change CanonicalRV.encodedRv (v.valuationSubring.subtype.mapMatrix A).det =
    ResidueRVAlgebra.residueRVHom v hv ((residue v.valuationSubring).mapMatrix A).det
  rw [← RingHom.map_det, ← RingHom.map_det]
  change CanonicalRV.encodedRv (A.det : VF) = CanonicalResidue.toRV v hv (residue v.valuationSubring A.det)
  rw [CanonicalResidue.toRV_residue]
  simp only [CanonicalResidue.reduction, hvA, if_true]

end SpecialTransformations.Section9
