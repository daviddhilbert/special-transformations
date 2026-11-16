module

public import Section9.RVGraphJacobianComparison

@[expose] public section

/-! Dividing a VF representative by a representative of its value
gives an integral unit. Its residue is determined by the RV label. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language IsLocalRing
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "VF" => VFType (M := M)
local notation "v" => Values.presentationValuation (M := M)
local notation "O" => Valuation.valuationSubring (Values.presentationValuation (M := M))

theorem exists_normalized_VF_representatives (a z : Fin n → VF) (ha : ∀ i, a i ≠ 0)
    (hval : ∀ i, Values.vrv (tupleRV z i) = Values.vrv (tupleRV a i)) :
    ∃ x : Fin n → O, (∀ i, a i * (x i : VF) = z i) ∧ (∀ i, v (x i : VF) = 1) ∧
      (residue O ∘ x) = residueNormalize (tupleRV a) (tupleRV z) ∧ ∀ i, residue O (x i) ≠ 0 := by
  have hv (i : Fin n) : v (z i) = v (a i) := by
    have he : Values.vfValueHom (z i) = Values.vfValueHom (a i) := hval i
    exact le_antisymm
      ((Values.presentation_compatible (z i) (a i)).mp ((Values.vf_pred_iff_gamma_le _ _).mpr he.ge))
      ((Values.presentation_compatible (a i) (z i)).mp ((Values.vf_pred_iff_gamma_le _ _).mpr he.le))
  have hq (i : Fin n) : v (z i / a i) = 1 := by
    rw [map_div₀, hv, div_self ((v).ne_zero_iff.mpr (ha i))]
  let x (i : Fin n) : O := ⟨z i / a i, (hq i).le⟩
  have hunit (i : Fin n) : residue O (x i) ≠ 0 := by
    intro h
    have h' := (Valuation.mem_maximalIdeal_iff VF v).mp ((residue_eq_zero_iff _).mp h)
    exact (ne_of_lt h') (hq i)
  refine ⟨x, fun i => ?_, hq, ?_, hunit⟩
  · change a i * (z i / a i) = z i
    rw [mul_comm, div_mul_cancel₀ _ (ha i)]
  · funext i
    have he : CanonicalRV.encodedRv (x i : VF) = residueRV (residue O (x i)) :=
      encodedRv_of_residue_ne_zero (x i) (hunit i)
    have hm : CanonicalRV.encodedRv (x i : VF) = tupleRV z i / tupleRV a i :=
      map_div₀ RVOperations.rvHom (z i) (a i)
    change residue O (x i) = residuePart (tupleRV z i / tupleRV a i)
    rw [← hm, he, residuePart_residueRV]

end SpecialTransformations.Section9
