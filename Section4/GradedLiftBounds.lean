module

public import Section4.GradedLifts

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

/-- Empty components above a prescribed bound add no VF dimension, even
if the finite-support construction selected a larger bookkeeping bound. -/
theorem rvGradedLift_dim_le_of_bound
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded)
    (U : RVGradedObject (M := M) S) (b : ℕ)
    (hU : rvBoundedGradingProperty S b U) : vfDim Γ (rvGradedLift Γ U).set ≤ b := by
  apply vfDim_listUnion_le hcan hs hsmall Γ hΓ
  intro V hV
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hV
  by_cases hkb : k ≤ b
  · exact (rvLiftObject Γ (U.obj k)).property.trans hkb
  · have he : rvLift (U.obj k) = DefSet.empty (rawMixedSpace k (U.obj k).arity) S :=
      DefSet.eq_of_carrier_eq (rvLift_empty_of_domain_empty _ (hU k (Nat.lt_of_not_ge hkb)))
    change vfDim Γ (rvLift (U.obj k)) ≤ b
    rw [he]
    change Dimension.dim rawVFSpace (AuxiliaryCoordinates.space Γ)
      (DefSet.empty (rawMixedSpace k (U.obj k).arity) S) ≤ b
    rw [Dimension.dim_empty rawVFSpace (AuxiliaryCoordinates.space Γ) (.rv 0)]
    exact Nat.zero_le b

def rvBoundedGradedLiftObject (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded) {b : ℕ}
    (U : RVBoundedGradedObject (M := M) S b) : VFObject Γ (M := M) S b :=
  ⟨rvGradedLift Γ U.obj, rvGradedLift_dim_le_of_bound hcan hs hsmall Γ hΓ U.obj b U.property⟩

def rvFiniteBoundedGradedLift (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded) {b : ℕ}
    (U : RVFiniteBoundedGradedObject (M := M) S b) : VFFiniteObject Γ (M := M) S b :=
  ⟨⟨rvGradedLift Γ U.obj.obj,
      rvGradedLift_dim_le_of_bound hcan hs hsmall Γ hΓ U.obj.obj b U.property⟩,
    rvGradedLift_finiteRVFibres Γ U.obj⟩

end SpecialTransformations.Section4

end
