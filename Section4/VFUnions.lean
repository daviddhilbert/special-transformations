module

public import Section4.VFDimensionRank
public import Section4.VFCategories
public import Section4.FiniteGluing

@[expose] public section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n r : ℕ}

theorem vfDim_union (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded)
    (A B : DefSet (rawMixedSpace (M := M) n r) S) :
    vfDim Γ (A.union B) = max (vfDim Γ A) (vfDim Γ B) := by
  apply le_antisymm
  · apply vfDim_le_of_point_trdeg hs hsmall Γ (A.union B) _
    intro a
    rcases a.property with ha | hb
    · exact (vfTupleTrdeg_le_vfDim hcan Γ hΓ A ⟨a.val, ha⟩).trans
        (by exact_mod_cast (le_max_left (vfDim Γ A) (vfDim Γ B)))
    · exact (vfTupleTrdeg_le_vfDim hcan Γ hΓ B ⟨a.val, hb⟩).trans
        (by exact_mod_cast (le_max_right (vfDim Γ A) (vfDim Γ B)))
  · apply max_le
    · exact Dimension.dim_mono rawVFSpace (AuxiliaryCoordinates.space Γ)
        (fun _ ha => Or.inl ha) ⟨n, mixed_has_dimension_bound Γ (A.union B)⟩
    · exact Dimension.dim_mono rawVFSpace (AuxiliaryCoordinates.space Γ)
        (fun _ hb => Or.inr hb) ⟨n, mixed_has_dimension_bound Γ (A.union B)⟩

theorem finiteRVFibres_union (A B : DefSet (rawMixedSpace (M := M) n r) S)
    (hA : finiteRVFibres (⟨(n, r), A⟩ : VFAllObject (M := M) S))
    (hB : finiteRVFibres (⟨(n, r), B⟩ : VFAllObject (M := M) S)) :
    finiteRVFibres (⟨(n, r), A.union B⟩ : VFAllObject (M := M) S) := by
  intro a
  exact (hA a).union (hB a)

end SpecialTransformations.Section4

end
