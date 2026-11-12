module

public import Section4.VFCoproductBounds

@[expose] public section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

theorem vfDim_emptyObject (Γ : DefinableGeometry.Space LRV M) :
    vfDim Γ (vfAllEmptyObject (M := M) S).set = 0 :=
  Dimension.dim_empty rawVFSpace (AuxiliaryCoordinates.space Γ) (.rv 0)

theorem finiteRVFibres_emptyObject : finiteRVFibres (vfAllEmptyObject (M := M) S) := by
  intro a
  exact Set.finite_empty

def vfAllListUnion : List (VFAllObject (M := M) S) → VFAllObject (M := M) S
  | [] => vfAllEmptyObject S
  | U :: rest => vfAllCoprodObject U (vfAllListUnion rest)

theorem vfDim_listUnion_le (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded)
    (L : List (VFAllObject (M := M) S)) (b : ℕ)
    (hL : ∀ U ∈ L, vfDim Γ U.set ≤ b) : vfDim Γ (vfAllListUnion L).set ≤ b := by
  induction L with
  | nil => simpa only [vfAllListUnion, vfDim_emptyObject] using Nat.zero_le b
  | cons U L ih =>
    change vfDim Γ (vfAllCoprodObject U (vfAllListUnion L)).set ≤ b
    rw [vfDim_coprod hcan hs hsmall Γ hΓ]
    exact max_le (hL U (List.mem_cons_self))
      (ih (fun V hV => hL V (List.mem_cons_of_mem U hV)))

theorem finiteRVFibres_listUnion (L : List (VFAllObject (M := M) S))
    (hL : ∀ U ∈ L, finiteRVFibres U) : finiteRVFibres (vfAllListUnion L) := by
  induction L with
  | nil => exact finiteRVFibres_emptyObject
  | cons U L ih =>
    exact finiteRVFibres_coprod (hL U (List.mem_cons_self))
      (ih (fun V hV => hL V (List.mem_cons_of_mem U hV)))

end SpecialTransformations.Section4

end
