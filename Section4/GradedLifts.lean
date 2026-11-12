module

public import Section4.VFListUnions
public import Section4.RVGrading
public import Section4.CanonicalLift

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

theorem rvLift_empty_of_domain_empty {k : ℕ} (U : RVObject (M := M) S k)
    (hU : U.domain.carrier = ∅) : (rvLift U).carrier = ∅ := by
  apply Set.Subset.antisymm
  · rintro p ⟨u, _, _⟩
    exact False.elim (hU.le u.property)
  · exact Set.empty_subset _

def rvGradedLiftBound (U : RVGradedObject (M := M) S) : ℕ :=
  Classical.choose (rvGradedObject_has_bound U)

theorem rvGradedLiftBound_spec (U : RVGradedObject (M := M) S) :
    ∀ k, rvGradedLiftBound U < k → (U.obj k).domain.carrier = ∅ :=
  Classical.choose_spec (rvGradedObject_has_bound U)

/-- Each degree is lifted by the actual canonical lift and the finite
list is combined by genuine definable coproducts. -/
def rvGradedLiftList (Γ : DefinableGeometry.Space LRV M)
    (U : RVGradedObject (M := M) S) : List (VFAllObject (M := M) S) :=
  (List.range (rvGradedLiftBound U + 1)).map (fun k => (rvLiftObject Γ (U.obj k)).obj)

def rvGradedLift (Γ : DefinableGeometry.Space LRV M)
    (U : RVGradedObject (M := M) S) : VFAllObject (M := M) S :=
  vfAllListUnion (rvGradedLiftList Γ U)

theorem rvGradedLift_dim_le (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded)
    (U : RVGradedObject (M := M) S) :
    vfDim Γ (rvGradedLift Γ U).set ≤ rvGradedLiftBound U := by
  apply vfDim_listUnion_le hcan hs hsmall Γ hΓ
  intro V hV
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hV
  exact (rvLiftObject Γ (U.obj k)).property.trans (Nat.le_of_lt_succ (List.mem_range.mp hk))

def rvGradedLiftObject (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded)
    (U : RVGradedObject (M := M) S) : VFObject Γ (M := M) S (rvGradedLiftBound U) :=
  ⟨rvGradedLift Γ U, rvGradedLift_dim_le hcan hs hsmall Γ hΓ U⟩

theorem rvGradedLift_finiteRVFibres (Γ : DefinableGeometry.Space LRV M)
    (U : RVFiniteGradedObject (M := M) S) : finiteRVFibres (rvGradedLift Γ U.obj) := by
  apply finiteRVFibres_listUnion
  intro V hV
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hV
  exact rvLift_finite_rv_fibres (U.obj.obj k) (U.property k)

def rvFiniteGradedLift (Γ : DefinableGeometry.Space LRV M)
    (U : RVFiniteGradedObject (M := M) S) : VFFiniteAllObject (M := M) S :=
  ⟨rvGradedLift Γ U.obj, rvGradedLift_finiteRVFibres Γ U⟩

end SpecialTransformations.Section4

end
