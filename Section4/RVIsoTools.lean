import Section4.RVRestrictions

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

def rvHomOfVolumePreserving {U V : RVObject (M := M) S k}
    (F : Map U.domain V.domain) (hvol : ∀ u, V.value (F u) = U.value u) : RVHom U V where
  map := F
  volumetric u := by rw [hvol u]
  finite_volume_images t := by
    apply (Set.finite_singleton t).subset
    rintro s ⟨a, ha, hs⟩
    exact Set.mem_singleton_iff.mpr (hs.symm.trans ((hvol a).trans ha))

def rvIsoOfVolumePreservingBijection {U V : RVObject (M := M) S k}
    (F : Map U.domain V.domain) (hF : Function.Bijective F)
    (hvol : ∀ u, V.value (F u) = U.value u) : U ≅ V where
  hom := rvHomOfVolumePreserving F hvol
  inv := rvHomOfVolumePreserving (F.inverse hF) (by
    intro v
    have h := hvol (F.inverse hF v)
    rw [Map.apply_inverse] at h
    exact h.symm)
  hom_inv_id := by apply RVHom.ext; apply Map.ext; intro u; exact Map.inverse_apply F hF u
  inv_hom_id := by apply RVHom.ext; apply Map.ext; intro v; exact Map.apply_inverse F hF v

def rvIsoOfCarrierEq {n : ℕ} (A B : DefSet (rawRVSpace (M := M) n) S)
    (f : Map A (DefSet.univ (rawRVSpace k) S))
    (g : Map B (DefSet.univ (rawRVSpace k) S)) (hAB : A.carrier = B.carrier)
    (hvol : ∀ a : A, (g ⟨a.val, hAB.le a.property⟩).val = (f a).val) :
    RVObject.mk n A f ≅ RVObject.mk n B g := by
  let F : Map A B := Map.inclusion hAB.le
  have hF : Function.Bijective F := by
    constructor
    · intro a b he
      exact Subtype.ext (congrArg (fun b : B => b.val) he)
    · intro b
      exact ⟨⟨b.val, hAB.ge b.property⟩, Subtype.ext rfl⟩
  exact rvIsoOfVolumePreservingBijection F hF hvol

theorem RVObject.restrict_eq_of_carrier_eq (U : RVObject (M := M) S k)
    (A B : DefSet (rawRVSpace (M := M) U.arity) S)
    (hA : A.carrier ⊆ U.domain.carrier) (hB : B.carrier ⊆ U.domain.carrier)
    (hAB : A.carrier = B.carrier) : U.restrict A hA = U.restrict B hB := by
  have he : A = B := DefSet.eq_of_carrier_eq hAB
  subst B
  rfl

end SpecialTransformations.Section4

end
