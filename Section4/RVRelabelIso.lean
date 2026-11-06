import Section4.RVCategories
import Section4.Fibres

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

def RVObject.relabel (U : RVObject (M := M) S k)
    (c : Map (DefSet.univ (rawRVSpace (M := M) k) S) (DefSet.univ (rawRVSpace k) S)) :
    RVObject (M := M) S k where
  arity := U.arity
  domain := U.domain
  volume := c.comp U.volume

/-- A finite-to-one, weight-preserving definable change of labels gives
an RV isomorphism on the unchanged underlying definable set. Both morphism
conditions are proved in each direction. -/
def rvRelabelIso (U : RVObject (M := M) S k)
    (c : Map (DefSet.univ (rawRVSpace (M := M) k) S) (DefSet.univ (rawRVSpace k) S))
    (hc : c.FiniteFibres) (hw : ∀ t, rvWeight (c t).val = rvWeight t.val) :
    U ≅ U.relabel c where
  hom := {
    map := Map.id U.domain
    volumetric := fun a => (hw (U.volume a)).symm.le
    finite_volume_images := fun t => by
      let b : DefSet.univ (rawRVSpace (M := M) k) S := ⟨t, Set.mem_univ _⟩
      apply (Set.finite_singleton (c b).val).subset
      rintro s ⟨a, ha, hs⟩
      have harg : U.volume a = b := Subtype.ext ha
      have hval : (U.relabel c).value a = (c b).val := by
        change (c (U.volume a)).val = (c b).val
        rw [harg]
      exact Set.mem_singleton_iff.mpr (hs.symm.trans hval) }
  inv := {
    map := Map.id U.domain
    volumetric := fun a => (hw (U.volume a)).le
    finite_volume_images := fun r => by
      apply (c.fibreCarrier_finite hc ⟨r, Set.mem_univ _⟩).subset
      rintro t ⟨a, ha, ht⟩
      exact ⟨U.volume a, ht, Subtype.ext ha⟩ }
  hom_inv_id := by apply RVHom.ext; apply Map.ext; intro a; rfl
  inv_hom_id := by apply RVHom.ext; apply Map.ext; intro a; rfl

end SpecialTransformations.Section4

end
