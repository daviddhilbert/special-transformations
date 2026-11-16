module

public import Section4.EmptyMaps
public import Section4.RVIsoTools

@[expose] public section

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

def rvEmptyIso (U : RVObject (M := M) S k) (hU : U.domain.carrier = ∅) :
    U ≅ RVObject.empty S k :=
  rvIsoOfVolumePreservingBijection (Map.fromEmpty hU _)
    (Map.bijective_of_empty _ hU rfl) (fun a => False.elim (hU.le a.property))

def rvSelfRestrictionIso (U : RVObject (M := M) S k) :
    U.restrict U.domain (Set.Subset.refl _) ≅ U :=
  rvIsoOfCarrierEq _ _ _ _ rfl (fun _ => rfl)

end SpecialTransformations.Section4

end
