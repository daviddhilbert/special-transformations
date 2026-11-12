module

public import Section4.RVProductSymmetry
public import Section4.RVEmptyIso
public import Section4.RVDimension

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {k l : ℕ}

def rvUnitObject (S : Set M) : RVObject (M := M) S 0 where
  arity := 0
  domain := DefSet.univ (rawRVSpace 0) S
  volume := Map.id _

theorem rvUnitObject_finite_volume (S : Set M) :
    (rvUnitObject (M := M) S).volume.FiniteFibres :=
  Map.finiteFibres_of_injective Function.injective_id

def rvProductRightUnitMap (U : RVObject (M := M) S k) :
    Map (rvProductObject U (rvUnitObject S)).domain U.domain :=
  (Map.prodFst U.domain (rvUnitObject S).domain).comp
    (rvUnpack U.domain (rvUnitObject S).domain)

theorem rvProductRightUnitMap_bijective (U : RVObject (M := M) S k) :
    Function.Bijective (rvProductRightUnitMap U) := by
  constructor
  · intro a b he
    apply (rvUnpack_bijective U.domain (rvUnitObject S).domain).1
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val he
    · exact funext (fun i : Fin 0 => i.elim0)
  · intro a
    let p : U.domain.prod (rvUnitObject S).domain :=
      ⟨(a.val, Fin.elim0), a.property, Set.mem_univ _⟩
    refine ⟨(rvPack U.domain (rvUnitObject S).domain).toImage p, ?_⟩
    change Map.prodFst U.domain (rvUnitObject S).domain
      (rvUnpack U.domain (rvUnitObject S).domain
        ((rvPack U.domain (rvUnitObject S).domain).toImage p)) = a
    rw [rvUnpack_pack]
    rfl

def rvProductRightUnitIso (U : RVObject (M := M) S k) :
    rvProductObject U (rvUnitObject S) ≅ U := by
  apply rvIsoOfVolumePreservingBijection (rvProductRightUnitMap U)
    (rvProductRightUnitMap_bijective U)
  intro a
  rw [rvProductObject_value]
  have hz : (rvUnitObject S).value
      ⟨(rvUnpack U.domain (rvUnitObject S).domain a).val.2,
        (rvUnpack U.domain (rvUnitObject S).domain a).property.2⟩ = Fin.elim0 :=
    funext (fun i : Fin 0 => i.elim0)
  rw [hz]
  simp only [rvAppend, Fin.append_elim0, Fin.cast_refl, Function.comp_id]
  rfl

def rvProductEmptyIso (U : RVObject (M := M) S k) :
    rvProductObject U (RVObject.empty S l) ≅ RVObject.empty S (k + l) := by
  apply rvEmptyIso
  apply Set.Subset.antisymm
  · rintro t ⟨a, ha⟩
    exact a.property.2
  · exact Set.empty_subset _

def rvEmptyProductIso (U : RVObject (M := M) S l) :
    rvProductObject (RVObject.empty S k) U ≅ RVObject.empty S (k + l) := by
  apply rvEmptyIso
  apply Set.Subset.antisymm
  · rintro t ⟨a, ha⟩
    exact a.property.1
  · exact Set.empty_subset _

/-- Every actual definable singleton in RV[0] represents the unit. -/
def rvSingletonUnitIso (U : RVObject (M := M) S 0)
    (hne : U.domain.carrier.Nonempty) (hsub : U.domain.carrier.Subsingleton) :
    U ≅ rvUnitObject S := by
  let F : Map U.domain (rvUnitObject S).domain := Map.toSubsingleton U.domain (rawRVSpace 0)
  have hF : Function.Bijective F := by
    constructor
    · intro a b _
      exact Subtype.ext (hsub a.property b.property)
    · intro b
      obtain ⟨a, ha⟩ := hne
      exact ⟨⟨a, ha⟩, Subtype.ext (funext (fun i : Fin 0 => i.elim0))⟩
  exact rvIsoOfVolumePreservingBijection F hF (fun _ => funext (fun i : Fin 0 => i.elim0))

end SpecialTransformations.Section4

end
