module

public import Section4.VFFiniteSemiring

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

/-- Any definable singleton, in any mixed ambient arity, is genuinely
definably isomorphic to the zero-coordinate singleton. -/
def vfAllSingletonIso (U : VFAllObject (M := M) S)
    (hne : U.set.carrier.Nonempty) (hU : U.set.carrier.Subsingleton) :
    U ≅ vfAllUnitObject S := by
  letI : Nonempty (rawMixedSpace (M := M) 0 0).Carrier := ⟨(Fin.elim0, Fin.elim0)⟩
  letI : Subsingleton (rawMixedSpace (M := M) 0 0).Carrier := by
    change Subsingleton ((Fin 0 → SpecialTransformations.Milestone0.Transfer.VFType (M := M)) ×
      (Fin 0 → CanonicalRV.RVSort M))
    infer_instance
  let f := Map.toSubsingleton U.set (rawMixedSpace (M := M) 0 0)
  apply DefinableSetCat.isoOfBijective (A := U) (B := vfAllUnitObject S) f
  constructor
  · intro a b _
    exact Subtype.ext (hU a.property b.property)
  · intro b
    obtain ⟨u, hu⟩ := hne
    exact ⟨⟨u, hu⟩, Subtype.ext
      (@Subsingleton.elim (rawMixedSpace (M := M) 0 0).Carrier inferInstance _ _)⟩

theorem vfAllClass_singleton (U : VFAllObject (M := M) S)
    (hne : U.set.carrier.Nonempty) (hU : U.set.carrier.Subsingleton) : vfAllClass U = 1 :=
  vfAllClass_iso (vfAllSingletonIso U hne hU)

def vfFiniteSingletonIso (U : VFFiniteAllObject (M := M) S)
    (hne : U.obj.set.carrier.Nonempty) (hU : U.obj.set.carrier.Subsingleton) :
    U ≅ vfFiniteUnitObject S := vfFiniteAllIsoOfAmbient (vfAllSingletonIso U.obj hne hU)

theorem vfFiniteClass_singleton (U : VFFiniteAllObject (M := M) S)
    (hne : U.obj.set.carrier.Nonempty) (hU : U.obj.set.carrier.Subsingleton) : vfFiniteClass U = 1 :=
  vfFiniteClass_iso (vfFiniteSingletonIso U hne hU)

end SpecialTransformations.Section4

end
