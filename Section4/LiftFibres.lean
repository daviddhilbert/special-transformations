import Section4.LiftMorphism
import Section4.Fibres
import Section4.RVCoordinates

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {n r : ℕ}

def rvTailMap (A : DefSet (rawMixedSpace (M := M) n r) S) :
    Map A (DefSet.univ (rawRVSpace (M := M) r) S) :=
  Map.ofCodes A Prod.snd (fun z => z ∘ Sum.inr)
    (fun _ => Set.DefinableFun.proj LRV) (fun c => c.property.2) (fun _ => rfl)

def tailFibre (A : DefSet (rawMixedSpace (M := M) n r) S)
    (s : Fin r → CanonicalRV.RVSort M) :
    DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range (rvValues s)) :=
  (rvTailMap A).fibre ⟨s, Set.mem_univ _⟩ ⟨rvValues s, ⟨s, rfl⟩⟩ (decode_rvValues s)

theorem mem_tailFibre (A : DefSet (rawMixedSpace (M := M) n r) S)
    (s : Fin r → CanonicalRV.RVSort M) (p : (rawMixedSpace (M := M) n r).Carrier) :
    p ∈ (tailFibre A s).carrier ↔ p ∈ A.carrier ∧ p.2 = s := by
  constructor
  · rintro ⟨a, rfl, he⟩
    exact ⟨a.property, congrArg Subtype.val he⟩
  · rintro ⟨hp, hs⟩
    exact ⟨⟨p, hp⟩, rfl, Subtype.ext hs⟩

variable [hM : M ⊨ Axioms.ACVF] {k : ℕ}

def liftFibre (U : RVObject (M := M) S k) (u : U.domain) := tailFibre (rvLift U) u.val

theorem mem_liftFibre (U : RVObject (M := M) S k) (u : U.domain)
    (p : (rawMixedSpace (M := M) k U.arity).Carrier) :
    p ∈ (liftFibre U u).carrier ↔ tupleRV p.1 = U.value u ∧ p.2 = u.val := by
  rw [liftFibre, mem_tailFibre]
  constructor
  · rintro ⟨⟨v, hv, hvol⟩, hs⟩
    have he : v = u := Subtype.ext (hv.trans hs)
    subst v
    exact ⟨hvol.symm, hs⟩
  · rintro ⟨hvol, hs⟩
    exact ⟨⟨u, hs.symm, hvol.symm⟩, hs⟩

end SpecialTransformations.Section4

end
