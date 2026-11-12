module

public import Section5.Assembly

@[expose] public section

/-! Real-base ambient tag equalities for restricting transformations to
domains with named imaginary parameters. The ambient domain uses only
retained coordinate indices; no representative of an imaginary is named. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

theorem keyTags_definable (ρ : Fin n → Fin m) :
    SetDefinable (keySpace (M := M) n m) S {p | ∀ i, p.1 i = p.2 (ρ i)} := by
  have hd := setDefinable (PresentedSet.univ (keySpace (M := M) n m) S)
  have hi (i : Fin n) : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M))
      (Fin n ⊕ Fin m) {z | z (.inl i) = z (.inr (ρ i))} := by
    letI := @CanonicalStructure.normalize M sM
    exact (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
  have hh : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M))
      (Fin n ⊕ Fin m) {z | ∀ i, z (.inl i) = z (.inr (ρ i))} := by
    letI := @CanonicalStructure.normalize M sM
    convert Set.definable_iInter_of_finite hi using 1
    ext z
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  have ht := @Set.Definable.inter M S LRV (CanonicalStructure.normalize (M := M))
    (Fin n ⊕ Fin m) _ _ hd hh
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin n ⊕ Fin m)
    {z | ∃ hz : z ∈ pDomain (keySpace n m),
      ∀ i, (pDecode (keySpace n m) ⟨z, hz⟩).1 i = (pDecode (keySpace n m) ⟨z, hz⟩).2 (ρ i)}
  convert ht using 1
  ext z
  constructor
  · rintro ⟨hz, hp⟩
    exact ⟨⟨hz, Set.mem_univ _⟩, fun i => congrArg Subtype.val (hp i)⟩
  · rintro ⟨⟨hz, _⟩, hp⟩
    exact ⟨hz, fun i => Subtype.ext (hp i)⟩

def taggedAmbient (ρ : Fin n → Fin m) : DefSet (M := M) S n m :=
  PresentedSet.mk {p | ∀ i, p.2 (ρ i) = rv (vfAt p i)} (by
    have hh := Map.definable_preimage (keyMap (PresentedSet.univ (pointSpace n m) S))
      (keyTags_definable (S := S) ρ)
    convert hh using 1
    ext p
    constructor
    · intro hp
      exact ⟨⟨p, Set.mem_univ _⟩, rfl, fun i => (hp i).symm⟩
    · rintro ⟨p, rfl, hp⟩
      exact fun i => (hp i).symm)

theorem taggedAmbient_allTagged (ρ : Fin n → Fin m) : AllTagged (taggedAmbient (S := S) ρ) :=
  fun j => ⟨ρ j, fun p hp => hp j⟩

theorem taggedAmbient_pullback (ρ : Fin n → Fin m) :
    IsRVPullback (carrier (taggedAmbient (M := M) (S := S) ρ)) := by
  apply (isRVPullback_iff _).mpr
  intro p hp q he i
  obtain ⟨hv, ht⟩ := (sameRV_iff _ _).mp he
  exact (congrFun ht (ρ i)).symm.trans ((hp i).trans (hv i))

theorem exists_taggedAmbient (A : Set (Point (M := M) n m))
    (hTags : ∀ j : Fin n, ∃ k : Fin m, Tagged A j k) :
    ∃ D : DefSet (M := M) S n m, A ⊆ carrier D ∧ AllTagged D ∧ IsRVPullback (carrier D) := by
  choose ρ hρ using hTags
  exact ⟨taggedAmbient ρ, (fun p hp i => hρ i p hp),
    taggedAmbient_allTagged ρ, taggedAmbient_pullback ρ⟩

end SpecialTransformations.Section5
