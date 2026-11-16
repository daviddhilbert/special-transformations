module

public import Section4.VFAllIsomorphismClasses
public import Section4.PositiveAdditiveRepresentatives
public import Section4.EmptyMaps
public import Section4.RVRestrictions
public import Mathlib.Tactic.Tauto

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

def VFAllScissor (A B C D : VFAllObject (M := M) S) : Prop :=
  ∃ i : ℕ × ℕ, ∃ X Y : DefSet (mixedFamily (M := M) i) S,
    A = DefinableSetCat.objOfSet i X ∧ B = DefinableSetCat.objOfSet i Y ∧
    C = DefinableSetCat.objOfSet i (X.union Y) ∧ D = DefinableSetCat.objOfSet i (X.inter Y)

def vfAllScissorPresentation (S : Set M) :
    PositiveAdditiveGrothendieck.Presentation (VFAllObject (M := M) S) where
  iso U V := Nonempty (U ≅ V)
  empty := vfAllEmptyObject S
  scissor := VFAllScissor

abbrev VFAllKPlus (S : Set M) := PositiveAdditiveGrothendieck.KPlus (vfAllScissorPresentation (M := M) S)

def vfAllClass (U : VFAllObject (M := M) S) : VFAllKPlus (M := M) S :=
  PositiveAdditiveGrothendieck.of (vfAllScissorPresentation S) U

theorem vfAllClass_iso {U V : VFAllObject (M := M) S} (e : U ≅ V) :
    vfAllClass U = vfAllClass V := PositiveAdditiveGrothendieck.of_iso _ ⟨e⟩

@[simp] theorem vfAllClass_empty : vfAllClass (vfAllEmptyObject (M := M) S) = 0 :=
  PositiveAdditiveGrothendieck.of_empty _

theorem vfAllClass_scissor {A B C D : VFAllObject (M := M) S} (h : VFAllScissor A B C D) :
    vfAllClass A + vfAllClass B = vfAllClass C + vfAllClass D :=
  PositiveAdditiveGrothendieck.of_scissor _ h

theorem vfAllIsoClass_scissor {A B C D : VFAllObject (M := M) S} (h : VFAllScissor A B C D) :
    vfAllIsoClass A + vfAllIsoClass B = vfAllIsoClass C + vfAllIsoClass D := by
  obtain ⟨i, X, Y, rfl, rfl, rfl, rfl⟩ := h
  let E := X.sdiff Y
  let I := X.inter Y
  have hdI : Disjoint E.carrier I.carrier :=
    Set.disjoint_left.mpr (fun _ he hi => he.2 hi.2)
  have hdY : Disjoint E.carrier Y.carrier :=
    Set.disjoint_left.mpr (fun _ he hy => he.2 hy)
  have heX : E.union I = X := by
    apply DefSet.eq_of_carrier_eq
    ext x
    change ((x ∈ X.carrier ∧ x ∉ Y.carrier) ∨ (x ∈ X.carrier ∧ x ∈ Y.carrier)) ↔ x ∈ X.carrier
    tauto
  have heU : E.union Y = X.union Y := by
    apply DefSet.eq_of_carrier_eq
    ext x
    change ((x ∈ X.carrier ∧ x ∉ Y.carrier) ∨ x ∈ Y.carrier) ↔ x ∈ X.carrier ∨ x ∈ Y.carrier
    tauto
  have hX := vfAllIsoClass_disjoint_union i E I hdI
  have hU := vfAllIsoClass_disjoint_union i E Y hdY
  rw [heX] at hX
  rw [heU] at hU
  rw [hX, hU]
  ac_rfl

def vfAllIsoClassInvariant : PositiveAdditiveGrothendieck.Invariant
    (vfAllScissorPresentation (M := M) S) (A := VFAllIsoClasses (M := M) S) where
  toFun := vfAllIsoClass
  iso h := vfAllIsoClass_eq_iff.mpr h
  empty := vfAllIsoClass_empty
  scissor := vfAllIsoClass_scissor

def vfAllKPlusToIsoClasses : VFAllKPlus (M := M) S →+ VFAllIsoClasses (M := M) S :=
  PositiveAdditiveGrothendieck.lift (vfAllScissorPresentation S) vfAllIsoClassInvariant

@[simp] theorem vfAllKPlusToIsoClasses_class (U : VFAllObject (M := M) S) :
    vfAllKPlusToIsoClasses (vfAllClass U) = vfAllIsoClass U :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

def vfAllEmptyIso (U : VFAllObject (M := M) S) (hU : U.set.carrier = ∅) :
    U ≅ vfAllEmptyObject S :=
  DefinableSetCat.isoOfBijective (A := U) (B := vfAllEmptyObject S)
    (Map.fromEmpty hU _) (Map.bijective_of_empty _ hU rfl)

theorem vfAllClass_coprod (U V : VFAllObject (M := M) S) :
    vfAllClass (vfAllCoprodObject U V) = vfAllClass U + vfAllClass V := by
  let W := vfAllCoprodObject U V
  let A := (mixedLeftTagMap U.set V.index.1 V.index.2).image
  let B := (mixedRightTagMap V.set U.index.1 U.index.2).image
  have eA : U ≅ DefinableSetCat.objOfSet W.index A :=
    DefinableSetCat.isoOfBijective (A := U) (B := DefinableSetCat.objOfSet W.index A)
      (mixedLeftTagMap U.set V.index.1 V.index.2).toImage
      (mixedLeftTagMap_toImage_bijective U.set V.index.1 V.index.2)
  have eB : V ≅ DefinableSetCat.objOfSet W.index B :=
    DefinableSetCat.isoOfBijective (A := V) (B := DefinableSetCat.objOfSet W.index B)
      (mixedRightTagMap V.set U.index.1 U.index.2).toImage
      (mixedRightTagMap_toImage_bijective V.set U.index.1 U.index.2)
  have eUnion : DefinableSetCat.objOfSet W.index (A.union B) ≅ W := Iso.refl W
  have he : (A.inter B).carrier = ∅ := by
    apply Set.Subset.antisymm
    · rintro x ⟨ha, hb⟩
      exact False.elim (Set.disjoint_left.mp (mixedTaggedImages_disjoint U.set V.set) ha hb)
    · exact Set.empty_subset _
  have eInter : DefinableSetCat.objOfSet W.index (A.inter B) ≅ vfAllEmptyObject S :=
    vfAllEmptyIso _ he
  have hs := vfAllClass_scissor (S := S) ⟨W.index, A, B, rfl, rfl, rfl, rfl⟩
  calc
    vfAllClass W = vfAllClass (DefinableSetCat.objOfSet W.index (A.union B)) +
        vfAllClass (DefinableSetCat.objOfSet W.index (A.inter B)) := by
      rw [vfAllClass_iso eUnion, vfAllClass_iso eInter, vfAllClass_empty, add_zero]
    _ = vfAllClass (DefinableSetCat.objOfSet W.index A) +
        vfAllClass (DefinableSetCat.objOfSet W.index B) := hs.symm
    _ = vfAllClass U + vfAllClass V := by rw [← vfAllClass_iso eA, ← vfAllClass_iso eB]

theorem vfAllClass_surjective : Function.Surjective (vfAllClass (M := M) (S := S)) :=
  PositiveAdditiveGrothendieck.of_surjective (vfAllScissorPresentation S) vfAllCoprodObject vfAllClass_coprod

/-- The geometric VF scissors identify precisely genuine definable
isomorphism classes, without imposing cancellation or groupification. -/
theorem vfAllClass_eq_iff_iso {U V : VFAllObject (M := M) S} :
    vfAllClass U = vfAllClass V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    apply vfAllIsoClass_eq_iff.mp
    simpa only [vfAllKPlusToIsoClasses_class] using congrArg vfAllKPlusToIsoClasses h
  · rintro ⟨e⟩
    exact vfAllClass_iso e

theorem vfAllKPlusToIsoClasses_bijective :
    Function.Bijective (vfAllKPlusToIsoClasses (M := M) (S := S)) := by
  constructor
  · intro a b h
    obtain ⟨U, rfl⟩ := vfAllClass_surjective a
    obtain ⟨V, rfl⟩ := vfAllClass_surjective b
    apply vfAllClass_eq_iff_iso.mpr
    apply vfAllIsoClass_eq_iff.mp
    simpa only [vfAllKPlusToIsoClasses_class] using h
  · intro a
    obtain ⟨U, rfl⟩ := vfAllIsoClass_surjective a
    exact ⟨vfAllClass U, vfAllKPlusToIsoClasses_class U⟩

def vfAllPositiveIsoEquiv : VFAllKPlus (M := M) S ≃+ VFAllIsoClasses (M := M) S :=
  AddEquiv.ofBijective vfAllKPlusToIsoClasses vfAllKPlusToIsoClasses_bijective

end SpecialTransformations.Section4

end
