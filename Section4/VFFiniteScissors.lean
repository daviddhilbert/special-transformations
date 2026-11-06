import Section4.VFAllScissors
import Section4.VFCoproductBounds

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

def vfFiniteAllEmpty (S : Set M) : VFFiniteAllObject (M := M) S :=
  ⟨vfAllEmptyObject S, fun _ => Set.finite_empty⟩

def vfFiniteAllRestrict (U : VFFiniteAllObject (M := M) S)
    (A : DefSet (mixedFamily (M := M) U.obj.index) S)
    (hA : A.carrier ⊆ U.obj.set.carrier) : VFFiniteAllObject (M := M) S :=
  ⟨DefinableSetCat.objOfSet U.obj.index A, fun a =>
    (U.property a).subset (fun _ h => hA h)⟩

def vfFiniteAllIsoOfAmbient {U V : VFFiniteAllObject (M := M) S}
    (e : U.obj ≅ V.obj) : U ≅ V where
  hom := ObjectProperty.homMk e.hom
  inv := ObjectProperty.homMk e.inv
  hom_inv_id := by apply ObjectProperty.hom_ext; exact e.hom_inv_id
  inv_hom_id := by apply ObjectProperty.hom_ext; exact e.inv_hom_id

def vfFiniteScissorPresentation (S : Set M) :
    PositiveAdditiveGrothendieck.Presentation (VFFiniteAllObject (M := M) S) where
  iso U V := Nonempty (U ≅ V)
  empty := vfFiniteAllEmpty S
  scissor A B C D := VFAllScissor A.obj B.obj C.obj D.obj

abbrev VFFiniteKPlus (S : Set M) :=
  PositiveAdditiveGrothendieck.KPlus (vfFiniteScissorPresentation (M := M) S)

def vfFiniteClass (U : VFFiniteAllObject (M := M) S) : VFFiniteKPlus (M := M) S :=
  PositiveAdditiveGrothendieck.of (vfFiniteScissorPresentation S) U

theorem vfFiniteClass_iso {U V : VFFiniteAllObject (M := M) S} (e : U ≅ V) :
    vfFiniteClass U = vfFiniteClass V := PositiveAdditiveGrothendieck.of_iso _ ⟨e⟩

@[simp] theorem vfFiniteClass_empty : vfFiniteClass (vfFiniteAllEmpty (M := M) S) = 0 :=
  PositiveAdditiveGrothendieck.of_empty _

theorem vfFiniteClass_scissor {A B C D : VFFiniteAllObject (M := M) S}
    (h : VFAllScissor A.obj B.obj C.obj D.obj) :
    vfFiniteClass A + vfFiniteClass B = vfFiniteClass C + vfFiniteClass D :=
  PositiveAdditiveGrothendieck.of_scissor _ h

theorem vfFiniteClass_coprod (U V : VFFiniteAllObject (M := M) S) :
    vfFiniteClass (vfFiniteAllCoprodObject U V) = vfFiniteClass U + vfFiniteClass V := by
  let W := vfFiniteAllCoprodObject U V
  let A := (mixedLeftTagMap U.obj.set V.obj.index.1 V.obj.index.2).image
  let B := (mixedRightTagMap V.obj.set U.obj.index.1 U.obj.index.2).image
  have hA : A.carrier ⊆ W.obj.set.carrier := fun _ h => Or.inl h
  have hB : B.carrier ⊆ W.obj.set.carrier := fun _ h => Or.inr h
  let UA := vfFiniteAllRestrict W A hA
  let UB := vfFiniteAllRestrict W B hB
  let UU := vfFiniteAllRestrict W (A.union B)
    (fun _ h => h.elim (fun hx => hA hx) (fun hy => hB hy))
  let UI := vfFiniteAllRestrict W (A.inter B) (fun _ h => hA h.1)
  have eA : U ≅ UA := vfFiniteAllIsoOfAmbient
    (DefinableSetCat.isoOfBijective
      (A := U.obj) (B := UA.obj)
      (mixedLeftTagMap U.obj.set V.obj.index.1 V.obj.index.2).toImage
      (mixedLeftTagMap_toImage_bijective U.obj.set V.obj.index.1 V.obj.index.2))
  have eB : V ≅ UB := vfFiniteAllIsoOfAmbient
    (DefinableSetCat.isoOfBijective
      (A := V.obj) (B := UB.obj)
      (mixedRightTagMap V.obj.set U.obj.index.1 U.obj.index.2).toImage
      (mixedRightTagMap_toImage_bijective V.obj.set U.obj.index.1 U.obj.index.2))
  have eUnion : UU ≅ W := vfFiniteAllIsoOfAmbient (Iso.refl W.obj)
  have he : (A.inter B).carrier = ∅ := by
    apply Set.Subset.antisymm
    · rintro x ⟨ha, hb⟩
      exact False.elim (Set.disjoint_left.mp (mixedTaggedImages_disjoint U.obj.set V.obj.set) ha hb)
    · exact Set.empty_subset _
  have eInter : UI ≅ vfFiniteAllEmpty S := vfFiniteAllIsoOfAmbient (vfAllEmptyIso _ he)
  have hs : vfFiniteClass UA + vfFiniteClass UB = vfFiniteClass UU + vfFiniteClass UI :=
    vfFiniteClass_scissor ⟨W.obj.index, A, B, rfl, rfl, rfl, rfl⟩
  calc
    vfFiniteClass W = vfFiniteClass UU + vfFiniteClass UI := by
      rw [vfFiniteClass_iso eUnion, vfFiniteClass_iso eInter, vfFiniteClass_empty, add_zero]
    _ = vfFiniteClass UA + vfFiniteClass UB := hs.symm
    _ = vfFiniteClass U + vfFiniteClass V := by
      rw [← vfFiniteClass_iso eA, ← vfFiniteClass_iso eB]

end SpecialTransformations.Section4

end
