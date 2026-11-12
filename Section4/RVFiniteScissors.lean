module

public import Section4.RVPositiveIsoComparison

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

def rvFiniteEmpty (S : Set M) (k : ℕ) : RVFiniteObject (M := M) S k :=
  ⟨RVObject.empty S k, by
    intro t
    apply Set.finite_empty.subset
    intro a _
    exact False.elim a.property⟩

def rvFiniteRestrict (U : RVFiniteObject (M := M) S k)
    (A : DefSet (rawRVSpace (M := M) U.obj.arity) S) (hA : A.carrier ⊆ U.obj.domain.carrier) :
    RVFiniteObject (M := M) S k :=
  ⟨U.obj.restrict A hA, U.obj.restrict_finite_volume U.property A hA⟩

def rvFiniteIsoOfAmbient {U V : RVFiniteObject (M := M) S k} (e : U.obj ≅ V.obj) : U ≅ V where
  hom := ObjectProperty.homMk e.hom
  inv := ObjectProperty.homMk e.inv
  hom_inv_id := by apply ObjectProperty.hom_ext; exact e.hom_inv_id
  inv_hom_id := by apply ObjectProperty.hom_ext; exact e.inv_hom_id

def rvFiniteScissorPresentation (S : Set M) (k : ℕ) :
    PositiveAdditiveGrothendieck.Presentation (RVFiniteObject (M := M) S k) where
  iso U V := Nonempty (U ≅ V)
  empty := rvFiniteEmpty S k
  scissor A B C D := RVScissor A.obj B.obj C.obj D.obj

abbrev RVFiniteKPlus (S : Set M) (k : ℕ) :=
  PositiveAdditiveGrothendieck.KPlus (rvFiniteScissorPresentation (M := M) S k)

def rvFiniteClass (U : RVFiniteObject (M := M) S k) : RVFiniteKPlus (M := M) S k :=
  PositiveAdditiveGrothendieck.of (rvFiniteScissorPresentation S k) U

theorem rvFiniteClass_iso {U V : RVFiniteObject (M := M) S k} (e : U ≅ V) :
    rvFiniteClass U = rvFiniteClass V :=
  PositiveAdditiveGrothendieck.of_iso _ ⟨e⟩

@[simp] theorem rvFiniteClass_empty : rvFiniteClass (rvFiniteEmpty (M := M) S k) = 0 :=
  PositiveAdditiveGrothendieck.of_empty _

theorem rvFiniteClass_scissor {A B C D : RVFiniteObject (M := M) S k}
    (h : RVScissor A.obj B.obj C.obj D.obj) :
    rvFiniteClass A + rvFiniteClass B = rvFiniteClass C + rvFiniteClass D :=
  PositiveAdditiveGrothendieck.of_scissor _ h

variable [hM : M ⊨ Axioms.ACVF]

theorem rvFiniteClass_coprod (U V : RVFiniteObject (M := M) S k) :
    rvFiniteClass (rvFiniteCoprodObject U V) = rvFiniteClass U + rvFiniteClass V := by
  let W := rvFiniteCoprodObject U V
  let A := (rvLeftTagMap U.obj.domain V.obj.arity).image
  let B := (rvRightTagMap V.obj.domain U.obj.arity).image
  have hA : A.carrier ⊆ W.obj.domain.carrier := fun _ h => Or.inl h
  have hB : B.carrier ⊆ W.obj.domain.carrier := fun _ h => Or.inr h
  have eA : U ≅ rvFiniteRestrict W A hA := rvFiniteIsoOfAmbient
    (rvIsoOfVolumePreservingBijection (rvLeftTagMap U.obj.domain V.obj.arity).toImage
      (rvLeftTagMap_toImage_bijective U.obj.domain V.obj.arity) (rvCoprod_value_left U.obj V.obj))
  have eB : V ≅ rvFiniteRestrict W B hB := rvFiniteIsoOfAmbient
    (rvIsoOfVolumePreservingBijection (rvRightTagMap V.obj.domain U.obj.arity).toImage
      (rvRightTagMap_toImage_bijective V.obj.domain U.obj.arity) (rvCoprod_value_right U.obj V.obj))
  have eUnion : rvFiniteRestrict W (A.union B) (rvUnionSubset W.obj A B hA hB) ≅ W :=
    rvFiniteIsoOfAmbient (rvSelfRestrictionIso W.obj)
  have he : (A.inter B).carrier = ∅ := by
    apply Set.Subset.antisymm
    · rintro x ⟨ha, hb⟩
      exact False.elim (Set.disjoint_left.mp
        (rvTaggedImages_disjoint U.obj.domain V.obj.domain) ha hb)
    · exact Set.empty_subset _
  have eInter : rvFiniteRestrict W (A.inter B) (fun _ h => hA h.1) ≅ rvFiniteEmpty S k :=
    rvFiniteIsoOfAmbient (rvEmptyIso _ he)
  have hs := rvFiniteClass_scissor (S := S) (k := k)
    (A := rvFiniteRestrict W A hA) (B := rvFiniteRestrict W B hB)
    (C := rvFiniteRestrict W (A.union B) (rvUnionSubset W.obj A B hA hB))
    (D := rvFiniteRestrict W (A.inter B) (fun _ h => hA h.1))
    ⟨W.obj, A, B, hA, hB, rfl, rfl, rfl, rfl⟩
  calc
    rvFiniteClass W = rvFiniteClass (rvFiniteRestrict W (A.union B) _) +
        rvFiniteClass (rvFiniteRestrict W (A.inter B) _) := by
      rw [rvFiniteClass_iso eUnion, rvFiniteClass_iso eInter, rvFiniteClass_empty, add_zero]
    _ = rvFiniteClass (rvFiniteRestrict W A hA) + rvFiniteClass (rvFiniteRestrict W B hB) := hs.symm
    _ = rvFiniteClass U + rvFiniteClass V := by
      rw [← rvFiniteClass_iso eA, ← rvFiniteClass_iso eB]

end SpecialTransformations.Section4

end
