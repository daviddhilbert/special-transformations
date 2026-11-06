import Section4.VFCoproduct
import Section4.DefinableUnionCoproduct
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.Algebra.Group.TypeTags.Basic

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

instance vfAllHasInitial : HasInitial (VFAllObject (M := M) S) :=
  (vfAllEmptyIsInitial (M := M) (S := S)).hasInitial

instance vfAllHasColimitPair (U V : VFAllObject (M := M) S) : HasColimit (pair U V) :=
  HasColimit.mk ⟨_, vfAllCoprodIsColimit U V⟩

instance vfAllHasBinaryCoproducts : HasBinaryCoproducts (VFAllObject (M := M) S) :=
  hasBinaryCoproducts_of_hasColimit_pair (VFAllObject (M := M) S)

instance vfAllCocartesianMonoidal : MonoidalCategory (VFAllObject (M := M) S) :=
  monoidalOfHasFiniteCoproducts _

instance vfAllCocartesianSymmetric : SymmetricCategory (VFAllObject (M := M) S) :=
  symmetricOfHasFiniteCoproducts _

abbrev VFAllIsoClasses (S : Set M) := Additive (Skeleton (VFAllObject (M := M) S))

def vfAllIsoClass (U : VFAllObject (M := M) S) : VFAllIsoClasses (M := M) S :=
  Additive.ofMul (toSkeleton U)

theorem vfAllIsoClass_eq_iff {U V : VFAllObject (M := M) S} :
    vfAllIsoClass U = vfAllIsoClass V ↔ Nonempty (U ≅ V) := toSkeleton_eq_toSkeleton_iff

theorem vfAllIsoClass_iso {U V : VFAllObject (M := M) S} (e : U ≅ V) :
    vfAllIsoClass U = vfAllIsoClass V := vfAllIsoClass_eq_iff.mpr ⟨e⟩

@[simp] theorem vfAllIsoClass_empty : vfAllIsoClass (vfAllEmptyObject (M := M) S) = 0 := by
  change toSkeleton (vfAllEmptyObject S) = (1 : Skeleton (VFAllObject S))
  rw [Skeleton.one_eq]
  exact congr_toSkeleton_of_iso (vfAllEmptyIsInitial.uniqueUpToIso initialIsInitial)

theorem vfAllIsoClass_coprod (U V : VFAllObject (M := M) S) :
    vfAllIsoClass (vfAllCoprodObject U V) = vfAllIsoClass U + vfAllIsoClass V := by
  change toSkeleton (vfAllCoprodObject U V) = toSkeleton U * toSkeleton V
  calc
    _ = toSkeleton (U ⨿ V) := congr_toSkeleton_of_iso
      (colimit.isoColimitCocone
        { cocone := BinaryCofan.mk (vfAllCoprodInl U V) (vfAllCoprodInr U V)
          isColimit := vfAllCoprodIsColimit U V }).symm
    _ = _ := Skeleton.toSkeleton_tensorObj U V

theorem vfAllIsoClass_surjective : Function.Surjective (vfAllIsoClass (M := M) (S := S)) := by
  intro a
  exact ⟨(fromSkeleton (VFAllObject S)).obj a.toMul, toSkeleton_fromSkeleton_obj a.toMul⟩

def vfAllCoprodUnionIso (i : ℕ × ℕ) (A B : DefSet (mixedFamily (M := M) i) S)
    (hd : Disjoint A.carrier B.carrier) :
    vfAllCoprodObject (DefinableSetCat.objOfSet i A) (DefinableSetCat.objOfSet i B) ≅
      DefinableSetCat.objOfSet i (A.union B) :=
  (vfAllCoprodIsColimit _ _).coconePointUniqueUpToIso (DefinableSetCat.unionIsColimit i A B hd)

theorem vfAllIsoClass_disjoint_union (i : ℕ × ℕ) (A B : DefSet (mixedFamily (M := M) i) S)
    (hd : Disjoint A.carrier B.carrier) :
    vfAllIsoClass (DefinableSetCat.objOfSet i (A.union B)) =
      vfAllIsoClass (DefinableSetCat.objOfSet i A) + vfAllIsoClass (DefinableSetCat.objOfSet i B) := by
  rw [← vfAllIsoClass_iso (vfAllCoprodUnionIso i A B hd), vfAllIsoClass_coprod]

end SpecialTransformations.Section4

end
