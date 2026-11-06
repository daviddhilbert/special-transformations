import Section4.RVCoproduct
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.Algebra.Group.TypeTags.Basic

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

instance rvHasInitial : HasInitial (RVObject (M := M) S k) :=
  (rvEmptyIsInitial (M := M) (S := S) (k := k)).hasInitial

instance rvHasColimitPair (U V : RVObject (M := M) S k) : HasColimit (pair U V) :=
  HasColimit.mk ⟨_, rvCoprodIsColimit U V⟩

instance rvHasBinaryCoproducts : HasBinaryCoproducts (RVObject (M := M) S k) :=
  hasBinaryCoproducts_of_hasColimit_pair (RVObject (M := M) S k)

instance rvCocartesianMonoidal : MonoidalCategory (RVObject (M := M) S k) :=
  monoidalOfHasFiniteCoproducts _

instance rvCocartesianSymmetric : SymmetricCategory (RVObject (M := M) S k) :=
  symmetricOfHasFiniteCoproducts _

/-- Actual isomorphism classes of definable objects, with addition induced
by the categorical coproduct. No scissor relations have been imposed here. -/
abbrev RVIsoClasses (S : Set M) (k : ℕ) := Additive (Skeleton (RVObject (M := M) S k))

def rvIsoClass (U : RVObject (M := M) S k) : RVIsoClasses (M := M) S k :=
  Additive.ofMul (toSkeleton U)

theorem rvIsoClass_eq_iff {U V : RVObject (M := M) S k} :
    rvIsoClass U = rvIsoClass V ↔ Nonempty (U ≅ V) :=
  toSkeleton_eq_toSkeleton_iff

theorem rvIsoClass_iso {U V : RVObject (M := M) S k} (e : U ≅ V) :
    rvIsoClass U = rvIsoClass V := rvIsoClass_eq_iff.mpr ⟨e⟩

@[simp] theorem rvIsoClass_empty : rvIsoClass (RVObject.empty (M := M) S k) = 0 := by
  change toSkeleton (RVObject.empty S k) = (1 : Skeleton (RVObject S k))
  rw [Skeleton.one_eq]
  exact congr_toSkeleton_of_iso (rvEmptyIsInitial.uniqueUpToIso initialIsInitial)

theorem rvIsoClass_coprod (U V : RVObject (M := M) S k) :
    rvIsoClass (rvCoprodObject U V) = rvIsoClass U + rvIsoClass V := by
  change toSkeleton (rvCoprodObject U V) = toSkeleton U * toSkeleton V
  calc
    _ = toSkeleton (U ⨿ V) := congr_toSkeleton_of_iso
      (colimit.isoColimitCocone
        { cocone := BinaryCofan.mk (rvCoprodInl U V) (rvCoprodInr U V)
          isColimit := rvCoprodIsColimit U V }).symm
    _ = _ := Skeleton.toSkeleton_tensorObj U V

theorem rvIsoClass_surjective :
    Function.Surjective (rvIsoClass (M := M) (S := S) (k := k)) := by
  intro a
  exact ⟨(fromSkeleton (RVObject S k)).obj a.toMul, toSkeleton_fromSkeleton_obj a.toMul⟩

end SpecialTransformations.Section4

end
