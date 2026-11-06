import Section4.RVProduct
import Section4.RVReindexing
import Section4.ProductBijections
import Mathlib.Logic.Equiv.Fin.Basic

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {n m k l : ℕ}

theorem rvUnpack_bijective (A : DefSet (rawRVSpace (M := M) n) S)
    (B : DefSet (rawRVSpace (M := M) m) S) : Function.Bijective (rvUnpack A B) := by
  constructor
  · intro a b he
    have h := congrArg (rvPack A B).toImage he
    simpa only [rvPack_unpack] using h
  · intro b
    exact ⟨(rvPack A B).toImage b, rvUnpack_pack A B b⟩

theorem rvAppend_flip (a : Fin k → CanonicalRV.RVSort M)
    (b : Fin l → CanonicalRV.RVSort M) :
    rvAppend b a ∘ (finAddFlip : Fin (k + l) ≃ Fin (l + k)) = rvAppend a b := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply, finAddFlip_apply_castAdd, rvAppend, Fin.append_right,
      Fin.append_left]
  · simp only [Function.comp_apply, finAddFlip_apply_natAdd, rvAppend, Fin.append_left,
      Fin.append_right]

def rvProductSwapMap (U : RVObject (M := M) S k) (V : RVObject (M := M) S l) :
    Map (rvProductObject U V).domain (rvProductObject V U).domain :=
  (rvPack V.domain U.domain).toImage.comp
    ((Map.prodSwap U.domain V.domain).comp (rvUnpack U.domain V.domain))

theorem rvProductSwapMap_bijective (U : RVObject (M := M) S k)
    (V : RVObject (M := M) S l) : Function.Bijective (rvProductSwapMap U V) :=
  (rvPackToImage_bijective V.domain U.domain).comp
    ((Map.prodSwap_bijective U.domain V.domain).comp (rvUnpack_bijective U.domain V.domain))

theorem rvProductSwapMap_unpack (U : RVObject (M := M) S k)
    (V : RVObject (M := M) S l) (a : (rvProductObject U V).domain) :
    rvUnpack V.domain U.domain (rvProductSwapMap U V a) =
      Map.prodSwap U.domain V.domain (rvUnpack U.domain V.domain a) :=
  rvUnpack_pack V.domain U.domain _

/-- The actual symmetry of the cartesian RV product. The label blocks
are permuted along the same finite-coordinate symmetry. -/
def rvProductCommReindexedIso (U : RVObject (M := M) S k) (V : RVObject (M := M) S l) :
    rvProductObject U V ≅ (rvProductObject V U).reindexVolume
      (finAddFlip : Fin (k + l) ≃ Fin (l + k)) := by
  apply rvIsoOfVolumePreservingBijection (rvProductSwapMap U V) (rvProductSwapMap_bijective U V)
  intro a
  change (rvProductObject V U).value (rvProductSwapMap U V a) ∘ finAddFlip =
    (rvProductObject U V).value a
  rw [rvProductObject_value, rvProductSwapMap_unpack, rvProductObject_value]
  exact rvAppend_flip _ _

end SpecialTransformations.Section4

end
