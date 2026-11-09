import Section9.VolumeResidueCorrespondence
import Section9.RVFiniteHead
import Section4.RVAppend

/-! The volume-pair set is the image of the label map. The label map
and the projections of the pair set have finite fibres in RV[n]. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {U V : RVObject (M := M) S n}

private theorem rvAppend_eq_productTuple (x y : Fin n → CanonicalRV.RVSort M) :
    rvAppend x y = productTuple x y := by
  apply productTuple_ext
  · intro i
    rw [productTuple_left]
    exact Fin.append_left x y i
  · intro i
    rw [productTuple_right]
    exact Fin.append_right x y i

noncomputable def volumePairMap (f : Map U.domain V.domain) :
    Map U.domain (volumeCorrespondence f) :=
  ((rvAppendMap S n n).comp ((U.volume.pair (V.volume.comp f)).toUniv)).corestrict
    (fun u => ⟨u, (rvAppend_eq_productTuple _ _).symm⟩)

@[simp] theorem volumePairMap_apply (f : Map U.domain V.domain) (u : U.domain) :
    (volumePairMap f u).val = productTuple (U.value u) (V.value (f u)) :=
  rvAppend_eq_productTuple _ _

theorem volumePairMap_surjective (f : Map U.domain V.domain) :
    Function.Surjective (volumePairMap f) := by
  intro p
  obtain ⟨u, hu⟩ := p.property
  exact ⟨u, Subtype.ext ((volumePairMap_apply f u).trans hu)⟩

theorem volumePairMap_finite (f : Map U.domain V.domain) (hU : U.volume.FiniteFibres) :
    (volumePairMap f).FiniteFibres := by
  intro p
  let x : DefSet.univ (rawRVSpace (M := M) n) S := ⟨p.val ∘ productLeft n n, Set.mem_univ _⟩
  apply (hU x).subset
  intro u hu
  apply Subtype.ext
  have he := congrArg (fun z : volumeCorrespondence f => z.val ∘ productLeft n n) hu
  rw [volumePairMap_apply] at he
  exact (funext (productTuple_left _ _)).symm.trans he

theorem volumePair_leftProjection_finite (f : Map U.domain V.domain) (hU : U.volume.FiniteFibres) :
    (rvHeadSelect (productLeft n n) (volumeCorrespondence f)).FiniteFibres := by
  intro x
  apply ((hU x).image (volumePairMap f)).subset
  intro p hp
  obtain ⟨u, hu⟩ := volumePairMap_surjective f p
  refine ⟨u, ?_, hu⟩
  apply Subtype.ext
  have he := congrArg (fun z : DefSet.univ (rawRVSpace (M := M) n) S => z.val) hp
  rw [← hu, rvHeadSelect_apply, volumePairMap_apply] at he
  exact (funext (productTuple_left _ _)).symm.trans he

end SpecialTransformations.Section9
