import Section4.RVLabelIsomorphisms
import Section4.RVCoordinates
import Section4.CodeMaps

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {n m k : ℕ}

def rvReindexEquiv (e : Fin m ≃ Fin n) :
    (Fin n → CanonicalRV.RVSort M) ≃ (Fin m → CanonicalRV.RVSort M) where
  toFun t := t ∘ e
  invFun t := t ∘ e.symm
  left_inv t := by funext i; exact congrArg t (e.apply_symm_apply i)
  right_inv t := by funext i; exact congrArg t (e.symm_apply_apply i)

theorem rvWeight_reindex (e : Fin m ≃ Fin n) (t : Fin n → CanonicalRV.RVSort M) :
    rvWeight (t ∘ e) = rvWeight t := by
  unfold rvWeight
  exact e.sum_comp (fun i => if (t i).val ≠ iRVZero then 1 else 0)

def rvReindexMap (S : Set M) (e : Fin m ≃ Fin n) :
    Map (DefSet.univ (rawRVSpace (M := M) n) S)
      (DefSet.univ (rawRVSpace (M := M) m) S) := by
  let F (z : Fin n → M) : Fin m → M := z ∘ e
  have hcode (c : (rawRVSpace (M := M) n).domain) :
      rvValues (((rawRVSpace n).decode c) ∘ e) = F c.val := by
    funext i
    exact congrFun (rvValues_decode c) (e i)
  refine Map.ofCodes _ (fun t => t ∘ e) F (fun _ => Set.DefinableFun.proj LRV)
    (fun c => ⟨((rawRVSpace n).decode c) ∘ e, hcode c⟩) ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode _).trans (hcode c).symm

theorem rvReindexMap_bijective (S : Set M) (e : Fin m ≃ Fin n) :
    Function.Bijective (rvReindexMap (M := M) S e) := by
  constructor
  · intro a b he
    apply Subtype.ext
    apply (rvReindexEquiv e).injective
    exact congrArg Subtype.val he
  · intro b
    refine ⟨⟨b.val ∘ e.symm, Set.mem_univ _⟩, Subtype.ext ?_⟩
    exact (rvReindexEquiv e).apply_symm_apply b.val

def RVObject.reindexVolume (U : RVObject (M := M) S k) (e : Fin m ≃ Fin k) :
    RVObject (M := M) S m where
  arity := U.arity
  domain := U.domain
  volume := (rvReindexMap S e).comp U.volume

theorem rvReindexVolume_weight (U : RVObject (M := M) S k)
    (e : Fin m ≃ Fin k) (a : U.domain) :
    rvWeight ((U.reindexVolume e).value a) = rvWeight (U.value a) :=
  rvWeight_reindex e (U.value a)

def rvReindexVolumeIso (U : RVObject (M := M) S k) (e : Equiv.Perm (Fin k)) :
    U ≅ U.reindexVolume e :=
  rvIsoOfLabelEquiv (Map.id U.domain) Function.bijective_id (rvReindexEquiv e)
    (rvWeight_reindex e) (fun _ => rfl)

end SpecialTransformations.Section4

end
