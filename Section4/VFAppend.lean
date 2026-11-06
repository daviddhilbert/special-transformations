import Section4.ProductRearrangement
import Section4.RealPresentations
import Section4.VFRealFibres
import Mathlib.Data.Fin.Tuple.Basic

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {n m : ℕ}

def vfAppend (a : Fin n → VFType (M := M)) (b : Fin m → VFType (M := M)) :
    Fin (n + m) → VFType (M := M) := Fin.append a b

theorem vfAppend_injective : Function.Injective
    (fun ab : (Fin n → VFType (M := M)) × (Fin m → VFType (M := M)) =>
      vfAppend ab.1 ab.2) := by
  intro a b he
  apply Prod.ext
  · funext i
    simpa only [vfAppend, Fin.append_left] using congrFun he (Fin.castAdd m i)
  · funext i
    simpa only [vfAppend, Fin.append_right] using congrFun he (Fin.natAdd n i)

def vfAppendMap (S : Set M) (n m : ℕ) :
    Map (DefSet.univ ((rawVFSpace (M := M) n).prod (rawVFSpace m)) S)
      (DefSet.univ (rawVFSpace (n + m)) S) := by
  let P := (rawVFSpace (M := M) n).prod (rawVFSpace m)
  let F (z : P.Index → M) : Fin (n + m) → M :=
    Fin.append (z ∘ Sum.inl) (z ∘ Sum.inr)
  have hcode (c : P.domain) :
      vfValues (vfAppend (P.decode c).1 (P.decode c).2) = F c.val := by
    have hl := vfValues_decode (M := M) (n := n) ⟨c.val ∘ Sum.inl, c.property.1⟩
    have hr := vfValues_decode (M := M) (n := m) ⟨c.val ∘ Sum.inr, c.property.2⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [P, Space.prod, vfValues, vfAppend, F, Fin.append_left] using congrFun hl j
    · simpa only [P, Space.prod, vfValues, vfAppend, F, Fin.append_right] using congrFun hr j
  refine Map.ofCodes _ (fun ab => vfAppend ab.1 ab.2) F ?_
    (fun c => ⟨vfAppend (P.decode c).1 (P.decode c).2, hcode c⟩) ?_
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [F, Fin.append_left, Function.comp_apply]
      exact Set.DefinableFun.proj LRV
    · simp only [F, Fin.append_right, Function.comp_apply]
      exact Set.DefinableFun.proj LRV
  · intro c
    apply vfValues_injective
    exact (vfValues_decode _).trans (hcode c).symm

theorem vfAppendMap_bijective (S : Set M) (n m : ℕ) :
    Function.Bijective (vfAppendMap (M := M) S n m) := by
  constructor
  · intro a b he
    exact Subtype.ext (vfAppend_injective (congrArg Subtype.val he))
  · intro t
    refine ⟨⟨(t.val ∘ Fin.castAdd m, t.val ∘ Fin.natAdd n), Set.mem_univ _⟩, ?_⟩
    exact Subtype.ext Fin.append_castAdd_natAdd

end SpecialTransformations.Section4

end
