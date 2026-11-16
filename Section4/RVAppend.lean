module

public import Section4.RVCoordinates
public import Section4.RVPadding
public import Section4.MapProduct
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {n m : ℕ}

def rvAppend (a : Fin n → CanonicalRV.RVSort M) (b : Fin m → CanonicalRV.RVSort M) :
    Fin (n + m) → CanonicalRV.RVSort M := Fin.append a b

theorem rvAppend_injective : Function.Injective
    (fun ab : (Fin n → CanonicalRV.RVSort M) × (Fin m → CanonicalRV.RVSort M) =>
      rvAppend ab.1 ab.2) := by
  intro a b he
  apply Prod.ext
  · funext i
    simpa only [rvAppend, Fin.append_left] using congrFun he (Fin.castAdd m i)
  · funext j
    simpa only [rvAppend, Fin.append_right] using congrFun he (Fin.natAdd n j)

theorem rvAppend_split (t : Fin (n + m) → CanonicalRV.RVSort M) :
    rvAppend (t ∘ Fin.castAdd m) (t ∘ Fin.natAdd n) = t :=
  Fin.append_castAdd_natAdd

def rvAppendMap (S : Set M) (n m : ℕ) :
    Map (DefSet.univ ((rawRVSpace (M := M) n).prod (rawRVSpace m)) S)
      (DefSet.univ (rawRVSpace (n + m)) S) := by
  let P := (rawRVSpace (M := M) n).prod (rawRVSpace m)
  let F (z : P.Index → M) : Fin (n + m) → M :=
    Fin.append (z ∘ Sum.inl) (z ∘ Sum.inr)
  have hcode (c : P.domain) :
      rvValues (rvAppend (P.decode c).1 (P.decode c).2) = F c.val := by
    have hl := rvValues_decode (M := M) (n := n) ⟨c.val ∘ Sum.inl, c.property.1⟩
    have hr := rvValues_decode (M := M) (n := m) ⟨c.val ∘ Sum.inr, c.property.2⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [P, Space.prod, rvValues, rvAppend, F, Fin.append_left] using congrFun hl j
    · simpa only [P, Space.prod, rvValues, rvAppend, F, Fin.append_right] using congrFun hr j
  refine Map.ofCodes _ (fun ab => rvAppend ab.1 ab.2) F ?_
    (fun c => ⟨rvAppend (P.decode c).1 (P.decode c).2, hcode c⟩) ?_
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [F, Fin.append_left, Function.comp_apply]
      exact Set.DefinableFun.proj LRV
    · simp only [F, Fin.append_right, Function.comp_apply]
      exact Set.DefinableFun.proj LRV
  · intro c
    apply rvValues_injective
    exact (rvValues_decode _).trans (hcode c).symm

@[simp] theorem rvAppendMap_apply (S : Set M)
    (a : DefSet.univ ((rawRVSpace (M := M) n).prod (rawRVSpace m)) S) :
    (rvAppendMap S n m a).val = rvAppend a.val.1 a.val.2 := rfl

theorem rvAppendMap_bijective (S : Set M) (n m : ℕ) :
    Function.Bijective (rvAppendMap (M := M) S n m) := by
  constructor
  · intro a b he
    exact Subtype.ext (rvAppend_injective (congrArg Subtype.val he))
  · intro t
    refine ⟨⟨(t.val ∘ Fin.castAdd m, t.val ∘ Fin.natAdd n), Set.mem_univ _⟩, ?_⟩
    exact Subtype.ext (rvAppend_split t.val)

theorem rvWeight_append (a : Fin n → CanonicalRV.RVSort M)
    (b : Fin m → CanonicalRV.RVSort M) :
    rvWeight (rvAppend a b) = rvWeight a + rvWeight b := by
  unfold rvWeight
  rw [Fin.sum_univ_add]
  simp only [rvAppend, Fin.append_left, Fin.append_right]

end SpecialTransformations.Section4

end
