import Section8.IsolatedGraph
import Section3.SortedTuples

/-! Fixing the RV radius codes in the graph isolation relation leaves a
definable VF set. Its field of VF parameters is the original one. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] {n m : ℕ}

/-- The raw code of the graph of a total function on the actual VF sorts. -/
def vfGraph (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M))) :
    Set (Fin n ⊕ Fin m → M) :=
  Set.range (fun x => Sum.elim (vfValues x) (vfValues (f x)))

def fixedIsolation (G : Set (Fin n ⊕ Fin m → M)) (t : Fin 2 → M) : Set (Fin n → M) :=
  {a | Sum.elim a t ∈ inputIsolation G}

theorem fixedIsolation_definable {S : Set M} {G : Set (Fin n ⊕ Fin m → M)}
    (hG : S.Definable LRV G) (t : Fin 2 → M) :
    (S ∪ Set.range t).Definable LRV (fixedIsolation G t) := by
  apply ((inputIsolation_definable hG).mono Set.subset_union_left).preimage_map
  intro i
  cases i with
  | inl j => exact Set.DefinableFun.proj LRV
  | inr j =>
    exact LRV.definableFun_const (Fin n) (Or.inr (Set.mem_range_self j))

theorem mem_fixedIsolation_vfGraph_iff
    (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (a : Fin n → VFType (M := M)) (t : Fin 2 → M) :
    vfValues a ∈ fixedIsolation (vfGraph f) t ↔
      Sum.elim (Sum.elim (vfValues a) (vfValues (f a))) t ∈ graphIsolation (vfGraph f) := by
  change Sum.elim (vfValues a) t ∈ inputIsolation (vfGraph f) ↔ _
  rw [mem_inputIsolation_iff]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨b, hb⟩ := hy.1
    have hba : b = a := vfValues_injective (funext (fun i => congrFun hb (.inl i)))
    subst b
    have he : vfValues (f a) = y := funext (fun i => congrFun hb (.inr i))
    rwa [← he] at hy
  · exact fun h => ⟨_, h⟩

variable [hM : M ⊨ Axioms.ACVF]

theorem fixedIsolation_sorted (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M))}
    (hf : S.Definable LRV (vfGraph f)) (t : Fin 2 → M) :
    DefinableOver (S ∪ Set.range t) (fun _ => .vf) (fixedIsolation (vfGraph f) t) := by
  apply raw_definableOver_sorted hc _ _ _ (fixedIsolation_definable hf t)
  intro a ha i
  obtain ⟨y, hy⟩ := (mem_inputIsolation_iff a t).mp ha
  obtain ⟨b, hb⟩ := hy.1
  have he : (b i).val = a i := congrFun hb (.inl i)
  change iVF (a i)
  rw [← he]
  exact (b i).property

/-- Semantic form of isolation at an actual graph point and two chosen
field representatives. The same predicate works uniformly in both codes. -/
theorem mem_fixedIsolation_iff_unique
    (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (a : Fin n → VFType (M := M)) (r s : VFType (M := M)) (hr : r ≠ 0) (hs : s ≠ 0) :
    vfValues a ∈ fixedIsolation (vfGraph f) ![iRv r.val, iRv s.val] ↔
      ∀ b : Fin n → VFType (M := M),
        vfValues b ∈ uniformBall (vfValues a) r.val →
        vfValues (f b) ∈ uniformBall (vfValues (f a)) s.val → b = a := by
  rw [mem_fixedIsolation_vfGraph_iff]
  constructor
  · intro h b hab hfab
    by_contra hne
    apply h.2.2
    refine ⟨Sum.elim (vfValues b) (vfValues (f b)), ⟨b, rfl⟩, ?_, ?_, ?_⟩
    · exact (rvUniformBall_eq _ r hr).symm ▸ hab
    · exact (rvUniformBall_eq _ s hs).symm ▸ hfab
    · exact fun he => hne (vfValues_injective (funext he))
  · intro h
    refine ⟨⟨a, rfl⟩, ?_, ?_⟩
    · intro j
      fin_cases j
      · exact ⟨rv_mem hM r.property, fun hz => hr ((CanonicalRV.encodedRv_zero_iff r).mp hz)⟩
      · exact ⟨rv_mem hM s.property, fun hz => hs ((CanonicalRV.encodedRv_zero_iff s).mp hz)⟩
    · rintro ⟨w, ⟨b, rfl⟩, hb, hfb, hne⟩
      have he := h b (rvUniformBall_eq _ r hr ▸ hb) (rvUniformBall_eq _ s hs ▸ hfb)
      exact hne (fun i => congrArg (fun x => vfValues x i) he)

end SpecialTransformations.Section8
