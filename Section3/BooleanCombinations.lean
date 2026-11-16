module

public import Enc

@[expose] public section
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.BooleanCombinations
variable {M : Type} {B : Set (Set M)}

theorem empty : IsBoolComb B (∅ : Set M) := by
  simpa using (IsBoolComb.univ (B := B)).compl

theorem inter {s t : Set M} (hs : IsBoolComb B s) (ht : IsBoolComb B t) :
    IsBoolComb B (s ∩ t) := by
  simpa only [Set.compl_union, compl_compl] using (hs.compl.union ht.compl).compl

theorem finite_iUnion {ι : Type} (s : Finset ι) (f : ι → Set M)
    (hf : ∀ i ∈ s, IsBoolComb B (f i)) : IsBoolComb B (⋃ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (empty (B := B))
  | @insert a s ha ih =>
    simpa only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left] using
      (hf a (Finset.mem_insert_self a s)).union
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem iUnion {ι : Type} [Fintype ι] (f : ι → Set M)
    (hf : ∀ i, IsBoolComb B (f i)) : IsBoolComb B (⋃ i, f i) := by
  simpa using finite_iUnion Finset.univ f (fun i _ => hf i)

theorem iInter {ι : Type} [Fintype ι] (f : ι → Set M)
    (hf : ∀ i, IsBoolComb B (f i)) : IsBoolComb B (⋂ i, f i) := by
  simpa only [Set.compl_iUnion, compl_compl] using
    (iUnion (fun i => (f i)ᶜ) (fun i => (hf i).compl)).compl

theorem boolean {ι : Type} [Fintype ι] (b : ι → Set M)
    (hb : ∀ i, IsBoolComb B (b i)) (t : Set ι → Bool) :
    IsBoolComb B {x | t {i | x ∈ b i} = true} := by
  classical
  let C (s : Set ι) : Set M := ⋂ i, if i ∈ s then b i else (b i)ᶜ
  have hC (s : Set ι) : IsBoolComb B (C s) := by
    apply iInter
    intro i
    split_ifs
    · exact hb i
    · exact (hb i).compl
  have he : {x | t {i | x ∈ b i} = true} =
      ⋃ s : {s : Set ι // t s = true}, C s.val := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hx
      refine ⟨⟨{i | x ∈ b i}, hx⟩, ?_⟩
      apply Set.mem_iInter.mpr
      intro i
      by_cases hi : x ∈ b i <;> simp [hi]
    · rintro ⟨s, hs⟩
      have heq : {i | x ∈ b i} = s.val := by
        ext i
        have hi := Set.mem_iInter.mp hs i
        change x ∈ (if i ∈ s.val then b i else (b i)ᶜ) at hi
        by_cases his : i ∈ s.val
        · simpa [his] using hi
        · simpa [his] using hi
      rw [heq]
      exact s.property
  rw [he]
  exact iUnion _ (fun s => hC s.val)

end SpecialTransformations.Section3.BooleanCombinations
