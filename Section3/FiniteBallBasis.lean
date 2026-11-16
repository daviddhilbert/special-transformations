module

public import Section3.BooleanCombinations

@[expose] public section
open Classical
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.BooleanCombinations
variable {α : Type} {B : Set (Set α)} {A : Set α}

/-- A Boolean combination has a finite ball basis determining membership.
The basis is mathematical data, not a list of newly named parameters. -/
theorem finite_basis (hA : IsBoolComb B A) :
    ∃ F : Finset (Set α), (∀ C ∈ F, C ∈ B) ∧
      ∀ x y, (∀ C ∈ F, (x ∈ C ↔ y ∈ C)) → (x ∈ A ↔ y ∈ A) := by
  induction hA with
  | @basic C hC =>
    exact ⟨{C}, (by intro D hD; have he := Finset.mem_singleton.mp hD; exact he.symm ▸ hC),
      fun x y hxy => hxy C (Finset.mem_singleton_self C)⟩
  | univ => exact ⟨∅, (fun C hC => False.elim (Finset.notMem_empty C hC)), fun _ _ _ => Iff.rfl⟩
  | compl h ih =>
    obtain ⟨F, hF, hd⟩ := ih
    exact ⟨F, hF, fun x y hxy => not_congr (hd x y hxy)⟩
  | union h h' ih ih' =>
    obtain ⟨F, hF, hd⟩ := ih
    obtain ⟨G, hG, hd'⟩ := ih'
    refine ⟨F ∪ G, ?_, ?_⟩
    · intro C hC
      exact (Finset.mem_union.mp hC).elim (hF C) (hG C)
    · intro x y hxy
      exact or_congr (hd x y (fun C hC => hxy C (Finset.mem_union_left G hC)))
        (hd' x y (fun C hC => hxy C (Finset.mem_union_right F hC)))

end SpecialTransformations.Section3.BooleanCombinations
