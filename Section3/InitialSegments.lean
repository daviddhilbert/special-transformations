module

public import Mathlib

@[expose] public section
open Classical
namespace SpecialTransformations.Section3.InitialSegments
variable {α β : Type} [LinearOrder β] (f : α → β)

def IsInitial (B : Set α) : Prop := ∀ ⦃x y⦄, x ∈ B → f y ≤ f x → y ∈ B

theorem nested {B C : Set α} (hB : IsInitial f B) (hC : IsInitial f C) :
    B ⊆ C ∨ C ⊆ B := by
  by_cases h : B ⊆ C
  · exact Or.inl h
  · right
    obtain ⟨b, hb, hbc⟩ := Set.not_subset.mp h
    intro c hc
    have hcb : f c ≤ f b := le_of_not_gt (fun hh => hbc (hC hc hh.le))
    exact hB hb hcb

/-- A proper initial set whose membership is determined by finitely many
nonempty initial sets is one of those sets. -/
theorem eq_basis (F : Finset (Set α)) (A : Set α) (a₀ : α)
    (hF : ∀ B ∈ F, IsInitial f B ∧ a₀ ∈ B)
    (hA : IsInitial f A) (ha₀ : a₀ ∈ A)
    (hdet : ∀ x y, (∀ B ∈ F, x ∈ B ↔ y ∈ B) → (x ∈ A ↔ y ∈ A))
    (hproper : A ≠ Set.univ) : ∃ B ∈ F, A = B := by
  have hcover (x : α) (hx : x ∈ A) : ∃ B ∈ F, x ∈ B ∧ B ⊆ A := by
    by_cases hsome : ∃ B ∈ F, x ∈ B
    · let G : Set (Set α) := {B | B ∈ F ∧ x ∈ B}
      have hfin : G.Finite := F.finite_toSet.subset (fun _ h => h.1)
      have hne : G.Nonempty := by
        obtain ⟨B, hB, hxB⟩ := hsome
        exact ⟨B, hB, hxB⟩
      obtain ⟨B, hB, hmin⟩ := hfin.exists_minimal hne
      refine ⟨B, hB.1, hB.2, ?_⟩
      intro y hy
      by_cases hyx : f y ≤ f x
      · exact hA hx hyx
      · apply (hdet x y ?_).mp hx
        intro C hC
        constructor
        · intro hxC
          rcases nested f (hF B hB.1).1 (hF C hC).1 with hBC | hCB
          · exact hBC hy
          · exact (hmin ⟨hC, hxC⟩ hCB) hy
        · intro hyC
          exact (hF C hC).1 hyC (le_of_not_ge hyx)
    · have hxnone : ∀ B ∈ F, x ∉ B := by simpa only [not_exists, not_and] using hsome
      apply False.elim
      apply hproper
      apply Set.eq_univ_of_forall
      intro y
      by_cases hyx : f y ≤ f x
      · exact hA hx hyx
      · apply (hdet x y ?_).mp hx
        intro B hB
        exact iff_of_false (hxnone B hB) (fun hyB => hxnone B hB ((hF B hB).1 hyB (le_of_not_ge hyx)))
  obtain ⟨B₀, hB₀, _, hB₀A⟩ := hcover a₀ ha₀
  let G : Set (Set α) := {B | B ∈ F ∧ B ⊆ A}
  have hfin : G.Finite := F.finite_toSet.subset (fun _ h => h.1)
  obtain ⟨B, hB, hmax⟩ := hfin.exists_maximal ⟨B₀, hB₀, hB₀A⟩
  refine ⟨B, hB.1, Set.Subset.antisymm ?_ hB.2⟩
  intro x hx
  obtain ⟨C, hC, hxC, hCA⟩ := hcover x hx
  rcases nested f (hF B hB.1).1 (hF C hC).1 with hBC | hCB
  · exact (hmax ⟨hC, hCA⟩ hBC) hxC
  · exact hCB hxC

end SpecialTransformations.Section3.InitialSegments
