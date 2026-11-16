module

public import Section4.CanonicalOrderController
public import Mathlib.Data.Finset.Max

@[expose] public section

open Classical

noncomputable section

namespace SpecialTransformations.Section4.FiniteOrder

variable {α : Type*} [LinearOrder α]

/-- Named endpoints, named points on either side of every endpoint, and
named midpoints suffice to hit every cell of a finite order partition.
No Archimedean or order-completeness hypothesis is used. -/
theorem exists_sample_same_pattern (F : Finset α) (D : Set α)
    (hne : D.Nonempty) (hFD : (F : Set α) ⊆ D)
    (hbelow : ∀ a ∈ D, ∃ b ∈ D, b < a)
    (habove : ∀ a ∈ D, ∃ b ∈ D, a < b)
    (hbetween : ∀ a ∈ D, ∀ b ∈ D, a < b → ∃ c ∈ D, a < c ∧ c < b)
    (x : α) : ∃ y ∈ D, Pattern F x y := by
  by_cases hx : x ∈ F
  · exact ⟨x, hFD hx, fun _ _ => ⟨Iff.rfl, Iff.rfl⟩⟩
  let L := F.filter (· < x)
  let U := F.filter (x < ·)
  have hLU (a : α) (ha : a ∈ F) : a ∈ L ∨ a ∈ U := by
    rcases lt_or_gt_of_ne (show a ≠ x from fun he => hx (he ▸ ha)) with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨ha, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨ha, h⟩)
  have hpat (y : α) (hyL : ∀ a ∈ L, a < y) (hyU : ∀ a ∈ U, y < a) :
      Pattern F x y := by
    intro a ha
    rcases hLU a ha with hl | hu
    · have hax := (Finset.mem_filter.mp hl).2
      have hay := hyL a hl
      exact ⟨iff_of_false (not_lt_of_ge hax.le) (not_lt_of_ge hay.le),
        iff_of_true hax hay⟩
    · have hxa := (Finset.mem_filter.mp hu).2
      have hya := hyU a hu
      exact ⟨iff_of_true hxa hya,
        iff_of_false (not_lt_of_ge hxa.le) (not_lt_of_ge hya.le)⟩
  by_cases hl : L.Nonempty
  · let a := L.max' hl
    have haL : a ∈ L := L.max'_mem hl
    have haD : a ∈ D := hFD (Finset.mem_filter.mp haL).1
    by_cases hu : U.Nonempty
    · let b := U.min' hu
      have hbU : b ∈ U := U.min'_mem hu
      have hbD : b ∈ D := hFD (Finset.mem_filter.mp hbU).1
      have hab : a < b := ((Finset.mem_filter.mp haL).2).trans
        (Finset.mem_filter.mp hbU).2
      obtain ⟨y, hyD, hay, hyb⟩ := hbetween a haD b hbD hab
      exact ⟨y, hyD, hpat y (fun c hc => lt_of_le_of_lt (L.le_max' c hc) hay)
        (fun c hc => lt_of_lt_of_le hyb (U.min'_le c hc))⟩
    · obtain ⟨y, hyD, hay⟩ := habove a haD
      exact ⟨y, hyD, hpat y (fun c hc => lt_of_le_of_lt (L.le_max' c hc) hay)
        (fun c hc => (hu ⟨c, hc⟩).elim)⟩
  · by_cases hu : U.Nonempty
    · let b := U.min' hu
      have hbU : b ∈ U := U.min'_mem hu
      have hbD : b ∈ D := hFD (Finset.mem_filter.mp hbU).1
      obtain ⟨y, hyD, hyb⟩ := hbelow b hbD
      exact ⟨y, hyD, hpat y (fun c hc => (hl ⟨c, hc⟩).elim)
        (fun c hc => lt_of_lt_of_le hyb (U.min'_le c hc))⟩
    · obtain ⟨y, hyD⟩ := hne
      exact ⟨y, hyD, hpat y (fun c hc => (hl ⟨c, hc⟩).elim)
        (fun c hc => (hu ⟨c, hc⟩).elim)⟩

theorem nonempty_inter_of_controls (F : Finset α) (A D : Set α)
    (hA : Controls F A) (hne : A.Nonempty) (hD : D.Nonempty)
    (hFD : (F : Set α) ⊆ D)
    (hbelow : ∀ a ∈ D, ∃ b ∈ D, b < a)
    (habove : ∀ a ∈ D, ∃ b ∈ D, a < b)
    (hbetween : ∀ a ∈ D, ∀ b ∈ D, a < b → ∃ c ∈ D, a < c ∧ c < b) :
    (A ∩ D).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy, hp⟩ := exists_sample_same_pattern F D hD hFD hbelow habove hbetween x
  exact ⟨y, (hA x y hp).mp hx, hy⟩

end SpecialTransformations.Section4.FiniteOrder

end
