module

public import Section4.FiniteOrderControllers
public import Mathlib.Data.Nat.Find

@[expose] public section

open Classical

noncomputable section

namespace SpecialTransformations.Section4.FiniteOrder

variable {α : Type*} [LinearOrder α]

theorem exists_minimal_controller {D : Set α} (hD : ∃ F, Controls F D) :
    ∃ F, Controls F D ∧ ∀ H, Controls H D → F.card ≤ H.card := by
  let P (n : ℕ) := ∃ F : Finset α, Controls F D ∧ F.card = n
  have hP : ∃ n, P n := by
    obtain ⟨F, hF⟩ := hD
    exact ⟨F.card, F, hF, rfl⟩
  obtain ⟨F, hF, hcard⟩ := Nat.find_spec hP
  refine ⟨F, hF, ?_⟩
  intro H hH
  rw [hcard]
  exact Nat.find_min' hP ⟨H, hH, rfl⟩

theorem Pattern.map_preimage {F : Finset α} (e : α ≃o α) {x y : α}
    (h : Pattern (F.map e.toEmbedding) x y) : Pattern F (e.symm x) (e.symm y) := by
  intro a ha
  have hm : e a ∈ F.map e.toEmbedding := Finset.mem_map.mpr ⟨a, ha, rfl⟩
  constructor
  · calc
      e.symm x < a ↔ e (e.symm x) < e a := e.lt_iff_lt.symm
      _ ↔ x < e a := by rw [e.apply_symm_apply]
      _ ↔ y < e a := (h (e a) hm).1
      _ ↔ e (e.symm y) < e a := by rw [e.apply_symm_apply]
      _ ↔ e.symm y < a := e.lt_iff_lt
  · calc
      a < e.symm x ↔ e a < e (e.symm x) := e.lt_iff_lt.symm
      _ ↔ e a < x := by rw [e.apply_symm_apply]
      _ ↔ e a < y := (h (e a) hm).2
      _ ↔ e a < e (e.symm y) := by rw [e.apply_symm_apply]
      _ ↔ a < e.symm y := e.lt_iff_lt

theorem controls_map {F : Finset α} {D : Set α} (hF : Controls F D)
    (e : α ≃o α) (hD : ∀ x, e x ∈ D ↔ x ∈ D) : Controls (F.map e.toEmbedding) D := by
  intro x y h
  have hx : x ∈ D ↔ e.symm x ∈ D := by
    simpa only [e.apply_symm_apply] using hD (e.symm x)
  have hy : y ∈ D ↔ e.symm y ∈ D := by
    simpa only [e.apply_symm_apply] using hD (e.symm y)
  exact hx.trans ((hF _ _ (h.map_preimage e)).trans hy.symm)

theorem minimal_map {F : Finset α} {D : Set α}
    (hmin : ∀ H, Controls H D → F.card ≤ H.card)
    (e : α ≃o α) (hD : ∀ x, e x ∈ D ↔ x ∈ D) :
    ∀ H, Controls H D → (F.map e.toEmbedding).card ≤ H.card := by
  intro H hH
  have hi : ∀ x, e.symm x ∈ D ↔ x ∈ D := by
    intro x
    simpa only [e.apply_symm_apply] using (hD (e.symm x)).symm
  simpa only [Finset.card_map] using hmin _ (controls_map hH e.symm hi)

variable [NoMinOrder α] [NoMaxOrder α] [DenselyOrdered α]

theorem exists_unique_minimal_controller {D : Set α} (hD : ∃ F, Controls F D) :
    ∃! F, Controls F D ∧ ∀ H, Controls H D → F.card ≤ H.card := by
  obtain ⟨F, hF, hmin⟩ := exists_minimal_controller hD
  refine ⟨F, ⟨hF, hmin⟩, ?_⟩
  intro G hG
  exact minimal_controller_unique hG.1 hF hG.2 hmin

/-- The finite endpoint set is intrinsic to D; every order automorphism
preserving D preserves its minimal controller, without a completeness assumption. -/
theorem minimal_controller_map_eq {F : Finset α} {D : Set α}
    (hF : Controls F D) (hmin : ∀ H, Controls H D → F.card ≤ H.card)
    (e : α ≃o α) (hD : ∀ x, e x ∈ D ↔ x ∈ D) : F.map e.toEmbedding = F :=
  minimal_controller_unique (controls_map hF e hD) hF (minimal_map hmin e hD) hmin

end SpecialTransformations.Section4.FiniteOrder

end
