module

public import Section4.CanonicalOrderController
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

open Classical

noncomputable section

namespace SpecialTransformations.Section4.FiniteOrder

variable {α : Type*} [LinearOrder α]

def TupleControls {n : ℕ} (c : Fin n → α) (A : Set α) : Prop :=
  ∀ x y, (∀ i, (x < c i ↔ y < c i) ∧ (c i < x ↔ c i < y)) → (x ∈ A ↔ y ∈ A)

theorem tupleControls_iff {n : ℕ} (c : Fin n → α) (A : Set α) :
    TupleControls c A ↔ Controls (Finset.univ.image c) A := by
  constructor
  · intro h x y hp
    exact h x y (fun i => hp (c i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  · intro h x y hp
    apply h x y
    rintro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hp i

theorem exists_controller_tuple (F : Finset α) :
    ∃ c : Fin F.card → α, Finset.univ.image c = F := by
  let e := F.equivFin.symm
  let c (i : Fin F.card) : α := (e i).val
  refine ⟨c, ?_⟩
  ext a
  constructor
  · rintro ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact (e i).property
  · intro ha
    refine Finset.mem_image.mpr ⟨e.symm ⟨a, ha⟩, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)

variable [NoMinOrder α] [NoMaxOrder α] [DenselyOrdered α]

/-- The formula saying that n cuts control A need not name the endpoint
set. At its least possible length every such tuple enumerates that set. -/
theorem minimal_controller_tuple_range {F : Finset α} {A : Set α}
    (hF : Controls F A) (hmin : ∀ H, Controls H A → F.card ≤ H.card)
    (c : Fin F.card → α) (hc : TupleControls c A) : Finset.univ.image c = F := by
  have hG := (tupleControls_iff c A).mp hc
  have hFG := minimal_controller_subset hF hmin hG
  symm
  apply Finset.eq_of_subset_of_card_le hFG
  exact (Finset.card_image_le).trans (by simp)

theorem minimal_controller_mem_iff_tuple {F : Finset α} {A : Set α}
    (hF : Controls F A) (hmin : ∀ H, Controls H A → F.card ≤ H.card) (a : α) :
    a ∈ F ↔ ∃ c : Fin F.card → α, TupleControls c A ∧ ∃ i, c i = a := by
  constructor
  · intro ha
    obtain ⟨c, hc⟩ := exists_controller_tuple F
    refine ⟨c, (tupleControls_iff c A).mpr (hc.symm ▸ hF), ?_⟩
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hc.symm ▸ ha)
    exact ⟨i, hi⟩
  · rintro ⟨c, hc, i, rfl⟩
    rw [← minimal_controller_tuple_range hF hmin c hc]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

end SpecialTransformations.Section4.FiniteOrder

end
