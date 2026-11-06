import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Set.Basic

open Classical

noncomputable section

namespace SpecialTransformations.Section4.FiniteOrder

variable {α : Type*} [LinearOrder α]

local instance : DecidableEq α := Classical.decEq α

def Pattern (F : Finset α) (x y : α) : Prop :=
  ∀ a ∈ F, (x < a ↔ y < a) ∧ (a < x ↔ a < y)

def Controls (F : Finset α) (D : Set α) : Prop :=
  ∀ x y, Pattern F x y → (x ∈ D ↔ y ∈ D)

theorem Pattern.symm {F : Finset α} {x y : α} (h : Pattern F x y) : Pattern F y x :=
  fun a ha => ⟨(h a ha).1.symm, (h a ha).2.symm⟩

theorem Pattern.trans {F : Finset α} {x y z : α}
    (h : Pattern F x y) (g : Pattern F y z) : Pattern F x z :=
  fun a ha => ⟨(h a ha).1.trans (g a ha).1, (h a ha).2.trans (g a ha).2⟩

theorem Pattern.between {F : Finset α} {x y z : α} (h : Pattern F x y)
    (hxz : x ≤ z) (hzy : z ≤ y) : Pattern F x z := by
  intro a ha
  constructor
  · exact ⟨fun hx => lt_of_le_of_lt hzy ((h a ha).1.mp hx),
      fun hz => lt_of_le_of_lt hxz hz⟩
  · exact ⟨fun hx => lt_of_lt_of_le hx hxz,
      fun hz => (h a ha).2.mpr (lt_of_lt_of_le hz hzy)⟩

theorem Pattern.restore {F : Finset α} {a x y : α} (h : Pattern (F.erase a) x y)
    (ha : (x < a ↔ y < a) ∧ (a < x ↔ a < y)) : Pattern F x y := by
  intro b hb
  by_cases hba : b = a
  · simpa only [hba] using ha
  · exact h b (Finset.mem_erase.mpr ⟨hba, hb⟩)

variable [NoMinOrder α] [NoMaxOrder α]

theorem finite_gap (F : Finset α) (a : α) : a ∉ F →
    ∃ l u, l < a ∧ a < u ∧ ∀ b ∈ F, b ≤ l ∨ u ≤ b := by
  induction F using Finset.induction_on with
  | empty =>
    intro _
    obtain ⟨l, hl⟩ := exists_lt a
    obtain ⟨u, hu⟩ := exists_gt a
    exact ⟨l, u, hl, hu, by simp⟩
  | @insert b F hb ih =>
    intro ha
    have haF : a ∉ F := fun h => ha (Finset.mem_insert_of_mem h)
    have hba : b ≠ a := by
      intro he
      subst b
      exact ha (Finset.mem_insert_self a F)
    obtain ⟨l, u, hl, hu, hgap⟩ := ih haF
    rcases lt_or_gt_of_ne hba with hbl | hbu
    · refine ⟨max l b, u, max_lt hl hbl, hu, ?_⟩
      intro c hc
      rcases Finset.mem_insert.mp hc with hcb | hc
      · subst c
        exact Or.inl (le_max_right l b)
      · exact (hgap c hc).elim (fun h => Or.inl (h.trans (le_max_left l b))) Or.inr
    · refine ⟨l, min u b, hl, lt_min hu hbu, ?_⟩
      intro c hc
      rcases Finset.mem_insert.mp hc with hcb | hc
      · subst c
        exact Or.inr (min_le_right u b)
      · exact (hgap c hc).elim Or.inl (fun h => Or.inr ((min_le_left u b).trans h))

theorem local_constant_of_missing {F : Finset α} {D : Set α} (hF : Controls F D)
    {a : α} (ha : a ∉ F) :
    ∃ l u, l < a ∧ a < u ∧ ∀ z, l < z → z < u → (z ∈ D ↔ a ∈ D) := by
  obtain ⟨l, u, hl, hu, hgap⟩ := finite_gap F a ha
  refine ⟨l, u, hl, hu, ?_⟩
  intro z hlz hzu
  apply hF z a
  intro b hb
  rcases hgap b hb with hbl | hub
  · have hbz := lt_of_le_of_lt hbl hlz
    have hba := lt_of_le_of_lt hbl hl
    exact ⟨iff_of_false (not_lt.mpr hbz.le) (not_lt.mpr hba.le), iff_of_true hbz hba⟩
  · have hzb := lt_of_lt_of_le hzu hub
    have hab := lt_of_lt_of_le hu hub
    exact ⟨iff_of_true hzb hab, iff_of_false (not_lt.mpr hzb.le) (not_lt.mpr hab.le)⟩

variable [DenselyOrdered α]

theorem erase_controls_ordered {F : Finset α} {D : Set α} (hF : Controls F D)
    {a l u : α} (hl : l < a) (hu : a < u)
    (hloc : ∀ z, l < z → z < u → (z ∈ D ↔ a ∈ D))
    (x y : α) (hxy : x ≤ y) (h : Pattern (F.erase a) x y) : x ∈ D ↔ y ∈ D := by
  by_cases hya : y < a
  · have hxa := lt_of_le_of_lt hxy hya
    exact hF x y (h.restore ⟨iff_of_true hxa hya,
      iff_of_false (not_lt.mpr hxa.le) (not_lt.mpr hya.le)⟩)
  by_cases hax : a < x
  · have hay := lt_of_lt_of_le hax hxy
    exact hF x y (h.restore ⟨iff_of_false (not_lt.mpr hax.le) (not_lt.mpr hay.le),
      iff_of_true hax hay⟩)
  have hxa : x ≤ a := le_of_not_gt hax
  have hay : a ≤ y := le_of_not_gt hya
  have hx : x ∈ D ↔ a ∈ D := by
    by_cases he : x = a
    · subst x; exact Iff.rfl
    have hxa' : x < a := lt_of_le_of_ne hxa he
    obtain ⟨p, hp, hpa⟩ := exists_between (max_lt hxa' hl)
    have hxp : x < p := lt_of_le_of_lt (le_max_left x l) hp
    have hlp : l < p := lt_of_le_of_lt (le_max_right x l) hp
    have hpu : p < u := hpa.trans hu
    have hpat := h.between hxp.le (hpa.le.trans hay)
    exact (hF x p (hpat.restore ⟨iff_of_true hxa' hpa,
      iff_of_false (not_lt.mpr hxa'.le) (not_lt.mpr hpa.le)⟩)).trans (hloc p hlp hpu)
  have hy : y ∈ D ↔ a ∈ D := by
    by_cases he : y = a
    · subst y; exact Iff.rfl
    have hay' : a < y := lt_of_le_of_ne hay (Ne.symm he)
    obtain ⟨q, haq, hq⟩ := exists_between (lt_min hay' hu)
    have hqy : q < y := lt_of_lt_of_le hq (min_le_left y u)
    have hqu : q < u := lt_of_lt_of_le hq (min_le_right y u)
    have hlq : l < q := hl.trans haq
    have hxq := h.between (hxa.trans haq.le) hqy.le
    have hpat := h.symm.trans hxq
    exact (hF y q (hpat.restore ⟨iff_of_false (not_lt.mpr hay'.le) (not_lt.mpr haq.le),
      iff_of_true hay' haq⟩)).trans (hloc q hlq hqu)
  exact hx.trans hy.symm

theorem erase_controls_of_local {F : Finset α} {D : Set α} (hF : Controls F D)
    {a l u : α} (hl : l < a) (hu : a < u)
    (hloc : ∀ z, l < z → z < u → (z ∈ D ↔ a ∈ D)) : Controls (F.erase a) D := by
  intro x y h
  rcases le_total x y with hxy | hyx
  · exact erase_controls_ordered hF hl hu hloc x y hxy h
  · exact (erase_controls_ordered hF hl hu hloc y x hyx h.symm).symm

/-- Minimal finite order controllers are contained in every controller.
This makes their endpoints canonical, even in a non-Dedekind-complete group. -/
theorem minimal_controller_subset {F G : Finset α} {D : Set α}
    (hF : Controls F D) (hmin : ∀ H, Controls H D → F.card ≤ H.card)
    (hG : Controls G D) : F ⊆ G := by
  intro a ha
  by_contra hnot
  obtain ⟨l, u, hl, hu, hloc⟩ := local_constant_of_missing hG hnot
  have he := erase_controls_of_local hF hl hu hloc
  have hstrict : F.erase a ⊂ F := by
    refine ⟨Finset.erase_subset a F, ?_⟩
    intro hback
    exact (Finset.mem_erase.mp (hback ha)).1 rfl
  exact (not_le_of_gt (Finset.card_lt_card hstrict)) (hmin _ he)

theorem minimal_controller_unique {F G : Finset α} {D : Set α}
    (hF : Controls F D) (hG : Controls G D)
    (hminF : ∀ H, Controls H D → F.card ≤ H.card)
    (hminG : ∀ H, Controls H D → G.card ≤ H.card) : F = G :=
  Finset.Subset.antisymm (minimal_controller_subset hF hminF hG)
    (minimal_controller_subset hG hminG hF)

end SpecialTransformations.Section4.FiniteOrder

end
