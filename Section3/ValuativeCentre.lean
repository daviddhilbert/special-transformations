module

public import Section3.BallGeometry

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical
namespace SpecialTransformations.Section3.Balls
variable {K : Type} [Field K] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

/-- Definition 2.6. Infinity is multiplicative valuation zero in the reversed
order. For nonempty discs avoiding zero the value is independent of the point. -/
noncomputable def valuativeCentre (v : Valuation K Γ) (B : Set K) : OrderDual Γ :=
  if 0 ∈ B then OrderDual.toDual (0 : Γ) else
    if h : B.Nonempty then OrderDual.toDual (v h.choose) else OrderDual.toDual (0 : Γ)

@[simp] theorem valuativeCentre_of_zero_mem (v : Valuation K Γ) (B : Set K)
    (h : 0 ∈ B) : valuativeCentre v B = OrderDual.toDual (0 : Γ) := by
  simp [valuativeCentre, h]

theorem valuativeCentre_of_constant (v : Valuation K Γ) (B : Set K)
    (a : K) (ha : a ∈ B) (hc : ∀ x ∈ B, v x = v a) :
    valuativeCentre v B = OrderDual.toDual (v a) := by
  classical
  by_cases h0 : 0 ∈ B
  · have hz : (0 : Γ) = v a := by simpa only [map_zero] using hc 0 h0
    simp only [valuativeCentre, if_pos h0, hz]
  · have hne : B.Nonempty := ⟨a, ha⟩
    simp only [valuativeCentre, if_neg h0, dif_pos hne, hc hne.choose hne.choose_spec]

theorem closedDisc_value_constant (v : Valuation K Γ) (a : K) (r : Radius Γ)
    (hzero : (0 : K) ∉ closedDisc v a r) (x : K) (hx : x ∈ closedDisc v a r) :
    v x = v a := by
  have hxa : v (x - a) < v a := by
    cases r with
    | none => exact (hzero (Set.mem_univ _)).elim
    | some γ =>
      have hγ : OrderDual.ofDual γ < v a := by
        apply lt_of_not_ge
        intro h
        apply hzero
        change v (0 - a) ≤ OrderDual.ofDual γ
        simpa only [zero_sub, Valuation.map_neg] using h
      exact lt_of_le_of_lt hx hγ
  simpa only [sub_add_cancel] using v.map_add_eq_of_lt_right hxa

theorem openDisc_value_constant (v : Valuation K Γ) (a : K) (r : OpenRadius Γ)
    (hzero : (0 : K) ∉ openDisc v a r) (x : K) (hx : x ∈ openDisc v a r) :
    v x = v a := by
  have hγa : (OrderDual.ofDual r : Γˣ).val ≤ v a := by
    apply le_of_not_gt
    intro h
    apply hzero
    change v (0 - a) < (OrderDual.ofDual r : Γˣ).val
    simpa only [zero_sub, Valuation.map_neg] using h
  simpa only [sub_add_cancel] using v.map_add_eq_of_lt_right (lt_of_lt_of_le hx hγa)

theorem valuativeCentre_closedDisc (v : Valuation K Γ) (a : K) (r : Radius Γ) :
    valuativeCentre v (closedDisc v a r) =
      if (0 : K) ∈ closedDisc v a r then OrderDual.toDual (0 : Γ) else
        OrderDual.toDual (v a) := by
  classical
  split_ifs with h
  · exact valuativeCentre_of_zero_mem v _ h
  · exact valuativeCentre_of_constant v _ a (centre_mem_closedDisc v a r)
      (closedDisc_value_constant v a r h)

theorem valuativeCentre_openDisc (v : Valuation K Γ) (a : K) (r : OpenRadius Γ) :
    valuativeCentre v (openDisc v a r) =
      if (0 : K) ∈ openDisc v a r then OrderDual.toDual (0 : Γ) else
        OrderDual.toDual (v a) := by
  classical
  split_ifs with h
  · exact valuativeCentre_of_zero_mem v _ h
  · exact valuativeCentre_of_constant v _ a (centre_mem_openDisc v a r)
      (openDisc_value_constant v a r h)

end SpecialTransformations.Section3.Balls
