module

public import Section3.BallGeometry

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Balls
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

include hv in
theorem rv_eq_of_sub_lt (x a : VFType (M := M)) (ha : a ≠ 0)
    (h : v (x - a) < v a) : iRv x.val = iRv a.val := by
  apply (CanonicalRV.encoded_eq_iff_close x.property a.property
    (fun he => ha (Subtype.ext he))).mpr
  intro hle
  exact (not_le_of_gt h) ((hv a (x - a)).mp hle)

include hv in
theorem closedDisc_rv_constant (a : VFType (M := M)) (r : Radius Γ)
    (hzero : (0 : VFType (M := M)) ∉ closedDisc v a r)
    (x : VFType (M := M)) (hx : x ∈ closedDisc v a r) : iRv x.val = iRv a.val := by
  have ha : a ≠ 0 := by
    intro h
    exact hzero (h ▸ centre_mem_closedDisc v a r)
  apply rv_eq_of_sub_lt v hv x a ha
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

include hv in
theorem openDisc_rv_constant (a : VFType (M := M)) (r : OpenRadius Γ)
    (hzero : (0 : VFType (M := M)) ∉ openDisc v a r)
    (x : VFType (M := M)) (hx : x ∈ openDisc v a r) : iRv x.val = iRv a.val := by
  have ha : a ≠ 0 := by
    intro h
    exact hzero (h ▸ centre_mem_openDisc v a r)
  have hγa : (OrderDual.ofDual r : Γˣ).val ≤ v a := by
    apply le_of_not_gt
    intro h
    apply hzero
    change v (0 - a) < (OrderDual.ofDual r : Γˣ).val
    simpa only [zero_sub, Valuation.map_neg] using h
  exact rv_eq_of_sub_lt v hv x a ha (lt_of_lt_of_le hx hγa)

end SpecialTransformations.Section3.Balls
