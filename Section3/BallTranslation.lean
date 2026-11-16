module

public import Section3.DiscCentres

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Balls
section General
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem sub_mem_closedDisc_iff (v : Valuation K Γ) (a c x : K) (r : Radius Γ) :
    x - c ∈ closedDisc v (a - c) r ↔ x ∈ closedDisc v a r := by
  have hd : (x - c) - (a - c) = x - a := by abel
  cases r with
  | none => rfl
  | some γ =>
    change v ((x - c) - (a - c)) ≤ OrderDual.ofDual γ ↔ v (x - a) ≤ OrderDual.ofDual γ
    rw [hd]

theorem sub_mem_openDisc_iff (v : Valuation K Γ) (a c x : K) (r : OpenRadius Γ) :
    x - c ∈ openDisc v (a - c) r ↔ x ∈ openDisc v a r := by
  have hd : (x - c) - (a - c) = x - a := by abel
  change v ((x - c) - (a - c)) < (OrderDual.ofDual r : Γˣ).val ↔
    v (x - a) < (OrderDual.ofDual r : Γˣ).val
  rw [hd]

end General

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

include hv in
theorem rv_sub_constant_openDisc (a c : VFType (M := M)) (r : OpenRadius Γ)
    (hc : c ∉ openDisc v a r) (x y : VFType (M := M))
    (hx : x ∈ openDisc v a r) (hy : y ∈ openDisc v a r) :
    iRv (x - c).val = iRv (y - c).val := by
  have hz : (0 : VFType (M := M)) ∉ openDisc v (a - c) r := by
    intro h
    apply hc
    apply (sub_mem_openDisc_iff v a c c r).mp
    simpa only [sub_self] using h
  exact (openDisc_rv_constant v hv (a - c) r hz (x - c)
    ((sub_mem_openDisc_iff v a c x r).mpr hx)).trans
      (openDisc_rv_constant v hv (a - c) r hz (y - c)
        ((sub_mem_openDisc_iff v a c y r).mpr hy)).symm

include hv in
theorem rv_sub_constant_closedDisc (a c : VFType (M := M)) (r : Radius Γ)
    (hc : c ∉ closedDisc v a r) (x y : VFType (M := M))
    (hx : x ∈ closedDisc v a r) (hy : y ∈ closedDisc v a r) :
    iRv (x - c).val = iRv (y - c).val := by
  have hz : (0 : VFType (M := M)) ∉ closedDisc v (a - c) r := by
    intro h
    apply hc
    apply (sub_mem_closedDisc_iff v a c c r).mp
    simpa only [sub_self] using h
  exact (closedDisc_rv_constant v hv (a - c) r hz (x - c)
    ((sub_mem_closedDisc_iff v a c x r).mpr hx)).trans
      (closedDisc_rv_constant v hv (a - c) r hz (y - c)
        ((sub_mem_closedDisc_iff v a c y r).mpr hy)).symm

end SpecialTransformations.Section3.Balls
