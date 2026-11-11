import Section3.Barycentre
import Section3.BallGeometry
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Barycentre
open Balls
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem mean_sub_eq (h00 : M ⊨ Axioms.ACVF00) (A : Finset (VFType (M := M)))
    (hne : A.Nonempty) (a : VFType (M := M)) :
    mean A - a = (∑ x ∈ A, (x - a)) / (A.card : VFType (M := M)) := by
  have hn := natCast_ne_zero h00 A.card (Finset.card_ne_zero.mpr hne)
  simp only [mean, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp [hn]

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv

theorem natCast_value_one (h00 : M ⊨ Axioms.ACVF00) (k : ℕ) (hk : k ≠ 0) :
    v (k : VFType (M := M)) = 1 := by
  have hl : v (k : VFType (M := M)) ≤ v 1 := (hv _ _).mp (by
    change iLe (Average.val (1 : VFType (M := M))) (Average.val (k : VFType (M := M)))
    rw [Average.val_one]
    exact Average.le_one_natCast k)
  have hr : v 1 ≤ v (k : VFType (M := M)) := (hv _ _).mp (by
    change iLe (Average.val (k : VFType (M := M))) (Average.val (1 : VFType (M := M)))
    rw [Average.val_one]
    exact Average.nat_unit h00 k hk)
  simpa only [map_one] using le_antisymm hl hr

theorem mean_mem_closedDisc (h00 : M ⊨ Axioms.ACVF00)
    (A : Finset (VFType (M := M))) (hne : A.Nonempty)
    (a : VFType (M := M)) (r : Radius Γ) (hA : ∀ x ∈ A, x ∈ closedDisc v a r) :
    mean A ∈ closedDisc v a r := by
  cases r with
  | none => trivial
  | some γ =>
    change v (mean A - a) ≤ OrderDual.ofDual γ
    rw [mean_sub_eq h00 A hne a, map_div₀,
      natCast_value_one v hv h00 A.card (Finset.card_ne_zero.mpr hne), div_one]
    exact v.map_sum_le hA

theorem mean_mem_openDisc (h00 : M ⊨ Axioms.ACVF00)
    (A : Finset (VFType (M := M))) (hne : A.Nonempty)
    (a : VFType (M := M)) (r : OpenRadius Γ) (hA : ∀ x ∈ A, x ∈ openDisc v a r) :
    mean A ∈ openDisc v a r := by
  change v (mean A - a) < (OrderDual.ofDual r : Γˣ).val
  rw [mean_sub_eq h00 A hne a, map_div₀,
    natCast_value_one v hv h00 A.card (Finset.card_ne_zero.mpr hne), div_one]
  exact v.map_sum_lt (Units.ne_zero _) hA

end SpecialTransformations.Section3.Barycentre
