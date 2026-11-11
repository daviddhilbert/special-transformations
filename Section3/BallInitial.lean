import Section3.RadialBalls
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Balls
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

theorem closedDisc_zero_downward (a : K) (ρ : Radius Γ)
    (hz : (0 : K) ∈ closedDisc v a ρ) {x y : K}
    (hx : x ∈ closedDisc v a ρ) (hxy : v y ≤ v x) : y ∈ closedDisc v a ρ := by
  cases ρ with
  | none => trivial
  | some γ =>
    have ha : v a ≤ OrderDual.ofDual γ := by
      change v (0 - a) ≤ OrderDual.ofDual γ at hz
      simpa only [zero_sub, Valuation.map_neg] using hz
    have hx' : v x ≤ OrderDual.ofDual γ := by
      have he : x = (x - a) + a := by ring
      rw [he]
      exact v.map_add_le hx ha
    exact v.map_sub_le (hxy.trans hx') ha

theorem openDisc_zero_downward (a : K) (ρ : OpenRadius Γ)
    (hz : (0 : K) ∈ openDisc v a ρ) {x y : K}
    (hx : x ∈ openDisc v a ρ) (hxy : v y ≤ v x) : y ∈ openDisc v a ρ := by
  have ha : v a < (OrderDual.ofDual ρ : Γˣ).val := by
    change v (0 - a) < (OrderDual.ofDual ρ : Γˣ).val at hz
    simpa only [zero_sub, Valuation.map_neg] using hz
  have hx' : v x < (OrderDual.ofDual ρ : Γˣ).val := by
    have he : x = (x - a) + a := by ring
    rw [he]
    exact v.map_add_lt hx ha
  exact v.map_sub_lt (lt_of_le_of_lt hxy hx') ha

end SpecialTransformations.Section3.Balls
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv

theorem ball_zero_downward (B : Set M) (hB : IsBall B)
    (hz : (0 : VFType (M := M)).val ∈ B)
    {x y : VFType (M := M)} (hx : x.val ∈ B) (hxy : v y ≤ v x) : y.val ∈ B := by
  obtain ⟨a, ⟨ρ, he⟩ | ⟨ρ, he⟩⟩ := encodedBall_disc v hv B hB
  · exact (Set.ext_iff.mp he y).mpr (Balls.openDisc_zero_downward v a ρ
      ((Set.ext_iff.mp he 0).mp hz) ((Set.ext_iff.mp he x).mp hx) hxy)
  · exact (Set.ext_iff.mp he y).mpr (Balls.closedDisc_zero_downward v a ρ
      ((Set.ext_iff.mp he 0).mp hz) ((Set.ext_iff.mp he x).mp hx) hxy)
end SpecialTransformations.Section3
