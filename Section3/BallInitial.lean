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

theorem openDisc_zero_downward (a : K) (ρ : Radius Γ)
    (hz : (0 : K) ∈ openDisc v a ρ) {x y : K}
    (hx : x ∈ openDisc v a ρ) (hxy : v y ≤ v x) : y ∈ openDisc v a ρ := by
  cases ρ with
  | none => trivial
  | some γ =>
    by_cases hγ : OrderDual.ofDual γ = 0
    · have heγ : γ = OrderDual.toDual (0 : Γ) := congrArg OrderDual.toDual hγ
      subst γ
      change (0 : K) ∈ openDisc v a (↑(0 : OrderDual Γ)) at hz
      change x ∈ openDisc v a (↑(0 : OrderDual Γ)) at hx
      change y ∈ openDisc v a (↑(0 : OrderDual Γ))
      have hz0 : (0 : K) = a := by simpa only [openDisc_infinity, Set.mem_singleton_iff] using hz
      have ha : a = 0 := hz0.symm
      have hx0 : x = 0 := by simpa only [openDisc_infinity, Set.mem_singleton_iff, ha] using hx
      have hy0 : y = 0 := (map_eq_zero v).mp (le_zero_iff.mp (by simpa only [hx0, map_zero] using hxy))
      simp only [openDisc_infinity, Set.mem_singleton_iff, ha, hy0]
    · have ha : v a < OrderDual.ofDual γ := by
        change (0 : K) ∈ if OrderDual.ofDual γ = 0 then {a} else {z | v (z - a) < OrderDual.ofDual γ} at hz
        rw [if_neg hγ] at hz
        change v (0 - a) < OrderDual.ofDual γ at hz
        simpa only [zero_sub, Valuation.map_neg] using hz
      have hx' : v x < OrderDual.ofDual γ := by
        have hx' : v (x - a) < OrderDual.ofDual γ := by
          simpa only [openDisc, if_neg hγ, Set.mem_ofPred_eq] using hx
        have he : x = (x - a) + a := by ring
        rw [he]
        exact v.map_add_lt hx' ha
      change y ∈ if OrderDual.ofDual γ = 0 then {a} else {z | v (z - a) < OrderDual.ofDual γ}
      rw [if_neg hγ]
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
  obtain ⟨a, ρ, he | he⟩ := encodedBall_disc v hv B hB
  · exact (Set.ext_iff.mp he y).mpr (Balls.openDisc_zero_downward v a ρ
      ((Set.ext_iff.mp he 0).mp hz) ((Set.ext_iff.mp he x).mp hx) hxy)
  · exact (Set.ext_iff.mp he y).mpr (Balls.closedDisc_zero_downward v a ρ
      ((Set.ext_iff.mp he 0).mp hz) ((Set.ext_iff.mp he x).mp hx) hxy)
end SpecialTransformations.Section3
