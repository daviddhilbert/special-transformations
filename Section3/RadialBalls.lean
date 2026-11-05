import Section3.EncodedBallGeometry
import Section3.DiscCentres
set_option backward.isDefEq.respectTransparency false
open Classical
namespace SpecialTransformations.Section3.Balls
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

theorem closedDisc_zero_radial (a : K) (ρ : Radius Γ) (hz : (0 : K) ∈ closedDisc v a ρ)
    (x y : K) (hxy : v x = v y) : x ∈ closedDisc v a ρ ↔ y ∈ closedDisc v a ρ := by
  cases ρ with
  | none => exact Iff.rfl
  | some γ =>
    have ha : v a ≤ OrderDual.ofDual γ := by
      change v (0 - a) ≤ OrderDual.ofDual γ at hz
      simpa only [zero_sub, Valuation.map_neg] using hz
    have he (z : K) : z ∈ closedDisc v a (↑γ) ↔ v z ≤ OrderDual.ofDual γ := by
      change v (z - a) ≤ OrderDual.ofDual γ ↔ _
      constructor
      · intro h
        have hz : z = (z - a) + a := by ring
        rw [hz]
        exact v.map_add_le h ha
      · intro h
        exact v.map_sub_le h ha
    change x ∈ closedDisc v a (↑γ) ↔ y ∈ closedDisc v a (↑γ)
    rw [he x, he y, hxy]

theorem openDisc_zero_radial (a : K) (ρ : Radius Γ) (hz : (0 : K) ∈ openDisc v a ρ)
    (x y : K) (hxy : v x = v y) : x ∈ openDisc v a ρ ↔ y ∈ openDisc v a ρ := by
  cases ρ with
  | none => exact Iff.rfl
  | some γ =>
    by_cases hγ : OrderDual.ofDual γ = 0
    · have heγ : γ = OrderDual.toDual (0 : Γ) := congrArg OrderDual.toDual hγ
      subst γ
      change (0 : K) ∈ openDisc v a (↑(0 : OrderDual Γ)) at hz
      have hz' : (0 : K) ∈ closedDisc v a (↑(0 : OrderDual Γ)) := by
        simpa only [closedDisc_infinity, openDisc_infinity] using hz
      change x ∈ openDisc v a (↑(0 : OrderDual Γ)) ↔ y ∈ openDisc v a (↑(0 : OrderDual Γ))
      simpa only [closedDisc_infinity, openDisc_infinity] using
        closedDisc_zero_radial v a (↑(0 : OrderDual Γ)) hz' x y hxy
    · have ha : v a < OrderDual.ofDual γ := by
        change (0 : K) ∈ if OrderDual.ofDual γ = 0 then {a} else {z | v (z - a) < OrderDual.ofDual γ} at hz
        rw [if_neg hγ] at hz
        change v (0 - a) < OrderDual.ofDual γ at hz
        simpa only [zero_sub, Valuation.map_neg] using hz
      have he (z : K) : z ∈ openDisc v a (↑γ) ↔ v z < OrderDual.ofDual γ := by
        simp only [openDisc, if_neg hγ, Set.mem_ofPred_eq]
        constructor
        · intro h
          have hz : z = (z - a) + a := by ring
          rw [hz]
          exact v.map_add_lt h ha
        · intro h
          exact v.map_sub_lt h ha
      change x ∈ openDisc v a (↑γ) ↔ y ∈ openDisc v a (↑γ)
      rw [he x, he y, hxy]

end SpecialTransformations.Section3.Balls

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv

theorem ball_zero_radial (B : Set M) (hB : IsBall B) (hz : (0 : VFType (M := M)).val ∈ B)
    (x y : VFType (M := M)) (hxy : v x = v y) : x.val ∈ B ↔ y.val ∈ B := by
  obtain ⟨a, ρ, he | he⟩ := encodedBall_disc v hv B hB
  · exact (Set.ext_iff.mp he x).trans
      ((Balls.openDisc_zero_radial v a ρ ((Set.ext_iff.mp he 0).mp hz) x y hxy).trans
        (Set.ext_iff.mp he y).symm)
  · exact (Set.ext_iff.mp he x).trans
      ((Balls.closedDisc_zero_radial v a ρ ((Set.ext_iff.mp he 0).mp hz) x y hxy).trans
        (Set.ext_iff.mp he y).symm)

theorem ball_avoiding_zero_rv (B : Set M) (hB : IsBall B)
    (hz : (0 : VFType (M := M)).val ∉ B) :
    ∃ t : M, iRV t ∧ ∀ x : VFType (M := M), x.val ∈ B → iRv x.val = t := by
  obtain ⟨a, ρ, he | he⟩ := encodedBall_disc v hv B hB
  · refine ⟨iRv a.val, rv_mem hM a.property, ?_⟩
    intro x hx
    exact Balls.openDisc_rv_constant v hv a ρ
      (fun h => hz ((Set.ext_iff.mp he 0).mpr h)) x ((Set.ext_iff.mp he x).mp hx)
  · refine ⟨iRv a.val, rv_mem hM a.property, ?_⟩
    intro x hx
    exact Balls.closedDisc_rv_constant v hv a ρ
      (fun h => hz ((Set.ext_iff.mp he 0).mpr h)) x ((Set.ext_iff.mp he x).mp hx)

end SpecialTransformations.Section3
