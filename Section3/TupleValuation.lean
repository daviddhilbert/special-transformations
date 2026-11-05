import Section3.BallGeometry
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.Balls
variable {K : Type} [Field K] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

/-- Minimum of the coordinate values in the paper's reversed order.
The empty tuple has value infinity. -/
noncomputable def tupleValuation (v : Valuation K Γ) {n : ℕ} (a : Fin n → K) :
    OrderDual Γ := OrderDual.toDual (Finset.univ.sup (fun i => v (a i)))

theorem tupleValuation_le_coordinate (v : Valuation K Γ) {n : ℕ} (a : Fin n → K)
    (i : Fin n) : tupleValuation v a ≤ OrderDual.toDual (v (a i)) := by
  exact Finset.le_sup (f := fun i => v (a i)) (Finset.mem_univ i)

theorem le_tupleValuation_iff (v : Valuation K Γ) {n : ℕ} (a : Fin n → K)
    (γ : OrderDual Γ) : γ ≤ tupleValuation v a ↔
      ∀ i, γ ≤ OrderDual.toDual (v (a i)) := by
  change Finset.univ.sup (fun i => v (a i)) ≤ OrderDual.ofDual γ ↔
    ∀ i, v (a i) ≤ OrderDual.ofDual γ
  simpa only [Finset.mem_univ, forall_const] using
    (Finset.sup_le_iff : Finset.univ.sup (fun i => v (a i)) ≤ OrderDual.ofDual γ ↔ _)

@[simp] theorem tupleValuation_zero (v : Valuation K Γ) {n : ℕ} :
    tupleValuation v (fun _ : Fin n => 0) = OrderDual.toDual (0 : Γ) := by
  change OrderDual.toDual (Finset.univ.sup (fun _ : Fin n => v (0 : K))) = _
  apply congrArg OrderDual.toDual
  simp

@[simp] theorem tupleValuation_empty (v : Valuation K Γ) (a : Fin 0 → K) :
    tupleValuation v a = OrderDual.toDual (0 : Γ) := by
  change OrderDual.toDual (Finset.univ.sup (fun i : Fin 0 => v (a i))) = _
  apply congrArg OrderDual.toDual
  simp [bot_eq_zero]

theorem closedPolydisc_uniform_iff (v : Valuation K Γ) {n : ℕ}
    (a x : Fin n → K) (γ : OrderDual Γ) :
    x ∈ closedPolydisc v a (fun _ => (γ : Radius Γ)) ↔
      γ ≤ tupleValuation v (fun i => x i - a i) := by
  exact (le_tupleValuation_iff v _ γ).symm

theorem openPolydisc_uniform_iff (v : Valuation K Γ) {n : ℕ}
    (a x : Fin n → K) (γ : OrderDual Γ) (hγ : OrderDual.ofDual γ ≠ 0) :
    x ∈ openPolydisc v a (fun _ => (γ : Radius Γ)) ↔
      γ < tupleValuation v (fun i => x i - a i) := by
  change (∀ i, x i ∈ openDisc v (a i) ↑γ) ↔ _
  simp only [openDisc, if_neg hγ, Set.mem_ofPred_eq]
  change (∀ i, v (x i - a i) < OrderDual.ofDual γ) ↔
    Finset.univ.sup (fun i => v (x i - a i)) < OrderDual.ofDual γ
  rw [Finset.sup_lt_iff (by simpa only [bot_eq_zero] using (pos_iff_ne_zero.mpr hγ))]
  simp

end SpecialTransformations.Section3.Balls
