import Section3.MixedPolynomialSupport
import Section3.PolynomialObstacles
import Section3.PolynomialRVConstant
import Section3.QuantifierFree
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
open MixedPolynomialSyntax
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m : ℕ}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv

theorem mixed_qf_rootFree_constant (S : Set M) (p : Parameters S)
    (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E)
    (φ : LRV.BoundedFormula (Fin p.length) (m + 1)) (hqf : φ.IsQF)
    (hws : WellSorted p.sorts contextSort φ)
    (a : VFType (M := M)) (r : Balls.OpenRadius Γ)
    (havoid : ∀ c ∈ PolynomialObstacles.obstacles E (MixedPolynomialSupport.formula p E hp φ),
      c ∉ Balls.openDisc v a r)
    (x y : VFType (M := M)) (hx : x ∈ Balls.openDisc v a r)
    (hy : y ∈ Balls.openDisc v a r) (ys : Fin m → M) (hys : ∀ j, iRV (ys j)) :
    φ.Realize p.values (Fin.cons x.val ys) ↔ φ.Realize p.values (Fin.cons y.val ys) := by
  apply MixedPolynomialSupport.formula_iff_of_support p E hp φ hqf hws x y ys hys
  intro q hq
  have he := polynomial_rv_constant_openDisc v hv (q.map E.subtype) a r
    (fun c hc => havoid c (PolynomialObstacles.root_mem E _ q hq c hc)) x y hx hy
  simpa only [Polynomial.eval_map] using he

theorem mixed_qf_rootFree_constant_closed (S : Set M) (p : Parameters S)
    (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E)
    (φ : LRV.BoundedFormula (Fin p.length) (m + 1)) (hqf : φ.IsQF)
    (hws : WellSorted p.sorts contextSort φ)
    (a : VFType (M := M)) (r : Balls.Radius Γ)
    (havoid : ∀ c ∈ PolynomialObstacles.obstacles E (MixedPolynomialSupport.formula p E hp φ),
      c ∉ Balls.closedDisc v a r)
    (x y : VFType (M := M)) (hx : x ∈ Balls.closedDisc v a r)
    (hy : y ∈ Balls.closedDisc v a r) (ys : Fin m → M) (hys : ∀ j, iRV (ys j)) :
    φ.Realize p.values (Fin.cons x.val ys) ↔ φ.Realize p.values (Fin.cons y.val ys) := by
  apply MixedPolynomialSupport.formula_iff_of_support p E hp φ hqf hws x y ys hys
  intro q hq
  have he := polynomial_rv_constant_closedDisc v hv (q.map E.subtype) a r
    (fun c hc => havoid c (PolynomialObstacles.root_mem E _ q hq c hc)) x y hx hy
  simpa only [Polynomial.eval_map] using he

/-- One finite original-base definable obstacle set controls all RV tuples
simultaneously. No RV tuple is added to the parameter base. -/
theorem mixed_finite_definable_obstacles (S : Set M) (U : Set (Fin (m + 1) → M))
    (hU : DefinableOver S contextSort U) :
    ∃ R : Finset (VFType (M := M)), R.Nonempty ∧
      DefinableAt S .vf (Subtype.val '' (R : Set (VFType (M := M)))) ∧
      (∀ (a : VFType (M := M)) (r : Balls.OpenRadius Γ),
        (∀ c ∈ R, c ∉ Balls.openDisc v a r) →
        ∀ x ∈ Balls.openDisc v a r, ∀ y ∈ Balls.openDisc v a r,
        ∀ ys : Fin m → M, (∀ j, iRV (ys j)) →
          (Fin.cons x.val ys ∈ U ↔ Fin.cons y.val ys ∈ U)) ∧
      (∀ (a : VFType (M := M)) (r : Balls.Radius Γ),
        (∀ c ∈ R, c ∉ Balls.closedDisc v a r) →
        ∀ x ∈ Balls.closedDisc v a r, ∀ y ∈ Balls.closedDisc v a r,
        ∀ ys : Fin m → M, (∀ j, iRV (ys j)) →
          (Fin.cons x.val ys ∈ U ↔ Fin.cons y.val ys ∈ U)) := by
  obtain ⟨p, φ, hqf, hws, heq⟩ := hU.quantifier_free hM
  let E := vfParameterField S
  have hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E :=
    fun i h => Subfield.subset_closure (p.mem_base i)
  let R := PolynomialObstacles.obstacles E (MixedPolynomialSupport.formula p E hp φ)
  have hφ (x : VFType (M := M)) (ys : Fin m → M) (hys : ∀ j, iRV (ys j)) :
      Fin.cons x.val ys ∈ U ↔ φ.Realize p.values (Fin.cons x.val ys) := by
    have hz : ∀ i, sortEval (contextSort i) ((Fin.cons x.val ys : Fin (m + 1) → M) i) := by
      intro i
      cases i using Fin.cases with
      | zero => exact x.property
      | succ j => exact hys j
    exact (Set.ext_iff.mp heq (Fin.cons x.val ys)).trans (and_iff_right hz)
  refine ⟨R, ⟨0, PolynomialObstacles.zero_mem E _⟩,
    PolynomialObstacles.obstacles_definable S E
      (vfParameterField_le_definableClosureField S) _, ?_, ?_⟩
  · intro a r havoid x hx y hy ys hys
    exact (hφ x ys hys).trans ((mixed_qf_rootFree_constant v hv S p E hp φ hqf hws a r havoid x y hx hy ys hys).trans
      (hφ y ys hys).symm)
  · intro a r havoid x hx y hy ys hys
    exact (hφ x ys hys).trans ((mixed_qf_rootFree_constant_closed v hv S p E hp φ hqf hws a r havoid x y hx hy ys hys).trans
      (hφ y ys hys).symm)

end SpecialTransformations.Section3
