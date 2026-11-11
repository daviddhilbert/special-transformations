import Section3.PolynomialSupport
import Section3.PolynomialObstacles
import Section3.PolynomialRVConstant
import Section3.QuantifierFree
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv

/-- The actual finite occurring-polynomial support controls a QF formula
on every ball avoiding its roots, without naming any root as a parameter. -/
theorem qf_rootFree_constant (S : Set M) (p : Parameters S)
    (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E)
    (φ : LRV.BoundedFormula (Fin p.length) 1) (hqf : φ.IsQF)
    (hws : WellSorted p.sorts (fun _ => .vf) φ)
    (a : VFType (M := M)) (r : Balls.OpenRadius Γ)
    (havoid : ∀ c ∈ PolynomialObstacles.obstacles E (PolynomialSupport.formula p E hp φ),
      c ∉ Balls.openDisc v a r)
    (x y : VFType (M := M)) (hx : x ∈ Balls.openDisc v a r)
    (hy : y ∈ Balls.openDisc v a r) :
    φ.Realize p.values ![x.val] ↔ φ.Realize p.values ![y.val] := by
  apply PolynomialSupport.formula_iff_of_support p E hp φ hqf hws x y
  intro q hq
  have he := polynomial_rv_constant_openDisc v hv (q.map E.subtype) a r
    (fun c hc => havoid c (PolynomialObstacles.root_mem E _ q hq c hc)) x y hx hy
  simpa only [Polynomial.eval_map] using he

/-- Every unary VF set definable over the original S has a finite S-definable
nonempty obstacle set. On an open ball missing it, membership is constant.
This strengthens pointwise local constancy and uses the completed QE input. -/
theorem finite_definable_obstacles (S U : Set M) (hU : DefinableAt S .vf U) :
    ∃ R : Finset (VFType (M := M)), R.Nonempty ∧
      DefinableAt S .vf (Subtype.val '' (R : Set (VFType (M := M)))) ∧
      ∀ (a : VFType (M := M)) (r : Balls.OpenRadius Γ),
        (∀ c ∈ R, c ∉ Balls.openDisc v a r) →
        ∀ x ∈ Balls.openDisc v a r, ∀ y ∈ Balls.openDisc v a r,
          (x.val ∈ U ↔ y.val ∈ U) := by
  obtain ⟨p, φ, hqf, hws, heq⟩ := hU.1.quantifier_free hM
  let E := vfParameterField S
  have hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E :=
    fun i h => Subfield.subset_closure (p.mem_base i)
  let R := PolynomialObstacles.obstacles E (PolynomialSupport.formula p E hp φ)
  have hφ (z : VFType (M := M)) : z.val ∈ U ↔ φ.Realize p.values ![z.val] := by
    have hz : ∀ i : Fin 1, sortEval SortTag.vf (![z.val] i) := by
      intro i; fin_cases i; exact z.property
    have he := Set.ext_iff.mp heq ![z.val]
    exact he.trans (and_iff_right hz)
  refine ⟨R, ⟨0, PolynomialObstacles.zero_mem E _⟩,
    PolynomialObstacles.obstacles_definable S E
      (vfParameterField_le_definableClosureField S) _, ?_⟩
  intro a r havoid x hx y hy
  exact (hφ x).trans ((qf_rootFree_constant v hv S p E hp φ hqf hws a r havoid x y hx hy).trans
    (hφ y).symm)

end SpecialTransformations.Section3
