module

public import CanonicalRV
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3

theorem polynomial_close_nhds {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    [Valued K Γ] (p : Polynomial K) (a : K) (ha : p.eval a ≠ 0) :
    {x : K | Valued.v (p.eval x - p.eval a) < Valued.v (p.eval a)} ∈ 𝓝 a := by
  let v : Valuation K Γ := Valued.v
  have hB : {y : K | v.restrict (y - p.eval a) < v.restrict (p.eval a)} ∈ 𝓝 (p.eval a) := by
    exact Valued.mem_nhds.mpr ⟨Units.mk0 _ ((v.restrict.ne_zero_iff).mpr ha), Set.Subset.rfl⟩
  have h := p.continuousAt.preimage_mem_nhds hB
  simpa only [Set.preimage_ofPred_eq, Valuation.restrict_lt_iff] using h

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem polynomial_rv_locally_constant {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    [Valued (VFType (M := M)) Γ]
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (p : Polynomial (VFType (M := M))) (a : VFType (M := M)) (ha : p.eval a ≠ 0) :
    {x : VFType (M := M) | iRv (p.eval x).val = iRv (p.eval a).val} ∈ 𝓝 a := by
  apply Filter.mem_of_superset (polynomial_close_nhds p a ha)
  intro x hx
  apply (CanonicalRV.encoded_eq_iff_close (p.eval x).property (p.eval a).property
    (fun h => ha (Subtype.ext h))).mpr
  change ¬ VFValued.predV (p.eval a) (p.eval x - p.eval a)
  rw [hv, not_le]
  exact hx

end SpecialTransformations.Section3