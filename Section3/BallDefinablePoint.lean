module

public import Section3.RootFreeConstancy
public import Section3.NearestRootDefinability
public import Section3.EncodedBallGeometry
public import Section3.MeanInBalls
public import Section3.DefinableMeans
public import Section3.ClosureBridge
public import Section3.CanonicalContext

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv

theorem qf_rootFree_constant_closed (S : Set M) (p : Parameters S)
    (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E)
    (φ : LRV.BoundedFormula (Fin p.length) 1) (hqf : φ.IsQF)
    (hws : WellSorted p.sorts (fun _ => .vf) φ)
    (a : VFType (M := M)) (r : Balls.Radius Γ)
    (havoid : ∀ c ∈ PolynomialObstacles.obstacles E (PolynomialSupport.formula p E hp φ),
      c ∉ Balls.closedDisc v a r)
    (x y : VFType (M := M)) (hx : x ∈ Balls.closedDisc v a r)
    (hy : y ∈ Balls.closedDisc v a r) :
    φ.Realize p.values ![x.val] ↔ φ.Realize p.values ![y.val] := by
  apply PolynomialSupport.formula_iff_of_support p E hp φ hqf hws x y
  intro q hq
  have he := polynomial_rv_constant_closedDisc v hv (q.map E.subtype) a r
    (fun c hc => havoid c (PolynomialObstacles.root_mem E _ q hq c hc)) x y hx hy
  simpa only [Polynomial.eval_map] using he

/-- One finite original-base definable obstacle set controls every open and
closed ball, including the singleton and whole-field conventions. -/
theorem finite_definable_obstacles_both (S U : Set M) (hU : DefinableAt S .vf U) :
    ∃ R : Finset (VFType (M := M)), R.Nonempty ∧
      DefinableAt S .vf (Subtype.val '' (R : Set (VFType (M := M)))) ∧
      (∀ (a : VFType (M := M)) (r : Balls.OpenRadius Γ),
        (∀ c ∈ R, c ∉ Balls.openDisc v a r) →
        ∀ x ∈ Balls.openDisc v a r, ∀ y ∈ Balls.openDisc v a r,
          (x.val ∈ U ↔ y.val ∈ U)) ∧
      (∀ (a : VFType (M := M)) (r : Balls.Radius Γ),
        (∀ c ∈ R, c ∉ Balls.closedDisc v a r) →
        ∀ x ∈ Balls.closedDisc v a r, ∀ y ∈ Balls.closedDisc v a r,
          (x.val ∈ U ↔ y.val ∈ U)) := by
  obtain ⟨p, φ, hqf, hws, heq⟩ := hU.1.quantifier_free hM
  let E := vfParameterField S
  have hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E :=
    fun i h => Subfield.subset_closure (p.mem_base i)
  let R := PolynomialObstacles.obstacles E (PolynomialSupport.formula p E hp φ)
  have hφ (z : VFType (M := M)) : z.val ∈ U ↔ φ.Realize p.values ![z.val] := by
    have hz : ∀ i : Fin 1, sortEval SortTag.vf (![z.val] i) := by
      intro i; fin_cases i; exact z.property
    exact (Set.ext_iff.mp heq ![z.val]).trans (and_iff_right hz)
  refine ⟨R, ⟨0, PolynomialObstacles.zero_mem E _⟩,
    PolynomialObstacles.obstacles_definable S E
      (vfParameterField_le_definableClosureField S) _, ?_, ?_⟩
  · intro a r havoid x hx y hy
    exact (hφ x).trans ((qf_rootFree_constant v hv S p E hp φ hqf hws a r havoid x y hx hy).trans
      (hφ y).symm)
  · intro a r havoid x hx y hy
    exact (hφ x).trans ((qf_rootFree_constant_closed v hv S p E hp φ hqf hws a r havoid x y hx hy).trans
      (hφ y).symm)

end SpecialTransformations.Section3

set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
open Barycentre RawClosure.Tuple
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv

/-- The containing ball need not be named over S. The nonempty proper
subset is definable over S; nearest-root selection preserves that base. -/
theorem definable_point_of_proper_subset_canonical
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (S A : Set M) (hA : DefinableAt S .vf A) (hne : A.Nonempty)
    (B : Set (VFType (M := M)))
    (hB : ∃ a, (∃ ρ : Balls.OpenRadius Γ, B = Balls.openDisc v a ρ) ∨
      (∃ ρ : Balls.Radius Γ, B = Balls.closedDisc v a ρ))
    (hsub : ∀ x : VFType (M := M), x.val ∈ A → x ∈ B)
    (hproper : ∃ b ∈ B, b.val ∉ A) :
    ∃ b : VFType (M := M), b ∈ B ∧ DefinableClosureAt S .vf b.val := by
  obtain ⟨R, hR, hRdef, hO, hC⟩ := finite_definable_obstacles_both v hv S A hA
  let T : Set (VFType (M := M)) := {a | a.val ∈ A}
  have hT : T.Nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨⟨a, hA.2 ha⟩, ha⟩
  have hTR : ∃ r ∈ R, r ∈ B := by
    by_contra hnot
    have hmiss : ∀ r ∈ R, r ∉ B := by simpa only [not_exists, not_and] using hnot
    obtain ⟨a, ha⟩ := hT
    obtain ⟨b, hb, hbA⟩ := hproper
    obtain ⟨c, ⟨ρ, hB'⟩ | ⟨ρ, hB'⟩⟩ := hB
    · have hab := hO c ρ (hB' ▸ hmiss) a (hB' ▸ hsub a ha) b (hB' ▸ hb)
      exact hbA (hab.mp ha)
    · have hab := hC c ρ (hB' ▸ hmiss) a (hB' ▸ hsub a ha) b (hB' ▸ hb)
      exact hbA (hab.mp ha)
  let N := Balls.nearestRoots v R T
  have hN : N.Nonempty := Balls.nearestRoots_nonempty v R hR T hT
  have hNdef : S.Definable₁ LRV (Subtype.val '' (N : Set (VFType (M := M)))) := by
    rw [← NearestRootSyntax.nearest_eq_image v hv R A hA.2]
    exact NearestRootSyntax.nearest_definable S _ A hRdef.raw_definable hA.raw_definable
  have hNB : ∀ x ∈ N, x ∈ B := by
    obtain ⟨c, ⟨ρ, hB'⟩ | ⟨ρ, hB'⟩⟩ := hB
    · rw [hB']
      exact Balls.nearestRoots_mem_openDisc v R T c ρ
        (fun x hx => hB' ▸ hsub x hx) (hB' ▸ hTR)
    · rw [hB']
      exact Balls.nearestRoots_mem_closedDisc v R T c ρ
        (fun x hx => hB' ▸ hsub x hx) (hB' ▸ hTR)
  have hmB : mean N ∈ B := by
    obtain ⟨c, ⟨ρ, hB'⟩ | ⟨ρ, hB'⟩⟩ := hB
    · rw [hB']
      exact mean_mem_openDisc v hv h00 N hN c ρ (hB' ▸ hNB)
    · rw [hB']
      exact mean_mem_closedDisc v hv h00 N hN c ρ (hB' ▸ hNB)
  have hF : RelationDefinable S (finiteFibreRelation (fun _ : Fin 0 → M => N)) := by
    exact hNdef.preimage_comp (Sum.inr : Fin 1 → Fin 0 ⊕ Fin 1)
  have hm := mean_definable h00 S (fun _ : Fin 0 → M => N) hF N.card (fun _ => le_rfl)
  have hsingle : S.Definable₁ LRV {(mean N).val} := DefinableConstants.singleton_of_constant hm
  exact ⟨mean N, hmB, raw_definable_sorted hc S {(mean N).val} .vf hsingle
    (by rintro x rfl; exact (mean N).property)⟩

end SpecialTransformations.Section3

namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Lemma 3.11, with the intended nonempty proper subset explicit. The
containing ball is not required to be S-definable. Every conclusion is over
the original S, in an arbitrary ACVF(0,0) model. -/
theorem lemma_3_11 (h00 : M ⊨ Axioms.ACVF00) (S A B : Set M)
    (hA : DefinableAt S .vf A) (hne : A.Nonempty) (hB : IsBall B)
    (hproper : A ⊂ B) : ∃ b ∈ B, DefinableClosureAt S .vf b := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have hcan : @CanonicalStructure.IsCanonical M N := CanonicalStructure.normalize_isCanonical
  have hN00 : @Theory.Model LRV M N Axioms.ACVF00 := normalized_model00 h00
  have hBN : @IsBall M N B := isBall_normalize B hB
  have hAN : @DefinableAt M N S .vf A := (definableAt_normalize_iff S .vf A).mpr hA
  have hex : ∃ b ∈ B, @DefinableClosureAt M N S .vf b := by
    letI := N
    letI := hN
    obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
    letI := hΓ
    have hdisc := encodedBall_disc v hv B hBN
    have hprop : ∃ b : VFType (M := M), b.val ∈ B ∧ b.val ∉ A := by
      obtain ⟨b, hb, hbA⟩ := Set.exists_of_ssubset hproper
      exact ⟨⟨b, isBall_subset_vf B hBN hb⟩, hb, hbA⟩
    obtain ⟨b, hb, hbdcl⟩ := definable_point_of_proper_subset_canonical v hv hcan hN00 S A hAN hne
      {b : VFType (M := M) | b.val ∈ B} hdisc (fun x hx => hproper.1 hx) hprop
    exact ⟨b.val, hb, hbdcl⟩
  obtain ⟨b, hb, hbdcl⟩ := hex
  exact ⟨b, hb, (definableClosureAt_normalize_iff S .vf b).mp hbdcl⟩

end SpecialTransformations.Section3
