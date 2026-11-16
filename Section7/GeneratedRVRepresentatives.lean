module

public import Section3.GeneratedBaseLifting
public import Section3.GammaDefinableClosureField
public import Section3.GeneralBallCenters
public import Section3.GammaFiniteMeans
public import Section3.RVUnaryLift
public import Section3.RVOperations

@[expose] public section

/-!
# Original-base representatives for Lemma 7.4

Use Section 3's genuine small-parameter saturation and generated-base
algebraic lifting. A finite algebraic witness is filtered by the named RV
class; its barycentre stays in that class in pure characteristic zero and
is definable over the original base. Closure of that base then puts the
representative in its VF part. No representative is added to the base.
-/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The checked VF definable-closure field is exactly the VF part of a
generated base, so it is the coefficient field of the paper statement. -/
theorem mem_generatedBase_vfField (B : Base (M := M)) (hB : VFGammaGeneratedBase B)
    (x : VFType (M := M)) : x ∈ vfDefinableClosureFieldBase B ↔ x.val ∈ B.real := by
  change DefinableClosureAtBase B .vf x.val ↔ x.val ∈ B.real
  constructor
  · intro hx
    have hx' : x.val ∈ (closureBase B).real := ⟨.vf, hx⟩
    rwa [hB.closure_eq_self] at hx'
  · intro hx
    exact real_definableAtBase B .vf _ (definableClosureAt_of_mem hx x.property)

private theorem rvFibre_openBall (t : CanonicalRV.RVSort M) (ht : t ≠ 0) :
    ∃ D : OpenBallCodes.OpenBall M, ∀ x : VFType (M := M),
      x.val ∈ OpenBallCodes.underlying D ↔ CanonicalRV.encodedRv x = t := by
  obtain ⟨a, ha⟩ := CanonicalRV.encodedRv_surjective t
  have ha0 : a ≠ 0 := by
    intro hz
    have hzero : CanonicalRV.encodedRv a = 0 := by rw [hz, RVOperations.rv_zero]
    exact ht (ha.symm.trans hzero)
  let q : OpenBallCodes.Code M := ⟨![a.val, a.val], ⟨by
    intro i
    fin_cases i <;> exact a.property, by
    intro he
    exact ha0 (Subtype.ext he)⟩⟩
  refine ⟨Quotient.mk _ q, ?_⟩
  intro x
  change x.val ∈ OpenBallCodes.rawBall q.val ↔ _
  rw [OpenBallCodes.rawBall, Set.mem_ofPred_eq, and_iff_right q.property,
    and_iff_right x.property, OpenBallCodes.body_realize]
  change (¬ iLe (iRv (iVFAdd x.val (iVFNeg a.val))) (iRv a.val)) ↔ _
  rw [← CanonicalRV.encoded_eq_iff_close x.property a.property
    (fun he => ha0 (Subtype.ext he))]
  rw [← ha]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- A finite algebraic witness in a named RV ball gives a definable
representative, by taking the mean after restricting to that ball. -/
theorem definable_rv_representative_of_algebraic_lift
    (h00 : M ⊨ Axioms.ACVF00) (S : Set M) (t : CanonicalRV.RVSort M)
    (ht : t.val ∈ S) (ht0 : t ≠ 0) (a : VFType (M := M))
    (ha : CanonicalRV.encodedRv a = t) (haAlg : AlgebraicAt S .vf a.val) :
    ∃ x : VFType (M := M), DefinableClosureAt S .vf x.val ∧ CanonicalRV.encodedRv x = t := by
  classical
  have htNamed : DefinableClosureAt S .rv t.val := definableClosureAt_of_mem ht t.property
  obtain ⟨D, hD, hDf, haD⟩ := haAlg
  let U : Set M := D ∩ {x | iVF x ∧ iRv x = t.val}
  have hpre : DefinableAt S .vf {x | iVF x ∧ iRv x = t.val} := by
    simpa only [Set.mem_singleton_iff] using
      htNamed.rv_preimage
  have hUd : DefinableAt S .vf U := hD.inter hpre
  have hUf : U.Finite := hDf.subset Set.inter_subset_left
  have haU : a.val ∈ U := ⟨haD, a.property, congrArg Subtype.val ha⟩
  let U' : Set (VFType (M := M)) := Subtype.val ⁻¹' U
  have hUf' : U'.Finite := hUf.preimage Subtype.val_injective.injOn
  let F := hUf'.toFinset
  have hFmem (x : VFType (M := M)) : x ∈ F ↔ x.val ∈ U := by
    exact hUf'.mem_toFinset
  have hne : F.Nonempty := ⟨a, (hFmem _).mpr haU⟩
  have himage : Subtype.val '' (F : Set (VFType (M := M))) = U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hFmem y).mp hy
    · intro hx
      exact ⟨⟨x, hUd.2 hx⟩, (hFmem _).mpr hx, rfl⟩
  let B : Base (M := M) := ⟨S, ∅⟩
  have hmeanDef : DefinableClosureAt S .vf (normalizedMean F) :=
    (at_base_empty_iff S .vf {normalizedMean F}).mp
      (finite_mean_definable_base h00 B F (real_definableAtBase B .vf _ (himage.symm ▸ hUd)))
  obtain ⟨O, hO⟩ := rvFibre_openBall t ht0
  have hmean := OpenBallCodes.normalized_mean_mem h00 O F hne (by
    intro x hx
    apply (hO x).mpr
    exact Subtype.ext ((hFmem x).mp hx).2.2)
  have hmeanVF : iVF (normalizedMean F) :=
    OpenBallCodes.underlying_subset_vf O hmean
  exact ⟨⟨normalizedMean F, hmeanVF⟩, hmeanDef, (hO _).mp hmean⟩

/-- Every nonzero named RV element of a generated base has a
representative in its VF part. -/
theorem generatedBase_rv_representative {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B) (t : CanonicalRV.RVSort M)
    (htB : t.val ∈ B.real) (ht0 : t ≠ 0) :
    ∃ x : VFType (M := M), x.val ∈ B.real ∧ CanonicalRV.encodedRv x = t := by
  have hclosed := hB.closure_eq_self
  obtain ⟨A, G, hAB, _, hA, hgen⟩ := hB
  have htNamed : DefinableClosureAt B.real .rv t.val := definableClosureAt_of_mem htB t.property
  have htAlg : AlgebraicAtBase B .rv t.val :=
    ⟨{t.val}, real_definableAtBase B .rv _ htNamed,
      Set.finite_singleton _, Set.mem_singleton _⟩
  obtain ⟨a, ha⟩ := algebraic_rv_closure_generated_lifts hκ hs h00 A hA
    ((Cardinal.mk_le_mk_of_subset hAB).trans_lt hsmall) G t (hgen.symm ▸ htAlg)
  have haAlg : AlgebraicAt B.real .vf a.val.val :=
    ((mem_vfAlgebraicClosureField A a.val).mp a.property).mono hAB
  obtain ⟨x, hx, hxt⟩ := definable_rv_representative_of_algebraic_lift h00 B.real t htB ht0 a.val ha haAlg
  refine ⟨x, ?_, hxt⟩
  have hx' : x.val ∈ (closureBase B).real := ⟨.vf, real_definableAtBase B .vf _ hx⟩
  rwa [hclosed] at hx'

end SpecialTransformations.Section7
