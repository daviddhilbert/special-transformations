import Section3.GammaValueFibreCounting
import Section3.GammaSpecialization
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Lemma3.15 over an arbitrary genuine Gamma-named base. The finite
value set uses its full invariant RV preimage over exactly that base. -/
theorem lemma_3_15_gamma_base (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (A : Set M) (hA : DefinableAtBase B .rv A) :
    (Values.finiteNonemptyValues A).Finite ∧
      GammaDefinableOverBase B (Values.finiteNonemptyValues A) := by
  obtain ⟨k,t,hAd⟩ := hA.specialize
  let S := B.real ∪ Set.range (rawTuple t)
  have hf := Values.finite_nonempty_values_finite h00 S A hAd
  obtain ⟨d,hbound⟩ := Values.finite_value_fibres_uniform_bound h00 S A hAd
  have hRV : A ⊆ {x | iRV x} := hA.proper
  have he : Values.gammaPullback (Values.finiteNonemptyValues A) = RawValueFibres.smallNonempty A d := by
    ext w
    constructor
    · rintro ⟨hw,hw0,hfin⟩
      exact (RawValueFibres.smallNonempty_iff A hRV d hbound ⟨w,hw⟩ hw0).mpr hfin
    · intro hw
      obtain ⟨b,hb⟩ := hw.1
      have hwRV : iRV w := hb.1
      have hw0 : w ≠ iRVZero := hb.2.1
      exact ⟨hwRV,hw0,(RawValueFibres.smallNonempty_iff A hRV d hbound ⟨w,hwRV⟩ hw0).mp hw⟩
  refine ⟨hf,?_⟩
  unfold GammaDefinableOverBase
  rw [he]
  exact small_nonempty_definable_base B A hA d

end SpecialTransformations.Section3.GammaParameters
