module

public import Section3.GammaSpecialization
public import Section3.RVIndependence
public import Section3.VFExchange

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Arbitrarily many named Gamma elements do not enlarge VF algebraic
closure. The witness relation specializes at RV representatives explicitly;
the checked RV-independence theorem then removes those parameters. -/
theorem algebraic_vf_iff_real (B : Base (M := M)) (b : VFType (M := M)) :
    AlgebraicAtBase B .vf b.val ↔ SpecialTransformations.Section3.AlgebraicAt B.real .vf b.val := by
  constructor
  · rintro ⟨A,hA,hfin,hb⟩
    obtain ⟨k,t,ht⟩ := hA.specialize
    have hB : ∀ x ∈ Set.range (rawTuple t), iRV x := by
      rintro x ⟨i,rfl⟩
      exact raw_rv (t i)
    exact (algebraicAt_vf_union_rv_iff B.real _ hB b).mp ⟨A,ht,hfin,hb⟩
  · rintro ⟨A,hA,hfin,hb⟩
    exact ⟨A,real_definableAtBase B .vf A hA,hfin,hb⟩

theorem algebraic_vf_iff_parameterField (B : Base (M := M)) (b : VFType (M := M)) :
    AlgebraicAtBase B .vf b.val ↔ IsAlgebraic (vfParameterField B.real) b :=
  (algebraic_vf_iff_real B b).trans (algebraicAt_vf_iff_parameterField B.real b)

/-- Lemma3.3 with genuine named Gamma parameters in the base. -/
theorem lemma_3_3_gamma_base (B : Base (M := M)) {n m : ℕ}
    (a : Fin n → VFType (M := M)) (t : Fin m → M) (ht : ∀ j, iRV (t j))
    (b : VFType (M := M))
    (hb : AlgebraicAtBase (⟨(B.real ∪ Set.range (fun i => (a i).val)) ∪ Set.range t,B.gamma⟩ : Base (M := M)) .vf b.val) :
    IsAlgebraic (vfParameterField (B.real ∪ Set.range (fun i => (a i).val))) b :=
  SpecialTransformations.Section3.lemma_3_3 B.real a t ht b ((algebraic_vf_iff_real _ b).mp hb)

/-- VF exchange over a base including genuine Gamma names. -/
theorem lemma_3_6_vf_gamma_base (B : Base (M := M)) (F : VFFieldBase B.real)
    (a b : VFType (M := M))
    (hab : AlgebraicAtBase (⟨insert b.val B.real,B.gamma⟩ : Base (M := M)) .vf a.val)
    (ha : ¬ AlgebraicAtBase B .vf a.val) :
    AlgebraicAtBase (⟨insert a.val B.real,B.gamma⟩ : Base (M := M)) .vf b.val := by
  apply (algebraic_vf_iff_real _ b).mpr
  exact SpecialTransformations.Section3.lemma_3_6_vf B.real F a b
    ((algebraic_vf_iff_real _ a).mp hab) (fun h => ha ((algebraic_vf_iff_real B a).mpr h))

/-- VF nonalgebraicity is preserved on adjoining arbitrary RV and Gamma
parameter sets. No cardinality, saturation or characteristic restriction. -/
theorem corollary_3_7_vf_gamma_base (B : Base (M := M)) (T : Set M)
    (hT : ∀ t ∈ T, iRV t) (G : Set (Values.Gamma (M := M))) (b : VFType (M := M))
    (hb : ¬ AlgebraicAtBase B .vf b.val) :
    ¬ AlgebraicAtBase (⟨B.real ∪ T,B.gamma ∪ G⟩ : Base (M := M)) .vf b.val := by
  intro h
  have hr := (algebraic_vf_iff_real _ b).mp h
  exact hb ((algebraic_vf_iff_real B b).mpr ((algebraicAt_vf_union_rv_iff B.real T hT b).mp hr))

end SpecialTransformations.Section3.GammaParameters
namespace SpecialTransformations.Section3
export GammaParameters (lemma_3_3_gamma_base lemma_3_6_vf_gamma_base corollary_3_7_vf_gamma_base)
end SpecialTransformations.Section3
