import Section4.GammaDefinablePoint
import Section3.FiniteValueDefinability

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

theorem gammaDcl_of_named_code (h00 : M ⊨ Axioms.ACVF00)
    (a : M) (haS : a ∈ S) (ha : GammaParameters.NonzeroRV a) :
    Values.gammaOf ⟨a, ha.1⟩ ha.2 ∈ GammaDcl S := by
  have had := definableClosureAt_of_mem (A := S) (σ := .rv) haS ha.1
  have hd := Values.finite_nonempty_values_definable h00 S {a} had
  have he : Values.finiteNonemptyValues {a} = {Values.gammaOf ⟨a, ha.1⟩ ha.2} := by
    ext γ
    constructor
    · rintro ⟨⟨t, ht, hta⟩, _⟩
      have he : t = (⟨a, ha.1⟩ : CanonicalRV.RVSort M) := Subtype.ext hta
      exact Subtype.ext (ht.symm.trans (congrArg Values.vrv he))
    · intro hγ
      have hγ' : γ = Values.gammaOf ⟨a, ha.1⟩ ha.2 := hγ
      subst γ
      refine ⟨⟨⟨a, ha.1⟩, rfl, rfl⟩, ?_⟩
      apply (Set.finite_singleton (⟨a, ha.1⟩ : CanonicalRV.RVSort M)).subset
      intro t ht
      exact Subtype.ext ht.2
  rwa [he] at hd

/-- The standing nontriviality of Gamma(S) supplies a positive named
value in the definable closure of the original substructure. -/
theorem exists_named_positive_gamma (C : BaseContext M) :
    ∃ δ : Values.Gamma (M := M), δ ∈ GammaDcl (C.base : Set M) ∧ 1 < δ := by
  obtain ⟨a, b, ha, hb, ha0, hb0, hne⟩ := C.nontrivial_values
  let α := Values.gammaOf ⟨a.val, ha⟩ ha0
  let β := Values.gammaOf ⟨b.val, hb⟩ hb0
  have hα : α ∈ GammaDcl (C.base : Set M) := gammaDcl_of_named_code C.model00 _ a.property ⟨ha, ha0⟩
  have hβ : β ∈ GammaDcl (C.base : Set M) := gammaDcl_of_named_code C.model00 _ b.property ⟨hb, hb0⟩
  have hαβ : α ≠ β := by
    intro he
    exact hne ((Values.vrv_eq_iff (⟨a.val, ha⟩ : CanonicalRV.RVSort M) ⟨b.val, hb⟩).mp
      (congrArg Subtype.val he))
  let δ := α * β⁻¹
  have hδ : δ ∈ GammaDcl (C.base : Set M) := gammaDcl_mul hα (gammaDcl_inv hβ)
  have hδ1 : δ ≠ 1 := by
    intro he
    apply hαβ
    have hh := congrArg (fun x => x * β) he
    simpa only [δ, mul_assoc, inv_mul_cancel, mul_one, one_mul] using hh
  rcases lt_or_gt_of_ne hδ1 with h | h
  · exact ⟨δ⁻¹, gammaDcl_inv hδ, Left.one_lt_inv_iff.mpr h⟩
  · exact ⟨δ, hδ, h⟩

theorem gamma_tuple_definable_point_base_context (C : BaseContext M)
    {n : ℕ} (A : Set (Fin n → Values.Gamma (M := M)))
    (hA : GammaSyntax.Definable (C.base : Set M) (fun a => a ∈ A))
    (hne : A.Nonempty) :
    ∃ γ ∈ A, ∀ i, Values.GammaDefinable (C.base : Set M) {γ i} := by
  obtain ⟨δ, hδ, hδ1⟩ := exists_named_positive_gamma C
  exact gamma_tuple_definable_point C.model00 δ hδ hδ1 A hA hne

end SpecialTransformations.Section4

end
