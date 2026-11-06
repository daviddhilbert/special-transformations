import Section4.ResidueParameterField
import Section4.ResidueFieldFunctions

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Ordinary algebraic closure properties of the coefficients used by the
term interpretation. The actual substructure construction below supplies
every field; no model-theoretic or dimension conclusion is assumed. -/
structure CoefficientContext (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] where
  field : Subfield (ModelResidue M)
  coefficients : Set (CanonicalRV.RVSort M)
  zero_mem : (0 : CanonicalRV.RVSort M) ∈ coefficients
  one_mem : (1 : CanonicalRV.RVSort M) ∈ coefficients
  mul_mem : ∀ {a b}, a ∈ coefficients → b ∈ coefficients → a * b ∈ coefficients
  inv_mem : ∀ {a}, a ∈ coefficients → a⁻¹ ∈ coefficients
  residuePart_mem : ∀ {a}, a ∈ coefficients → residuePart a ∈ field

theorem residuePart_zero : residuePart (0 : CanonicalRV.RVSort M) = 0 := by
  apply residueRV_injective
  have hz : ValuedModelMap.inK (0 : CanonicalRV.RVSort M) :=
    residueRV_zero (M := M) ▸ residueRV_inK (0 : ModelResidue M)
  rw [residueRV_part hz, residueRV_zero]

def extendedCoefficients (B : LRV.Substructure M) (E : Subfield (ModelResidue M)) :
    Set (CanonicalRV.RVSort M) :=
  {c | ∃ b : CanonicalRV.RVSort M, b.val ∈ B ∧ ∃ u ∈ E, c = b * residueRV u}

theorem extendedCoefficients_base (B : LRV.Substructure M) (E : Subfield (ModelResidue M))
    {c : CanonicalRV.RVSort M} (hc : c.val ∈ B) : c ∈ extendedCoefficients B E :=
  ⟨c, hc, 1, E.one_mem, by simp⟩

theorem extendedCoefficients_residue (B : LRV.Substructure M) (E : Subfield (ModelResidue M))
    {u : ModelResidue M} (hu : u ∈ E) : residueRV u ∈ extendedCoefficients B E :=
  ⟨1, by rw [RVOperations.one_val]; exact SubstructureRVGroup.rvOne_mem B,
    u, hu, (one_mul _).symm⟩

theorem extendedCoefficients_mul (B : LRV.Substructure M) (E : Subfield (ModelResidue M))
    {c d : CanonicalRV.RVSort M} (hc : c ∈ extendedCoefficients B E)
    (hd : d ∈ extendedCoefficients B E) : c * d ∈ extendedCoefficients B E := by
  obtain ⟨b, hb, u, hu, rfl⟩ := hc
  obtain ⟨b', hb', u', hu', rfl⟩ := hd
  refine ⟨b * b', rv_mul_mem_base B hb hb', u * u', E.mul_mem hu hu', ?_⟩
  rw [residueRV_mul]
  ac_rfl

theorem extendedCoefficients_inv (B : LRV.Substructure M) (E : Subfield (ModelResidue M))
    {c : CanonicalRV.RVSort M} (hc : c ∈ extendedCoefficients B E) :
    c⁻¹ ∈ extendedCoefficients B E := by
  obtain ⟨b, hb, u, hu, rfl⟩ := hc
  exact ⟨b⁻¹, rv_inv_mem_base B hb, u⁻¹, E.inv_mem hu, by rw [mul_inv, residueRV_inv]⟩

theorem extendedCoefficients_part (B : LRV.Substructure M) (E : Subfield (ModelResidue M))
    (hE : residueParameterField B ≤ E) {c : CanonicalRV.RVSort M}
    (hc : c ∈ extendedCoefficients B E) : residuePart c ∈ E := by
  obtain ⟨b, hb, u, hu, rfl⟩ := hc
  by_cases hu0 : u = 0
  · rw [hu0, residueRV_zero, mul_zero, residuePart_zero]
    exact E.zero_mem
  · by_cases hK : ValuedModelMap.inK (b * residueRV u)
    · have hbK : ValuedModelMap.inK b := ((inK_mul_residueRV b u).mp hK).resolve_right hu0
      have hpart : residuePart (b * residueRV u) = residuePart b * u := by
        apply residueRV_injective
        rw [residueRV_part hK, residueRV_mul, residueRV_part hbK]
      rw [hpart]
      exact E.mul_mem (hE (residuePart_mem B b hb)) hu
    · rw [residuePart, dif_neg hK]
      exact E.zero_mem

def coefficientContextOfSubstructure (B : LRV.Substructure M) (E : Subfield (ModelResidue M))
    (hE : residueParameterField B ≤ E) : CoefficientContext M where
  field := E
  coefficients := extendedCoefficients B E
  zero_mem := extendedCoefficients_base B E (by
    rw [RVOperations.zero_val]
    exact SubstructureRVGroup.rvZero_mem B)
  one_mem := extendedCoefficients_base B E (by
    rw [RVOperations.one_val]
    exact SubstructureRVGroup.rvOne_mem B)
  mul_mem := extendedCoefficients_mul B E
  inv_mem := extendedCoefficients_inv B E
  residuePart_mem := extendedCoefficients_part B E hE

end SpecialTransformations.Section4.ResiduePurity

end
