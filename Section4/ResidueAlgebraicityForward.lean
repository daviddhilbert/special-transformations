module

public import Section4.ResidueRelativeQF
public import Section4.PureFieldAlgebraicity
public import Section4.TupleTranscendence
public import ProvedResidueClosure
public import VFAlgClosed

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem residue_unary_field_definable (B : LRV.Substructure M) (E : Subfield (ModelResidue M))
    (hE : residueParameterField B ≤ E) {D : Set M}
    (hD : DefinableAt (residueExtendedBase B E) .rv D) :
    (E : Set (ModelResidue M)).Definable₁ Language.ring
      {a : ModelResidue M | (residueRV a).val ∈ D} := by
  obtain ⟨⟨p, φ, hw, he⟩, hRV⟩ := hD
  let s : Fin 1 → CanonicalRV.RVSort M := fun _ => 1
  have hs : ∀ i, s i ∈ extendedCoefficients B E := by
    intro i
    exact extendedCoefficients_base B E (by
      change (1 : CanonicalRV.RVSort M).val ∈ B
      rw [RVOperations.one_val]
      exact SubstructureRVGroup.rvOne_mem B)
  let Q := scopedContextOfSubstructure B E hE p s hs
  have h := Scoped.formula_definable Q φ hw
  change Relative.Def E _ at h
  change Relative.Def E {z : Fin 1 → ModelResidue M | (residueRV (z 0)).val ∈ D}
  convert h using 1
  ext z
  have h' := Set.ext_iff.mp he (residueInputs s z)
  change ((residueInputs s z) 0 ∈ D ↔
    (∀ i, iRV (residueInputs s z i)) ∧ φ.Realize p.values (residueInputs s z)) at h'
  have hz : (residueInputs s z) 0 = (residueRV (z 0)).val := by
    simp only [residueInputs, s, one_mul]
  rw [hz] at h'
  exact h'.trans (and_iff_right (fun i => by
    change iRV (s i * residueRV (z i)).val
    exact (s i * residueRV (z i)).property))

/-- RV algebraicity of a residue element over B and named residue-field
parameters implies ordinary algebraicity over the actual coefficient field. -/
theorem residue_isAlgebraic_of_algebraicAt (B : LRV.Substructure M)
    (E : Subfield (ModelResidue M)) (hE : residueParameterField B ≤ E) (a : ModelResidue M)
    (ha : AlgebraicAt (residueExtendedBase B E) .rv (residueRV a).val) : IsAlgebraic E a := by
  obtain ⟨D, hD, hfin, haD⟩ := ha
  let U : Set (ModelResidue M) := {x | (residueRV x).val ∈ D}
  have hU : (E : Set (ModelResidue M)).Definable₁ Language.ring U :=
    residue_unary_field_definable B E hE hD
  have hi : Function.Injective (fun x : ModelResidue M => (residueRV x).val) :=
    Subtype.val_injective.comp residueRV_injective
  have hUf : U.Finite := hfin.preimage hi.injOn
  letI : IsAlgClosed (SpecialTransformations.Milestone0.Transfer.VFType (M := M)) :=
    VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  exact finite_field_definable_isAlgebraic E U hU hUf a haD

theorem residue_isAlgebraic_over_tuple (B : LRV.Substructure M) {n : ℕ}
    (a : Fin n → ModelResidue M) (b : ModelResidue M)
    (hb : AlgebraicAt ((B : Set M) ∪ Set.range (fun i => (residueRV (a i)).val))
      .rv (residueRV b).val) : IsAlgebraic (tupleField (residueParameterField B) a) b := by
  let E := tupleField (residueParameterField B) a
  apply residue_isAlgebraic_of_algebraicAt B E (le_tupleField _ _) b
  apply hb.mono
  rintro x (hx | ⟨i, rfl⟩)
  · exact Or.inl hx
  · exact Or.inr ⟨⟨a i, tuple_mem_tupleField (residueParameterField B) a i⟩, rfl⟩

end SpecialTransformations.Section4.ResiduePurity

end
