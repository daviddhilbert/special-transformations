module

public import Section4.ResidueDefinableField
public import Section4.ResiduePolynomialFunctions
public import Section4.ResidueAlgebraicityForward

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem residue_unary_image_definable
    (hcan : CanonicalStructure.IsCanonical (M := M))
    (E : Subfield (ModelResidue M)) (S : Set M)
    (hE : E ≤ residueDefinableField S) (D : Set (ModelResidue M))
    (hD : (E : Set (ModelResidue M)).Definable₁ Language.ring D) :
    DefinableAt S .rv (residueRaw '' D) := by
  have h := residueFieldImage_definable_of_definable_names hcan E S
    (fun c => hE c.property) {a : Fin 1 → ModelResidue M | a 0 ∈ D} hD
  refine ⟨?_, ?_⟩
  · convert h using 1
    ext z
    change (∃ a ∈ D, residueRaw a = z 0) ↔
      ∃ a : Fin 1 → ModelResidue M, a 0 ∈ D ∧ residueFieldValues a = z
    constructor
    · rintro ⟨a, ha, he⟩
      refine ⟨fun _ => a, ha, ?_⟩
      funext i
      fin_cases i
      exact he
    · rintro ⟨a, ha, he⟩
      exact ⟨a 0, ha, congrFun he 0⟩
  · rintro z ⟨a, ha, rfl⟩
    exact (residueRV a).property

/-- Every field-algebraic residue element is RV-algebraic over any base
over which its coefficient field is definable. -/
theorem residue_algebraicAt_of_isAlgebraic
    (hcan : CanonicalStructure.IsCanonical (M := M))
    (E : Subfield (ModelResidue M)) (S : Set M)
    (hE : E ≤ residueDefinableField S) (a : ModelResidue M)
    (ha : IsAlgebraic E a) : AlgebraicAt S .rv (residueRaw a) := by
  obtain ⟨p, hp, hpa⟩ := ha
  let D : Set (ModelResidue M) := {x | p.eval₂ E.subtype x = 0}
  have haD : a ∈ D := by
    change p.eval₂ E.subtype a = 0
    exact hpa
  exact ⟨residueRaw '' D,
    residue_unary_image_definable hcan E S hE D (polynomial_roots_definable E p),
    (polynomial_roots_finite E p hp).image residueRaw, ⟨a, haD, rfl⟩⟩

/-- The actual residue-field and RV algebraic closures agree over the
base substructure together with a finite tuple of residue parameters. -/
theorem residue_algebraicAt_iff_isAlgebraic
    (hcan : CanonicalStructure.IsCanonical (M := M))
    (B : LRV.Substructure M) {n : ℕ}
    (a : Fin n → ModelResidue M) (b : ModelResidue M) :
    AlgebraicAt ((B : Set M) ∪ Set.range (fun i => residueRaw (a i))) .rv (residueRaw b) ↔
      IsAlgebraic (tupleField (residueParameterField B) a) b := by
  constructor
  · exact residue_isAlgebraic_over_tuple B a b
  · exact residue_algebraicAt_of_isAlgebraic hcan _ _
      (tupleField_le_residueDefinableField B a) b

end SpecialTransformations.Section4.ResiduePurity

end
