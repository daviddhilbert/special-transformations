module

public import Section6.PaperPreparation
public import Section6.NativeEnvelopeConstruction
public import Section6.DenefPasRecognition

@[expose] public section

/-! Relative field-sort quantifier elimination for the native henselian
theory and for Denef–Pas expansions. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.Paper

theorem proposition_6_4 {C : Type} [LRV.Structure C] (E : FirstOrder.Language.{0, 0})
    (S : LRV.Substructure C) (sS : ↥(S : Set C) → SortTag)
    (hS : ∀ s, sortEval (sS s) (s : C)) :
    NamedLogic.HasVFQE sS (HenselianTheory.named E S) :=
  proposition_6_4_of_native_inputs E S sS hS
    (UniformNormalizedElimination.nativeEnvelopes E)

open AngularComponent DenefPasCodes DenefPasLanguage DenefPasParameters DenefPasSorts

theorem corollary_6_5 (E : FirstOrder.Language.{0, 0}) (p : AuxiliarySorts E)
    {I : Type} (s : I → SortKind) (φ : (language E).Formula I) :
    ∃ ψ : (language E).Formula I, WellSorted p s Fin.elim0 ψ ∧ IsFieldQF ψ ∧
      ∀ (K Γ : Type) [Field K] [LinearOrderedCommGroupWithZero Γ]
        (v : Valuation K Γ) (a : Data v) [CharZero K] [CharZero (Residue v)]
        [HenselianLocalRing v.valuationSubring] (d : AuxiliaryStructure p v),
        letI : E.Structure (Aux v) := auxiliaryStructure p v d
        letI : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
        ∀ z : I → DenefPasAuxLift.Model E v a, Sorted E v a s z →
          (φ.Realize z ↔ ψ.Realize z) :=
  corollary_6_5_of_native_inputs DenefPasHenselianModels.ordinaryRecognition E p
    (UniformNormalizedElimination.nativeEnvelopes (DenefPasMorley.signature E)) s φ

#check @proposition_6_4
#print axioms proposition_6_4
#check @corollary_6_5
#print axioms corollary_6_5

end SpecialTransformations.Section6.Paper
