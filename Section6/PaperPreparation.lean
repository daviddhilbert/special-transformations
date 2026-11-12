module

public import Section6.EarlierPreparation
public import Section6.ExpandedNormalForm
public import Section6.SyntacticLemma63
public import Section6.NamedLogic
public import Section6.DenefPasConclusion

@[expose] public section

/-! Section 6 statements using the proved earlier preparation and the
normalization obtained from the native envelopes. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section5

namespace SpecialTransformations.Section6.Paper

section Native

open RVTermSupport RVAbstraction RVGraphLanguage NamedLanguage

theorem syntactic_lemma_6_3 {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
    {κ : Cardinal} (hs : Saturated C κ) (h00 : C ⊨ Axioms.ACVF00)
    (S : LRV.Substructure C) (hsmall : Cardinal.mk ↥(S : Set C) < κ)
    {E : _root_.FirstOrder.Language.{0, 0}} {β : Type} {n : ℕ}
    (φ : (Expanded E).Formula ((SubVF S ⊕ Fin n) ⊕ (SubRV (S : Set C) ⊕ β)))
    (hφ : Fragment φ) :
    ∃ ψ : (Source E S).Formula β, RVQuantified S ψ ∧
      ∀ (X : LRV.Substructure C) (hSX : S ≤ X)
        [E.Structure (SubRV (X : Set C))], HenselianInputs X →
        ∀ b : β → SubRV (X : Set C),
        (@Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _
          (FVBinding.existsVF S (OriginalParameterSyntax.nameInput S φ))
          (RVSubstructure.inclusion X ∘ b) ↔
          @Formula.Realize _ _ (sourceStructure (E := E) S X hSX) _ ψ
            (RVSubstructure.inclusion X ∘ b)) :=
  Section6.syntactic_lemma_6_3 S (rvQFDefinitions_of_acvf S) h00
    Values.presentationValuation Values.presentation_compatible
    (uniformVerticalObstacles hs hsmall Values.presentationValuation Values.presentation_compatible)
    φ hφ

theorem proposition_6_4_of_native_inputs {C : Type} [LRV.Structure C] (E : _root_.FirstOrder.Language.{0, 0})
    (S : LRV.Substructure C) (sS : ↥(S : Set C) → SortTag)
    (hS : ∀ s, sortEval (sS s) (s : C))
    (hEnvelopes : UniformNormalizedElimination.NativeEnvelopes E) :
    NamedLogic.HasVFQE sS (HenselianTheory.named E S) :=
  NamedLogic.proposition_6_4 E S sS hS EnvelopeUniformity.earlierPreparation
    hEnvelopes (HenselianElimination.rvLiteralNormalForm_of_nativeEnvelopes hEnvelopes)

end Native

section DenefPas

open AngularComponent DenefPasCodes DenefPasLanguage DenefPasParameters DenefPasSorts

theorem corollary_6_5_of_native_inputs (hRecognition : DenefPasHenselianModels.OrdinaryRecognition)
    (E : _root_.FirstOrder.Language.{0, 0}) (p : AuxiliarySorts E)
    (hEnv : UniformNormalizedElimination.NativeEnvelopes (DenefPasMorley.signature E))
    {I : Type} (s : I → SortKind) (φ : (language E).Formula I) :
    ∃ ψ : (language E).Formula I, WellSorted p s Fin.elim0 ψ ∧ IsFieldQF ψ ∧
      ∀ (K Γ : Type) [Field K] [LinearOrderedCommGroupWithZero Γ]
        (v : Valuation K Γ) (a : Data v) [CharZero K] [CharZero (Residue v)]
        [HenselianLocalRing v.valuationSubring] (d : AuxiliaryStructure p v),
        letI : E.Structure (Aux v) := auxiliaryStructure p v d
        letI : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
        ∀ z : I → DenefPasAuxLift.Model E v a, Sorted E v a s z →
          (φ.Realize z ↔ ψ.Realize z) :=
  DenefPasTheorem.corollary_6_5 hRecognition E p EnvelopeUniformity.earlierPreparation
    hEnv (HenselianElimination.rvLiteralNormalForm_of_nativeEnvelopes hEnv) s φ

end DenefPas

end SpecialTransformations.Section6.Paper
