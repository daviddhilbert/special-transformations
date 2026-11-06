import Section6.EnvelopeUniformity
import Section6.SortedFragment

/-! Compactness turns the proved common-envelope comparison into one
formula for all models. NativeEnvelopes records the ordinary algebraic
representation input separately; no elimination, type-invariance or
functional-closure assertion occurs in its constructor. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.UniformNormalizedElimination
open RVTermSupport RVAbstraction AlignedComparison

inductive NativeEnvelope (M : Type) [LRV.Structure M] : Prop
  | in_model {U : Type} [LRV.Structure U] [U ⊨ Axioms.ACVF]
      (h00 : U ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := U))
      (f : M ↪[LRV] U) (hH : HenselianInputs (ExpandedImages.Image f)) : NativeEnvelope M

/-- Ordinary valued-field representation and the displayed earlier/EP
data used by Lemma 6.2. This remains an explicit reference input. -/
def NativeEnvelopes (E : _root_.FirstOrder.Language.{0, 0}) : Prop :=
  ∀ (M : Type) [sM : (Expanded E).Structure M], M ⊨ HenselianTheory.expanded E →
    letI := (LHom.sumInl : LRV →ᴸ Expanded E).reduct M
    NativeEnvelope M

theorem eliminate (E : _root_.FirstOrder.Language.{0, 0})
    (hMarker : NativeAmalgamation.SaturatedElementaryExtensionAt)
    (hEarlier : EnvelopeUniformity.EarlierPreparation) (hEnvelopes : NativeEnvelopes E)
    {r m n : ℕ}
    (φ : (Expanded E).Formula ((Fin r ⊕ Fin n) ⊕ (Fin m ⊕ Empty))) (hφ : Fragment φ) :
    ∃ ψ : (Expanded E).Formula (Context r m), ExpandedLogic.IsVFQF ψ ∧
      ExpandedLogic.WellSorted sorts (fun _ => .rv) ψ ∧
      ∀ (M : (HenselianTheory.expanded E).ModelType.{0, 0, 0}) (a : Context r m → M),
        (∀ i, ExpandedLogic.tagEval (E := E) (sorts i) (a i)) →
        ((NormalizedQuery.formula φ).Realize a ↔ ψ.Realize a) := by
  obtain ⟨ψ, ⟨hψ, hsψ⟩, he⟩ := SortedFragment.definable_of_sorted_type_invariant
    (HenselianTheory.expanded E) sorts (NormalizedQuery.formula φ) (fun M N a b ha hb ht => by
      letI := (LHom.sumInl : LRV →ᴸ Expanded E).reduct M
      letI := (LHom.sumInl : LRV →ᴸ Expanded E).reduct N
      have hM := hEnvelopes M (inferInstance : M ⊨ HenselianTheory.expanded E)
      have hN := hEnvelopes N (inferInstance : N ⊨ HenselianTheory.expanded E)
      cases hM with
      | in_model hU hcU f hX =>
        cases hN with
        | in_model hV hcV g hY =>
          exact EnvelopeUniformity.existential_type_invariant hMarker hEarlier
            inferInstance inferInstance hU hV hcU hcV f g hX hY a b ha hb φ hφ
            (fun χ hχ hsχ => ht χ ⟨hχ, hsχ⟩))
  exact ⟨ψ, hψ, hsψ, he⟩

end SpecialTransformations.Section6.UniformNormalizedElimination
