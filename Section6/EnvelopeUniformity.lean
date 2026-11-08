import Section6.NativeImageComparison
import Section6.NativeImageTransport
import Section6.NativeAmalgamation
import Section6.CountableEnvelope
import Section6.NativeExpandedSyntax

/-! The common-envelope argument combines the accepted earlier
preparation inputs with actual native algebraic envelopes. The input
constructor below contains only the earlier RV definition and vertical
obstacle interfaces; it contains no henselian elimination assertion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace SpecialTransformations.Section6.EnvelopeUniformity
open RVTermSupport RVAbstraction RVGraphLanguage AlignedComparison

inductive PreparationInputs {C I : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
    (z : I → C) : Prop
  | of_valuation {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
      (v : Valuation (VF (M := C)) Γ)
      (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
      (hdefs : RVQFDefinitions (Substructure.closure LRV (Set.range z)))
      (hObstacles : ∀ k, UniformVerticalObstacles v
        ((Substructure.closure LRV (Set.range z)) : Set C) k) : PreparationInputs z

/-- Exactly the accepted earlier preparation interfaces on finite
generated bases inside a genuinely saturated ACVF(0,0) model. -/
def EarlierPreparation : Prop :=
  ∀ (C : Type) (sC : LRV.Structure C) (hC : @Theory.Model LRV C sC Axioms.ACVF)
    (h00 : @Theory.Model LRV C sC Axioms.ACVF00)
    (hc : @CanonicalStructure.IsCanonical C sC) (κ : Cardinal),
    Order.succ Cardinal.aleph0 ≤ κ → @MarkerBridge.SatAt LRV C sC κ →
    ∀ (r m : ℕ) (z : Context r m → C),
      (∀ i, @sortEval C sC (sorts i) (z i)) → @PreparationInputs C (Context r m) sC hC z

variable {E : _root_.FirstOrder.Language.{0, 0}} {M N U V : Type}
variable [(Expanded E).Structure M] [(Expanded E).Structure N]
variable [LRV.Structure M] [LRV.Structure N] [LRV.Structure U] [LRV.Structure V]
variable [(LHom.sumInl : LRV →ᴸ Expanded E).IsExpansionOn M]
variable [(LHom.sumInl : LRV →ᴸ Expanded E).IsExpansionOn N]
variable [U ⊨ Axioms.ACVF] [V ⊨ Axioms.ACVF]

theorem existential_type_invariant (hEarlier : EarlierPreparation) {r m n : ℕ}
    (hM : M ⊨ HenselianTheory.expanded E) (hN : N ⊨ HenselianTheory.expanded E)
    (hU : U ⊨ Axioms.ACVF00) (hV : V ⊨ Axioms.ACVF00)
    (hcU : CanonicalStructure.IsCanonical (M := U))
    (hcV : CanonicalStructure.IsCanonical (M := V))
    (f : M ↪[LRV] U) (g : N ↪[LRV] V)
    (hX : HenselianInputs (ExpandedImages.Image f))
    (hY : HenselianInputs (ExpandedImages.Image g))
    (a : Context r m → M) (b : Context r m → N)
    (ha : ∀ i, ExpandedLogic.tagEval (E := E) (sorts i) (a i))
    (hb : ∀ i, ExpandedLogic.tagEval (E := E) (sorts i) (b i))
    (φ : (Expanded E).Formula ((Fin r ⊕ Fin n) ⊕ (Fin m ⊕ Empty))) (hφ : Fragment φ)
    (htype : ∀ χ : (Expanded E).Formula (Context r m),
      ExpandedLogic.IsVFQF χ → ExpandedLogic.WellSorted sorts (fun _ => .rv) χ →
      (χ.Realize a ↔ χ.Realize b)) :
    (NormalizedQuery.formula φ).Realize a ↔ (NormalizedQuery.formula φ).Realize b := by
  have haU := fun i => (NativeImageTransport.sorts_preserved f (sorts i) (a i)).mpr (ha i)
  have hbV := fun i => (NativeImageTransport.sorts_preserved g (sorts i) (b i)).mpr (hb i)
  have hqf := NativeExpandedSyntax.envelope_qf_type (inferInstance : U ⊨ Axioms.ACVF)
    (inferInstance : V ⊨ Axioms.ACVF) hcU hcV f g sorts a b haU hbV htype
  let κ := Order.succ Cardinal.aleph0
  obtain ⟨C, sC, h00, hc, hsat, j, k, hjk⟩ := NativeAmalgamation.common_countable_envelope
    hU hV hcU hcV (f ∘ a) (g ∘ b) hqf
  letI := sC
  letI : C ⊨ Axioms.ACVF := h00.mono (by intro σ hσ; exact Or.inl (Or.inl hσ))
  let f' := j.toEmbedding.comp f
  let g' := k.toEmbedding.comp g
  have halign : f' ∘ a = g' ∘ b := hjk
  have haC := fun i => (NativeImageTransport.sorts_preserved f' (sorts i) (a i)).mpr (ha i)
  have hX' := NativeImageTransport.henselian_range_comp f hX hcU hc j
  have hY' := NativeImageTransport.henselian_range_comp g hY hcV hc k
  have hp := hEarlier C sC inferInstance h00 hc κ le_rfl hsat r m (f' ∘ a) haC
  cases hp with
  | of_valuation v hv hdefs hObstacles =>
    exact NativeImageComparison.existential_type_invariant hM hN hc h00 f' g' hX' hY'
      a b halign haC hdefs v hv hObstacles φ hφ htype

end SpecialTransformations.Section6.EnvelopeUniformity
