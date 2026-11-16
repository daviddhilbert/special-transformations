module

public import Section6.EarlierPreparation
public import Section6.ExpandedNormalForm
public import Section6.NativeEnvelopeConstruction

@[expose] public section

/-! Standalone finite-tuple elimination in the expanded henselian theory. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.Paper

open RVTermSupport

/-- Eliminate a finite existential VF tuple from a VF-quantifier-free
formula, preserving every original free VF and RV variable. The resulting
formula works in every model of the expanded henselian theory. -/
theorem lemma_6_3 (E : FirstOrder.Language.{0, 0}) {V R : Type} [Fintype V] [Fintype R]
    {n : ℕ} (φ : (Expanded E).Formula ((V ⊕ Fin n) ⊕ R))
    (hs : ExpandedLogic.WellSorted (Sum.elim (fun _ => .vf) (fun _ => .rv)) (fun _ => .rv) φ)
    (hq : ExpandedLogic.IsVFQF φ) :
    ∃ ψ : (Expanded E).Formula (V ⊕ R), ExpandedLogic.IsVFQF ψ ∧
      ExpandedLogic.WellSorted (Sum.elim (fun _ => .vf) (fun _ => .rv)) (fun _ => .rv) ψ ∧
      ∀ (M : (HenselianTheory.expanded E).ModelType.{0, 0, 0}) (v : V → M) (r : R → M),
        (∀ i, ExpandedLogic.tagEval (E := E) .vf (v i)) →
        (∀ i, ExpandedLogic.tagEval (E := E) .rv (r i)) →
        ((∃ x : Fin n → M, (∀ i, ExpandedLogic.tagEval (E := E) .vf (x i)) ∧
          φ.Realize (Sum.elim (Sum.elim v x) r)) ↔ ψ.Realize (Sum.elim v r)) := by
  have hEnv := UniformNormalizedElimination.nativeEnvelopes E
  obtain ⟨χ, hχ, hnorm⟩ :=
    HenselianElimination.rvLiteralNormalForm_of_nativeEnvelopes hEnv (V ⊕ Fin n) R φ hs hq
  obtain ⟨ψ, hψ, hsψ, helim⟩ :=
    FiniteNormalizedElimination.eliminate EnvelopeUniformity.earlierPreparation hEnv χ hχ
  refine ⟨ψ, hψ, hsψ, fun M v r hv hr => Iff.trans ?_ (helim M v r hv hr)⟩
  apply exists_congr
  intro x
  refine and_congr_right fun hx => hnorm M (Sum.elim v x) r ?_ hr
  rintro (i | i)
  · exact hv i
  · exact hx i

end SpecialTransformations.Section6.Paper
