import Section6.GeneratedDenaming
import Section6.ExpandedRenaming

/-! The sentence case of generated-base denaming returns precisely the
original free context, with no repeated RV coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.SentenceDenaming
open RVTermSupport RVAbstraction RVGraphExpansion

variable {C I : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
variable {E : _root_.FirstOrder.Language.{0, 0}}

theorem dename (hcan : CanonicalStructure.IsCanonical (M := C))
    (s : I → SortTag) (v : I → C) (hv : ∀ i, sortEval (s i) (v i))
    (φ : (Auxiliary (NamedExtra E (Substructure.closure LRV (Set.range v)))).Sentence) :
    ∃ χ : (Expanded E).Formula I, ExpandedLogic.IsVFQF χ ∧
      ExpandedLogic.WellSorted s (fun _ => .rv) χ ∧
      ∀ (X : LRV.Substructure C) (hBX : Substructure.closure LRV (Set.range v) ≤ X)
        [E.Structure (SubRV (X : Set C))],
        letI := RVSubstructure.extraStructure (E := E) X
        letI := namedExtraStructure (E := E) (Substructure.closure LRV (Set.range v)) X hBX
        letI := RVSubstructure.auxiliaryStructure (E := NamedExtra E
          (Substructure.closure LRV (Set.range v))) X
        (χ.Realize (fun i => (⟨v i, hBX (Substructure.subset_closure (Set.mem_range_self i))⟩ : X)) ↔
          φ.Realize (M := SubRV (X : Set C))) := by
  obtain ⟨χ, hχ, hsχ, heχ⟩ := GeneratedDenaming.dename_rv_formula hcan s v hv φ
  let e : I ⊕ Empty ≃ I := Equiv.sumEmpty I Empty
  have he : ∀ j, s (e j) = Sum.elim s (fun _ => SortTag.rv) j := by
    intro j
    cases j with
    | inl i => rfl
    | inr i => exact i.elim
  refine ⟨(BoundedFormula.relabelEquiv e) χ, ExpandedRenaming.isVFQF e χ hχ,
    ExpandedRenaming.wellSorted e _ _ he _ χ hsχ, ?_⟩
  intro X hBX _
  letI := RVSubstructure.extraStructure (E := E) X
  have h := heχ X hBX (fun i : Empty => i.elim)
  have hvX :
      (fun i => (⟨v i, hBX (Substructure.subset_closure (Set.mem_range_self i))⟩ : X)) ∘ e =
      Sum.elim (fun i => (⟨v i, hBX (Substructure.subset_closure (Set.mem_range_self i))⟩ : X))
        (RVSubstructure.inclusion X ∘ (fun i : Empty => i.elim)) := by
    funext j
    cases j with
    | inl i => rfl
    | inr i => exact i.elim
  have h0 : (fun i : Empty => i.elim) = (default : Empty → SubRV (X : Set C)) :=
    Subsingleton.elim _ _
  simpa only [Formula.Realize, BoundedFormula.realize_relabelEquiv, hvX, Sentence.Realize, h0] using h

end SpecialTransformations.Section6.SentenceDenaming
