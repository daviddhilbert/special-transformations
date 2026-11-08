import Section6.UniformNormalizedElimination
import Section6.RVFragmentRenaming

/-! The uniform normalized-form theorem for arbitrary finite VF and
RV parameter types. Only the variable indices change; FV parameters
remain free and all quantified witnesses are the original FV tuple. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.FiniteNormalizedElimination
open RVTermSupport RVAbstraction

variable {E : _root_.FirstOrder.Language.{0, 0}} {V R : Type} [Fintype V] [Fintype R]

def rvEquiv : R ≃ Fin (Fintype.card R) ⊕ Empty :=
  (Fintype.equivFin R).trans (Equiv.sumEmpty _ Empty).symm

def freeEquiv : V ⊕ R ≃ AlignedComparison.Context (Fintype.card V) (Fintype.card R) :=
  (Fintype.equivFin V).sumCongr rvEquiv

def inputEquiv (n : ℕ) : (V ⊕ Fin n) ⊕ R ≃
    (Fin (Fintype.card V) ⊕ Fin n) ⊕ (Fin (Fintype.card R) ⊕ Empty) :=
  ((Fintype.equivFin V).sumCongr (Equiv.refl _)).sumCongr rvEquiv

theorem eliminate
    (hEarlier : EnvelopeUniformity.EarlierPreparation)
    (hEnvelopes : UniformNormalizedElimination.NativeEnvelopes E) {n : ℕ}
    (φ : (Expanded E).Formula ((V ⊕ Fin n) ⊕ R)) (hφ : Fragment φ) :
    ∃ ψ : (Expanded E).Formula (V ⊕ R), ExpandedLogic.IsVFQF ψ ∧
      ExpandedLogic.WellSorted (Sum.elim (fun _ => .vf) (fun _ => .rv)) (fun _ => .rv) ψ ∧
      ∀ (M : (HenselianTheory.expanded E).ModelType.{0, 0, 0}) (v : V → M) (r : R → M),
        (∀ i, ExpandedLogic.tagEval (E := E) .vf (v i)) →
        (∀ i, ExpandedLogic.tagEval (E := E) .rv (r i)) →
        ((∃ x : Fin n → M, (∀ i, ExpandedLogic.tagEval (E := E) .vf (x i)) ∧
          φ.Realize (Sum.elim (Sum.elim v x) r)) ↔ ψ.Realize (Sum.elim v r)) := by
  let φ' := (BoundedFormula.relabelEquiv (inputEquiv (V := V) (R := R) n)) φ
  have hφ' : Fragment φ' := RVFragmentRenaming.fragment
    ((Fintype.equivFin V).sumCongr (Equiv.refl _)) rvEquiv φ hφ
  obtain ⟨ψ, hψ, hsψ, he⟩ := UniformNormalizedElimination.eliminate E hEarlier hEnvelopes φ' hφ'
  have hs : ∀ j, Sum.elim (fun _ => SortTag.vf) (fun _ => .rv)
      ((freeEquiv (V := V) (R := R)).symm j) = AlignedComparison.sorts j := by
    intro j
    rcases j with j | (j | j)
    · rfl
    · rfl
    · exact j.elim
  refine ⟨(BoundedFormula.relabelEquiv (freeEquiv (V := V) (R := R)).symm) ψ,
    ExpandedRenaming.isVFQF _ ψ hψ,
    ExpandedRenaming.wellSorted _ _ _ hs _ ψ hsψ, ?_⟩
  intro M v r hv hr
  let c := v ∘ (Fintype.equivFin V).symm
  let d := Sum.elim (r ∘ (Fintype.equivFin R).symm) (fun e : Empty => e.elim)
  let a := Sum.elim c d
  have ha : ∀ i, ExpandedLogic.tagEval (E := E) (AlignedComparison.sorts i) (a i) := by
    intro i
    rcases i with i | (i | i)
    · exact hv _
    · exact hr _
    · exact i.elim
  have hbody (x : Fin n → M) :
      Formula.Realize φ' (Sum.elim (Sum.elim c x) d) ↔ φ.Realize (Sum.elim (Sum.elim v x) r) := by
    have hi : Sum.elim (Sum.elim c x) d ∘ inputEquiv (V := V) (R := R) n =
        Sum.elim (Sum.elim v x) r := by
      funext j
      rcases j with (j | j) | j
      · simp [inputEquiv, c]
      · rfl
      · simp [inputEquiv, rvEquiv, d]
    simpa only [φ', Formula.Realize, BoundedFormula.realize_relabelEquiv, hi]
  have hout : (Sum.elim v r) ∘ (freeEquiv (V := V) (R := R)).symm = a := by
    funext j
    rcases j with j | (j | j)
    · rfl
    · rfl
    · exact j.elim
  rw [Formula.Realize, BoundedFormula.realize_relabelEquiv, hout]
  have hquery := NormalizedQuery.realize φ' c d
  have hbind :
      (∃ x : Fin n → M, (∀ i, ExpandedLogic.tagEval (E := E) .vf (x i)) ∧
        φ.Realize (Sum.elim (Sum.elim v x) r)) ↔ (NormalizedQuery.formula φ').Realize a := by
    rw [hquery]
    exact exists_congr (fun x => and_congr Iff.rfl (hbody x).symm)
  exact hbind.trans (he M a ha)

end SpecialTransformations.Section6.FiniteNormalizedElimination
