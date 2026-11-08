import Section6.OneStepPresentation
import Section6.FiniteNormalizedElimination

/-! Join the constructed normalized existential theorem to the full
logical QE interface. Earlier RV-literal normalization is taken as given,
as authorized by the author: it changes only atoms of a formula already
without VF quantifiers. It does not eliminate the FV witness quantified
by the theorem below. The native representation and earlier preparation
inputs remain separately visible. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.HenselianElimination
open RVTermSupport RVAbstraction FiniteSortContext

def RVLiteralNormalForm (E : _root_.FirstOrder.Language.{0, 0}) : Prop :=
  ∀ (V R : Type) [Fintype V] [Fintype R] (φ : (Expanded E).Formula (V ⊕ R)),
    ExpandedLogic.WellSorted (Sum.elim (fun _ => .vf) (fun _ => .rv)) (fun _ => .rv) φ →
    ExpandedLogic.IsVFQF φ →
    ∃ χ : (Expanded E).Formula (V ⊕ R), Fragment χ ∧
      ∀ (M : (HenselianTheory.expanded E).ModelType.{0, 0, 0}) (v : V → M) (r : R → M),
        (∀ i, ExpandedLogic.tagEval (E := E) .vf (v i)) →
        (∀ i, ExpandedLogic.tagEval (E := E) .rv (r i)) →
        (φ.Realize (Sum.elim v r) ↔ χ.Realize (Sum.elim v r))

theorem finite_oneStep (E : _root_.FirstOrder.Language.{0, 0})
    (hEarlier : EnvelopeUniformity.EarlierPreparation)
    (hEnvelopes : UniformNormalizedElimination.NativeEnvelopes E)
    (hNormal : RVLiteralNormalForm E) : FiniteContextLogic.FiniteOneStep (HenselianTheory.expanded E) := by
  intro I _ s n sn φ hsφ hφ
  letI := Fintype.ofFinite I
  let V := VFPart (Sum.elim s sn)
  let R := RVPart (Sum.elim s sn)
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype R := Fintype.ofFinite R
  let θ : (Expanded E).Formula ((V ⊕ Fin 1) ⊕ R) := OneStepPresentation.body s sn φ
  obtain ⟨χ, hχ, hχsem⟩ := hNormal (V ⊕ Fin 1) R θ
    (OneStepPresentation.body_wellSorted s sn φ hsφ) (OneStepPresentation.body_isVFQF s sn φ hφ)
  obtain ⟨ψ, hψ, hsψ, heψ⟩ := FiniteNormalizedElimination.eliminate hEarlier hEnvelopes χ hχ
  let g : V ⊕ R → I ⊕ Fin n := (partition (Sum.elim s sn)).symm
  have hg : ∀ i : V ⊕ R, Sum.elim s sn (g i) = Sum.elim (fun _ => SortTag.vf) (fun _ => .rv) i := by
    rintro (i | i) <;> exact i.property
  have hsψ' := ExpandedParameterRelabel.wellSorted g
    (Sum.elim (fun _ => .vf) (fun _ => .rv)) s sn (fun _ => .rv) hg ψ hsψ
  rw [ExpandedOpenBounds.sortAssem_empty] at hsψ'
  refine ⟨BoundedFormula.relabel g ψ, ExpandedParameterRelabel.isVFQF g ψ hψ, hsψ', ?_⟩
  intro M _ hM v x hv hx
  letI := hM
  letI : Nonempty M := ⟨Structure.funMap (L := Expanded E) (.inl Fn.rvZero) Fin.elim0⟩
  let model := Theory.ModelType.of (HenselianTheory.expanded E) M
  let z := Sum.elim v x
  let vV : V → M := fun i => z i.val
  let vR : R → M := fun i => z i.val
  have hz : ∀ i, ExpandedLogic.tagEval (E := E) (Sum.elim s sn i) (z i) := by
    rintro (i | i)
    · exact hv i
    · exact hx i
  have hvV : ∀ i, ExpandedLogic.tagEval (E := E) .vf (vV i) := by
    intro i
    have h := hz i.val
    rw [i.property] at h
    exact h
  have hvR : ∀ i, ExpandedLogic.tagEval (E := E) .rv (vR i) := by
    intro i
    have h := hz i.val
    rw [i.property] at h
    exact h
  have hwitness (w : Fin 1 → M) (hw : ∀ i, ExpandedLogic.tagEval (E := E) .vf (w i)) :
      χ.Realize (Sum.elim (Sum.elim vV w) vR) ↔ φ.Realize v (Fin.snoc x (w 0)) := by
    have hn := hχsem model (Sum.elim vV w) vR
      (by rintro (i | i); exact hvV i; exact hw i) hvR
    exact hn.symm.trans (OneStepPresentation.body_realize s sn φ v x w)
  have hex :
      (∃ a : M, ExpandedLogic.tagEval (E := E) .vf a ∧ φ.Realize v (Fin.snoc x a)) ↔
      ∃ w : Fin 1 → M, (∀ i, ExpandedLogic.tagEval (E := E) .vf (w i)) ∧
        χ.Realize (Sum.elim (Sum.elim vV w) vR) := by
    constructor
    · rintro ⟨a, ha, hφa⟩
      exact ⟨fun _ => a, fun _ => ha, (hwitness (fun _ => a) (fun _ => ha)).mpr hφa⟩
    · rintro ⟨w, hw, hχw⟩
      exact ⟨w 0, hw 0, (hwitness w hw).mp hχw⟩
  have hclose : (BoundedFormula.relabel g ψ).Realize v x ↔ Formula.Realize ψ (Sum.elim vV vR) := by
    rw [BoundedFormula.realize_relabel]
    have h0 : x ∘ (Fin.natAdd n : Fin 0 → Fin (n + 0)) = (default : Fin 0 → M) :=
      Subsingleton.elim _ _
    have hv' : Sum.elim v (x ∘ Fin.castAdd 0) ∘ g = Sum.elim vV vR := by
      funext i
      cases i <;> rfl
    rw [h0, hv']
    rfl
  exact hex.trans ((heψ model vV vR hvV hvR).trans hclose.symm)

/-- Relative QE in the canonical unnamed henselian language, with the
authorized earlier normal form, preparation and ordinary envelope inputs
printed explicitly. The named-base adapter is a separate logical step. -/
theorem hasVFQE (E : _root_.FirstOrder.Language.{0, 0})
    (hEarlier : EnvelopeUniformity.EarlierPreparation)
    (hEnvelopes : UniformNormalizedElimination.NativeEnvelopes E)
    (hNormal : RVLiteralNormalForm E) : ExpandedLogic.HasVFQE (HenselianTheory.expanded E) :=
  FiniteContextLogic.hasVFQE_of_finite _ (finite_oneStep E hEarlier hEnvelopes hNormal)

end SpecialTransformations.Section6.HenselianElimination
