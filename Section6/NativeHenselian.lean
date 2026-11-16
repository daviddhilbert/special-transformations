module

public import Section6.HenselianValuationRing
public import Section6.NativeRV

@[expose] public section

/-! Ordinary characteristic zero and henselianity of the valued field
extracted from a model of the native theory. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer RVElim

namespace SpecialTransformations.Section6.NativeValuation

variable {M Γ : Type} [LRV.Structure M] [LinearOrderedCommGroupWithZero Γ]
variable [hM : M ⊨ HenselianTheory.valuedField]
variable (v : Valuation (NativeField.VF M) Γ)
variable (hv : ∀ a b, predV a b ↔ v a ≤ v b)

def fieldInterpretation : HenselianTheory.FieldInterpretation (M := M) v where
  pack := Subtype.val
  injective := Subtype.val_injective
  sort z := ⟨fun h => ⟨⟨z, h⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact a.property⟩
  zero := rfl
  one := rfl
  add _ _ := rfl
  neg _ := rfl
  mul _ _ := rfl
  rvOne := NativeRV.rv_one
  compare := hv

omit hM in
theorem valuedField_of_hen00 (h : M ⊨ HenselianTheory.hen00) :
    M ⊨ HenselianTheory.valuedField :=
  h.mono (fun _ hσ => Or.inl (Or.inl (Or.inl hσ)))

include hv

theorem charZero (h : M ⊨ HenselianTheory.hen00) : CharZero (NativeField.VF M) := by
  apply charZero_of_inj_zero
  intro n hn
  cases n with
  | zero => rfl
  | succ k =>
    have hσ : Axioms.charZeroVF k ∈ HenselianTheory.hen00 := Or.inl (Or.inr ⟨k, rfl⟩)
    have he := sentence_realize h hσ
    change ¬ (pEq (tVFNumeral (k + 1)) tVFZero : Bf 0).Realize default default at he
    simp only [pEq, BoundedFormula.realize_bdEqual,
      HenselianTheory.realize_numeral (fieldInterpretation v hv), realize_tVFZero,
      ← (fieldInterpretation v hv).zero, (fieldInterpretation v hv).injective.eq_iff] at he
    exact (he hn).elim

theorem residueCharZero (h : M ⊨ HenselianTheory.hen00) :
    CharZero (IsLocalRing.ResidueField v.valuationSubring) := by
  apply (CharZero.charZero_iff_forall_prime_ne_zero _).mpr
  intro p hp he
  have hσ : Axioms.residueCharZero p ∈ HenselianTheory.hen00 := Or.inr ⟨p, hp, rfl⟩
  have hm := sentence_realize h hσ
  change ¬ (HenselianTheory.inMaximalIdeal (tVFNumeral p : Tm 0)).Realize default default at hm
  rw [HenselianTheory.realize_inMaximalIdeal (fieldInterpretation v hv) _ _ _
    (HenselianTheory.realize_numeral (fieldInterpretation v hv) _ p)] at hm
  let z : v.valuationSubring := p
  have hz : IsLocalRing.residue v.valuationSubring z = 0 := by
    simpa only [z, map_natCast] using he
  have hsmall := (Valuation.mem_maximalIdeal_iff _ v).mp ((IsLocalRing.residue_eq_zero_iff z).mp hz)
  have hcast : (z : NativeField.VF M) = (p : NativeField.VF M) :=
    map_natCast v.valuationSubring.subtype p
  exact hm (hcast ▸ hsmall)

theorem henselian (h : M ⊨ HenselianTheory.hen00) : HenselianLocalRing v.valuationSubring := by
  apply HenselianTheory.valuationRing_henselian v
  intro n
  apply (HenselianTheory.henselScheme_realize (fieldInterpretation v hv) n).mp
  exact sentence_realize h (Or.inl (Or.inl (Or.inr ⟨n, rfl⟩)))

theorem nontrivial : ∃ x : NativeField.VF M, x ≠ 0 ∧ v x < 1 := by
  have hm : Axioms.axNontrivialRV ∈ HenselianTheory.valuedField := by
    simp [HenselianTheory.valuedField, Axioms.repairRV, Axioms.ofList]
  have he := sentence_realize hM hm
  change (exSorted .vf (∼(pEq &0 tVFZero) ⊓ ∼(pLe (tRv &0) (tRv tVFOne)))).Realize
    (default : Empty → M) (default : Fin 0 → M) at he
  have hlast (x : M) : (Fin.snoc (default : Fin 0 → M) x : Fin 1 → M) 0 = x :=
    Fin.snoc_last (α := fun _ : Fin 1 => M) x default
  simp only [exSorted,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, BoundedFormula.realize_not,
    sortPred, pVF_realize, pEq, BoundedFormula.realize_bdEqual, realize_tVFZero,
    realize_pLe, realize_tRv, realize_tVFOne, realize_tv_last_snoc,
    RVCalc.realize_var_inr, hlast] at he
  obtain ⟨x, hx, hx0, hval⟩ := he
  let a : NativeField.VF M := ⟨x, hx⟩
  refine ⟨a, fun h => hx0 (congrArg Subtype.val h), ?_⟩
  rw [← not_le, ← map_one v, ← hv]
  exact hval

end SpecialTransformations.Section6.NativeValuation
