module

public import Section6.NativeRV
public import ResidueTranscendentalTransport
public import CanonicalStructure

@[expose] public section

/-! The quotient identification respects all the operations and predicates
on the native RV sort. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer TrivCase RVElim

namespace SpecialTransformations.Section6.NativeRV

open NativeField NativeValuation

variable {M Γ : Type} [LRV.Structure M] [LinearOrderedCommGroupWithZero Γ]
variable [hM : M ⊨ HenselianTheory.valuedField]
variable (v : Valuation (NativeField.VF M) Γ)
variable (hv : ∀ a b, NativeValuation.predV a b ↔ v a ≤ v b)

def quotientValue (q : _root_.RVCalc.RV v) : M := (equiv v hv q).val

private theorem q_injective : Function.Injective (quotientValue v hv) :=
  Subtype.val_injective.comp (equiv v hv).injective

@[simp] theorem quotientValue_rv (x : NativeField.VF M) :
    quotientValue v hv (_root_.RVCalc.rv v x) = iRv x.val :=
  congrArg Subtype.val (equiv_rv v hv x)

@[simp] theorem equiv_zero : quotientValue v hv none = iRVZero := by
  rw [← _root_.RVCalc.rv_zero (v := v), quotientValue_rv]
  exact rv_zero_eq hM

@[simp] theorem equiv_one : quotientValue v hv (some 1) = iRVOne := by
  have he : _root_.RVCalc.rv v 1 = some 1 := by simp [_root_.RVCalc.rv, Units.mk0_one]
  rw [← he, quotientValue_rv]
  exact rv_one

theorem equiv_mul (p q : _root_.RVCalc.RV v) :
    quotientValue v hv (_root_.RVCalc.rvMul v p q) = iRVMul (quotientValue v hv p) (quotientValue v hv q) := by
  obtain ⟨x, rfl⟩ := quotient_surjective v p
  obtain ⟨y, rfl⟩ := quotient_surjective v q
  rw [← ResidueTranscendentalTransport.rv_mul_all, quotientValue_rv, quotientValue_rv, quotientValue_rv]
  exact rv_mul_hom_of_model hM x.property y.property

private theorem repair {σ : LRV.Sentence} (h : σ ∈ Axioms.repairRV) :
    σ ∈ HenselianTheory.valuedField := by simp [HenselianTheory.valuedField, h]

private theorem group {σ : LRV.Sentence} (h : σ ∈ HenselianTheory.rvGroupBase) :
    σ ∈ HenselianTheory.valuedField := by simp [HenselianTheory.valuedField, h]

private theorem not_units_zero : ¬ iUnits (iRVZero (M := M)) := by
  have he := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := pUnits &0 ⟹ exSorted .rv (pUnits &1 ⊓ pEq (tRVMul &1 &0) tRVOne))
    (group (σ := Axioms.rvMulInv) (by simp [HenselianTheory.rvGroupBase, Axioms.ofList]))
    ![iRVZero] (by intro i; fin_cases i; exact rv_zero_mem hM)
  have h₀ (a : M) : (Fin.snoc ![iRVZero] a : Fin 2 → M) 0 = iRVZero := by
    exact Fin.snoc_castSucc _ _ (0 : Fin 1)
  have h₁ (a : M) : (Fin.snoc ![iRVZero] a : Fin 2 → M) 1 = a := by
    change (Fin.snoc ![iRVZero] a : Fin 2 → M) (Fin.last 1) = a
    exact Fin.snoc_last (α := fun _ : Fin 2 => M) a ![iRVZero]
  have h : iUnits (iRVZero (M := M)) → ∃ b : M, iRV b ∧ iUnits b ∧ iRVMul b iRVZero = iRVOne := by
    simpa only [BoundedFormula.realize_imp, exSorted, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
      pUnits_realize, pEq, BoundedFormula.realize_bdEqual, sortPred_realize, realize_tv_last_snoc,
      realize_tRVMul, realize_tRVOne_T, RVCalc.realize_var_inr, Matrix.cons_val_zero, h₀, h₁] using he
  intro hu
  obtain ⟨b, hb, _, hmul⟩ := h hu
  rw [rv_mul_zero_right_of_model hM hb] at hmul
  exact NativeField.vf_zero_ne_one hM (vf_eq_zero_of_rv_eq_zero hM (NativeField.vf_one_mem hM)
    (rv_one.trans hmul.symm)).symm

theorem equiv_units (q : _root_.RVCalc.RV v) :
    iUnits (quotientValue v hv q) ↔ _root_.RVCalc.vrv v q = 1 := by
  rcases eq_or_ne q none with rfl | h
  · rw [equiv_zero, _root_.RVCalc.vrv_none]
    exact iff_of_false not_units_zero zero_ne_one
  have hn : quotientValue v hv q ≠ iRVZero := fun hq => h (q_injective v hv (hq.trans (equiv_zero v hv).symm))
  change iUnits (equiv v hv q).val ↔ _
  rw [units_iff_le_one hM (equiv v hv q).property hn, ← equiv_one v hv]
  simp only [quotientValue, equiv_le, _root_.RVCalc.vrv_some, map_one]
  exact ⟨fun hq => le_antisymm hq.1 hq.2, fun hq => ⟨hq.le, hq.ge⟩⟩

theorem equiv_inv (q : _root_.RVCalc.RV v) :
    quotientValue v hv (q.map Inv.inv) = iRVInvFn (quotientValue v hv q) := by
  rcases eq_or_ne q none with rfl | h
  · have he := sentence_realize hM (φ := Axioms.rvInvZero)
      (repair (by simp [Axioms.repairRV, Axioms.ofList]))
    change (pEq (tRVInv tRVZero) tRVZero : Bf 0).Realize default default at he
    change quotientValue v hv none = iRVInvFn (quotientValue v hv none)
    rw [equiv_zero]
    exact (by simpa only [pEq, BoundedFormula.realize_bdEqual, CanonicalStructure.realize_tRVInv,
      realize_tRVZero] using he : iRVInvFn iRVZero = iRVZero).symm
  · have ha := (equiv v hv q).property
    have hq : quotientValue v hv q ≠ iRVZero := fun he => h (q_injective v hv (he.trans (equiv_zero v hv).symm))
    have hmem : Axioms.sdRVInv ∈ HenselianTheory.valuedField := by
      simp [HenselianTheory.valuedField, Axioms.sortAxioms, Axioms.sortClosure, Axioms.ofList]
    have hh := allSorted_realize hM (ss := ![SortTag.rv]) (φ := pRVsort (tRVInv &0))
      hmem ![quotientValue v hv q] (by intro i; fin_cases i; exact ha)
    have hi : iRV (iRVInvFn (quotientValue v hv q)) := by
      simpa only [pRVsort_realize, CanonicalStructure.realize_tRVInv, RVCalc.realize_var_inr,
        Matrix.cons_val_zero] using hh
    obtain ⟨r, hr⟩ := (equiv v hv).surjective ⟨iRVInvFn (quotientValue v hv q), hi⟩
    have hr' : quotientValue v hv r = iRVInvFn (quotientValue v hv q) := congrArg Subtype.val hr
    have hp := allSorted_realize hM (ss := ![SortTag.rv])
      (φ := pRV &0 ⟹ pEq (tRVMul (tRVInv &0) &0) tRVOne)
      (repair (σ := Axioms.rvInvMul) (by simp [Axioms.repairRV, Axioms.ofList]))
      ![quotientValue v hv q] (by intro i; fin_cases i; exact ha)
    have hmul : iRVMul (iRVInvFn (quotientValue v hv q)) (quotientValue v hv q) = iRVOne := by
      have hh' : quotientValue v hv q ≠ iRVZero →
          iRVMul (iRVInvFn (quotientValue v hv q)) (quotientValue v hv q) = iRVOne := by
        simpa only [BoundedFormula.realize_imp,
        pRV_realize, pEq, BoundedFormula.realize_bdEqual, realize_tRVMul, CanonicalStructure.realize_tRVInv,
        realize_tRVOne_T, RVCalc.realize_var_inr, Matrix.cons_val_zero] using hp
      exact hh' hq
    have he : _root_.RVCalc.rvMul v r q = some 1 :=
      q_injective v hv (by rw [equiv_mul, hr', hmul, equiv_one])
    suffices q.map Inv.inv = r by rw [this, hr']
    cases q with
    | none => exact (h rfl).elim
    | some q =>
      cases r with
      | none => simp [_root_.RVCalc.rvMul] at he
      | some r =>
        rw [_root_.RVCalc.rvMul_some] at he
        exact congrArg some (eq_inv_of_mul_eq_one_left (Option.some.inj he)).symm

end SpecialTransformations.Section6.NativeRV
