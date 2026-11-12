module

public import Section6.NativeValuation
public import CanonicalRV
public import RVValueMap

@[expose] public section

/-! Identification of a native henselian RV sort with the quotient of its
extracted valuation. Adapted from the released ACVF-QE `CanonicalRV` and
`QF2Fragment` at `f3ef4ee679f921079aa8f742a2807a9cc724d2d6`.
Copyright 2026 Yimu Yin. MIT. The field core suffices for these proofs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Milestone0.RVCalc (realize_var_inr realize_tRVInfty)

namespace SpecialTransformations.Section6.NativeRV

open NativeValuation

variable {M : Type} [LRV.Structure M]

private theorem rvGroup_mem {s : LRV.Sentence} (h : s ∈ HenselianTheory.rvGroupBase) :
    s ∈ HenselianTheory.valuedField := by simp [HenselianTheory.valuedField, h]

private theorem repair_mem {s : LRV.Sentence} (h : s ∈ Axioms.repairRV) :
    s ∈ HenselianTheory.valuedField := by simp [HenselianTheory.valuedField, h]

private theorem rvAxioms_mem {s : LRV.Sentence} (h : s ∈ Axioms.rvAxioms) :
    s ∈ HenselianTheory.valuedField := by simp [HenselianTheory.valuedField, h]

theorem rv_mul_comm_of_model (hM : M ⊨ HenselianTheory.valuedField) {a b : M} (ha : iRV a) (hb : iRV b) :
    iRVMul a b = iRVMul b a := by
  have h := allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv])
    (φ := (pEq (tRVMul &0 &1) (tRVMul &1 &0)))
    (rvGroup_mem (s := Axioms.rvMulComm)
      (by simp [HenselianTheory.rvGroupBase, Axioms.ofList]))
    ![a, b] (by intro i; fin_cases i <;> simp [ha, hb])
  simpa [pEq, BoundedFormula.realize_bdEqual, realize_tRVMul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] using h

theorem rv_mul_zero_right_of_model (hM : M ⊨ HenselianTheory.valuedField) {a : M} (ha : iRV a) :
    iRVMul a iRVZero = iRVZero := by
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pEq (tRVMul &0 tRVInfty) tRVInfty))
    (rvGroup_mem (s := Axioms.rvMulInfty)
      (by simp [HenselianTheory.rvGroupBase, Axioms.ofList]))
    ![a] (by intro i; fin_cases i; simpa using ha)
  simpa [tRVInfty, pEq, BoundedFormula.realize_bdEqual, realize_tRVMul, realize_tRVZero,
    Matrix.cons_val_zero] using h

theorem rv_one_mul_of_model (hM : M ⊨ HenselianTheory.valuedField) {a : M}
    (ha : iRV a) (ha0 : a ≠ iRVZero) : iRVMul iRVOne a = a := by
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := pRV &0 ⟹ pEq (tRVMul tRVOne &0) &0)
    (repair_mem (s := Axioms.rvMulOneRV) (by simp [Axioms.repairRV, Axioms.ofList]))
    ![a] (by intro i; fin_cases i; exact ha)
  exact (by simpa only [BoundedFormula.realize_imp, pRV_realize, pEq,
    BoundedFormula.realize_bdEqual, realize_tRVMul, realize_tRVOne_T,
    realize_var_inr, Matrix.cons_val_zero] using h : a ≠ iRVZero → _) ha0

variable [hM : M ⊨ HenselianTheory.valuedField]

abbrev RVSort (M : Type) [LRV.Structure M] := {x : M // iRV x}

def encodedRv (a : NativeField.VF M) : RVSort M := ⟨iRv a.1, NativeValuation.rv_mem hM a.2⟩

theorem encodedRv_zero_iff (a : NativeField.VF M) :
    iRv a.1 = iRVZero ↔ a = 0 := by
  constructor
  · exact fun h => Subtype.ext (vf_eq_zero_of_rv_eq_zero hM a.2 h)
  · rintro rfl
    exact rv_zero_eq hM

theorem encoded_eq_iff_close {x y : M} (hx : iVF x) (hy : iVF y)
    (hy0 : y ≠ iVFZero) :
    iRv x = iRv y ↔ ¬ iLe (iRv (iVFAdd x (iVFNeg y))) (iRv y) := by
  have h' := allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf])
    (φ := (∼(pEq &1 tVFZero) ⟹ (pEq (tRv &0) (tRv &1) ⇔
      ∼(pLe (tRv (tVFAdd &0 (tVFNeg &1))) (tRv &1)))))
    (repair_mem (s := Axioms.rvEqLink) (by simp [Axioms.repairRV, Axioms.ofList]))
    ![x, y] (by intro i; fin_cases i <;> simp [hx, hy])
  have h3 : y ≠ iVFZero → (iRv x = iRv y ↔
      ¬ (pLe (tRv (tVFAdd &0 (tVFNeg &1))) (tRv &1)).Realize default ![x, y]) := by
    simpa [pEq, BoundedFormula.realize_bdEqual, BoundedFormula.realize_not,
      BoundedFormula.realize_iff, realize_tVFZero, realize_tRv,
      RVCalc.realize_var_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] using h'
  have hh := h3 hy0
  rw [realize_pLe] at hh
  simpa [realize_tRv, realize_tVFAdd, realize_tVFNeg, RVCalc.realize_var_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hh

theorem encodedRv_surjective : Function.Surjective (encodedRv (M := M)) := by
  rintro ⟨y, hy⟩
  by_cases hy0 : y = iRVZero
  · exact ⟨0, Subtype.ext ((rv_zero_eq hM).trans hy0.symm)⟩
  have hmem : Axioms.rvSurj ∈ HenselianTheory.valuedField :=
    rvAxioms_mem (by simp [Axioms.rvAxioms, Axioms.ofList])
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (∼(pEq &0 tRVZero) ⟹ exSorted .vf (pEq (tRv &1) &0))) hmem ![y]
    (by intro i; fin_cases i; simpa using hy)
  simp only [pEq, BoundedFormula.realize_bdEqual, BoundedFormula.realize_imp,
    BoundedFormula.realize_not, exSorted, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, sortPred, realize_tRVZero, realize_tRv, pVF_realize] at h
  obtain ⟨x, hx, he⟩ := h hy0
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

theorem rv_one : iRv (iVFOne (M := M)) = iRVOne := by
  let t : RVSort M := ⟨iRVOne, NativeValuation.rv_one_mem hM⟩
  obtain ⟨a, ha⟩ := encodedRv_surjective t
  have ha' : iRv a.val = iRVOne := congrArg Subtype.val ha
  have h1 : iVF (iVFOne (M := M)) := NativeField.vf_one_mem hM
  have hr1 := NativeValuation.rv_mem hM h1
  have hn : iRv (iVFOne (M := M)) ≠ iRVZero :=
    rv_ne_zero_of_ne_zero h1 (Ne.symm (NativeField.vf_zero_ne_one hM))
  calc
    iRv iVFOne = iRVMul iRVOne (iRv iVFOne) := (rv_one_mul_of_model hM hr1 hn).symm
    _ = iRVMul (iRv iVFOne) iRVOne :=
      rv_mul_comm_of_model hM (NativeValuation.rv_one_mem hM) hr1
    _ = iRv (iVFMul iVFOne a.val) := by
      rw [← ha', NativeValuation.rv_mul_hom_of_model hM h1 a.property]
    _ = iRv a.val := by
      rw [NativeField.vf_mul_comm hM h1 a.property, NativeField.vf_mul_one hM a.property]
    _ = iRVOne := ha'

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (NativeField.VF M) Γ)
    (hv : ∀ a b, NativeValuation.predV a b ↔ v a ≤ v b)

include hv

theorem same_fibers (a b : NativeField.VF M) :
    _root_.RVCalc.rv v a = _root_.RVCalc.rv v b ↔ encodedRv a = encodedRv b := by
  rw [Subtype.ext_iff]
  change _ ↔ iRv a.1 = iRv b.1
  by_cases ha : a = 0
  · subst a
    rw [_root_.RVCalc.rv_zero,
      show iRv (0 : NativeField.VF M).1 = iRVZero from rv_zero_eq hM]
    simpa only [eq_comm] using
      ((_root_.RVCalc.rv_eq_none_iff (v := v) (x := b)).trans (encodedRv_zero_iff b).symm)
  by_cases hb : b = 0
  · subst b
    rw [_root_.RVCalc.rv_zero,
      show iRv (0 : NativeField.VF M).1 = iRVZero from rv_zero_eq hM]
    exact (_root_.RVCalc.rv_eq_none_iff (v := v)).trans (encodedRv_zero_iff a).symm
  have hsource : _root_.RVCalc.rv v a = _root_.RVCalc.rv v b ↔ v (a - b) < v b := by
    rw [eq_comm, _root_.RVCalc.rv_eq_iff hb ha, ← neg_sub a b, Valuation.map_neg]
  rw [hsource, encoded_eq_iff_close a.2 b.2 (fun he => hb (Subtype.ext he))]
  change v (a - b) < v b ↔ ¬ NativeValuation.predV b (a - b)
  rw [hv, not_le]

omit hv in
theorem quotient_surjective : Function.Surjective (_root_.RVCalc.rv v) := by
  intro q
  cases q with
  | none => exact ⟨0, _root_.RVCalc.rv_zero⟩
  | some q =>
    obtain ⟨x, _, hx⟩ := _root_.RVCalc.rv_surjective v q
    exact ⟨x, hx⟩

def equiv : _root_.RVCalc.RV v ≃ RVSort M :=
  CanonicalRV.equivOfSameFibers (_root_.RVCalc.rv v) encodedRv (quotient_surjective v)
    encodedRv_surjective (same_fibers v hv)

@[simp] theorem equiv_rv (a : NativeField.VF M) :
    equiv v hv (_root_.RVCalc.rv v a) = encodedRv a :=
  CanonicalRV.equivOfSameFibers_apply _ _ _ _ _ a

theorem equiv_le (q r : _root_.RVCalc.RV v) :
    iLe (equiv v hv q).val (equiv v hv r).val ↔ _root_.RVCalc.vrv v r ≤ _root_.RVCalc.vrv v q := by
  obtain ⟨x, rfl⟩ := quotient_surjective v q
  obtain ⟨y, rfl⟩ := quotient_surjective v r
  simpa only [equiv_rv, encodedRv, NativeValuation.predV, _root_.RVCalc.vrv_rv] using hv y x

end SpecialTransformations.Section6.NativeRV
