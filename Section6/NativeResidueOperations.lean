module

public import Section6.NativeRVOperations
public import Section6.ConcreteLogic
public import Section6.ConcreteResidueOps

@[expose] public section

/-! Transport of residue addition and negation through the quotient
identification. The axiom-realization steps adapt the corresponding
ACVF-QE `ValuedModelMap` arguments to the henselian valued-field core.
Copyright 2026 Yimu Yin. MIT. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer TrivCase

namespace SpecialTransformations.Section6.NativeRV

open NativeField NativeValuation ConcreteValued

variable {M Γ : Type} [LRV.Structure M] [LinearOrderedCommGroupWithZero Γ]
variable [hM : M ⊨ HenselianTheory.valuedField]
variable (v : Valuation (NativeField.VF M) Γ)
variable (hv : ∀ a b, NativeValuation.predV a b ↔ v a ≤ v b)


private def inK (q : M) : Prop := iUnits q ∨ q = iRVZero

private theorem kField_mem {s : LRV.Sentence} (h : s ∈ Axioms.kField) :
    s ∈ HenselianTheory.valuedField := by simp [HenselianTheory.valuedField, h]

private theorem allK {n : ℕ} {φ : Bf n} (h : allSortedK (fun _ => .rv) φ ∈ HenselianTheory.valuedField)
    (z : Fin n → M) (hr : ∀ i, iRV (z i)) (hk : ∀ i, inK (z i)) : φ.Realize default z := by
  have he := sentence_realize hM h
  simp only [allSortedK, Sentence.Realize, BoundedFormula.realize_alls, BoundedFormula.realize_imp,
    BoundedFormula.realize_inf, sortedHyps_realize, residueHyps_realize] at he
  exact he z ⟨hr, hk⟩

private theorem kAdd_zero {q : M} (hr : iRV q) (hk : inK q) :
    iKAdd q iRVZero = q := by
  have hmem : allSortedK (fun _ : Fin 1 => .rv) (pEq (tKAdd &0 tRVZero) &0) ∈
      HenselianTheory.valuedField := kField_mem (by
    rw [show (fun _ : Fin 1 => SortTag.rv) = ![SortTag.rv] from by funext i; fin_cases i; rfl]
    simp [Axioms.kField, Axioms.ofList])
  have h := allK hmem ![q] (by intro i; fin_cases i; exact hr) (by intro i; fin_cases i; exact hk)
  simpa only [pEq, BoundedFormula.realize_bdEqual, realize_tKAdd, realize_tRVZero,
    RVCalc.realize_var_inr, Matrix.cons_val_zero] using h

private theorem kAdd_comm {q r : M} (hq : iRV q) (hr : iRV r) (hq' : inK q) (hr' : inK r) :
    iKAdd q r = iKAdd r q := by
  have hmem : allSortedK (fun _ : Fin 2 => .rv) (pEq (tKAdd &0 &1) (tKAdd &1 &0)) ∈
      HenselianTheory.valuedField := kField_mem (by
    rw [show (fun _ : Fin 2 => SortTag.rv) = ![SortTag.rv, .rv] from by funext i; fin_cases i <;> rfl]
    simp [Axioms.kField, Axioms.ofList])
  have h := allK hmem ![q, r] (by intro i; fin_cases i <;> simp [hq, hr])
    (by intro i; fin_cases i <;> simp [hq', hr'])
  simpa only [pEq, BoundedFormula.realize_bdEqual, realize_tKAdd,
    RVCalc.realize_var_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

private theorem kNeg_zero : iKNeg (iRVZero (M := M)) = iRVZero := by
  have hm : Axioms.sdKNeg ∈ HenselianTheory.valuedField := by
    simp [HenselianTheory.valuedField, Axioms.sortAxioms, Axioms.sortClosure, Axioms.ofList]
  have hn := allSorted_realize hM (ss := ![SortTag.rv]) (φ := pInK &0 ⟹ pInK (tKNeg &0))
    hm ![iRVZero (M := M)] (by intro i; fin_cases i; exact rv_zero_mem hM)
  have hnk : inK (iKNeg (iRVZero (M := M))) := by
    have hn' : inK (iRVZero (M := M)) → inK (iKNeg (iRVZero (M := M))) := by
      simpa [Axioms.sdKNeg, BoundedFormula.realize_imp, pInK_realize, realize_tKNeg,
        RVCalc.realize_var_inr, inK] using hn
    exact hn' (Or.inr rfl)
  have hnr := hnk.elim
    (fun hu => by
      have hm' : Axioms.sdUnits ∈ HenselianTheory.valuedField := by
        simp [HenselianTheory.valuedField, Axioms.sortAxioms, Axioms.sortClosure, Axioms.ofList]
      have hs := sentence_realize hM hm'
      simp only [Axioms.sdUnits, allOne, Sentence.Realize, BoundedFormula.realize_alls,
        BoundedFormula.realize_imp, pUnits_realize, pRVsort_realize, RVCalc.realize_var_inr] at hs
      exact hs ![iKNeg iRVZero] hu)
    (fun he => he.symm ▸ rv_zero_mem hM)
  have hmem : allSortedK (fun _ : Fin 1 => .rv) (pEq (tKAdd &0 (tKNeg &0)) tRVZero) ∈
      HenselianTheory.valuedField := kField_mem (by
    rw [show (fun _ : Fin 1 => SortTag.rv) = ![SortTag.rv] from by funext i; fin_cases i; rfl]
    simp [Axioms.kField, Axioms.ofList])
  have h := allK hmem ![iRVZero] (by intro i; fin_cases i; exact rv_zero_mem hM)
    (by intro i; fin_cases i; exact Or.inr rfl)
  have he : iKAdd iRVZero (iKNeg (iRVZero (M := M))) = iRVZero := by
    simpa only [pEq, BoundedFormula.realize_bdEqual, realize_tKAdd, realize_tKNeg, realize_tRVZero,
      RVCalc.realize_var_inr, Matrix.cons_val_zero] using h
  rwa [kAdd_comm (rv_zero_mem hM) hnr (Or.inr rfl) hnk, kAdd_zero hnr hnk] at he

private theorem inK_equiv (q : _root_.RVCalc.RV v) :
    inK (quotientValue v hv q) ↔ q ∈ Set.range (ConcreteRV.residueCode v) := by
  have hzero : quotientValue v hv q = iRVZero ↔ q = none := by
    constructor
    · intro h
      exact (equiv v hv).injective (Subtype.ext (h.trans (equiv_zero v hv).symm))
    · rintro rfl
      exact equiv_zero v hv
  rw [inK, equiv_units, hzero, ConcreteRV.residueCode_range, Set.mem_setOf_eq, or_comm]

private theorem kAdd_units (x y : NativeField.VF M) (hx : iUnits (iRv x.val))
    (hy : iUnits (iRv y.val)) :
    iKAdd (iRv x.val) (iRv y.val) =
      if iUnits (iRv (x + y).val) then iRv (x + y).val else iRVZero := by
  have hm : Axioms.kAddLink ∈ HenselianTheory.valuedField := by
    simp [HenselianTheory.valuedField, Axioms.repairRV, Axioms.ofList]
  have h := allSorted_realize hM (φ := pUnits (tRv &0) ⟹ (pUnits (tRv &1) ⟹
      ((pUnits (tRv (tVFAdd &0 &1)) ⟹ pEq (tKAdd (tRv &0) (tRv &1)) (tRv (tVFAdd &0 &1))) ⊓
       (∼(pUnits (tRv (tVFAdd &0 &1))) ⟹ pEq (tKAdd (tRv &0) (tRv &1)) tRVZero))))
    hm ![x.val, y.val] (by intro i; fin_cases i <;> simp [x.property, y.property])
  have he : (iUnits (iRv (x + y).val) → iKAdd (iRv x.val) (iRv y.val) = iRv (x + y).val) ∧
      (¬ iUnits (iRv (x + y).val) → iKAdd (iRv x.val) (iRv y.val) = iRVZero) := by
    change (iUnits (iRv (iVFAdd x.val y.val)) →
      iKAdd (iRv x.val) (iRv y.val) = iRv (iVFAdd x.val y.val)) ∧
      (¬ iUnits (iRv (iVFAdd x.val y.val)) → iKAdd (iRv x.val) (iRv y.val) = iRVZero)
    simpa [BoundedFormula.realize_imp, BoundedFormula.realize_inf, pUnits_realize,
      pEq, BoundedFormula.realize_bdEqual, realize_tRv, realize_tKAdd, realize_tVFAdd,
      realize_tRVZero, RVCalc.realize_var_inr, hx, hy] using h
  split_ifs with hq
  · exact he.1 hq
  · exact he.2 hq

theorem equiv_addResidue (p q : _root_.RVCalc.RV v) :
    quotientValue v hv (addResidue v p q) = iKAdd (quotientValue v hv p) (quotientValue v hv q) := by
  classical
  by_cases h : p ∈ Set.range (ConcreteRV.residueCode v) ∧ q ∈ Set.range (ConcreteRV.residueCode v)
  · have hp := (inK_equiv v hv p).mpr h.1
    have hq := (inK_equiv v hv q).mpr h.2
    have hpr : iRV (quotientValue v hv p) := (equiv v hv p).property
    have hqr : iRV (quotientValue v hv q) := (equiv v hv q).property
    rcases eq_or_ne p none with rfl | hp0
    · obtain ⟨r, rfl⟩ := h.2
      rw [← ConcreteRV.residueCode_zero v, addResidue_code, zero_add, ConcreteRV.residueCode_zero,
        equiv_zero, kAdd_comm (rv_zero_mem hM) hqr (Or.inr rfl) hq, kAdd_zero hqr hq]
    rcases eq_or_ne q none with rfl | hq0
    · obtain ⟨r, rfl⟩ := h.1
      rw [← ConcreteRV.residueCode_zero v, addResidue_code, add_zero, ConcreteRV.residueCode_zero,
        equiv_zero, kAdd_zero hpr hp]
    have hpv : _root_.RVCalc.vrv v p = 1 := by
      rcases hp with hu | he
      · exact (equiv_units v hv p).mp hu
      · exact (hp0 ((equiv v hv).injective (Subtype.ext (he.trans (equiv_zero v hv).symm)))).elim
    have hqv : _root_.RVCalc.vrv v q = 1 := by
      rcases hq with hu | he
      · exact (equiv_units v hv q).mp hu
      · exact (hq0 ((equiv v hv).injective (Subtype.ext (he.trans (equiv_zero v hv).symm)))).elim
    obtain ⟨x, rfl⟩ := quotient_surjective v p
    obtain ⟨y, rfl⟩ := quotient_surjective v q
    rw [_root_.RVCalc.vrv_rv] at hpv hqv
    have hu (z : NativeField.VF M) : iUnits (iRv z.val) ↔ v z = 1 := by
      simpa only [quotientValue_rv, _root_.RVCalc.vrv_rv] using
        equiv_units v hv (_root_.RVCalc.rv v z)
    rw [addResidue_rv v x y hpv hqv, quotientValue_rv, quotientValue_rv,
      kAdd_units x y ((hu x).mpr hpv) ((hu y).mpr hqv), hu]
    split <;> simp only [quotientValue_rv, equiv_zero]
  · have hj : ¬ inK (quotientValue v hv p) ∨ ¬ inK (quotientValue v hv q) := by
      simp only [inK_equiv]
      exact not_and_or.mp h
    have hm : Axioms.kJunkZero ∈ HenselianTheory.valuedField := by
      simp [HenselianTheory.valuedField, Axioms.repairRV, Axioms.ofList]
    have he := allSorted_realize hM
      (φ := (∼(pInK &0) ⊔ ∼(pInK &1)) ⟹ pEq (tKAdd &0 &1) tRVZero)
      hm ![quotientValue v hv p, quotientValue v hv q] (by intro i; fin_cases i <;> exact (equiv v hv _).property)
    rw [addResidue, if_neg h, equiv_zero]
    have hzero : (¬ inK (quotientValue v hv p) ∨ ¬ inK (quotientValue v hv q)) →
        iKAdd (quotientValue v hv p) (quotientValue v hv q) = iRVZero := by
      simpa only [BoundedFormula.realize_imp, BoundedFormula.realize_sup, BoundedFormula.realize_not,
        BoundedFormula.realize_bdEqual, pInK_realize, realize_tKAdd, realize_tRVZero, pEq, inK,
        RVCalc.realize_var_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using he
    exact (hzero hj).symm

theorem equiv_negResidue (p : _root_.RVCalc.RV v) :
    quotientValue v hv (negResidue v p) = iKNeg (quotientValue v hv p) := by
  by_cases h : p ∈ Set.range (ConcreteRV.residueCode v)
  · rcases eq_or_ne p none with rfl | hp
    · rw [← ConcreteRV.residueCode_zero v, negResidue_code, neg_zero, ConcreteRV.residueCode_zero,
        equiv_zero, kNeg_zero]
    have hval : _root_.RVCalc.vrv v p = 1 := by
      rw [ConcreteRV.residueCode_range] at h
      exact h.resolve_left hp
    obtain ⟨x, rfl⟩ := quotient_surjective v p
    rw [_root_.RVCalc.vrv_rv] at hval
    have hu := (equiv_units v hv (_root_.RVCalc.rv v x)).mpr (by rwa [_root_.RVCalc.vrv_rv])
    rw [quotientValue_rv] at hu
    have hm : Axioms.kNegLink ∈ HenselianTheory.valuedField := by
      simp [HenselianTheory.valuedField, Axioms.repairRV, Axioms.ofList]
    have he := allSorted_realize hM
      (φ := pUnits (tRv &0) ⟹ pEq (tKNeg (tRv &0)) (tRv (tVFNeg &0)))
      hm ![x.val] (by intro i; fin_cases i; exact x.property)
    rw [negResidue_rv v x hval, quotientValue_rv, quotientValue_rv]
    change iRv (iVFNeg x.val) = _
    exact (by simpa [pEq, BoundedFormula.realize_imp, pUnits_realize, realize_tRv,
      realize_tVFNeg, realize_tKNeg, encodedRv, hu] using he :
      iKNeg (iRv x.val) = iRv (iVFNeg x.val)).symm
  · have hj : ¬ inK (quotientValue v hv p) := fun hp => h ((inK_equiv v hv p).mp hp)
    have hm : Axioms.kNegJunkZero ∈ HenselianTheory.valuedField := by
      simp [HenselianTheory.valuedField, Axioms.repairRV, Axioms.ofList]
    have he := allSorted_realize hM (φ := ∼(pInK &0) ⟹ pEq (tKNeg &0) tRVZero)
      hm ![quotientValue v hv p] (by intro i; fin_cases i; exact (equiv v hv p).property)
    rw [negResidue, if_neg h, equiv_zero]
    have hzero : ¬ inK (quotientValue v hv p) → iKNeg (quotientValue v hv p) = iRVZero := by
      simpa only [BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
        pInK_realize, realize_tKNeg, realize_tRVZero, pEq, inK,
        RVCalc.realize_var_inr, Matrix.cons_val_zero] using he
    exact (hzero hj).symm

end SpecialTransformations.Section6.NativeRV
