import Section6.NativeField

/-! The valuation predicate of a model of the henselian valued-field core.
The order arguments are adapted from the released ACVF-QE modules
`RVCalc` and `VFValued` at `f3ef4ee679f921079aa8f742a2807a9cc724d2d6`.
Copyright 2026 Yimu Yin. MIT. Algebraic closedness is absent from this core. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Milestone0.RVCalc (realize_var_inr realize_tRVInfty)

namespace SpecialTransformations.Section6.NativeValuation

open NativeField

private theorem sort_mem {s : LRV.Sentence} (h : s ∈ Axioms.sortClosure) :
    s ∈ HenselianTheory.valuedField := by
  simp [HenselianTheory.valuedField, Axioms.sortAxioms, h]

theorem rv_mem {M : Type} [LRV.Structure M] (hM : M ⊨ HenselianTheory.valuedField) {x : M} (hx : iVF x) :
    iRV (iRv x) := by
  have hmem : allSorted ![.vf] (pRVsort (tRv &0)) ∈ HenselianTheory.valuedField :=
    sort_mem (by simp [Axioms.sortClosure, Axioms.ofList, Axioms.sdRv])
  have h := allSorted_realize hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simpa only [pRVsort_realize, realize_tRv, realize_tv, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Matrix.cons_val_zero] using h

theorem rv_zero_mem {M : Type} [LRV.Structure M] (hM : M ⊨ HenselianTheory.valuedField) :
    iRV (iRVZero (M := M)) := by
  have h := sentence_realize hM (φ := Axioms.sdRVZero)
    (sort_mem (s := Axioms.sdRVZero) (by simp [Axioms.sortClosure, Axioms.ofList]))
  rw [Axioms.sdRVZero, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pRVsort_realize, realize_tRVZero] at h
  exact h

theorem rv_one_mem {M : Type} [LRV.Structure M] (hM : M ⊨ HenselianTheory.valuedField) :
    iRV (iRVOne (M := M)) := by
  have h := sentence_realize hM (φ := Axioms.sdRVOne)
    (sort_mem (s := Axioms.sdRVOne) (by simp [Axioms.sortClosure, Axioms.ofList]))
  rw [Axioms.sdRVOne, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pRVsort_realize, realize_tRVOne_T] at h
  exact h

variable {M : Type} [LRV.Structure M]

theorem rv_mul_hom_of_model (hM : M ⊨ HenselianTheory.valuedField) {x y : M} (hx : iVF x) (hy : iVF y) :
    iRv (iVFMul x y) = iRVMul (iRv x) (iRv y) := by
  have h := allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf])
    (φ := (pEq (tRv (tVFMul &0 &1)) (tRVMul (tRv &0) (tRv &1))))
    (by
      change Axioms.rvMulHom ∈ HenselianTheory.valuedField
      simp [HenselianTheory.valuedField, Axioms.rvAxioms, Axioms.ofList]) ![x, y] (by intro i; fin_cases i <;> simp [hx, hy])
  simpa [pEq, BoundedFormula.realize_bdEqual, realize_tRv, realize_tVFMul, realize_tRVMul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

theorem rv_zero_eq (hM : M ⊨ HenselianTheory.valuedField) : iRv (iVFZero (M := M)) = iRVZero := by
  have h := sentence_realize hM (φ := Axioms.rvZeroEq) (by
      change Axioms.rvZeroEq ∈ HenselianTheory.valuedField
      simp [HenselianTheory.valuedField, Axioms.rvAxioms, Axioms.ofList])
  rw [Axioms.rvZeroEq, Sentence.Realize] at h
  simpa [Sentence.Realize, Formula.Realize, pEq, BoundedFormula.realize_bdEqual, realize_tRv,
    realize_tVFZero, tRVInfty, realize_tRVInfty, realize_tRVZero] using h

theorem le_refl_rv (hM : M ⊨ HenselianTheory.valuedField) {a : M} (ha : iRV a) : iLe a a := by
  by_cases h0 : a = iRVZero
  · subst h0
    have hz0 : iVF (iVFZero (M := M)) := NativeField.vf_zero_mem (M := M) hM
    have h := allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf])
      (φ := (pLe (tRv &0) (tRv (tVFAdd &0 &1)) ⊔ pLe (tRv &1) (tRv (tVFAdd &0 &1))))
      (by
      change Axioms.rvUltrametric ∈ HenselianTheory.valuedField
      simp [HenselianTheory.valuedField, Axioms.rvAxioms, Axioms.ofList]) ![iVFZero, iVFZero] (by
        intro i; fin_cases i <;> simpa using hz0)
    have h2 : iLe (iRv (iVFZero (M := M))) (iRv (iVFAdd iVFZero iVFZero)) ∨
        iLe (iRv (iVFZero (M := M))) (iRv (iVFAdd iVFZero iVFZero)) := by
      simpa [realize_pLe, realize_tRv, realize_tVFAdd, realize_var_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, BoundedFormula.realize_sup] using h
    rcases h2 with h2 | h2
    · simpa [NativeField.vf_add_zero hM hz0, rv_zero_eq hM] using h2
    · simpa [NativeField.vf_add_zero hM hz0, rv_zero_eq hM] using h2
  · have h := allSorted_realize hM (ss := ![SortTag.rv]) (φ := (pRV &0 ⟹ pLe &0 &0))
      (by
      change Axioms.leRefl ∈ HenselianTheory.valuedField
      simp [HenselianTheory.valuedField, Axioms.preorderRV, Axioms.ofList]) ![a] (by intro i; fin_cases i; simpa using ha)
    have h2 : a ≠ iRVZero → iLe a a := by
      simpa [pRV_realize, realize_pLe, realize_var_inr, Matrix.cons_val_zero] using h
    exact h2 h0

theorem le_top_rv (hM : M ⊨ HenselianTheory.valuedField) {a : M} (ha : iRV a) : iLe a iRVZero := by
  by_cases h0 : a = iRVZero
  · subst h0; exact le_refl_rv hM ha
  · have h := allSorted_realize hM (ss := ![SortTag.rv]) (φ := (pRV &0 ⟹ pLe &0 tRVInfty))
      (by
      change Axioms.leTop ∈ HenselianTheory.valuedField
      simp [HenselianTheory.valuedField, Axioms.preorderRV, Axioms.ofList]) ![a] (by intro i; fin_cases i; simpa using ha)
    have h2 : a ≠ iRVZero → iLe a iRVZero := by
      simpa [pRV_realize, realize_pLe, realize_var_inr, Matrix.cons_val_zero,
        realize_tRVInfty] using h
    exact h2 h0

theorem le_infty_eq (hM : M ⊨ HenselianTheory.valuedField) {a : M} (ha : iRV a) (h : iLe iRVZero a) :
    a = iRVZero := by
  by_cases h0 : a = iRVZero
  · exact h0
  · have h' := allSorted_realize hM (ss := ![SortTag.rv])
      (φ := (pRV &0 ⟹ (pLe tRVInfty &0 ⟹ pEq &0 tRVInfty)))
      (by
      change Axioms.leInftyEq ∈ HenselianTheory.valuedField
      simp [HenselianTheory.valuedField, Axioms.preorderRV, Axioms.ofList]) ![a] (by intro i; fin_cases i; simpa using ha)
    have h2 : a ≠ iRVZero → iLe iRVZero a → a = iRVZero := by
      simpa [pRV_realize, realize_pLe, pEq, BoundedFormula.realize_bdEqual, realize_var_inr,
        Matrix.cons_val_zero, realize_tRVInfty] using h'
    exact h2 h0 h

theorem le_trans_rv (hM : M ⊨ HenselianTheory.valuedField) {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c)
    (hab : iLe a b) (hbc : iLe b c) : iLe a c := by
  by_cases ha0 : a = iRVZero
  · subst ha0
    by_cases hb0 : b = iRVZero
    · subst hb0; exact hbc
    · exact absurd (le_infty_eq hM hb hab) hb0
  · by_cases hb0 : b = iRVZero
    · subst hb0
      by_cases hc0 : c = iRVZero
      · subst hc0; exact le_top_rv hM ha
      · exact absurd (le_infty_eq hM hc hbc) hc0
    · by_cases hc0 : c = iRVZero
      · subst hc0; exact le_top_rv hM ha
      · have h := allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv, SortTag.rv])
          (φ := (pRV &0 ⟹ (pRV &1 ⟹ (pRV &2 ⟹
            (pLe &0 &1 ⟹ (pLe &1 &2 ⟹ pLe &0 &2))))))
          (by
      change Axioms.leTrans ∈ HenselianTheory.valuedField
      simp [HenselianTheory.valuedField, Axioms.preorderRV, Axioms.ofList]) ![a, b, c] (by intro i; fin_cases i <;> simp [ha, hb, hc])
        have h2 : a ≠ iRVZero → b ≠ iRVZero → c ≠ iRVZero →
            iLe a b → iLe b c → iLe a c := by
          simpa [pRV_realize, realize_pLe, realize_var_inr, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two] using h
        exact h2 ha0 hb0 hc0 hab hbc

theorem le_total_rv (hM : M ⊨ HenselianTheory.valuedField) {a b : M} (ha : iRV a) (hb : iRV b) :
    iLe a b ∨ iLe b a := by
  by_cases ha0 : a = iRVZero
  · subst ha0; exact Or.inr (le_top_rv hM hb)
  · by_cases hb0 : b = iRVZero
    · subst hb0; exact Or.inl (le_top_rv hM ha)
    · have h := allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv])
        (φ := (pRV &0 ⟹ (pRV &1 ⟹ (pLe &0 &1 ⊔ pLe &1 &0))))
        (by
      change Axioms.leTotal ∈ HenselianTheory.valuedField
      simp [HenselianTheory.valuedField, Axioms.preorderRV, Axioms.ofList]) ![a, b] (by intro i; fin_cases i <;> simp [ha, hb])
      have h2 : a ≠ iRVZero → b ≠ iRVZero → (iLe a b ∨ iLe b a) := by
        simpa [pRV_realize, realize_pLe, realize_var_inr, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, BoundedFormula.realize_sup] using h
      exact h2 ha0 hb0

theorem units_iff_le_one (hM : M ⊨ HenselianTheory.valuedField) {a : M} (ha : iRV a) (ha0 : a ≠ iRVZero) :
    iUnits a ↔ (iLe iRVOne a ∧ iLe a iRVOne) := by
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pRV &0 ⟹ (pUnits &0 ⇔ (pLe tRVOne &0 ⊓ pLe &0 tRVOne))))
    (by
      change Axioms.leClassOne ∈ HenselianTheory.valuedField
      simp [HenselianTheory.valuedField, Axioms.preorderRV, Axioms.ofList]) ![a] (by intro i; fin_cases i; simpa using ha)
  have h2 : a ≠ iRVZero → (iUnits a ↔ (iLe iRVOne a ∧ iLe a iRVOne)) := by
    simpa [pRV_realize, pUnits_realize, realize_pLe, BoundedFormula.realize_inf,
      BoundedFormula.realize_iff, realize_var_inr, realize_tRVOne_T, Matrix.cons_val_zero] using h
  exact h2 ha0

theorem le_mul_iff (hM : M ⊨ HenselianTheory.valuedField) {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c)
    (hc0 : c ≠ iRVZero) :
    (iLe a b ↔ iLe (iRVMul a c) (iRVMul b c)) := by
  have h := allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv, SortTag.rv])
    (φ := (pRV &2 ⟹ (pLe &0 &1 ⇔ pLe (tRVMul &0 &2) (tRVMul &1 &2))))
    (by
      change Axioms.leMulCompatFull ∈ HenselianTheory.valuedField
      simp [HenselianTheory.valuedField, Axioms.repairRV, Axioms.ofList]) ![a, b, c] (by intro i; fin_cases i <;> simp [ha, hb, hc])
  have h2 : c ≠ iRVZero → (iLe a b ↔ iLe (iRVMul a c) (iRVMul b c)) := by
    simpa [pRV_realize, realize_pLe, realize_tRVMul, BoundedFormula.realize_iff, realize_var_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two] using h
  exact h2 hc0

theorem vf_eq_zero_of_rv_eq_zero (hM : M ⊨ HenselianTheory.valuedField) {x : M} (hx : iVF x)
    (h : iRv x = iRVZero) : x = iVFZero := by
  have h' := allSorted_realize hM (ss := ![SortTag.vf])
    (φ := (pEq (tRv &0) tRVInfty ⟹ pEq &0 tVFZero))
    (by
      change Axioms.rvEqInfty ∈ HenselianTheory.valuedField
      simp [HenselianTheory.valuedField, Axioms.rvAxioms, Axioms.ofList]) ![x] (by intro i; fin_cases i; simpa using hx)
  have h2 : iRv x = iRVZero → x = iVFZero := by
    simpa [pEq, BoundedFormula.realize_bdEqual, realize_tRv, realize_var_inr, realize_tVFZero,
      realize_tRVInfty, Matrix.cons_val_zero] using h'
  exact h2 h

theorem rv_ultrametric (hM : M ⊨ HenselianTheory.valuedField) {x y : M} (hx : iVF x) (hy : iVF y) :
    iLe (iRv x) (iRv (iVFAdd x y)) ∨ iLe (iRv y) (iRv (iVFAdd x y)) := by
  have h := allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf])
    (φ := (pLe (tRv &0) (tRv (tVFAdd &0 &1)) ⊔ pLe (tRv &1) (tRv (tVFAdd &0 &1))))
    (by
      change Axioms.rvUltrametric ∈ HenselianTheory.valuedField
      simp [HenselianTheory.valuedField, Axioms.rvAxioms, Axioms.ofList]) ![x, y] (by intro i; fin_cases i <;> simp [hx, hy])
  simpa [realize_pLe, realize_tRv, realize_tVFAdd, realize_var_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, BoundedFormula.realize_sup] using h

variable [hM : M ⊨ HenselianTheory.valuedField]

noncomputable instance instFieldVF : Field (NativeField.VF M) :=
  NativeField.vfFieldOfModel (hM := hM)

/-- The paper's `v x ≤ v y` on the `VF` sort: `iLe (rv y) (rv x)`. -/
def predV (x y : NativeField.VF M) : Prop := iLe (iRv y.1) (iRv x.1)

/-- `rv` of a nonzero `VF`-element is not `∞`. -/
theorem rv_ne_zero_of_ne_zero {z : M} (hz : iVF z) (hz0 : z ≠ Transfer.iVFZero) :
    iRv z ≠ iRVZero := by
  intro h
  exact hz0 (vf_eq_zero_of_rv_eq_zero hM hz h)

/-- **`predV` is a valuation predicate.**  All seven fields come from `RVCalc`: the preorder laws,
`∞` as top, the ultrametric inequality, and scale invariance (`le_mul_iff`) together with
multiplicativity of `rv` (`rv_mul_hom_of_model`). -/
theorem isValPred_predV : VFValued.IsValPred (predV (M := M)) where
  refl := fun x => le_refl_rv hM (rv_mem hM x.2)
  trans := fun x y z h1 h2 =>
    le_trans_rv hM (rv_mem hM z.2) (rv_mem hM y.2)
      (rv_mem hM x.2) h2 h1
  zero_le := fun x => by
    have h0 : ((0 : NativeField.VF M)).1 = Transfer.iVFZero := rfl
    show iLe (iRv x.1) (iRv ((0 : NativeField.VF M)).1)
    rw [h0, rv_zero_eq hM]
    exact le_top_rv hM (rv_mem hM x.2)
  zero_eq := fun x h => by
    have h0 : ((0 : NativeField.VF M)).1 = Transfer.iVFZero := rfl
    have hh : iLe (iRv ((0 : NativeField.VF M)).1) (iRv x.1) := h
    rw [h0, rv_zero_eq hM] at hh
    exact Subtype.ext (vf_eq_zero_of_rv_eq_zero hM x.2
      (le_infty_eq hM (rv_mem hM x.2) hh))
  ultra := fun x y => rv_ultrametric hM x.2 y.2
  total := fun x y =>
    (le_total_rv hM (rv_mem hM x.2) (rv_mem hM y.2)).elim
      Or.inr Or.inl
  scale := fun x y z hz => by
    have hz' : iRv z.1 ≠ iRVZero :=
      rv_ne_zero_of_ne_zero z.2 (fun h => hz (Subtype.ext h))
    have h := le_mul_iff hM (rv_mem hM y.2) (rv_mem hM x.2)
      (rv_mem hM z.2) hz'
    have hy : (y * z).1 = iVFMul y.1 z.1 := rfl
    have hx : (x * z).1 = iVFMul x.1 z.1 := rfl
    show iLe (iRv y.1) (iRv x.1) ↔ iLe (iRv (y * z).1) (iRv (x * z).1)
    rw [hy, hx, rv_mul_hom_of_model hM y.2 z.2,
      rv_mul_hom_of_model hM x.2 z.2]
    exact h

/-- The valued-field core determines an ordinary Mathlib valuation on its VF sort. -/
theorem exists_valuation_predV :
    ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ)
      (w : Valuation (NativeField.VF M) Γ),
      ∀ x y : NativeField.VF M, predV x y ↔ w x ≤ w y :=
  VFValued.exists_valuation_of_isValPred (isValPred_predV (M := M))


end SpecialTransformations.Section6.NativeValuation
