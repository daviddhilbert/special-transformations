module

public import Section6.ConcreteLogic

@[expose] public section

/-! The field and residue-field sentences in the ordinary tagged structure. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer TrivCase
open SpecialTransformations.Section6.ConcreteRV

namespace SpecialTransformations.Section6.ConcreteValued

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation K Γ)
local instance : LRV.Structure (Carrier v) := nativeStructure v

theorem snoc_map_inl {n : ℕ} (z : Fin n → K) (x : K) :
    (Fin.snoc (fun i => (Sum.inl (z i) : Carrier v)) (Sum.inl x) : Fin (n + 1) → Carrier v) =
      fun i => Sum.inl (Fin.snoc (α := fun _ : Fin (n + 1) => K) z x i) := by
  funext i
  cases i using Fin.lastCases <;> simp

theorem snoc_map_residue {n : ℕ} (z : Fin n → ConcreteRV.Residue v)
    (x : ConcreteRV.Residue v) :
    (Fin.snoc (fun i => (Sum.inr (residueCode v (z i)) : Carrier v))
      (Sum.inr (residueCode v x)) : Fin (n + 1) → Carrier v) =
      fun i => Sum.inr (residueCode v
        (Fin.snoc (α := fun _ : Fin (n + 1) => ConcreteRV.Residue v) z x i)) := by
  funext i
  cases i using Fin.lastCases <;> simp

theorem rvZero_code : iRVZero (M := Carrier v) = Sum.inr (residueCode v 0) := by
  rw [rvZero_eq, residueCode_zero]

theorem rvOne_code : iRVOne (M := Carrier v) = Sum.inr (residueCode v 1) := by
  rw [rvOne_eq, residueCode_one]

private theorem residueCode_eq_iff {r s : ConcreteRV.Residue v} :
    residueCode v r = residueCode v s ↔ r = s := (residueCode_injective v).eq_iff

macro "native_vf_simp" : tactic =>
  `(tactic| simp only [pEq, BoundedFormula.realize_bdEqual, BoundedFormula.realize_sup,
      BoundedFormula.realize_inf, BoundedFormula.realize_imp, BoundedFormula.realize_not,
      realize_tv, Term.realize_var, Sum.elim_inr, Function.comp_apply,
      realize_tVFZero, realize_tVFOne, realize_tVFAdd, realize_tVFNeg, realize_tVFMul,
      vfZero_eq, vfOne_eq, vfAdd_eq, vfNeg_eq, vfMul_eq, Sum.inl.injEq])

macro "native_k_simp" : tactic =>
  `(tactic| simp only [pEq, BoundedFormula.realize_bdEqual, BoundedFormula.realize_sup,
      BoundedFormula.realize_inf, BoundedFormula.realize_imp, BoundedFormula.realize_not,
      realize_tv, Term.realize_var, Sum.elim_inr, Function.comp_apply,
      realize_tRVZero, realize_tRVOne_T, realize_tKAdd, realize_tKNeg, realize_tRVMul,
      rvZero_code, rvOne_code, kAdd_eq, kNeg_eq, rvMul_eq, Sum.inr.injEq,
      addResidue_code, negResidue_code, ← residueCode_mul, residueCode_eq_iff])

theorem model_vfField : Carrier v ⊨ Axioms.vfField := by
  constructor
  intro σ hσ
  simp only [Axioms.vfField, Axioms.ofList, Set.mem_ofPred_eq, Axioms.fieldAxioms,
    List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [allVF v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_vf_simp
    exact add_assoc ..
  · rw [allVF v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_vf_simp
    exact add_comm ..
  · rw [allVF v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_vf_simp
    exact add_zero _
  · rw [allVF v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_vf_simp
    exact add_neg_cancel _
  · rw [allVF v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_vf_simp
    exact mul_assoc ..
  · rw [allVF v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_vf_simp
    exact mul_comm ..
  · rw [allVF v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_vf_simp
    exact mul_one _
  · rw [allVF v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_vf_simp
    exact mul_add ..
  · change ¬ (pEq (tVFZero : Tm 0) tVFOne).Realize (default : Empty → Carrier v) default
    native_vf_simp
    exact zero_ne_one
  · rw [allVF v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    simp only [BoundedFormula.realize_sup, exVF, snoc_map_inl]
    native_vf_simp
    change x 0 = 0 ∨ ∃ y : K, x 0 * y = 1
    by_cases h : x 0 = 0
    · exact Or.inl h
    · exact Or.inr ⟨(x 0)⁻¹, mul_inv_cancel₀ h⟩

theorem model_kField : Carrier v ⊨ Axioms.kField := by
  constructor
  intro σ hσ
  simp only [Axioms.kField, Axioms.ofList, Set.mem_ofPred_eq,
    List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [allResidue v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_k_simp
    exact add_assoc ..
  · rw [allResidue v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_k_simp
    exact add_comm ..
  · rw [allResidue v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_k_simp
    exact add_zero _
  · rw [allResidue v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_k_simp
    exact add_neg_cancel _
  · rw [allResidue v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_k_simp
    exact mul_assoc ..
  · rw [allResidue v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_k_simp
    exact mul_comm ..
  · rw [allResidue v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_k_simp
    exact mul_one _
  · rw [allResidue v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_k_simp
    exact mul_add ..
  · change ¬ (pEq (tRVZero : Tm 0) tRVOne).Realize (default : Empty → Carrier v) default
    native_k_simp
    exact zero_ne_one
  · rw [allResidue v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    simp only [BoundedFormula.realize_sup, exResidue, snoc_map_residue]
    native_k_simp
    change x 0 = 0 ∨ ∃ y : ConcreteRV.Residue v, x 0 * y = 1
    by_cases h : x 0 = 0
    · exact Or.inl h
    · exact Or.inr ⟨(x 0)⁻¹, mul_inv_cancel₀ h⟩

end SpecialTransformations.Section6.ConcreteValued
