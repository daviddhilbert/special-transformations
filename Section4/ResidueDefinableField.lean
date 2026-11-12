module

public import Section4.ResidueFieldInterpretation
public import Section4.TupleTranscendence
public import Section3.SortedFunctionClosure

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def residueDefinableField (S : Set M) : Subfield (ModelResidue M) where
  carrier := {a | DefinableClosureAt S .rv (residueRaw a)}
  zero_mem' := by
    change DefinableClosureAt S .rv (residueRV (0 : ModelResidue M)).val
    rw [residueRV_zero, RVOperations.zero_val]
    exact definableClosureAt_function_symbol S Fn.rvZero Fin.elim0 (fun i => i.elim0) (fun i => i.elim0)
  one_mem' := by
    change DefinableClosureAt S .rv (residueRV (1 : ModelResidue M)).val
    rw [residueRV_one, RVOperations.one_val]
    exact definableClosureAt_function_symbol S Fn.rvOne Fin.elim0 (fun i => i.elim0) (fun i => i.elim0)
  add_mem' := by
    intro a b ha hb
    change DefinableClosureAt S .rv (residueRV (a + b)).val
    rw [residueRV_add]
    exact definableClosureAt_function_symbol S Fn.kAdd ![residueRaw a, residueRaw b]
      (by intro i; fin_cases i; exact (residueRV a).property; exact (residueRV b).property)
      (by intro i; fin_cases i; exact ha; exact hb)
  mul_mem' := by
    intro a b ha hb
    change DefinableClosureAt S .rv (residueRV (a * b)).val
    rw [residueRV_mul, RVOperations.mul_val]
    exact definableClosureAt_function_symbol S Fn.rvMul ![residueRaw a, residueRaw b]
      (by intro i; fin_cases i; exact (residueRV a).property; exact (residueRV b).property)
      (by intro i; fin_cases i; exact ha; exact hb)
  neg_mem' := by
    intro a ha
    change DefinableClosureAt S .rv (residueRV (-a)).val
    rw [residueRV_neg]
    exact definableClosureAt_function_symbol S Fn.kNeg ![residueRaw a]
      (by intro i; fin_cases i; exact (residueRV a).property)
      (by intro i; fin_cases i; exact ha)
  inv_mem' := by
    intro a ha
    change DefinableClosureAt S .rv (residueRV a⁻¹).val
    rw [residueRV_inv, RVOperations.inv_val]
    exact definableClosureAt_function_symbol S Fn.rvInv ![residueRaw a]
      (by intro i; fin_cases i; exact (residueRV a).property)
      (by intro i; fin_cases i; exact ha)

theorem residueParameterField_le_definableField (B : LRV.Substructure M) :
    residueParameterField B ≤ residueDefinableField (B : Set M) := by
  intro a ha
  exact definableClosureAt_of_mem ha (residueRV a).property

theorem tupleField_le_residueDefinableField (B : LRV.Substructure M) {n : ℕ}
    (a : Fin n → ModelResidue M) :
    tupleField (residueParameterField B) a ≤
      residueDefinableField ((B : Set M) ∪ Set.range (fun i => residueRaw (a i))) := by
  apply sup_le
  · intro x hx
    exact definableClosureAt_of_mem (Or.inl hx) (residueRV x).property
  · apply Subfield.closure_le.mpr
    rintro x ⟨i, rfl⟩
    exact definableClosureAt_of_mem (Or.inr ⟨i, rfl⟩) (residueRV (a i)).property

end SpecialTransformations.Section4.ResiduePurity

end
