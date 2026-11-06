import Section4.ResidueScaledFunctions

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The actual residue subfield named by an LRV substructure. The full
residue predicate includes zero, and named RV inversion closes this field
under inverses without introducing another language. -/
def residueParameterField (B : LRV.Substructure M) : Subfield (ModelResidue M) where
  carrier := {a | (residueRV a).val ∈ B}
  zero_mem' := by
    change (residueRV (0 : ModelResidue M)).val ∈ B
    rw [residueRV_zero, RVOperations.zero_val]
    exact SubstructureRVGroup.rvZero_mem B
  one_mem' := by
    change (residueRV (1 : ModelResidue M)).val ∈ B
    rw [residueRV_one, RVOperations.one_val]
    exact SubstructureRVGroup.rvOne_mem B
  add_mem' := by
    intro a b ha hb
    change (residueRV (a + b)).val ∈ B
    rw [residueRV_add]
    exact B.fun_mem Fn.kAdd ![(residueRV a).val, (residueRV b).val]
      (by intro i; fin_cases i; exact ha; exact hb)
  mul_mem' := by
    intro a b ha hb
    change (residueRV (a * b)).val ∈ B
    rw [residueRV_mul, RVOperations.mul_val]
    exact B.fun_mem Fn.rvMul ![(residueRV a).val, (residueRV b).val]
      (by intro i; fin_cases i; exact ha; exact hb)
  neg_mem' := by
    intro a ha
    change (residueRV (-a)).val ∈ B
    rw [residueRV_neg]
    exact B.fun_mem Fn.kNeg ![(residueRV a).val]
      (by intro i; fin_cases i; exact ha)
  inv_mem' := by
    intro a ha
    change (residueRV a⁻¹).val ∈ B
    rw [residueRV_inv, RVOperations.inv_val]
    exact B.fun_mem Fn.rvInv ![(residueRV a).val]
      (by intro i; fin_cases i; exact ha)

theorem residuePart_mem (B : LRV.Substructure M) (c : CanonicalRV.RVSort M)
    (hc : c.val ∈ B) : residuePart c ∈ residueParameterField B := by
  by_cases hK : ValuedModelMap.inK c
  · change (residueRV (residuePart c)).val ∈ B
    rw [residueRV_part hK]
    exact hc
  · rw [residuePart, dif_neg hK]
    exact (residueParameterField B).zero_mem

theorem rv_mul_mem_base (B : LRV.Substructure M) {c d : CanonicalRV.RVSort M}
    (hc : c.val ∈ B) (hd : d.val ∈ B) : (c * d).val ∈ B := by
  rw [RVOperations.mul_val]
  exact B.fun_mem Fn.rvMul ![c.val, d.val]
    (by intro i; fin_cases i; exact hc; exact hd)

theorem rv_inv_mem_base (B : LRV.Substructure M) {c : CanonicalRV.RVSort M}
    (hc : c.val ∈ B) : (c⁻¹).val ∈ B := by
  rw [RVOperations.inv_val]
  exact B.fun_mem Fn.rvInv ![c.val] (by intro i; fin_cases i; exact hc)

end SpecialTransformations.Section4.ResiduePurity

end
