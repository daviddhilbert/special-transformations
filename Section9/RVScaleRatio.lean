module

public import Section9.UniformRVScaling

@[expose] public section

/-! The normalization factor in the residue chart is a term in the
two scale tuples and the residue determinant. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "RV" => CanonicalRV.RVSort M

private theorem realize_rvMul {ι : Type} (a b : LRV.Term ι) (z : ι → M) :
    (Term.func Fn.rvMul ![a,b]).realize z = iRVMul (a.realize z) (b.realize z) := by
  change Structure.funMap (L := LRV) Fn.rvMul (fun i => (![a,b] i).realize z) = _
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem realize_rvInv {ι : Type} (a : LRV.Term ι) (z : ι → M) :
    (Term.func Fn.rvInv ![a]).realize z = iRVInvFn (a.realize z) := by
  change Structure.funMap (L := LRV) Fn.rvInv (fun i => (![a] i).realize z) = _
  congr 1
  funext i
  fin_cases i
  rfl

private theorem exists_rv_product_term {ι : Type} (q : Fin n → ι) (I : Finset (Fin n)) :
    ∃ t : LRV.Term ι, ∀ z : ι → RV,
      t.realize (Subtype.val ∘ z) = (∏ i ∈ I, z (q i)).val := by
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨.func Fn.rvOne Fin.elim0, fun z => ?_⟩
    rw [Finset.prod_empty, RVOperations.one_val]
    change Structure.funMap (L := LRV) Fn.rvOne (fun i => (Fin.elim0 i : LRV.Term ι).realize _) = _
    congr 1
    funext i
    exact i.elim0
  | insert i I hi ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨.func Fn.rvMul ![.var (q i), t], fun z => ?_⟩
    rw [realize_rvMul, Term.realize_var, ht, Finset.prod_insert hi, RVOperations.mul_val]
    rfl

theorem exists_rv_scale_ratio_term :
    ∃ t : LRV.Term (Fin (n+n) ⊕ Unit), ∀ (a b : Fin n → RV) (d : RV),
      t.realize (Sum.elim (rvValues (productTuple a b)) (fun _ => d.val)) =
        ((((∏ i, b i) / ∏ i, a i) * d) : RV).val := by
  let l : Fin n → Fin (n+n) ⊕ Unit := Sum.inl ∘ productLeft n n
  let r : Fin n → Fin (n+n) ⊕ Unit := Sum.inl ∘ productRight n n
  obtain ⟨A, hA⟩ := exists_rv_product_term (M := M) l Finset.univ
  obtain ⟨B, hB⟩ := exists_rv_product_term (M := M) r Finset.univ
  let I : LRV.Term (Fin (n+n) ⊕ Unit) := .func Fn.rvInv ![A]
  let Q : LRV.Term (Fin (n+n) ⊕ Unit) := .func Fn.rvMul ![B, I]
  refine ⟨.func Fn.rvMul ![Q, .var (.inr ())], fun a b d => ?_⟩
  let z : Fin (n+n) ⊕ Unit → RV := Sum.elim (productTuple a b) (fun _ => d)
  have hz : Sum.elim (rvValues (productTuple a b)) (fun _ : Unit => d.val) = Subtype.val ∘ z := by
    funext i
    cases i <;> rfl
  rw [hz]
  rw [realize_rvMul, Term.realize_var, show Q = Term.func Fn.rvMul ![B,I] from rfl,
    realize_rvMul, show I = Term.func Fn.rvInv ![A] from rfl, realize_rvInv]
  rw [hA, hB, div_eq_mul_inv, RVOperations.mul_val, RVOperations.mul_val, RVOperations.inv_val]
  simp only [z, l, r, Function.comp_apply, Sum.elim_inl, Sum.elim_inr, productTuple_left, productTuple_right]

end SpecialTransformations.Section9
