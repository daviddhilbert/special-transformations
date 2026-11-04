/-
**The `VF` field laws and the `Field` instance on `VFType`, over the frozen encoding.**

`Milestone0/Encoding.lean` states `Axioms.vfField` as `allSorted`-guarded sentences and contains no
realisation lemmas for them, so nothing importing `Enc` could treat the `VF` sort as a field.  This
file ports that layer from `QE/Assembly_val.lean` (where it is proved against that file's own copy of
the encoding) onto the frozen one.

It sits on `QF2Fragment` (which already supplies the term-realisation and sort-discipline lemmas) and
`RVCalc` (the `iLe`/`rv` order calculus), so it contains only what those two do not: the `VF` sort
as a type, its `Zero`/`One`/`Add`/`Neg`/`Mul` instances, the field laws, and `vfFieldOfModel`.

Payoff: with `Field (VFType M)` available, `VFValued` can put a genuine Mathlib `Valuation` on it and
the paper's valuation-theoretic lemmas become instantiable at a model of the frozen `ACVF`.
-/
import RVCalc

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0

namespace Transfer

/-- Extract an equation from an `allSorted`-guarded `pEq` sentence. -/
theorem eq_of_allSorted {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {k : ℕ}
    {ss : Fin k → SortTag} {a b : Tm k} (hmem : allSorted ss (pEq a b) ∈ Axioms.ACVF)
    (x : Fin k → M) (hx : ∀ i, (match ss i with
      | .vf => iVF (x i)
      | .rv => iRV (x i))) :
    a.realize (Sum.elim (default : Empty → M) x)
      = b.realize (Sum.elim (default : Empty → M) x) := by
  have h := allSorted_realize hM hmem x hx
  simpa only [pEq, BoundedFormula.realize_bdEqual] using h

/-- The reduction of the `VF` field axioms to a list membership in `vfField`. -/
theorem mem_vfField {s : LRV.Sentence} (h : s ∈ Axioms.vfField) : s ∈ Axioms.ACVF :=
  RVCalc.mem_ACVF_vfField h

theorem vf_add_assoc {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFAdd (iVFAdd x y) z = iVFAdd x (iVFAdd y z) := by
  have hmem : allSorted ![.vf, .vf, .vf]
      (pEq (tVFAdd (tVFAdd &0 &1) &2) (tVFAdd &0 (tVFAdd &1 &2))) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y, z] (by intro i; fin_cases i <;> simp [hx, hy, hz])
  simpa [realize_tVFAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    using h

theorem vf_add_comm {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVFAdd x y = iVFAdd y x := by
  have hmem : allSorted ![.vf, .vf] (pEq (tVFAdd &0 &1) (tVFAdd &1 &0)) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y] (by intro i; fin_cases i <;> simp [hx, hy])
  simpa [realize_tVFAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

theorem vf_add_zero {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVFAdd x iVFZero = x := by
  have hmem : allSorted ![.vf] (pEq (tVFAdd &0 tVFZero) &0) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simpa [realize_tVFAdd, realize_tVFZero, Matrix.cons_val_zero] using h

theorem vf_add_neg {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVFAdd x (iVFNeg x) = iVFZero := by
  have hmem : allSorted ![.vf] (pEq (tVFAdd &0 (tVFNeg &0)) tVFZero) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simpa [realize_tVFAdd, realize_tVFNeg, realize_tVFZero, Matrix.cons_val_zero] using h

theorem vf_mul_assoc {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFMul (iVFMul x y) z = iVFMul x (iVFMul y z) := by
  have hmem : allSorted ![.vf, .vf, .vf]
      (pEq (tVFMul (tVFMul &0 &1) &2) (tVFMul &0 (tVFMul &1 &2))) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y, z] (by intro i; fin_cases i <;> simp [hx, hy, hz])
  simpa [realize_tVFMul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    using h

theorem vf_mul_comm {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVFMul x y = iVFMul y x := by
  have hmem : allSorted ![.vf, .vf] (pEq (tVFMul &0 &1) (tVFMul &1 &0)) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y] (by intro i; fin_cases i <;> simp [hx, hy])
  simpa [realize_tVFMul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

theorem vf_mul_one {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVFMul x iVFOne = x := by
  have hmem : allSorted ![.vf] (pEq (tVFMul &0 tVFOne) &0) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simpa [realize_tVFMul, realize_tVFOne, Matrix.cons_val_zero] using h

theorem vf_left_distrib {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFMul x (iVFAdd y z) = iVFAdd (iVFMul x y) (iVFMul x z) := by
  have hmem : allSorted ![.vf, .vf, .vf]
      (pEq (tVFMul &0 (tVFAdd &1 &2)) (tVFAdd (tVFMul &0 &1) (tVFMul &0 &2)))
      ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y, z] (by intro i; fin_cases i <;> simp [hx, hy, hz])
  simpa [realize_tVFAdd, realize_tVFMul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using h

/-- `0 ≠ 1` on the `VF` sort. -/
theorem vf_zero_ne_one {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iVFZero (M := M) ≠ iVFOne := by
  have hmem : (∼(pEq tVFZero tVFOne)) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := sentence_realize hM hmem
  rw [Sentence.Realize] at h
  simp only [Formula.Realize, BoundedFormula.realize_not, pEq, BoundedFormula.realize_bdEqual,
    realize_tVFZero, realize_tVFOne] at h
  exact h

/-- **The invertibility law**: a `VF`-element is `0` or has a multiplicative inverse.  The
encoding states it this way because the language has no inverse symbol. -/
theorem vf_mul_inv_or_zero {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : x = iVFZero ∨ ∃ y : M, iVF y ∧ iVFMul x y = iVFOne := by
  have hmem : allSorted ![.vf]
      (pEq &0 tVFZero ⊔ exSorted .vf (pEq (tVFMul &0 &1) tVFOne)) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := allSorted_realize hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simp only [BoundedFormula.realize_sup, exSorted, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, sortPred, pEq, BoundedFormula.realize_bdEqual, realize_tVFZero,
    realize_tVFMul, realize_tVFOne, realize_tv, Term.realize_var, Sum.elim_inr, Function.comp_apply, pVF_realize, Term.realize_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
  exact h
/-! ### The `VF` sort as a field -/

section VFField

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The `VF` sort of an `ACVF`-model, as a type. -/
def VFType : Type := {x : M // iVF x}

instance vfInstZero : Zero (VFType (M := M)) := ⟨⟨iVFZero, vf_zero_mem hM⟩⟩

instance vfInstOne : One (VFType (M := M)) := ⟨⟨iVFOne, vf_one_mem hM⟩⟩

instance vfInstAdd : Add (VFType (M := M)) :=
  ⟨fun x y => ⟨iVFAdd x.1 y.1, vf_add_mem hM x.2 y.2⟩⟩

instance vfInstNeg : Neg (VFType (M := M)) :=
  ⟨fun x => ⟨iVFNeg x.1, vf_neg_mem hM x.2⟩⟩

instance vfInstMul : Mul (VFType (M := M)) :=
  ⟨fun x y => ⟨iVFMul x.1 y.1, vf_mul_mem hM x.2 y.2⟩⟩

/-- The inverse on the `VF` sort: `0⁻¹ = 0`, and a nonzero element inverts by the
invertibility law. -/
noncomputable def vfInvFun (x : VFType (M := M)) : VFType (M := M) := by
  classical
  exact if h : x.1 = iVFZero then 0
    else
      let w := (vf_mul_inv_or_zero hM x.2).resolve_left h
      ⟨Classical.choose w, (Classical.choose_spec w).1⟩

noncomputable instance vfInstInv : Inv (VFType (M := M)) := ⟨vfInvFun⟩

theorem vfInv_zero : (0 : VFType (M := M))⁻¹ = 0 := dif_pos rfl

theorem vfInv_val {x : VFType (M := M)} (hx : x ≠ 0) :
    iVFMul x.1 ((x⁻¹ : VFType (M := M))).1 = iVFOne := by
  have hx' : x.1 ≠ iVFZero := fun h => hx (Subtype.ext h)
  have hval : ((x⁻¹ : VFType (M := M))).1
      = Classical.choose ((vf_mul_inv_or_zero hM x.2).resolve_left hx') := by
    show (vfInvFun x).1 = _
    unfold vfInvFun
    exact congrArg Subtype.val (dif_neg hx')
  rw [hval]
  exact (Classical.choose_spec ((vf_mul_inv_or_zero hM x.2).resolve_left hx')).2

/-- **The `VF` sort is a field.** -/
noncomputable def vfFieldOfModel : Field (VFType (M := M)) :=
  Field.ofMinimalAxioms (VFType (M := M))
    (fun a b c => Subtype.ext (vf_add_assoc hM a.2 b.2 c.2))
    (fun a => Subtype.ext (by
      show iVFAdd iVFZero a.1 = a.1
      rw [vf_add_comm hM (vf_zero_mem hM) a.2]
      exact vf_add_zero hM a.2))
    (fun a => Subtype.ext (by
      show iVFAdd (iVFNeg a.1) a.1 = iVFZero
      rw [vf_add_comm hM (vf_neg_mem hM a.2) a.2]
      exact vf_add_neg hM a.2))
    (fun a b c => Subtype.ext (vf_mul_assoc hM a.2 b.2 c.2))
    (fun a b => Subtype.ext (vf_mul_comm hM a.2 b.2))
    (fun a => Subtype.ext (by
      show iVFMul iVFOne a.1 = a.1
      rw [vf_mul_comm hM (vf_one_mem hM) a.2]
      exact vf_mul_one hM a.2))
    (fun a ha => Subtype.ext (vfInv_val ha))
    vfInv_zero
    (fun a b c => Subtype.ext (vf_left_distrib hM a.2 b.2 c.2))
    ⟨0, 1, fun h => vf_zero_ne_one hM (congrArg Subtype.val h)⟩

end VFField

end Transfer

end SpecialTransformations.Milestone0
