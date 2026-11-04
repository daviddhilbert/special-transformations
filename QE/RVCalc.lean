/-
# The `RV`/`Γ` order calculus in the frozen tagged encoding (member m6, swarm smw1kqpdk)

Direction: the `RV`-polynomial / `RV`-calculus layer of the tagged `L_RV`.

The frozen encoding `Milestone0/Encoding.lean` axiomatises `RV` with a preorder `≤` (`iLe`), the
unary `Kˣ` (`iUnits`), `×` (`iRVMul`) and the projection `rv` (`iRv`).  Its `ACVF` carries the
`repairRV` sentences `rvMulOneRV`, `rvMulInvRV`, `leMulCompatFull`, `rvEqLink`, …, which make
`RV ∖ {0}` a group and the order scale-invariant.  What the tree has not had until now is the
**calculus**: the elementary lemmas that any use of `≤` has to unfold.  `QE/Sec3Infra.lean`,
`QE/Sec4Polydisc.lean`, `QE/Sec3_sat.lean` speak the vocabulary (`{x | iVF x ∧ iLe t (iRv (iVFAdd x
(iVFNeg a)))}` is a ball) but no lemma about `iLe` exists anywhere in the tree.

This file supplies that layer, from the axioms, for an arbitrary `M ⊨ Axioms.ACVF`:

* the preorder: reflexivity (also at `0`), transitivity, totality, `0 = ∞` is top and alone in its
  class, `Kˣ` is the class of `1` (`leClassOne` read off), scale invariance in both directions;
* `rv` calculus: `iRv 1 = iRVOne` (`rv_one`), `iRVOne ≠ iRVZero`, `-x` has the same `Γ`-class as
  `x` (`rv_neg_class`, the lemma that is not in the tree and that every additive argument needs);
* the **ultrametric and the strict triangle**: `v(x) < v(y) → v(x+y) = v(x)`
  (`rv_add_of_lt`), the only additive input of root lifting (`rv:root:lift:vf`, Lemma 3.2) and of
  Hensel's lemma in the tagged encoding;
* `rvEqLink` in the form used by lifting: `v(x - y) > v y → iRv x = iRv y` (`rv_eq_of_close`),
  i.e. `rv` is constant on the open ball of radius `v y` around `y`.

No statement here is a hypothesis in disguise: every one is derived from `Axioms.ACVF`
(`repairRV`, `preorderRV`, `rvAxioms`, `vfField`) by unfolding `allSorted`/`sortedHyps`/`pLe`.
-/
import Enc
import QF2Fragment

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0

namespace SpecialTransformations.Milestone0

namespace RVCalc

variable {M : Type} [LRV.Structure M]
open LRV
open SpecialTransformations.Milestone0.Transfer

/-- realization of a free variable: stated with the constructor shape `Term.var (Sum.inr i)` so
that it is a keyed `simp` lemma (the encoding's `tv i h` is the same term, but `tv` is a plain
`def`, which blocks keyed matching). -/
@[simp] theorem realize_var_inr {k : ℕ} (i : Fin k) (v : Empty → M) (x : Fin k → M) :
    Term.realize (L := LRV) (Sum.elim v x) ((Term.var ∘ Sum.inr) i) = x i := rfl

/-- `∞ = 0` realizes to `iRVZero`.  Stated for `tRVInfty` because the axioms use that name, and
`realize_tRVZero` is keyed on `tRVZero`. -/
@[simp] theorem realize_tRVInfty {k : ℕ} (v : Empty ⊕ Fin k → M) :
    (tRVInfty (n := k)).realize v = iRVZero := realize_tRVZero v

/-! ## 1. Axiom membership -/

theorem mem_ACVF_preorderRV {s : LRV.Sentence} (h : s ∈ Axioms.preorderRV) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union] at *
  tauto

theorem mem_ACVF_rvAxioms {s : LRV.Sentence} (h : s ∈ Axioms.rvAxioms) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union] at *
  tauto

theorem mem_ACVF_vfField {s : LRV.Sentence} (h : s ∈ Axioms.vfField) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union] at *
  tauto

theorem mem_ACVF_ofList_preorder {s : LRV.Sentence}
    (h : s ∈ Axioms.ofList [Axioms.leRefl, Axioms.leTrans, Axioms.leTotal, Axioms.leTop,
      Axioms.leInftyEq, Axioms.leClassOne, Axioms.leMulCompat]) : s ∈ Axioms.ACVF :=
  mem_ACVF_preorderRV (by simpa [Axioms.preorderRV] using h)

theorem mem_ACVF_leRefl : Axioms.leRefl ∈ Axioms.ACVF :=
  mem_ACVF_ofList_preorder (by simp [Axioms.ofList])

theorem mem_ACVF_leTrans : Axioms.leTrans ∈ Axioms.ACVF :=
  mem_ACVF_ofList_preorder (by simp [Axioms.ofList])

theorem mem_ACVF_leTotal : Axioms.leTotal ∈ Axioms.ACVF :=
  mem_ACVF_ofList_preorder (by simp [Axioms.ofList])

theorem mem_ACVF_leTop : Axioms.leTop ∈ Axioms.ACVF :=
  mem_ACVF_ofList_preorder (by simp [Axioms.ofList])

theorem mem_ACVF_leInftyEq : Axioms.leInftyEq ∈ Axioms.ACVF :=
  mem_ACVF_ofList_preorder (by simp [Axioms.ofList])

theorem mem_ACVF_leClassOne : Axioms.leClassOne ∈ Axioms.ACVF :=
  mem_ACVF_ofList_preorder (by simp [Axioms.ofList])

theorem mem_ACVF_rvUltrametric : Axioms.rvUltrametric ∈ Axioms.ACVF :=
  mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])

theorem mem_ACVF_rvZeroEq : Axioms.rvZeroEq ∈ Axioms.ACVF :=
  mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])

theorem mem_ACVF_rvEqInfty : Axioms.rvEqInfty ∈ Axioms.ACVF :=
  mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])

theorem mem_ACVF_rvMulHom : Axioms.rvMulHom ∈ Axioms.ACVF :=
  mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])

theorem mem_ACVF_rvEqLink : Axioms.rvEqLink ∈ Axioms.ACVF :=
  mem_ACVF_repairRV (by simp [Axioms.repairRV, Axioms.ofList])

theorem mem_ACVF_leMulCompatFull : Axioms.leMulCompatFull ∈ Axioms.ACVF :=
  mem_ACVF_repairRV (by simp [Axioms.repairRV, Axioms.ofList])

theorem mem_ACVF_rvMulOneRV : Axioms.rvMulOneRV ∈ Axioms.ACVF :=
  mem_ACVF_repairRV (by simp [Axioms.repairRV, Axioms.ofList])

theorem mem_ACVF_rvMulInvRV : Axioms.rvMulInvRV ∈ Axioms.ACVF :=
  mem_ACVF_repairRV (by simp [Axioms.repairRV, Axioms.ofList])

theorem mem_ACVF_axNontrivialRV : Axioms.axNontrivialRV ∈ Axioms.ACVF :=
  mem_ACVF_repairRV (by simp [Axioms.repairRV, Axioms.ofList])

theorem mem_ACVF_kNegLink : Axioms.kNegLink ∈ Axioms.ACVF :=
  mem_ACVF_repairRV (by simp [Axioms.repairRV, Axioms.ofList])

theorem mem_ACVF_of_fieldAxioms {s : LRV.Sentence}
    (h : s ∈ Axioms.fieldAxioms .vf tVFZero tVFOne tVFAdd tVFMul tVFNeg) : s ∈ Axioms.ACVF :=
  mem_ACVF_vfField (by simpa [Axioms.vfField, Axioms.ofList] using h)

/-- `rv 0 = 0` (the encoding's `∞` is the interpretation of the `RV`-zero). -/
theorem rv_zero_eq (hM : M ⊨ Axioms.ACVF) : iRv (iVFZero (M := M)) = iRVZero := by
  have h := sentence_realize hM (φ := Axioms.rvZeroEq) mem_ACVF_rvZeroEq
  rw [Axioms.rvZeroEq, Sentence.Realize] at h
  simpa [Sentence.Realize, Formula.Realize, pEq, BoundedFormula.realize_bdEqual, realize_tRv,
    realize_tVFZero, tRVInfty, realize_tRVInfty, realize_tRVZero] using h

/-! ## 2. Elementary algebra of the `VF` sort, from `vfField`

The reduction needs only a handful of ring identities; they are proved here once so that the
calculus below never mentions `allSorted`. -/

theorem vf_add_comm (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y) :
    iVFAdd x y = iVFAdd y x := by
  have h := allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf])
    (φ := (pEq (tVFAdd &0 &1) (tVFAdd &1 &0)))
    (mem_ACVF_of_fieldAxioms (by simp [Axioms.fieldAxioms])) ![x, y]
    (by intro i; fin_cases i <;> simp [hx, hy])
  simpa [pEq, BoundedFormula.realize_bdEqual, realize_tVFAdd, realize_var_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

theorem vf_add_assoc (hM : M ⊨ Axioms.ACVF) {x y z : M} (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFAdd (iVFAdd x y) z = iVFAdd x (iVFAdd y z) := by
  have h := allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf, SortTag.vf])
    (φ := (pEq (tVFAdd (tVFAdd &0 &1) &2) (tVFAdd &0 (tVFAdd &1 &2))))
    (mem_ACVF_of_fieldAxioms (by simp [Axioms.fieldAxioms])) ![x, y, z]
    (by intro i; fin_cases i <;> simp [hx, hy, hz])
  simpa [pEq, BoundedFormula.realize_bdEqual, realize_tVFAdd, realize_var_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two] using h

theorem vf_add_zero (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) : iVFAdd x iVFZero = x := by
  have h := allSorted_realize hM (ss := ![SortTag.vf])
    (φ := (pEq (tVFAdd &0 tVFZero) &0))
    (mem_ACVF_of_fieldAxioms (by simp [Axioms.fieldAxioms])) ![x]
    (by intro i; fin_cases i; simpa using hx)
  simpa [pEq, BoundedFormula.realize_bdEqual, realize_tVFAdd, realize_tVFZero,
    realize_var_inr, Matrix.cons_val_zero] using h

theorem vf_zero_add (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) : iVFAdd iVFZero x = x := by
  rw [vf_add_comm hM (vf_zero_mem (M := M) hM) hx, vf_add_zero hM hx]

theorem vf_add_neg (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iVFAdd x (iVFNeg x) = iVFZero := by
  have h := allSorted_realize hM (ss := ![SortTag.vf])
    (φ := (pEq (tVFAdd &0 (tVFNeg &0)) tVFZero))
    (mem_ACVF_of_fieldAxioms (by simp [Axioms.fieldAxioms])) ![x]
    (by intro i; fin_cases i; simpa using hx)
  simpa [pEq, BoundedFormula.realize_bdEqual, realize_tVFAdd, realize_tVFNeg, realize_tVFZero,
    realize_var_inr, Matrix.cons_val_zero] using h

theorem vf_add_left_cancel (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iVF a) (hb : iVF b)
    (hc : iVF c) (h : iVFAdd a b = iVFAdd a c) : b = c := by
  have hna : iVF (iVFNeg a) := vf_neg_mem (M := M) hM ha
  have h1 : iVFAdd (iVFNeg a) (iVFAdd a b) = iVFAdd (iVFNeg a) (iVFAdd a c) := by rw [h]
  rw [← vf_add_assoc hM hna ha hb, ← vf_add_assoc hM hna ha hc,
    vf_add_comm hM hna ha, vf_add_neg hM ha, vf_zero_add hM hb,
    vf_zero_add hM hc] at h1
  exact h1

theorem vf_mul_comm (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y) :
    iVFMul x y = iVFMul y x := by
  have h := allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf])
    (φ := (pEq (tVFMul &0 &1) (tVFMul &1 &0)))
    (mem_ACVF_of_fieldAxioms (by simp [Axioms.fieldAxioms])) ![x, y]
    (by intro i; fin_cases i <;> simp [hx, hy])
  simpa [pEq, BoundedFormula.realize_bdEqual, realize_tVFMul, realize_var_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

theorem vf_mul_one (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) : iVFMul x iVFOne = x := by
  have h := allSorted_realize hM (ss := ![SortTag.vf])
    (φ := (pEq (tVFMul &0 tVFOne) &0))
    (mem_ACVF_of_fieldAxioms (by simp [Axioms.fieldAxioms])) ![x]
    (by intro i; fin_cases i; simpa using hx)
  simpa [pEq, BoundedFormula.realize_bdEqual, realize_tVFMul, realize_tVFOne,
    realize_var_inr, Matrix.cons_val_zero] using h

theorem vf_mul_add (hM : M ⊨ Axioms.ACVF) {x y z : M} (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFMul x (iVFAdd y z) = iVFAdd (iVFMul x y) (iVFMul x z) := by
  have h := allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf, SortTag.vf])
    (φ := (pEq (tVFMul &0 (tVFAdd &1 &2)) (tVFAdd (tVFMul &0 &1) (tVFMul &0 &2))))
    (mem_ACVF_of_fieldAxioms (by simp [Axioms.fieldAxioms])) ![x, y, z]
    (by intro i; fin_cases i <;> simp [hx, hy, hz])
  simpa [pEq, BoundedFormula.realize_bdEqual, realize_tVFMul, realize_tVFAdd,
    realize_var_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two] using h

theorem vf_zero_ne_one (hM : M ⊨ Axioms.ACVF) : iVFZero (M := M) ≠ iVFOne := by
  have h := sentence_realize hM (φ := (∼(pEq tVFZero tVFOne)))
    (mem_ACVF_of_fieldAxioms (by simp [Axioms.fieldAxioms]))
  simpa [Sentence.Realize, Formula.Realize, pEq, BoundedFormula.realize_not,
    BoundedFormula.realize_bdEqual, realize_tVFZero, realize_tVFOne] using h

theorem vf_mul_zero (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iVFMul x iVFZero = iVFZero := by
  have hz0 : iVF (iVFZero (M := M)) := vf_zero_mem (M := M) hM
  have hz : iVF (iVFMul x iVFZero) := vf_mul_mem (M := M) hM hx hz0
  have h2 : iVFAdd (iVFZero (M := M)) iVFZero = iVFZero := vf_add_zero hM hz0
  have h1 : iVFAdd (iVFMul x iVFZero) iVFZero = iVFMul x iVFZero := vf_add_zero hM hz
  have h3 : iVFAdd (iVFMul x iVFZero) (iVFMul x iVFZero) = iVFMul x iVFZero := by
    rw [← vf_mul_add hM hx hz0 hz0, h2]
  exact (vf_add_left_cancel hM hz hz0 hz (h1.trans h3.symm)).symm

/-- `-0 = 0` -/
theorem vf_neg_zero (hM : M ⊨ Axioms.ACVF) : iVFNeg (iVFZero (M := M)) = iVFZero := by
  have hz0 : iVF (iVFZero (M := M)) := vf_zero_mem (M := M) hM
  have hn : iVF (iVFNeg (iVFZero (M := M))) := vf_neg_mem (M := M) hM hz0
  exact (vf_zero_add hM hn).symm.trans (vf_add_neg hM hz0)

/-- `(x + y) + (-y) = x` -/
theorem vf_add_add_neg (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y) :
    iVFAdd (iVFAdd x y) (iVFNeg y) = x := by
  rw [vf_add_assoc hM hx hy (vf_neg_mem (M := M) hM hy), vf_add_neg hM hy, vf_add_zero hM hx]

theorem vf_add_eq_zero_of_eq_neg (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y)
    (h : x = iVFNeg y) : iVFAdd x y = iVFZero := by
  rw [h, vf_add_comm hM (vf_neg_mem (M := M) hM hy) hy, vf_add_neg hM hy]

/-- `x = 0` follows from `-x = 0` -/
theorem vf_eq_zero_of_neg_eq_zero (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x)
    (h : iVFNeg x = iVFZero (M := M)) : x = iVFZero := by
  have h1 : iVFAdd x (iVFNeg x) = iVFZero := vf_add_neg hM hx
  rw [h, vf_add_zero hM hx] at h1
  exact h1

/-- `-1 ≠ 0` in the `VF` sort -/
theorem vf_neg_one_ne_zero (hM : M ⊨ Axioms.ACVF) :
    iVFNeg (iVFOne (M := M)) ≠ iVFZero := by
  intro h
  exact vf_zero_ne_one hM (vf_eq_zero_of_neg_eq_zero hM (vf_one_mem (M := M) hM) h).symm

/-- `(-1)·(-1) = 1` in the `VF` sort -/
theorem vf_neg_one_mul_neg_one (hM : M ⊨ Axioms.ACVF) :
    iVFMul (iVFNeg (iVFOne (M := M))) (iVFNeg iVFOne) = iVFOne := by
  have h1 : iVF (iVFOne (M := M)) := vf_one_mem (M := M) hM
  have h2 : iVF (iVFNeg (iVFOne (M := M))) := vf_neg_mem (M := M) hM h1
  have h3 : iVF (iVFMul (iVFNeg (iVFOne (M := M))) (iVFNeg iVFOne)) :=
    vf_mul_mem (M := M) hM h2 h2
  have hd := vf_mul_add hM h2 h1 h2
  have hz : iVFAdd (iVFOne (M := M)) (iVFNeg iVFOne) = iVFZero := vf_add_neg hM h1
  rw [hz, vf_mul_zero hM h2, vf_mul_one hM h2] at hd
  have hR : iVFAdd (iVFNeg (iVFOne (M := M))) iVFOne = iVFZero := by
    rw [vf_add_comm hM h2 h1]; exact vf_add_neg hM h1
  exact vf_add_left_cancel hM h2 h3 h1 (hd.symm.trans hR.symm)

/-! ## 3. The preorder on `RV` -/

/-- `≤` is reflexive at every `RV`-element (`leRefl` is guarded by `≠ 0`; at `0` the statement is
the ultrametric axiom at `(0,0)` together with `rv 0 = 0`). -/
theorem le_refl_rv (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) : iLe a a := by
  by_cases h0 : a = iRVZero
  · subst h0
    have hz0 : iVF (iVFZero (M := M)) := vf_zero_mem (M := M) hM
    have h := allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf])
      (φ := (pLe (tRv &0) (tRv (tVFAdd &0 &1)) ⊔ pLe (tRv &1) (tRv (tVFAdd &0 &1))))
      mem_ACVF_rvUltrametric ![iVFZero, iVFZero] (by
        intro i; fin_cases i <;> simpa using hz0)
    have h2 : iLe (iRv (iVFZero (M := M))) (iRv (iVFAdd iVFZero iVFZero)) ∨
        iLe (iRv (iVFZero (M := M))) (iRv (iVFAdd iVFZero iVFZero)) := by
      simpa [realize_pLe, realize_tRv, realize_tVFAdd, realize_var_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, BoundedFormula.realize_sup] using h
    rcases h2 with h2 | h2
    · simpa [vf_add_zero hM hz0, rv_zero_eq hM] using h2
    · simpa [vf_add_zero hM hz0, rv_zero_eq hM] using h2
  · have h := allSorted_realize hM (ss := ![SortTag.rv]) (φ := (pRV &0 ⟹ pLe &0 &0))
      mem_ACVF_leRefl ![a] (by intro i; fin_cases i; simpa using ha)
    have h2 : a ≠ iRVZero → iLe a a := by
      simpa [pRV_realize, realize_pLe, realize_var_inr, Matrix.cons_val_zero] using h
    exact h2 h0

/-- `0 = ∞` is the top element of the preorder. -/
theorem le_top_rv (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) : iLe a iRVZero := by
  by_cases h0 : a = iRVZero
  · subst h0; exact le_refl_rv hM ha
  · have h := allSorted_realize hM (ss := ![SortTag.rv]) (φ := (pRV &0 ⟹ pLe &0 tRVInfty))
      mem_ACVF_leTop ![a] (by intro i; fin_cases i; simpa using ha)
    have h2 : a ≠ iRVZero → iLe a iRVZero := by
      simpa [pRV_realize, realize_pLe, realize_var_inr, Matrix.cons_val_zero,
        realize_tRVInfty] using h
    exact h2 h0

/-- `0` is alone in its class: `0 ≤ a` forces `a = 0`. -/
theorem le_infty_eq (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) (h : iLe iRVZero a) :
    a = iRVZero := by
  by_cases h0 : a = iRVZero
  · exact h0
  · have h' := allSorted_realize hM (ss := ![SortTag.rv])
      (φ := (pRV &0 ⟹ (pLe tRVInfty &0 ⟹ pEq &0 tRVInfty)))
      mem_ACVF_leInftyEq ![a] (by intro i; fin_cases i; simpa using ha)
    have h2 : a ≠ iRVZero → iLe iRVZero a → a = iRVZero := by
      simpa [pRV_realize, realize_pLe, pEq, BoundedFormula.realize_bdEqual, realize_var_inr,
        Matrix.cons_val_zero, realize_tRVInfty] using h'
    exact h2 h0 h

theorem le_trans_rv (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c)
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
          mem_ACVF_leTrans ![a, b, c] (by intro i; fin_cases i <;> simp [ha, hb, hc])
        have h2 : a ≠ iRVZero → b ≠ iRVZero → c ≠ iRVZero →
            iLe a b → iLe b c → iLe a c := by
          simpa [pRV_realize, realize_pLe, realize_var_inr, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two] using h
        exact h2 ha0 hb0 hc0 hab hbc

theorem le_total_rv (hM : M ⊨ Axioms.ACVF) {a b : M} (ha : iRV a) (hb : iRV b) :
    iLe a b ∨ iLe b a := by
  by_cases ha0 : a = iRVZero
  · subst ha0; exact Or.inr (le_top_rv hM hb)
  · by_cases hb0 : b = iRVZero
    · subst hb0; exact Or.inl (le_top_rv hM ha)
    · have h := allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv])
        (φ := (pRV &0 ⟹ (pRV &1 ⟹ (pLe &0 &1 ⊔ pLe &1 &0))))
        mem_ACVF_leTotal ![a, b] (by intro i; fin_cases i <;> simp [ha, hb])
      have h2 : a ≠ iRVZero → b ≠ iRVZero → (iLe a b ∨ iLe b a) := by
        simpa [pRV_realize, realize_pLe, realize_var_inr, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, BoundedFormula.realize_sup] using h
      exact h2 ha0 hb0

/-- `Kˣ` is the class of `1` (`leClassOne` read off). -/
theorem units_iff_le_one (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) (ha0 : a ≠ iRVZero) :
    iUnits a ↔ (iLe iRVOne a ∧ iLe a iRVOne) := by
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pRV &0 ⟹ (pUnits &0 ⇔ (pLe tRVOne &0 ⊓ pLe &0 tRVOne))))
    mem_ACVF_leClassOne ![a] (by intro i; fin_cases i; simpa using ha)
  have h2 : a ≠ iRVZero → (iUnits a ↔ (iLe iRVOne a ∧ iLe a iRVOne)) := by
    simpa [pRV_realize, pUnits_realize, realize_pLe, BoundedFormula.realize_inf,
      BoundedFormula.realize_iff, realize_var_inr, realize_tRVOne_T, Matrix.cons_val_zero] using h
  exact h2 ha0

/-- the order is invariant under scaling by a nonzero `RV`-element, in both directions
(`leMulCompatFull`). -/
theorem le_mul_iff (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c)
    (hc0 : c ≠ iRVZero) :
    (iLe a b ↔ iLe (iRVMul a c) (iRVMul b c)) := by
  have h := allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv, SortTag.rv])
    (φ := (pRV &2 ⟹ (pLe &0 &1 ⇔ pLe (tRVMul &0 &2) (tRVMul &1 &2))))
    mem_ACVF_leMulCompatFull ![a, b, c] (by intro i; fin_cases i <;> simp [ha, hb, hc])
  have h2 : c ≠ iRVZero → (iLe a b ↔ iLe (iRVMul a c) (iRVMul b c)) := by
    simpa [pRV_realize, realize_pLe, realize_tRVMul, BoundedFormula.realize_iff, realize_var_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two] using h
  exact h2 hc0

/-! ## 4. `(-1)·x = -x`, and the `rv` calculus -/

theorem vf_add_mul (hM : M ⊨ Axioms.ACVF) {x y z : M} (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFMul (iVFAdd y z) x = iVFAdd (iVFMul y x) (iVFMul z x) := by
  rw [vf_mul_comm hM (vf_add_mem (M := M) hM hy hz) hx, vf_mul_add hM hx hy hz,
    vf_mul_comm hM hy hx, vf_mul_comm hM hz hx]

theorem vf_zero_mul (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iVFMul (iVFZero (M := M)) x = iVFZero := by
  rw [vf_mul_comm hM (vf_zero_mem (M := M) hM) hx, vf_mul_zero hM hx]

theorem vf_neg_one_mul (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iVFMul (iVFNeg (iVFOne (M := M))) x = iVFNeg x := by
  have h1 : iVF (iVFOne (M := M)) := vf_one_mem (M := M) hM
  have hn : iVF (iVFNeg (iVFOne (M := M))) := vf_neg_mem (M := M) hM h1
  have hprod : iVF (iVFMul (iVFNeg (iVFOne (M := M))) x) := vf_mul_mem (M := M) hM hn hx
  have hz : iVFAdd (iVFOne (M := M)) (iVFNeg iVFOne) = iVFZero := vf_add_neg hM h1
  have hd := vf_add_mul hM hx h1 hn
  rw [hz, vf_zero_mul hM hx, vf_mul_comm hM h1 hx, vf_mul_one hM hx] at hd
  exact vf_add_left_cancel hM hx hprod (vf_neg_mem (M := M) hM hx)
    (hd.symm.trans (vf_add_neg hM hx).symm)

/-- `rv x = 0` forces `x = 0` (`rvEqInfty`). -/
theorem vf_eq_zero_of_rv_eq_zero (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x)
    (h : iRv x = iRVZero) : x = iVFZero := by
  have h' := allSorted_realize hM (ss := ![SortTag.vf])
    (φ := (pEq (tRv &0) tRVInfty ⟹ pEq &0 tVFZero))
    mem_ACVF_rvEqInfty ![x] (by intro i; fin_cases i; simpa using hx)
  have h2 : iRv x = iRVZero → x = iVFZero := by
    simpa [pEq, BoundedFormula.realize_bdEqual, realize_tRv, realize_var_inr, realize_tVFZero,
      realize_tRVInfty, Matrix.cons_val_zero] using h'
  exact h2 h

/-- `rv 1 = 1`. -/
theorem rv_one (hM : M ⊨ Axioms.ACVF) : iRv (iVFOne (M := M)) = iRVOne := by
  have h1 : iVF (iVFOne (M := M)) := vf_one_mem (M := M) hM
  have hr : iRV (iRv (iVFOne (M := M))) := rv_mem hM h1
  have hmm : iVFMul (iVFOne (M := M)) iVFOne = iVFOne := vf_mul_one hM h1
  have hsq : iRVMul (iRv (iVFOne (M := M))) (iRv (iVFOne (M := M)))
      = iRv (iVFOne (M := M)) := by
    rw [← rv_mul_hom_of_model hM h1 h1, hmm]
  by_cases h0 : iRv (iVFOne (M := M)) = iRVZero
  · exact absurd (vf_eq_zero_of_rv_eq_zero hM h1 h0) (fun hh => vf_zero_ne_one hM hh.symm)
  · obtain ⟨b, hb, hb0, hbinv⟩ := rv_mul_inv_exists_of_model hM hr h0
    calc iRv (iVFOne (M := M)) = iRVMul iRVOne (iRv (iVFOne (M := M))) :=
          (rv_mul_one_any hM hr).symm
      _ = iRVMul (iRVMul b (iRv (iVFOne (M := M)))) (iRv (iVFOne (M := M))) := by
          rw [← hbinv]
      _ = iRVMul b (iRVMul (iRv (iVFOne (M := M))) (iRv (iVFOne (M := M)))) :=
          rv_mul_assoc_of_model hM hb hr hr
      _ = iRVMul b (iRv (iVFOne (M := M))) := by rw [hsq]
      _ = iRVOne := hbinv

/-- `1 ≠ 0` in the `RV` sort. -/
theorem rv_one_ne_zero (hM : M ⊨ Axioms.ACVF) : iRVOne (M := M) ≠ iRVZero := by
  intro h
  exact vf_zero_ne_one hM (vf_eq_zero_of_rv_eq_zero hM (vf_one_mem (M := M) hM)
    (by rw [rv_one hM]; exact h)).symm

/-- `rv(-1)` is a unit, i.e. lies in the class of `1`.  This is the step that makes the *additive*
structure of `ACVF` accessible: `rv(-x) = rv(-1)·rv(x)` and `rv(-1) ∈ Kˣ`, so `-x` and `x` have the
same value. -/
theorem rv_neg_one_units (hM : M ⊨ Axioms.ACVF) :
    iUnits (iRv (iVFNeg (iVFOne (M := M)))) := by
  have h1 : iVF (iVFOne (M := M)) := vf_one_mem (M := M) hM
  have hn : iVF (iVFNeg (iVFOne (M := M))) := vf_neg_mem (M := M) hM h1
  have hr : iRV (iRv (iVFNeg (iVFOne (M := M)))) := rv_mem hM hn
  have hr0 : iRv (iVFNeg (iVFOne (M := M))) ≠ iRVZero := by
    intro h
    exact vf_neg_one_ne_zero hM (vf_eq_zero_of_rv_eq_zero hM hn h)
  have hsq : iRVMul (iRv (iVFNeg (iVFOne (M := M)))) (iRv (iVFNeg (iVFOne (M := M))))
      = iRVOne := by
    rw [← rv_mul_hom_of_model hM hn hn, vf_neg_one_mul_neg_one hM, rv_one hM]
  have hone : iRV (iRVOne (M := M)) := rv_one_mem (M := M) hM
  have hboth : iLe iRVOne (iRv (iVFNeg (iVFOne (M := M))))
      ∧ iLe (iRv (iVFNeg (iVFOne (M := M)))) iRVOne := by
    rcases le_total_rv hM hr hone with hle | hle
    · -- `e ≤ 1` scaled by `e` gives `e·e ≤ 1·e`, i.e. `1 ≤ e`
      have hiff := (le_mul_iff hM hr hone hr hr0).1 hle
      rw [hsq, rv_mul_one_any hM hr] at hiff
      exact ⟨hiff, hle⟩
    · have hiff := (le_mul_iff hM hone hr hr hr0).1 hle
      rw [hsq, rv_mul_one_any hM hr] at hiff
      exact ⟨hle, hiff⟩
  exact (units_iff_le_one hM hr hr0).2 hboth

/-- `-x` and `x` have the same value: both `iLe` directions between `rv(-x)` and `rv(x)`. -/
theorem rv_neg_class (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iLe (iRv (iVFNeg x)) (iRv x) ∧ iLe (iRv x) (iRv (iVFNeg x)) := by
  have h1 : iVF (iVFOne (M := M)) := vf_one_mem (M := M) hM
  have hn1 : iVF (iVFNeg (iVFOne (M := M))) := vf_neg_mem (M := M) hM h1
  have hnx : iVF (iVFNeg x) := vf_neg_mem (M := M) hM hx
  have he : iUnits (iRv (iVFNeg (iVFOne (M := M)))) := rv_neg_one_units hM
  have hre : iRV (iRv (iVFNeg (iVFOne (M := M)))) := rv_mem hM hn1
  have hre0 : iRv (iVFNeg (iVFOne (M := M))) ≠ iRVZero := by
    intro h
    exact vf_neg_one_ne_zero hM (vf_eq_zero_of_rv_eq_zero hM hn1 h)
  have hone : iRV (iRVOne (M := M)) := rv_one_mem (M := M) hM
  have hneg : iRv (iVFNeg x) = iRVMul (iRv (iVFNeg (iVFOne (M := M)))) (iRv x) := by
    rw [← rv_mul_hom_of_model hM hn1 hx, vf_neg_one_mul hM hx]
  have hboth := (units_iff_le_one hM hre hre0).1 he
  by_cases hx0 : x = iVFZero
  · subst hx0
    have hz : iRv (iVFNeg (iVFZero (M := M))) = iRVZero := by
      rw [vf_neg_zero hM, rv_zero_eq hM]
    have hz' : iRv (iVFZero (M := M)) = iRVZero := rv_zero_eq hM
    have hr0 : iRV (iRVZero (M := M)) := rv_zero_mem hM
    rw [hz, hz']
    exact ⟨le_refl_rv hM hr0, le_refl_rv hM hr0⟩
  · have hc : iRV (iRv x) := rv_mem hM hx
    have hc0 : iRv x ≠ iRVZero := fun h => hx0 (vf_eq_zero_of_rv_eq_zero hM hx h)
    have hleft : iLe (iRv x) (iRVMul (iRv (iVFNeg (iVFOne (M := M)))) (iRv x)) := by
      have := (le_mul_iff hM hone hre hc hc0).1 hboth.1
      rwa [rv_mul_one_any hM hc] at this
    have hright : iLe (iRVMul (iRv (iVFNeg (iVFOne (M := M)))) (iRv x)) (iRv x) := by
      have := (le_mul_iff hM hre hone hc hc0).1 hboth.2
      rwa [rv_mul_one_any hM hc] at this
    rw [hneg]
    exact ⟨hright, hleft⟩

/-- the ultrametric inequality `v(x+y) ≥ min(v x, v y)`, in the disjunctive form of the axiom. -/
theorem rv_ultrametric (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y) :
    iLe (iRv x) (iRv (iVFAdd x y)) ∨ iLe (iRv y) (iRv (iVFAdd x y)) := by
  have h := allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf])
    (φ := (pLe (tRv &0) (tRv (tVFAdd &0 &1)) ⊔ pLe (tRv &1) (tRv (tVFAdd &0 &1))))
    mem_ACVF_rvUltrametric ![x, y] (by intro i; fin_cases i <;> simp [hx, hy])
  simpa [realize_pLe, realize_tRv, realize_tVFAdd, realize_var_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, BoundedFormula.realize_sup] using h

/-- **The strict triangle**: if `v x < v y` then `v (x+y) = v x`.  This is the only additive input
of root lifting (Lemma 3.2) and of Hensel's lemma in the tagged encoding. -/
theorem rv_add_of_lt (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y)
    (hxy : iLe (iRv x) (iRv y)) (hlt : ¬ iLe (iRv y) (iRv x)) :
    iLe (iRv (iVFAdd x y)) (iRv x) ∧ iLe (iRv x) (iRv (iVFAdd x y)) := by
  have hny : iVF (iVFNeg y) := vf_neg_mem (M := M) hM hy
  have hs : iVF (iVFAdd x y) := vf_add_mem (M := M) hM hx hy
  have hx' : iRV (iRv x) := rv_mem hM hx
  have hy' : iRV (iRv y) := rv_mem hM hy
  have hs' : iRV (iRv (iVFAdd x y)) := rv_mem hM hs
  have hny' : iRV (iRv (iVFNeg y)) := rv_mem hM hny
  have hadd : iVFAdd (iVFAdd x y) (iVFNeg y) = x := vf_add_add_neg hM hx hy
  -- ultrametric at `(x+y, -y)`, using `(x+y) + (-y) = x`
  have hu := rv_ultrametric hM hs hny
  rw [hadd] at hu
  have h1 : iLe (iRv (iVFAdd x y)) (iRv x) := by
    rcases hu with hu | hu
    · exact hu
    · exact absurd (le_trans_rv hM hy' hny' hx' (rv_neg_class hM hy).2 hu) hlt
  refine ⟨h1, ?_⟩
  -- ultrametric at `(x, y)`, and `v y ≤ v (x+y)` together with `v (x+y) ≤ v x` is excluded
  rcases rv_ultrametric hM hx hy with hu | hu
  · exact hu
  · exact absurd (le_trans_rv hM hy' hs' hx' hu h1) hlt

/-- `rv` is constant on the open ball of radius `v y` around `y`: if `v(x - y) > v y` then
`rv x = rv y` (`rvEqLink` in the form used by lifting). -/
theorem rv_eq_of_close (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y)
    (hy0 : y ≠ iVFZero) (h : ¬ iLe (iRv (iVFAdd x (iVFNeg y))) (iRv y)) : iRv x = iRv y := by
  have h' := allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf])
    (φ := (∼(pEq &1 tVFZero) ⟹ (pEq (tRv &0) (tRv &1) ⇔
      ∼(pLe (tRv (tVFAdd &0 (tVFNeg &1))) (tRv &1)))))
    mem_ACVF_rvEqLink ![x, y] (by intro i; fin_cases i <;> simp [hx, hy])
  have h3 : y ≠ iVFZero → (iRv x = iRv y
      ↔ ¬ (pLe (tRv (tVFAdd &0 (tVFNeg &1))) (tRv &1)).Realize default ![x, y]) := by
    simpa [pEq, BoundedFormula.realize_bdEqual, BoundedFormula.realize_not,
      BoundedFormula.realize_iff, realize_tVFZero, realize_tRv, realize_var_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h'
  have h2 : y ≠ iVFZero → (iRv x = iRv y ↔ ¬ iLe (iRv (iVFAdd x (iVFNeg y))) (iRv y)) := by
    intro hy0
    have h4 := h3 hy0
    rw [realize_pLe] at h4
    simpa [realize_tRv, realize_tVFAdd, realize_tVFNeg, realize_var_inr, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] using h4
  exact (h2 hy0).2 h

end RVCalc

end SpecialTransformations.Milestone0
