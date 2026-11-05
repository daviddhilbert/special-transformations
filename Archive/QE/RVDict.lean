/-
**The dictionary between the encoding's `iRv` and Yin's `rv` on the valuation.**

`QE/VFValued.lean` puts a genuine Mathlib valuation `w` on `Transfer.VFType M` for every
`M ⊨ Axioms.ACVF`; this file shows the encoding's residue projection `iRv` and Yin's
`YinRV.rv w` classify a `VF`-element the same way.  That is the missing link which lets
`QE/Lemma32_root_lifting.lean`'s theorems (`rv:root:lift:vf` = Lemma 3.2) be *instantiated* at a
model of the frozen theory instead of re-proved, and the same dictionary serves
`lift:divisible:hull` (3.5) and `e:transc` (3.7).

The two sides say the same thing in different vocabulary:

* the encoding's `Axioms.rvEqLink` reads `rv x = rv y ↔ ¬ (v(x - y) ≤ v y)` for `y ≠ 0`;
* Yin's `YinRV.rv_eq_iff` reads `rv x = rv y ↔ v x = v y ∧ v (x/y - 1) < 1` for `y ≠ 0`.

Both are equivalent to `v(x - y) < v y`, which is the content of `rv_class_iff`.
-/
import VFValued
import Lemma32_root_lifting

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.RVDict

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The field identity used on the Yin side: `a / b - 1 = (a - b) / b` for `b ≠ 0`. -/
theorem divsub_one_eq {K : Type*} [Field K] {a b : K} (hb : b ≠ 0) : a / b - 1 = (a - b) / b := by
  rw [← div_self hb, div_sub_div_same]

/-- **`Axioms.rvEqLink` as an iff**: two `VF`-elements have the same `rv` class exactly when their
difference is strictly closer than the second, `¬ (v(x - y) ≤ v y)`. -/
theorem rv_eq_iff_le {x y : M} (hx : iVF x) (hy : iVF y) (hy0 : y ≠ Transfer.iVFZero) :
    (iRv x = iRv y ↔ ¬ iLe (iRv (iVFAdd x (iVFNeg y))) (iRv y)) := by
  have h' := Transfer.allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf])
    (φ := (∼(pEq &1 tVFZero) ⟹ (pEq (tRv &0) (tRv &1) ⇔
      ∼(pLe (tRv (tVFAdd &0 (tVFNeg &1))) (tRv &1)))))
    RVCalc.mem_ACVF_rvEqLink ![x, y] (by intro i; fin_cases i <;> simp [hx, hy])
  have h3 : y ≠ Transfer.iVFZero → (iRv x = iRv y
      ↔ ¬ (pLe (tRv (tVFAdd &0 (tVFNeg &1))) (tRv &1)).Realize default ![x, y]) := by
    simpa [pEq, BoundedFormula.realize_bdEqual, BoundedFormula.realize_not,
      BoundedFormula.realize_iff, Transfer.realize_tVFZero, Transfer.realize_tRv,
      RVCalc.realize_var_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] using h'
  have h2 : y ≠ Transfer.iVFZero → (iRv x = iRv y
      ↔ ¬ iLe (iRv (iVFAdd x (iVFNeg y))) (iRv y)) := by
    intro hy0
    have h4 := h3 hy0
    rw [Transfer.realize_pLe] at h4
    simpa [Transfer.realize_tRv, Transfer.realize_tVFAdd, Transfer.realize_tVFNeg,
      RVCalc.realize_var_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] using h4
  exact h2 hy0

/-- **The class dictionary.**  For a nonzero `b`, the encoding's `rv`-class of `a` and `b` agrees
with Yin's `rv`-class under the valuation `w` of `QE/VFValued.lean`. -/
theorem rv_class_iff {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation (Transfer.VFType (M := M)) Γ}
    (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    (a b : Transfer.VFType (M := M)) (hb : b ≠ 0) :
    iRv a.1 = iRv b.1 ↔ YinRV.rv w a = YinRV.rv w b := by
  have hb0 : b.1 ≠ Transfer.iVFZero := fun h => hb (Subtype.ext h)
  have hbw : w b ≠ 0 := (Valuation.ne_zero_iff w).mpr hb
  -- the encoding side, in valuation vocabulary
  have hL : iRv a.1 = iRv b.1 ↔ w (a - b) < w b := by
    rw [rv_eq_iff_le a.2 b.2 hb0]
    have hmem : iVF (iVFAdd a.1 (iVFNeg b.1)) :=
      Transfer.vf_add_mem hM a.2 (Transfer.vf_neg_mem hM b.2)
    have hsub : ((a - b : Transfer.VFType (M := M))).1 = iVFAdd a.1 (iVFNeg b.1) := rfl
    have h1 : (¬ iLe (iRv (iVFAdd a.1 (iVFNeg b.1))) (iRv b.1))
        ↔ ¬ VFValued.predV b ⟨iVFAdd a.1 (iVFNeg b.1), hmem⟩ := by
      simp only [VFValued.predV]
    rw [h1, hw b ⟨iVFAdd a.1 (iVFNeg b.1), hmem⟩, not_le]
    have heq : (⟨iVFAdd a.1 (iVFNeg b.1), hmem⟩ : Transfer.VFType (M := M)) = a - b :=
      Subtype.ext hsub.symm
    rw [heq]
  -- the Yin side, reduced to the same inequality
  have hdiv : w (a / b - 1) = w (a - b) / w b := by
    rw [← Valuation.map_div w (a - b) b]
    congr 1
    exact divsub_one_eq (K := Transfer.VFType (M := M)) (a := a) (b := b) hb
  have hpos : 0 < w b := pos_iff_ne_zero.mpr hbw
  have hR : YinRV.rv w a = YinRV.rv w b ↔ w (a - b) < w b := by
    rw [YinRV.rv_eq_iff (v := w) hb]
    constructor
    · rintro ⟨-, hlt⟩
      have h2 : w (a - b) / w b < 1 := hdiv ▸ hlt
      exact (div_lt_one₀ hpos).mp h2
    · intro hlt
      refine ⟨?_, ?_⟩
      · have h := Valuation.map_add_eq_of_lt_right (v := w) (x := a - b) (y := b) hlt
        have e : (a - b) + b = a := sub_add_cancel a b
        simpa [e] using h
      · have h2 : w (a - b) / w b < 1 := (div_lt_one₀ hpos).mpr hlt
        exact (hdiv.symm ▸ h2)
  exact hL.trans hR.symm

end SpecialTransformations.Milestone0.RVDict
