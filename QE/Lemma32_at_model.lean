/-
**Lemma 3.2 (`rv:root:lift:vf`) at a model of the frozen `ACVF`, plus the value-level corollaries
a port consumes.**

`QE/VFField.lean` + `QE/VFAlgClosed.lean` + `QE/VFValued.lean` together say that the `VF` sort of
every model of `Axioms.ACVF` is an algebraically closed valued field in Mathlib's sense, and
`QE/RVDict.lean` identifies the encoding's `iRv`-classes with Yin's `rv`-classes under that
valuation.  So `YinRV.rv_root_lift_rv` — the paper's Lemma 3.2, proved unconditionally in
`QE/Lemma32_root_lifting.lean` — *applies*, and does not have to be re-proved.

What a full port of Lemma 3.2 still owes is the syntactic half: reading the encoding's
`RV`-polynomial hypothesis as the `huniv`/`hred` pair below.  The corollaries here are the two
translation steps that half needs:

* `rv_class_value` — a common `iRv`-class forces equal values (`w a = w b`);
* `rv_unit_value` — the class of `iRVOne` is the value-one class (`w c = 1`), which is exactly what
  `huniv` asks for, in the encoding's vocabulary.
-/
import VFAlgClosed
import RVDict
import Lemma32_root_lifting

open FirstOrder FirstOrder.Language
open Polynomial
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.M5AtModel

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- **Lemma 3.2 at a model of the frozen `ACVF`.**  This is `YinRV.rv_root_lift_rv` — a theorem about
valued fields, proved unconditionally in `QE/Lemma32_root_lifting.lean` — instantiated at
`Transfer.VFType M`, which `QF/VFField` and `QF/VFAlgClosed` make an algebraically closed field and
`QF/VFValued` a valued one. -/
theorem rv_root_lift_at_model {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (Transfer.VFType (M := M)) Γ)
    {F : (Transfer.VFType (M := M))[X]} (hF : F ≠ 0) {b : Transfer.VFType (M := M)}
    {t : YinRV.RV w} (ht : t ≠ YinRV.rvZero w) (hb : YinRV.rv w b = t)
    (huniv : ∀ i ∈ F.support, w (F.coeff i * b ^ i) = 1)
    (hred : w (∑ i ∈ F.support, F.coeff i * b ^ i) < 1) :
    ∃ b' : Transfer.VFType (M := M), YinRV.rv w b' = t ∧ F.IsRoot b' := by
  letI : IsAlgClosed (Transfer.VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType (M := M) (hM := hM)
  exact YinRV.rv_root_lift_rv w hF ht hb huniv hred

/-- **A common `iRv`-class forces equal values.**  This is the first conjunct of Yin's
`rv_eq_iff`, transported to the encoding by the class dictionary. -/
theorem rv_class_value {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation (Transfer.VFType (M := M)) Γ}
    (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {a b : Transfer.VFType (M := M)} (hb : b ≠ 0)
    (h : iRv a.1 = iRv b.1) : w a = w b := by
  have h' : YinRV.rv w a = YinRV.rv w b := (RVDict.rv_class_iff hw a b hb).mp h
  exact (YinRV.rv_eq_iff (v := w) hb).mp h' |>.1

/-- **The class of `iRVOne` is the value-one class.**  `iRVOne` is `rv 1`, so an element whose
`iRv`-class is that class has value `1` — which is exactly the `huniv` hypothesis of Lemma 3.2, read
in the encoding's vocabulary. -/
theorem rv_unit_value {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation (Transfer.VFType (M := M)) Γ}
    (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {c : Transfer.VFType (M := M)} (h : iRv c.1 = iRVOne) : w c = 1 := by
  have h1 : ((1 : Transfer.VFType (M := M))).1 = Transfer.iVFOne := rfl
  have hone : iRv ((1 : Transfer.VFType (M := M))).1 = iRVOne := by
    rw [h1]; exact RVCalc.rv_one hM
  have hne : (1 : Transfer.VFType (M := M)) ≠ 0 := by
    intro h
    have h' : (1 : Transfer.VFType (M := M)).1 = (0 : Transfer.VFType (M := M)).1 := by rw [h]
    have h1 : (1 : Transfer.VFType (M := M)).1 = Transfer.iVFOne := rfl
    have h0 : (0 : Transfer.VFType (M := M)).1 = Transfer.iVFZero := rfl
    rw [h1, h0] at h'
    exact RVCalc.vf_zero_ne_one hM h'.symm
  have hv := rv_class_value (M := M) hw hne (a := c) (b := 1) (by rw [hone]; exact h)
  have hw1 : w (1 : Transfer.VFType (M := M)) = 1 := Valuation.map_one w
  rw [hw1] at hv
  exact hv

end SpecialTransformations.Milestone0.M5AtModel
