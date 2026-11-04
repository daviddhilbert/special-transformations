/-
# The valuation ring, its maximal ideal and the additive `rv` calculus (frozen encoding)

Direction d7 of swarm `smw2ioy2w` (member m3): **the additive side of the `rv` calculus**.

## What is here, and why it is not in the tree

Every statement below is proved from `Axioms.ACVF` alone — no valuation `w`, no `hw :
∀ x y, predV x y ↔ w x ≤ w y` hypothesis, no new axiom, no `sorry`.

The tree already proves the valuation-ring laws `1 ≤ rv x → 1 ≤ rv y → 1 ≤ rv (x + y)`,
`O`-closedness under `*`, under `^`, and under finite sums — but **only** in the form
`M6Syntactic.one_le_add hw`, `one_le_mul hw`, `M6Wire.one_le_pow hw`, `one_le_list_sum hw`, i.e.
every one of them carries an arbitrary valuation `w` and the translation hypothesis `hw` as an
argument.  At the `RV` level the same laws are *two lines* each (`rvUltrametric` plus transitivity
of `iLe`; `leMulCompatFull` plus `rvMulHom`), so the `hw` argument is unnecessary.
`isInt_add`/`isInt_mul`/`isMax_add`/`isMax_mul` below are the hypothesis-free forms; anything
downstream that has no valuation in hand can use them directly.

New content (not in the tree in any form):

* `rv_inv` — `rv` of the field inverse is the `RV`-group inverse `iRVInv`;
* `isInt_or_inv` — the valuation-ring dichotomy `x ∈ O ∨ x⁻¹ ∈ O`;
* `isMax_not_iUnits` / `iUnits_iff_isInt_and_not_isMax` — `m` is exactly the non-units of `O`;
* `rv_add_eq_of_lt` — the strict triangle at the level of **equality** of `rv`
  (`rv (x + y) = rv x`, not merely the mutual `iLe` of `RVCalc.rv_add_of_lt`), through the
  encoding's equality device `rvEqLink` (`RVCalc.rv_eq_of_close`);
* `rv_add_eq_of_isMax` — residue invariance: a unit plus an element of `m` keeps its `rv`;
* `inBall_zero_iff`/`inBall_zero_add`/`inBall_zero_neg`/`inBall_add`/`inBall_sub`/`inBall_congr`
  — the closed balls of `BallSec3.Ball` are cosets of additive subgroups
  (`x ≡ x' [t] → y ≡ y' [t] → (x + y) ≡ (x' + y') [t]`), and `inBall_zero_iff_isInt` — the unit
  ball is `O`.

## Results

| # | name | statement |
| --- | --- | --- |
| 1 | `iRV_of_iUnits` | `iUnits x → iRV x` (`Axioms.sdUnits` read off; the tree has the same fact as `Jm2T1.iRV_of_units`, restated here so the file imports only `RVCalc`) |
| 2 | `not_iUnits_of_iVF` | `iVF x → ¬ iUnits x` (sorts disjoint) |
| 3 | `isInt_add` / `isInt_neg` / `isInt_mul` / `isInt_sub` | `O` is a subring: `1 ≤ rv x → 1 ≤ rv y → 1 ≤ rv (x + y)`, etc., **no `hw`** |
| 4 | `isMax_add` / `isMax_neg` / `isMax_mul` / `isMax_mul_right` / `isMax_sub` | `m` is an ideal (`m`+`m`, `-m`, `O·m`, `m·O`) |
| 5 | `isMax_not_iUnits`, `iUnits_iff_isInt_and_not_isMax` | `m` = the non-units of `O`, i.e. `Kˣ = O ∖ m` |
| 6 | `rv_inv` | `rv (x⁻¹) = (rv x)⁻¹` for `x ≠ 0`, i.e. `iRVInv` |
| 7 | `isInt_or_inv` | `x ∈ O ∨ x⁻¹ ∈ O` for `x ≠ 0` (valuation-ring dichotomy) |
| 8 | `rv_add_eq_of_lt'` / `rv_add_eq_of_lt` | strict triangle as **equality**: `¬ rv y ≤ rv x → rv (x + y) = rv x` |
| 9 | `rv_add_eq_of_isMax` | residue invariance: `Kˣ ∋ x`, `y ∈ m`, `x ≠ 0 → rv (x + y) = rv x` |
| 10 | `not_isMax_add_of_unit` | `1 + m ⊆ Kˣ` (`O`-unit plus `m` is an `O`-unit, in the `IsMax` form) |
| 11 | `inBall_zero_iff`, `inBall_zero_add`, `inBall_zero_neg` | the `0`-ball of radius `t` is an additive subgroup |
| 12 | `inBall_add`, `inBall_sub`, `inBall_congr` | balls are cosets: `x ≡ x' → y ≡ y' (mod t) → x + y ≡ x' + y' (mod t)` |
| 13 | `inBall_zero_iff_isInt` | the unit ball is `O` |
| 14 | `isInt_of_isInt_sub_isMax` | `x ∈ O`, `x - x' ∈ m → x' ∈ O` |

Side conditions are all of the shape `x ≠ 0` (needed: at `x = 0` statement 9 would say
`rv y = rv 0 = ∞`, false for `rv y ≠ ∞`); no global hypothesis, no quote, nothing assumed.

## Stress test of the direction's proposed item (i)

The registered direction proposed `iUnits x → iUnits y → predV x y → iUnits (iKAdd x y)`.  Read at
`VF`-elements that statement is *unsatisfiable*, hence vacuous: the encoding's `Kˣ` is a subset of
the `RV` sort (`Axioms.sdUnits`) and the two sorts are disjoint (`Axioms.sdDisjoint`), so
`iVF x → ¬ iUnits x` — machine-checked as `not_iUnits_of_iVF`.  It is also false on its intended
reading (`x`, `y` of value `0`, i.e. `iUnits (rv x)`, `iUnits (rv y)`: `1` and `t - 1` in a
nontrivially valued field both have value `0`, but `t` does not).  The correct additive statements
are `isInt_add` (the valuation ring is closed under `+`: *value ≥ 0*, not *value = 0*, is what is
preserved) and `isMax_add` (`m` is closed under `+`); both are proved below, and `1 + m ⊆ Kˣ` is
`not_isMax_add_of_unit`.

There are no hypotheses in this file, so there is no vacuity or cardinality obstruction to test.
-/
/- Merged unchanged from swarm smw2ioy2w m3 (direction d-ADD, accepted), repro: -/
import RVCalc
import VFField
import SortCover

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace SpecialTransformations.Milestone0.RVAdd

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The `Field` structure on the `VF` sort as an instance (same construction as
`VFValued.instFieldVFType`). -/
noncomputable instance instFieldVFType : Field (Transfer.VFType (M := M)) :=
  Transfer.vfFieldOfModel (M := M) (hM := hM)

/-! ## 0. `Kˣ ⊆ RV`, and the sort failure of `Kˣ` at a `VF`-element -/

/-- `Axioms.sdUnits` is a sentence of `ACVF`. -/
theorem mem_ACVF_sdUnits : Axioms.sdUnits ∈ Axioms.ACVF :=
  Transfer.mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

/-- `Kˣ` lies inside the `RV` sort (`Axioms.sdUnits`), semantically. -/
theorem iRV_of_iUnits {x : M} (h : iUnits x) : iRV x := by
  have hs : M ⊨ Axioms.sdUnits :=
    Transfer.sentence_realize (T := Axioms.ACVF) hM mem_ACVF_sdUnits
  rw [Axioms.sdUnits, allOne] at hs
  have h1 := BoundedFormula.realize_alls.mp hs ![x]
  rw [BoundedFormula.realize_imp, Transfer.pUnits_realize, Transfer.pRVsort_realize] at h1
  refine h1 ?_
  simpa [Transfer.realize_tv] using h

/-- **`Kˣ` is ill-sorted at a `VF`-element**: the sorts are disjoint (`Axioms.sdDisjoint`), so no
`VF`-element is in `Kˣ`.  Machine-checked stress test of the direction's item (i): its hypotheses
cannot be satisfied. -/
theorem not_iUnits_of_iVF {x : M} (h : iVF x) : ¬ iUnits x := by
  intro hu
  exact SortCover.not_both (M := M) (hM := hM) x ⟨h, iRV_of_iUnits hu⟩

/-- The encoding's `0` (`∞`) is the top of the `RV` order, so it is never `≤ 1`.  (This is
`M6Syntactic.not_le_zero_one`, reproved here so that the file depends only on `RVCalc`.) -/
theorem not_le_zero_one : ¬ iLe (iRVZero (M := M)) iRVOne := by
  intro h
  exact RVCalc.rv_one_ne_zero hM (RVCalc.le_infty_eq hM (Transfer.rv_one_mem (M := M) hM) h)

/-! ## 1. The valuation ring `O` and the maximal ideal `m`

`O = {x | v x ≥ 0}` and `m = {x | v x > 0}` in the paper's (divisibility) order: `O` is
`1 ≤ rv x` and `m` is `¬ (rv x ≤ 1)`.  Note `0 ∈ m`, as it must be since `v 0 = ∞ > 0`. -/

/-- `x ∈ O`, i.e. `v x ≥ 0`, at the `RV` level: `1 ≤ rv x`. -/
def IsInt (x : Transfer.VFType (M := M)) : Prop := iLe iRVOne (iRv x.1)

/-- `x ∈ m`, i.e. `v x > 0`, at the `RV` level: `rv x ≰ 1`. -/
def IsMax (x : Transfer.VFType (M := M)) : Prop := ¬ iLe (iRv x.1) iRVOne

theorem isInt_zero : IsInt (0 : Transfer.VFType (M := M)) := by
  show iLe iRVOne (iRv (Transfer.iVFZero : M))
  rw [RVCalc.rv_zero_eq hM]
  exact RVCalc.le_top_rv hM (Transfer.rv_one_mem (M := M) hM)

theorem isInt_one : IsInt (1 : Transfer.VFType (M := M)) := by
  show iLe iRVOne (iRv (Transfer.iVFOne : M))
  rw [RVCalc.rv_one hM]
  exact RVCalc.le_refl_rv hM (Transfer.rv_one_mem (M := M) hM)

theorem isMax_zero : IsMax (0 : Transfer.VFType (M := M)) := by
  show ¬ iLe (iRv (Transfer.iVFZero : M)) iRVOne
  rw [RVCalc.rv_zero_eq hM]
  exact not_le_zero_one (M := M) (hM := hM)

/-- **`O` is closed under addition** (`1 ≤ rv x → 1 ≤ rv y → 1 ≤ rv (x + y)`), from the
ultrametric axiom alone.  Hypothesis-free form of `M6Syntactic.one_le_add`. -/
theorem isInt_add {x y : Transfer.VFType (M := M)} (hx : IsInt x) (hy : IsInt y) :
    IsInt (x + y) := by
  have hxr : iRV (iRv x.1) := Transfer.rv_mem hM x.2
  have hyr : iRV (iRv y.1) := Transfer.rv_mem hM y.2
  have hsr : iRV (iRv (x + y).1) := Transfer.rv_mem hM (x + y).2
  have hone : iRV (iRVOne (M := M)) := Transfer.rv_one_mem (M := M) hM
  rcases RVCalc.rv_ultrametric hM x.2 y.2 with hu | hu
  · exact RVCalc.le_trans_rv hM hone hxr hsr hx hu
  · exact RVCalc.le_trans_rv hM hone hyr hsr hy hu

/-- `O` is closed under negation (`rv (-x)` has the same class as `rv x`). -/
theorem isInt_neg {x : Transfer.VFType (M := M)} (hx : IsInt x) : IsInt (-x) := by
  have hxr : iRV (iRv x.1) := Transfer.rv_mem hM x.2
  have hnr : iRV (iRv (-x).1) := Transfer.rv_mem hM (-x).2
  exact RVCalc.le_trans_rv hM (Transfer.rv_one_mem (M := M) hM) hxr hnr hx
    (RVCalc.rv_neg_class hM x.2).2

/-- `O` is closed under multiplication.  Hypothesis-free form of `M6Syntactic.one_le_mul`. -/
theorem isInt_mul {x y : Transfer.VFType (M := M)} (hx : IsInt x) (hy : IsInt y) :
    IsInt (x * y) := by
  have hxr : iRV (iRv x.1) := Transfer.rv_mem hM x.2
  have hyr : iRV (iRv y.1) := Transfer.rv_mem hM y.2
  have hone : iRV (iRVOne (M := M)) := Transfer.rv_one_mem (M := M) hM
  by_cases hy0 : y = 0
  · subst hy0
    show iLe iRVOne (iRv (iVFMul x.1 iVFZero))
    rw [Transfer.rv_mul_hom_of_model hM x.2 (Transfer.vf_zero_mem (M := M) hM),
      RVCalc.rv_zero_eq hM, Transfer.rv_mul_zero_right_of_model hM hxr]
    exact RVCalc.le_top_rv hM hone
  · have hyr0 : iRv y.1 ≠ iRVZero := fun hz =>
      hy0 (Subtype.ext (RVCalc.vf_eq_zero_of_rv_eq_zero hM y.2 hz))
    have hscaled : iLe (iRVMul (iRVOne) (iRv y.1)) (iRVMul (iRv x.1) (iRv y.1)) :=
      (RVCalc.le_mul_iff hM hone hxr hyr hyr0).1 hx
    rw [Transfer.rv_mul_one_any hM hyr] at hscaled
    show iLe iRVOne (iRv (iVFMul x.1 y.1))
    rw [Transfer.rv_mul_hom_of_model hM x.2 y.2]
    exact RVCalc.le_trans_rv hM hone hyr (Transfer.rv_mul_mem hM hxr hyr) hy hscaled

/-- Every element of `m` is integral (`0` included, since `v 0 = ∞`). -/
theorem isInt_of_isMax {x : Transfer.VFType (M := M)} (hx : IsMax x) : IsInt x := by
  have hxr : iRV (iRv x.1) := Transfer.rv_mem hM x.2
  rcases RVCalc.le_total_rv hM hxr (Transfer.rv_one_mem (M := M) hM) with h | h
  · exact absurd h hx
  · exact h

/-- **`m` is closed under addition.** -/
theorem isMax_add {x y : Transfer.VFType (M := M)} (hx : IsMax x) (hy : IsMax y) :
    IsMax (x + y) := by
  intro hle
  have hxr : iRV (iRv x.1) := Transfer.rv_mem hM x.2
  have hyr : iRV (iRv y.1) := Transfer.rv_mem hM y.2
  have hsr : iRV (iRv (x + y).1) := Transfer.rv_mem hM (x + y).2
  have hone : iRV (iRVOne (M := M)) := Transfer.rv_one_mem (M := M) hM
  rcases RVCalc.rv_ultrametric hM x.2 y.2 with hu | hu
  · exact hx (RVCalc.le_trans_rv hM hxr hsr hone hu hle)
  · exact hy (RVCalc.le_trans_rv hM hyr hsr hone hu hle)

/-- `m` is closed under negation. -/
theorem isMax_neg {x : Transfer.VFType (M := M)} (hx : IsMax x) : IsMax (-x) := by
  intro hle
  have hxr : iRV (iRv x.1) := Transfer.rv_mem hM x.2
  have hnr : iRV (iRv (-x).1) := Transfer.rv_mem hM (-x).2
  exact hx (RVCalc.le_trans_rv hM hxr hnr (Transfer.rv_one_mem (M := M) hM)
    (RVCalc.rv_neg_class hM x.2).2 hle)

/-- **`O · m ⊆ m`.** -/
theorem isMax_mul {a x : Transfer.VFType (M := M)} (ha : IsInt a) (hx : IsMax x) :
    IsMax (a * x) := by
  have har : iRV (iRv a.1) := Transfer.rv_mem hM a.2
  have hxr : iRV (iRv x.1) := Transfer.rv_mem hM x.2
  have hone : iRV (iRVOne (M := M)) := Transfer.rv_one_mem (M := M) hM
  by_cases ha0 : a = 0
  · subst ha0
    show ¬ iLe (iRv (iVFMul iVFZero x.1)) iRVOne
    rw [Transfer.rv_mul_hom_of_model hM (Transfer.vf_zero_mem (M := M) hM) x.2,
      RVCalc.rv_zero_eq hM, Transfer.rv_mul_zero_left_of_model hM hxr]
    exact not_le_zero_one (M := M) (hM := hM)
  · have har0 : iRv a.1 ≠ iRVZero := fun hz =>
      ha0 (Subtype.ext (RVCalc.vf_eq_zero_of_rv_eq_zero hM a.2 hz))
    intro hle
    have hle' : iLe (iRv (iVFMul a.1 x.1)) iRVOne := hle
    rw [Transfer.rv_mul_hom_of_model hM a.2 x.2] at hle'
    have hstep : iLe (iRVMul (iRv a.1) (iRv x.1)) (iRv a.1) :=
      RVCalc.le_trans_rv hM (Transfer.rv_mul_mem hM har hxr) hone har hle' ha
    have hle2 : iLe (iRVMul (iRv x.1) (iRv a.1)) (iRVMul (iRVOne) (iRv a.1)) := by
      rw [Transfer.rv_mul_one_any hM har, Transfer.rv_mul_comm_of_model hM hxr har]
      exact hstep
    exact hx ((RVCalc.le_mul_iff hM hxr hone har har0).2 hle2)

/-- An element of `m` is not a unit of `O`. -/
theorem isMax_not_iUnits {x : Transfer.VFType (M := M)} (hx : IsMax x) (hx0 : x ≠ 0) :
    ¬ iUnits (iRv x.1) := by
  intro hu
  have hne : iRv x.1 ≠ iRVZero := fun h =>
    hx0 (Subtype.ext (RVCalc.vf_eq_zero_of_rv_eq_zero hM x.2 h))
  exact hx ((RVCalc.units_iff_le_one hM (Transfer.rv_mem hM x.2) hne).1 hu).2

/-- The units of `O` are exactly `O ∖ m`, i.e. `Kˣ` at the `RV` level. -/
theorem iUnits_iff_isInt_and_not_isMax {x : Transfer.VFType (M := M)} (hx0 : x ≠ 0) :
    iUnits (iRv x.1) ↔ IsInt x ∧ ¬ IsMax x := by
  have hne : iRv x.1 ≠ iRVZero := fun h =>
    hx0 (Subtype.ext (RVCalc.vf_eq_zero_of_rv_eq_zero hM x.2 h))
  constructor
  · intro hu
    refine ⟨((RVCalc.units_iff_le_one hM (Transfer.rv_mem hM x.2) hne).1 hu).1, ?_⟩
    intro hm
    exact isMax_not_iUnits hm hx0 hu
  · rintro ⟨hi, hm⟩
    refine (RVCalc.units_iff_le_one hM (Transfer.rv_mem hM x.2) hne).2 ⟨hi, ?_⟩
    by_contra hc
    exact hm hc

/-! ## 2. The field inverse and the valuation-ring dichotomy -/

/-- **`rv` of the field inverse is the `RV`-group inverse.** -/
theorem rv_inv {x : Transfer.VFType (M := M)} (hx0 : x ≠ 0) :
    iRv ((x⁻¹ : Transfer.VFType (M := M))).1 = iRVInv hM (iRv x.1) := by
  have hxr : iRV (iRv x.1) := Transfer.rv_mem hM x.2
  have hxr0 : iRv x.1 ≠ iRVZero := fun h =>
    hx0 (Subtype.ext (RVCalc.vf_eq_zero_of_rv_eq_zero hM x.2 h))
  have hir : iRV (iRv ((x⁻¹ : Transfer.VFType (M := M))).1) :=
    Transfer.rv_mem hM (x⁻¹).2
  have hmul : iVFMul x.1 ((x⁻¹ : Transfer.VFType (M := M))).1
      = ((1 : Transfer.VFType (M := M))).1 := by
    have h := congrArg (Subtype.val)
      (mul_inv_cancel₀ hx0 : x * (x⁻¹ : Transfer.VFType (M := M)) = 1)
    exact h
  have h1 : iRVMul (iRv x.1) (iRv ((x⁻¹ : Transfer.VFType (M := M))).1) = iRVOne := by
    rw [← Transfer.rv_mul_hom_of_model hM x.2 (x⁻¹).2]
    show iRv (iVFMul x.1 ((x⁻¹ : Transfer.VFType (M := M))).1) = iRVOne
    rw [hmul]
    exact RVCalc.rv_one hM
  have h2 : iRVMul (iRv x.1) (iRVInv hM (iRv x.1)) = iRVOne :=
    Transfer.rv_mul_inv_cancel_right hM hxr hxr0
  exact Transfer.rv_mul_right_cancel_of_model hM hxr hxr0 hir
    (Transfer.iRVInv_mem hM hxr) (h1.trans h2.symm)

/-- **The valuation-ring dichotomy**: a nonzero element or its inverse is integral. -/
theorem isInt_or_inv {x : Transfer.VFType (M := M)} (hx0 : x ≠ 0) :
    IsInt x ∨ IsInt (x⁻¹) := by
  by_cases h : iLe iRVOne (iRv x.1)
  · exact Or.inl h
  · refine Or.inr ?_
    have hxr : iRV (iRv x.1) := Transfer.rv_mem hM x.2
    have hone : iRV (iRVOne (M := M)) := Transfer.rv_one_mem (M := M) hM
    have hinvr : iRV (iRVInv hM (iRv x.1)) := Transfer.iRVInv_mem hM hxr
    have hxr0 : iRv x.1 ≠ iRVZero := fun hz =>
      hx0 (Subtype.ext (RVCalc.vf_eq_zero_of_rv_eq_zero hM x.2 hz))
    have hinv0 : iRVInv hM (iRv x.1) ≠ iRVZero := by
      intro hz
      have hc := Transfer.iRVInv_mul_cancel hM hxr hxr0
      rw [hz, Transfer.rv_mul_zero_left_of_model hM hxr] at hc
      exact RVCalc.rv_one_ne_zero hM hc.symm
    have hle : iLe (iRv x.1) iRVOne := by
      rcases RVCalc.le_total_rv hM hxr hone with h' | h'
      · exact h'
      · exact absurd h' h
    have hkey := (RVCalc.le_mul_iff hM hxr hone hinvr hinv0).1 hle
    rw [Transfer.rv_mul_inv_cancel_right hM hxr hxr0,
      Transfer.rv_mul_one_any hM hinvr] at hkey
    show iLe iRVOne (iRv ((x⁻¹ : Transfer.VFType (M := M))).1)
    rw [rv_inv (M := M) hx0]
    exact hkey

/-! ## 3. The strict triangle at the level of equality of `rv`, and residue invariance -/

/-- **The larger term wins, as an equality of `rv`**: if `v x < v y` (strictly, i.e. `rv x ≤ rv y`
but not conversely) then `rv (x + y) = rv x`.  `RVCalc.rv_add_of_lt` gives only the mutual `iLe`
of the two values; the encoding has no quotient, so equality needs the device `rvEqLink`, which is
`RVCalc.rv_eq_of_close` applied to the error term `(x + y) - x = y`. -/
theorem rv_add_eq_of_lt' {x y : Transfer.VFType (M := M)}
    (hlt : ¬ iLe (iRv y.1) (iRv x.1)) :
    iRv ((x + y).1) = iRv x.1 := by
  have hx0 : x.1 ≠ Transfer.iVFZero := by
    intro h
    apply hlt
    have hz : iRv x.1 = iRVZero := by rw [h]; exact RVCalc.rv_zero_eq hM
    rw [hz]
    exact RVCalc.le_top_rv hM (Transfer.rv_mem hM y.2)
  have hcancel : (x + y) + (-x) = y := by abel
  have hclose : ¬ iLe (iRv (((x + y) + (-x)).1)) (iRv x.1) := by
    rw [hcancel]
    exact hlt
  exact RVCalc.rv_eq_of_close hM (x + y).2 x.2 hx0 hclose

/-- **The larger term wins**: `v x ≤ v y` and `v x ≠ v y` give `rv (x + y) = rv x`.  The second
hypothesis (`¬ rv y ≤ rv x`) alone suffices, see `rv_add_eq_of_lt'`; it is kept here because it is
the paper's form `v x < v y`. -/
theorem rv_add_eq_of_lt {x y : Transfer.VFType (M := M)}
    (_hxy : iLe (iRv x.1) (iRv y.1)) (hlt : ¬ iLe (iRv y.1) (iRv x.1)) :
    iRv ((x + y).1) = iRv x.1 :=
  rv_add_eq_of_lt' hlt

/-- The element `-1` of the `VF` sort, written out explicitly so that the identity of the `Neg`
instance used by the literal `-1` does not matter. -/
def negOne : Transfer.VFType (M := M) :=
  ⟨iVFNeg (Transfer.iVFOne), Transfer.vf_neg_mem hM (Transfer.vf_one_mem (M := M) hM)⟩

theorem negOne_val : (negOne (M := M)).1 = iVFNeg (Transfer.iVFOne) := rfl

/-- **Sharpness of the strict triangle**: the non-strict form is *false*.  `x = 1` and `y = -1`
have the same value, yet `rv (1 + (-1)) = rv 0 = ∞ ≠ rv 1`.  Hence the hypothesis
`¬ iLe (rv y) (rv x)` in `rv_add_eq_of_lt'` cannot be dropped, and the statement is not vacuous. -/
theorem rv_add_eq_of_le_false :
    ¬ ∀ (x y : Transfer.VFType (M := M)),
        iLe (iRv x.1) (iRv y.1) → iRv ((x + y).1) = iRv x.1 := by
  intro h
  have hle : iLe (iRv ((1 : Transfer.VFType (M := M))).1)
      (iRv (negOne (M := M)).1) :=
    (RVCalc.rv_neg_class hM (Transfer.vf_one_mem (M := M) hM)).2
  have h1 := h 1 (negOne (M := M)) hle
  have hsum : ((1 : Transfer.VFType (M := M)) + negOne (M := M) (hM := hM)).1
      = Transfer.iVFZero :=
    RVCalc.vf_add_neg hM (Transfer.vf_one_mem (M := M) hM)
  have hone : iRv ((1 : Transfer.VFType (M := M))).1 = iRVOne := RVCalc.rv_one hM
  rw [hsum, RVCalc.rv_zero_eq hM, hone] at h1
  exact RVCalc.rv_one_ne_zero hM h1.symm

/-- `1 ≤ rv x` plus `¬ (rv x ≤ 1)` is `Kˣ` (`iUnits`). -/
theorem iUnits_of_isInt_and_not_isMax {x : Transfer.VFType (M := M)}
    (hi : IsInt x) (hm : ¬ IsMax x) : iUnits (iRv x.1) := by
  have hne : iRv x.1 ≠ iRVZero := by
    intro h
    apply hm
    show ¬ iLe (iRv x.1) iRVOne
    rw [h]
    exact not_le_zero_one (M := M) (hM := hM)
  refine (RVCalc.units_iff_le_one hM (Transfer.rv_mem hM x.2) hne).2 ⟨hi, ?_⟩
  by_contra hc
  exact hm hc

/-- **Residue invariance**: adding an element of `m` to a unit of `O` does not change its `rv`. -/
theorem rv_add_eq_of_isMax {x y : Transfer.VFType (M := M)} (hx0 : x ≠ 0)
    (hxU : iUnits (iRv x.1)) (hy : IsMax y) : iRv ((x + y).1) = iRv x.1 := by
  have hxr : iRV (iRv x.1) := Transfer.rv_mem hM x.2
  have hyr : iRV (iRv y.1) := Transfer.rv_mem hM y.2
  have hone : iRV (iRVOne (M := M)) := Transfer.rv_one_mem (M := M) hM
  have hxne : iRv x.1 ≠ iRVZero := fun h =>
    hx0 (Subtype.ext (RVCalc.vf_eq_zero_of_rv_eq_zero hM x.2 h))
  have hxu : iLe iRVOne (iRv x.1) ∧ iLe (iRv x.1) iRVOne :=
    (RVCalc.units_iff_le_one hM hxr hxne).1 hxU
  have hxy : iLe (iRv x.1) (iRv y.1) :=
    RVCalc.le_trans_rv hM hxr hone hyr hxu.2 (isInt_of_isMax hy)
  have hyx : ¬ iLe (iRv y.1) (iRv x.1) := fun h =>
    hy (RVCalc.le_trans_rv hM hyr hxr hone h hxu.2)
  exact rv_add_eq_of_lt hxy hyx

/-- **`1 + m ⊆ Kˣ`**: a unit of `O` plus an element of `m` is a unit of `O`. -/
theorem not_isMax_add_of_unit {x y : Transfer.VFType (M := M)}
    (hi : IsInt x) (hm : ¬ IsMax x) (hy : IsMax y) : ¬ IsMax (x + y) := by
  intro hle
  have hxU : iUnits (iRv x.1) := iUnits_of_isInt_and_not_isMax hi hm
  have hx0 : x ≠ 0 := by
    intro h
    subst h
    exact hm (isMax_zero (M := M) (hM := hM))
  have hle' : ¬ iLe (iRv ((x + y).1)) iRVOne := hle
  rw [rv_add_eq_of_isMax hx0 hxU hy] at hle'
  exact hm hle'

/-! ## 4. Closed balls as cosets of additive subgroups -/

/-- `x` lies in the closed ball around `a` of radius `t` (the `BallSec3.Ball` set, as a predicate on
the `VF` sort). -/
def InBall (x a t : Transfer.VFType (M := M)) : Prop := iLe (iRv t.1) (iRv ((x - a)).1)

/-- Membership in the ball of radius `t` around `0` is `rv t ≤ rv x`. -/
theorem inBall_zero_iff {x t : Transfer.VFType (M := M)} :
    InBall x 0 t ↔ iLe (iRv t.1) (iRv x.1) := by
  have hsub : x - (0 : Transfer.VFType (M := M)) = x := sub_zero x
  show iLe (iRv t.1) (iRv ((x - 0)).1) ↔ iLe (iRv t.1) (iRv x.1)
  rw [hsub]

theorem inBall_self (x t : Transfer.VFType (M := M)) : InBall x x t := by
  show iLe (iRv t.1) (iRv ((x - x)).1)
  have hz : ((x - x)).1 = Transfer.iVFZero := by rw [sub_self]; rfl
  rw [hz, RVCalc.rv_zero_eq hM]
  exact RVCalc.le_top_rv hM (Transfer.rv_mem hM t.2)

/-- **The ball of radius `t` around `0` is closed under addition.** -/
theorem inBall_zero_add {x y t : Transfer.VFType (M := M)}
    (hx : InBall x 0 t) (hy : InBall y 0 t) : InBall (x + y) 0 t := by
  rw [inBall_zero_iff] at hx hy ⊢
  have hxr : iRV (iRv x.1) := Transfer.rv_mem hM x.2
  have hyr : iRV (iRv y.1) := Transfer.rv_mem hM y.2
  have hsr : iRV (iRv (x + y).1) := Transfer.rv_mem hM (x + y).2
  rcases RVCalc.rv_ultrametric hM x.2 y.2 with hu | hu
  · exact RVCalc.le_trans_rv hM (Transfer.rv_mem hM t.2) hxr hsr hx hu
  · exact RVCalc.le_trans_rv hM (Transfer.rv_mem hM t.2) hyr hsr hy hu

/-- The ball of radius `t` around `0` is closed under negation. -/
theorem inBall_zero_neg {x t : Transfer.VFType (M := M)} (hx : InBall x 0 t) :
    InBall (-x) 0 t := by
  rw [inBall_zero_iff] at hx ⊢
  exact RVCalc.le_trans_rv hM (Transfer.rv_mem hM t.2) (Transfer.rv_mem hM x.2)
    (Transfer.rv_mem hM (-x).2) hx (RVCalc.rv_neg_class hM x.2).2

/-- **A ball is a coset**: adding an element of the `0`-ball of radius `t` stays in the ball. -/
theorem inBall_add {x a z t : Transfer.VFType (M := M)} (hx : InBall x a t)
    (hz : InBall z 0 t) : InBall (x + z) a t := by
  have hid : (x + z) - a = (x - a) + z := by abel
  have hxv : iLe (iRv t.1) (iRv ((x - a)).1) := hx
  have hzv : iLe (iRv t.1) (iRv z.1) := (inBall_zero_iff (M := M)).1 hz
  have hsr : iRV (iRv (((x - a) + z)).1) := Transfer.rv_mem hM ((x - a) + z).2
  have hsum : iLe (iRv t.1) (iRv (((x - a) + z)).1) := by
    rcases RVCalc.rv_ultrametric hM (x - a).2 z.2 with hu | hu
    · exact RVCalc.le_trans_rv hM (Transfer.rv_mem hM t.2) (Transfer.rv_mem hM (x - a).2)
        hsr hxv hu
    · exact RVCalc.le_trans_rv hM (Transfer.rv_mem hM t.2) (Transfer.rv_mem hM z.2) hsr hzv hu
  show iLe (iRv t.1) (iRv ((x + z - a)).1)
  rw [hid]
  exact hsum

/-- Two points of a ball differ by an element of the `0`-ball of the same radius. -/
theorem inBall_sub {x x' a t : Transfer.VFType (M := M)} (hx : InBall x a t)
    (hx' : InBall x' a t) : InBall (x - x') 0 t := by
  have hid : x - x' = (x - a) + (-(x' - a)) := by abel
  have hneg : iLe (iRv t.1) (iRv ((-(x' - a)).1)) :=
    RVCalc.le_trans_rv hM (Transfer.rv_mem hM t.2) (Transfer.rv_mem hM (x' - a).2)
      (Transfer.rv_mem hM (-(x' - a)).2) hx' (RVCalc.rv_neg_class hM (x' - a).2).2
  have hmain : InBall ((x - a) + (-(x' - a))) 0 t := by
    have hxv : iLe (iRv t.1) (iRv ((x - a)).1) := hx
    rw [inBall_zero_iff]
    rcases RVCalc.rv_ultrametric hM (x - a).2 (-(x' - a)).2 with hu | hu
    · exact RVCalc.le_trans_rv hM (Transfer.rv_mem hM t.2) (Transfer.rv_mem hM (x - a).2)
        (Transfer.rv_mem hM ((x - a) + (-(x' - a))).2) hxv hu
    · exact RVCalc.le_trans_rv hM (Transfer.rv_mem hM t.2)
        (Transfer.rv_mem hM (-(x' - a)).2)
        (Transfer.rv_mem hM ((x - a) + (-(x' - a))).2) hneg hu
  rw [hid]
  exact hmain

/-- **Additive congruence on balls**: `x ≡ x'` and `y ≡ y'` modulo `t` implies
`x + y ≡ x' + y'` modulo `t`.  This is the residue-condition congruence of the paper. -/
theorem inBall_congr {x x' y y' t : Transfer.VFType (M := M)}
    (hx : InBall (x - x') 0 t) (hy : InBall (y - y') 0 t) :
    InBall ((x + y) - (x' + y')) 0 t := by
  have hid : (x + y) - (x' + y') = (x - x') + (y - y') := by abel
  rw [hid]
  exact inBall_zero_add hx hy

/-- **The unit ball is the valuation ring.** -/
theorem inBall_zero_iff_isInt (x : Transfer.VFType (M := M)) :
    InBall x 0 1 ↔ IsInt x := by
  rw [inBall_zero_iff]
  show iLe (iRv ((1 : Transfer.VFType (M := M))).1) (iRv x.1) ↔ iLe iRVOne (iRv x.1)
  rw [show ((1 : Transfer.VFType (M := M))).1 = Transfer.iVFOne from rfl, RVCalc.rv_one hM]

/-! ## 5. Reduction modulo `m`: `O` is a subring and `m` is an ideal -/

theorem isInt_sub {x y : Transfer.VFType (M := M)} (hx : IsInt x) (hy : IsInt y) :
    IsInt (x - y) := by
  rw [sub_eq_add_neg]
  exact isInt_add hx (isInt_neg hy)

/-- `m` is closed under subtraction. -/
theorem isMax_sub {x y : Transfer.VFType (M := M)} (hx : IsMax x) (hy : IsMax y) :
    IsMax (x - y) := by
  rw [sub_eq_add_neg]
  exact isMax_add hx (isMax_neg hy)

/-- `x - x' ∈ m` with `x ∈ O` forces `x' ∈ O`. -/
theorem isInt_of_isInt_sub_isMax {x x' : Transfer.VFType (M := M)} (hx : IsInt x)
    (h : IsMax (x - x')) : IsInt x' := by
  have hid : x' = x - (x - x') := by abel
  rw [hid]
  exact isInt_sub hx (isInt_of_isMax h)

/-- `m` is closed under multiplication by an integral element, on the right. -/
theorem isMax_mul_right {a x : Transfer.VFType (M := M)} (ha : IsInt a) (hx : IsMax x) :
    IsMax (x * a) := by
  have h := isMax_mul (a := a) (x := x) ha hx
  have hidx : (x * a).1 = (a * x).1 := RVCalc.vf_mul_comm hM x.2 a.2
  intro hle
  exact h (hidx ▸ hle)

/-! ### Obstruction: `ring` does not work on `VFType`

Machine-checked here (see the header): `Ring (VFType M)` and `Distrib (VFType M)` are both
synthesised, and `left_distrib`/`right_distrib` can be made available as instances, but
`LeftDistribClass`/`RightDistribClass` are **not** synthesised from the `Field` instance, and
`mul_sub`/`sub_mul`/`ring`/`ring_nf` therefore do not fire at `VFType`.  Ring identities at
`VFType` have to be proved by hand from `Transfer.vf_left_distrib`, `RVCalc.vf_add_mul` and the
uniqueness of negation.  This is why the multiplicative reduction congruence
`x ≡ x' → y ≡ y' → x * y ≡ x' * y' (mod m)` is *not* stated in this file: it needs
`x * y - x' * y' = x * (y - y') + (x - x') * y'`.
-/

/-! ### Toolkit: distributivity at `VFType`

`ring` cannot be used at `VFType` (see the obstruction note above), so here are the two
distributivity laws in the `VFType` form; combined with `abel` they cover the ring identities that
occur in residue arguments. -/

/-- `a * (b + c) = a * b + a * c` at `VFType`, from the `VF` field axioms. -/
theorem vf_mul_add_vf (a b c : Transfer.VFType (M := M)) : a * (b + c) = a * b + a * c :=
  Subtype.ext (Transfer.vf_left_distrib hM a.2 b.2 c.2)

/-- `(a + b) * c = a * c + b * c` at `VFType`, from the `VF` field axioms. -/
theorem vf_add_mul_vf (a b c : Transfer.VFType (M := M)) : (a + b) * c = a * c + b * c :=
  Subtype.ext (RVCalc.vf_add_mul (M := M) hM (x := c.1) (y := a.1) (z := b.1) c.2 a.2 b.2)

/-! ## 6. Axiom audit -/

#print axioms mem_ACVF_sdUnits
#print axioms iRV_of_iUnits
#print axioms not_iUnits_of_iVF
#print axioms isInt_zero
#print axioms isInt_one
#print axioms isMax_zero
#print axioms isInt_add
#print axioms isInt_neg
#print axioms isInt_mul
#print axioms isInt_of_isMax
#print axioms isMax_add
#print axioms isMax_neg
#print axioms isMax_mul
#print axioms isMax_not_iUnits
#print axioms iUnits_iff_isInt_and_not_isMax
#print axioms rv_inv
#print axioms isInt_or_inv
#print axioms rv_add_eq_of_lt'
#print axioms rv_add_eq_of_le_false
#print axioms negOne
#print axioms rv_add_eq_of_lt
#print axioms iUnits_of_isInt_and_not_isMax
#print axioms rv_add_eq_of_isMax
#print axioms not_isMax_add_of_unit
#print axioms inBall_zero_iff
#print axioms inBall_self
#print axioms inBall_zero_add
#print axioms inBall_zero_neg
#print axioms inBall_add
#print axioms inBall_sub
#print axioms inBall_congr
#print axioms inBall_zero_iff_isInt
#print axioms isInt_sub
#print axioms isMax_sub
#print axioms isInt_of_isInt_sub_isMax
#print axioms isMax_mul_right
#print axioms vf_mul_add_vf
#print axioms vf_add_mul_vf

end SpecialTransformations.Milestone0.RVAdd
