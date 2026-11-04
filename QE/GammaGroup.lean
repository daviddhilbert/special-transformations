/-
**Γ(M) as an ordered abelian group, step d1: `RV ∖ {0}` is a commutative group.**

The paper's `Γ(M) = RV(M)/Kˣ(M)`.  This file builds the *group half* for the frozen encoding
from `Axioms.ACVF` alone:

* `RVStar M` — the multiplicative carrier of nonzero `RV`-elements, with `iRVMul` closed
  by `Transfer.rv_mul_mem`, no zero divisors (`Transfer.rv_mul_eq_zero_of_model`), and
  inverses from `Transfer.iRVInv` (`Transfer.iRVInv_mul_cancel`);
* `CommGroup (RVStar M)` — **this file** (direction d1): associativity, neutrality and
  invertibility come from the axioms `rvMulAssoc`, `rvMulOneRV`/`rvMulInvRV` (through the
  `Transfer` API), commutativity from `rvMulComm`;
* `units_ne_zero`, `units_mul`, `iRVInv_units`, `KStar : Subgroup (RVStar M)` — `Kˣ` really is
  a subgroup of `RV ∖ {0}` (closed under `1`, `·` and the *chosen* inverse), so
  `RVStar M ⧸ KStar` — the paper's `Γ(M)` **as a group** — is a `CommGroup` from Mathlib alone
  (`example : CommGroup (RVStar M ⧸ KStar) := inferInstance`, checked at the end of §4).

MERGE note for d2/d3: the `CommGroup (RVStar M)` instance (`commGroupRVStar`) is d1's
deliverable — do not restate it; `KStar` is available for `RVStar ⧸ KStar` if a Mathlib
quotient group is preferred to the value-class setoid `Cls`.

Not in this file (direction d2, the *order* half): the value-class setoid
`Cls a b := iLe a b ∧ iLe b a`, the quotient `GammaOf M`, `LinearOrder (GammaOf M)` and
`CovariantClass (GammaOf M) (GammaOf M) (· * ·) (· ≤ ·)` (the last from `RVCalc.le_mul_iff`
= `leMulCompatFull`).

Together with `QE/StandingField.lean`'s `Field (KOf M)` this is the frozen `(K, Γ)` pair of
a model of `ACVF`, at which the Prestel–Engler quotations of `QE/ClassicalProps.lean`
(henselization with same residue/value group, divisible hull) are stated.

## Hypothesis audit (report standard)

There is **no** named hypothesis in this file.  The only assumptions are the ambient
`[LRV.Structure M]` and `[hM : M ⊨ Axioms.ACVF]`, the standing setup of the whole project
(carried identically by `QE/RVCalc.lean`, `QE/StandingField.lean`, `QE/VFValued.lean`), so
nothing here can be vacuous or cardinality-forcing.  Non-vacuity checks:

* `rvStar_nonempty : Nonempty (RVStar M)` — the carrier is inhabited, so the group laws are
  equations between existing elements, not vacuous truths over an empty type;
* `rvStar_val_mul`/`rvStar_val_one`/`rvStar_val_inv` — the operations are *computed* on
  values as `iRVMul`, `iRVOne`, `Transfer.iRVInv`: they are not constant and not projections;
* every law is *proved*: there is no pre-existing `Group`/`CommGroup`/`Monoid` instance on
  `M` or on the subtype in the tree, and no field of `CommGroup (RVStar M)` is assumed.
-/
import RVCalc
import Jm2T1
import Standing

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace SpecialTransformations.Milestone0.GammaGroup

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ### The `RV`-nonzero comm group -/

/-- The carrier of Γ's group part: nonzero `RV` elements as a type. -/
def RVStar (M : Type) [LRV.Structure M] : Type := {x : M // iRV x ∧ x ≠ iRVZero}

/-- One of the group (the class of `iRVOne`). -/
noncomputable def RVStarOne : RVStar M := ⟨iRVOne, Transfer.rv_one_mem hM, RVCalc.rv_one_ne_zero hM⟩

/-- Multiplication of nonzeros is nonzero (no zero divisors on `RV`). -/
theorem rvStar_mul_nonzero {a b : M} (ha : iRV a ∧ a ≠ iRVZero) (hb : iRV b ∧ b ≠ iRVZero) :
    iRVMul a b ≠ iRVZero := by
  intro h
  rw [Transfer.rv_mul_eq_zero_of_model hM ha.1 hb.1] at h
  rcases h with h | h
  · exact ha.2 h
  · exact hb.2 h

/-- Absorption at a `rvZero` factor. -/
theorem rv_mul_zero_left {a : M} (ha : iRV a) : iRVMul iRVZero a = iRVZero :=
  (Transfer.rv_mul_eq_zero_of_model hM (Transfer.rv_zero_mem hM) ha).mpr (Or.inl rfl)

/-- The inverse of a nonzero is nonzero. -/
theorem rvStar_inv_nonzero {a : M} (ha : iRV a ∧ a ≠ iRVZero) : Transfer.iRVInv hM a ≠ iRVZero := by
  intro h0
  have hc := Transfer.iRVInv_mul_cancel hM ha.1 ha.2
  rw [h0, show iRVMul iRVZero a = iRVZero from
    (Transfer.rv_mul_eq_zero_of_model hM (Transfer.rv_zero_mem hM) ha.1).mpr (Or.inl rfl)] at hc
  exact (RVCalc.rv_one_ne_zero hM) hc.symm

noncomputable section

/-! ### 1. The operations on `RVStar M` -/

/-- Multiplication on `RVStar M`, inherited from `iRVMul`. -/
def rvStarMul (a b : RVStar M) : RVStar M :=
  ⟨iRVMul a.1 b.1, Transfer.rv_mul_mem hM a.2.1 b.2.1, rvStar_mul_nonzero a.2 b.2⟩

/-- Inversion on `RVStar M`, from the chosen `RV`-inverse `Transfer.iRVInv`. -/
def rvStarInv (a : RVStar M) : RVStar M :=
  ⟨Transfer.iRVInv hM a.1, Transfer.iRVInv_mem hM a.2.1, rvStar_inv_nonzero a.2⟩

instance rvStarMulInst : Mul (RVStar M) := ⟨rvStarMul⟩

instance rvStarOneInst : One (RVStar M) := ⟨RVStarOne⟩

instance rvStarInvInst : Inv (RVStar M) := ⟨rvStarInv⟩

/-- The value of a product is the `iRVMul` of the values (`rfl`). -/
@[simp] theorem rvStar_val_mul (a b : RVStar M) : (a * b).1 = iRVMul a.1 b.1 := rfl

/-- The value of `1` is `iRVOne` (`rfl`). -/
@[simp] theorem rvStar_val_one : (1 : RVStar M).1 = iRVOne := rfl

/-- The value of an inverse is `Transfer.iRVInv` (`rfl`). -/
@[simp] theorem rvStar_val_inv (a : RVStar M) : (a⁻¹).1 = Transfer.iRVInv hM a.1 := rfl

/-- `RVStar M` is inhabited — non-vacuity of every law below. -/
theorem rvStar_nonempty : Nonempty (RVStar M) := ⟨RVStarOne⟩

/-! ### 2. The group laws, from the frozen `Transfer` API -/

/-- Associativity, from the `rvMulAssoc` axiom. -/
theorem rvStar_mul_assoc (a b c : RVStar M) : (a * b) * c = a * (b * c) :=
  Subtype.ext (Transfer.rv_mul_assoc_of_model hM a.2.1 b.2.1 c.2.1)

/-- `1 * a = a`, from `rvMulOneRV` through `rv_mul_one_any` (no nonzero side condition). -/
theorem rvStar_one_mul (a : RVStar M) : 1 * a = a :=
  Subtype.ext (Transfer.rv_mul_one_any hM a.2.1)

/-- `a * 1 = a`. -/
theorem rvStar_mul_one (a : RVStar M) : a * 1 = a :=
  Subtype.ext (Transfer.rv_mul_one_any_right hM a.2.1)

/-- `a⁻¹ * a = 1`, from `rvMulInvRV` through the choosing function `Transfer.iRVInv`. -/
theorem rvStar_inv_mul_cancel (a : RVStar M) : a⁻¹ * a = 1 :=
  Subtype.ext (Transfer.iRVInv_mul_cancel hM a.2.1 a.2.2)

/-- Commutativity, from the `rvMulComm` axiom. -/
theorem rvStar_mul_comm (a b : RVStar M) : a * b = b * a :=
  Subtype.ext (Transfer.rv_mul_comm_of_model hM a.2.1 b.2.1)

/-- **`RV ∖ {0}` is a commutative group.**  This is the group half of the paper's `Γ(M)`:
`RVStar ⧸ Kˣ` is the paper's `Γ` as a group (see `units_ne_zero` below for `Kˣ ⊆ RVStar`). -/
instance commGroupRVStar : CommGroup (RVStar M) :=
  { Group.ofLeftAxioms rvStar_mul_assoc rvStar_one_mul rvStar_inv_mul_cancel with
      mul_comm := rvStar_mul_comm }

/-! ### 3. Consequences used downstream -/

/-- `a * a⁻¹ = 1` (the other side of the inverse law). -/
theorem rvStar_mul_inv_cancel (a : RVStar M) : a * a⁻¹ = 1 := mul_inv_cancel a

/-! ### 4. `Kˣ ⊆ RV ∖ {0}`

`rvMulInv` (a member of `Axioms.rvGroup`, hence of `Axioms.ACVF`) inverts every unit *inside*
`Kˣ`.  An inverse of `0` would give `1 = b · 0 = 0`, which `rv_one_ne_zero` forbids.  This is
the only place in the file where a `pUnits`-guarded axiom is unfolded. -/

/-- The witness form of `rvMulInv`, extracted from `Axioms.ACVF`. -/
theorem units_exists_inv {a : M} (ha : iUnits a) :
    ∃ b : M, iRV b ∧ (iUnits b ∧ iRVMul b a = iRVOne) := by
  have hr : iRV a := Jm2.iRV_of_inK (Or.inl ha)
  have hmem : Axioms.rvMulInv ∈ Axioms.ACVF :=
    Transfer.mem_ACVF_of_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])
  have h := Transfer.allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pUnits &0 ⟹ exSorted .rv (pUnits &1 ⊓ pEq (tRVMul &1 &0) tRVOne)))
    hmem ![a] (by intro i; fin_cases i; simpa using hr)
  rw [BoundedFormula.realize_imp] at h
  have h2 := h ((Transfer.pUnits_realize (M := M) &0 (default : Empty → M) ![a]).mpr
    (by simpa using ha))
  simpa [exSorted, sortPred, Transfer.sortPred_realize, Transfer.pRVsort_realize,
    BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, Transfer.pUnits_realize, pEq, BoundedFormula.realize_bdEqual,
    Transfer.realize_tRVMul, Transfer.realize_tRVOne_T, RVCalc.realize_var_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h2

/-- **`Kˣ ⊆ RV ∖ {0}`**: a unit is nonzero. -/
theorem units_ne_zero {a : M} (ha : iUnits a) : a ≠ iRVZero := by
  intro h0
  obtain ⟨b, hb, -, hbinv⟩ := units_exists_inv (M := M) ha
  rw [h0, Transfer.rv_mul_zero_right_of_model hM hb] at hbinv
  exact RVCalc.rv_one_ne_zero hM hbinv.symm

/-! ### 5. `Kˣ` as a subgroup of `RVStar M`

The paper's `Γ(M) = RV ∖ {0} / Kˣ`.  Once `Kˣ` is a subgroup of `RVStar M`, the quotient
`RVStar M ⧸ KStar` is a `CommGroup` *from Mathlib alone* (`Quotient.commGroup`), i.e. the
paper's `Γ(M)` exists as a group with no further congruence work.  Closure under `·` is the
axiom `rvMulMem`; closure under `⁻¹` needs the *chosen* inverse `Transfer.iRVInv` to be a unit,
which follows from `rvMulInv`'s unit inverse by cancellation. -/

/-- Units are closed under `iRVMul`: the axiom `rvMulMem` (`Axioms.rvGroup`). -/
theorem units_mul {a b : M} (ha : iUnits a) (hb : iUnits b) : iUnits (iRVMul a b) := by
  have hra : iRV a := Jm2.iRV_of_inK (Or.inl ha)
  have hrb : iRV b := Jm2.iRV_of_inK (Or.inl hb)
  have hmem : Axioms.rvMulMem ∈ Axioms.ACVF :=
    Transfer.mem_ACVF_of_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])
  have h := Transfer.allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv])
    (φ := (pUnits &0 ⟹ (pUnits &1 ⟹ pUnits (tRVMul &0 &1))))
    hmem ![a, b] (by intro i; fin_cases i <;> simp [hra, hrb])
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp] at h
  have h1 := h ((Transfer.pUnits_realize (M := M) &0 (default : Empty → M) ![a, b]).mpr
    (by simpa using ha))
  have h2 := h1 ((Transfer.pUnits_realize (M := M) &1 (default : Empty → M) ![a, b]).mpr
    (by simpa using hb))
  simpa [Transfer.pUnits_realize, Transfer.realize_tRVMul, RVCalc.realize_var_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h2

/-- The *chosen* inverse `Transfer.iRVInv` of a unit is a unit.  `units_exists_inv` gives some
unit inverse `b` of `a`; `iRVInv` is another inverse, so `iRVInv a = b` by cancellation. -/
theorem iRVInv_units {a : M} (ha : iUnits a) : iUnits (Transfer.iRVInv hM a) := by
  obtain ⟨b, hb, hbu, hbinv⟩ := units_exists_inv (M := M) ha
  have ha0 : a ≠ iRVZero := units_ne_zero ha
  have hra : iRV a := Jm2.iRV_of_inK (Or.inl ha)
  have hrinv : iRV (Transfer.iRVInv hM a) := Transfer.iRVInv_mem hM hra
  have h1 : Transfer.iRVInv hM a = b :=
    Transfer.rv_mul_left_cancel_of_model hM (a := Transfer.iRVInv hM a) (b := a) (c := b)
      hrinv hra ha0 hb (by
        rw [Transfer.iRVInv_mul_cancel hM hra ha0]; exact hbinv.symm)
  rw [h1]
  exact hbu

/-- **`Kˣ` is a subgroup of `RV ∖ {0}`**: `1` is a unit (`rvOneMem`), units are closed under
`·` (`rvMulMem`) and under the chosen inverse (`iRVInv_units`). -/
def KStar : Subgroup (RVStar M) where
  carrier := {a | iUnits a.1}
  one_mem' := StandingTree.rv_one_units
  mul_mem' := by
    intro a b ha hb
    exact units_mul ha hb
  inv_mem' := by
    intro a ha
    exact iRVInv_units ha

/-- Membership in `KStar` is being a unit on values. -/
@[simp] theorem mem_KStar {a : RVStar M} : a ∈ KStar ↔ iUnits a.1 where
  mp := fun h => h
  mpr := fun h => h

/-- The paper's `Γ(M)` **as a group** is Mathlib's quotient `RVStar M ⧸ KStar`; it is a
`CommGroup` with no further work (`Quotient.commGroup`).  (The *order* on it is direction d2,
via the value-class setoid `Cls`.) -/
example : CommGroup (RVStar M ⧸ KStar) := inferInstance

/-! ### The value-class setoid and the ordered quotient (d2, swarm smw2ioy2w m2; direction abandoned by budget, file verified and merged judge-side) -/

def ClsRel (a b : RVStar M) : Prop := iLe a.1 b.1 ∧ iLe b.1 a.1

theorem clsRel_refl (a : RVStar M) : ClsRel a a :=
  ⟨RVCalc.le_refl_rv hM a.2.1, RVCalc.le_refl_rv hM a.2.1⟩

theorem clsRel_symm {a b : RVStar M} (h : ClsRel a b) : ClsRel b a := ⟨h.2, h.1⟩

theorem clsRel_trans {a b c : RVStar M} (h₁ : ClsRel a b) (h₂ : ClsRel b c) : ClsRel a c :=
  ⟨RVCalc.le_trans_rv hM a.2.1 b.2.1 c.2.1 h₁.1 h₂.1,
   RVCalc.le_trans_rv hM c.2.1 b.2.1 a.2.1 h₂.2 h₁.2⟩

/-- **The value-class setoid** on `RV ∖ {0}`: `a` and `b` have the same value. -/
def Cls (M : Type) [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] : Setoid (RVStar M) :=
  ⟨ClsRel, ⟨clsRel_refl, clsRel_symm, clsRel_trans⟩⟩

theorem clsRel_iff {a b : RVStar M} : (Cls M).r a b ↔ iLe a.1 b.1 ∧ iLe b.1 a.1 :=
  Iff.rfl

/-- **The value group** `Γ(M) = RV(M)^× / K^×(M)`: nonzero `RV`-elements modulo
value classes.  (An `abbrev` so that instance search sees through it.) -/
abbrev GammaOf (M : Type) [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] : Type := Quotient (Cls M)

/-- The class of a nonzero `RV`-element, `Γ`'s quotient map. -/
abbrev gammaMk (a : RVStar M) : GammaOf M := Quotient.mk (Cls M) a

theorem gammaMk_surjective : Function.Surjective (gammaMk (M := M)) :=
  fun q => Quotient.inductionOn q (fun a => ⟨a, rfl⟩)

theorem gammaMk_eq_iff {a b : RVStar M} : gammaMk a = gammaMk b ↔ ClsRel a b :=
  Quotient.eq

/-- Two nonzero `RV`-elements have the same image in `Γ` iff they are mutually `≤`. -/
theorem gammaMk_eq_iff_le {a b : RVStar M} :
    gammaMk a = gammaMk b ↔ iLe a.1 b.1 ∧ iLe b.1 a.1 :=
  Quotient.eq

/-! ### Congruence lemmas: `Cls` is a congruence for `Mul` and `Inv` -/

theorem le_of_cls_left {a a' b : RVStar M} (h : ClsRel a a') (hab : iLe a.1 b.1) :
    iLe a'.1 b.1 :=
  RVCalc.le_trans_rv hM a'.2.1 a.2.1 b.2.1 h.2 hab

theorem le_of_cls_right {a b b' : RVStar M} (h : ClsRel b b') (hab : iLe a.1 b.1) :
    iLe a.1 b'.1 :=
  RVCalc.le_trans_rv hM a.2.1 b.2.1 b'.2.1 hab h.1

theorem iLe_congr {a a' b b' : RVStar M} (ha : ClsRel a a') (hb : ClsRel b b') :
    (iLe a.1 b.1 ↔ iLe a'.1 b'.1) :=
  ⟨fun h => le_of_cls_right hb (le_of_cls_left ha h),
   fun h => le_of_cls_left (clsRel_symm ha) (le_of_cls_right (clsRel_symm hb) h)⟩

/-- Scaling by a nonzero `RV`-element preserves `≤` on the right (`leMulCompatFull`). -/
theorem le_mul_right_rv {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c) (hc0 : c ≠ iRVZero)
    (h : iLe a b) : iLe (iRVMul a c) (iRVMul b c) :=
  (RVCalc.le_mul_iff hM ha hb hc hc0).mp h

/-- Scaling by a nonzero `RV`-element preserves `≤` on the left (`leMulCompatFull`, commutativity). -/
theorem le_mul_left_rv {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c) (hc0 : c ≠ iRVZero)
    (h : iLe a b) : iLe (iRVMul c a) (iRVMul c b) := by
  have h' := le_mul_right_rv (M := M) ha hb hc hc0 h
  simpa only [Transfer.rv_mul_comm_of_model hM hc ha, Transfer.rv_mul_comm_of_model hM hc hb] using h'

/-- `Cls` is compatible with `Mul`. -/
theorem clsRel_mul {a a' b b' : RVStar M} (ha : ClsRel a a') (hb : ClsRel b b') :
    ClsRel (a * b) (a' * b') := by
  refine ⟨?_, ?_⟩
  · exact RVCalc.le_trans_rv hM (Transfer.rv_mul_mem hM a.2.1 b.2.1)
      (Transfer.rv_mul_mem hM a'.2.1 b.2.1) (Transfer.rv_mul_mem hM a'.2.1 b'.2.1)
      (le_mul_right_rv (M := M) (a := a.1) (b := a'.1) (c := b.1) a.2.1 a'.2.1 b.2.1 b.2.2 ha.1)
      (le_mul_left_rv (M := M) (a := b.1) (b := b'.1) (c := a'.1) b.2.1 b'.2.1 a'.2.1 a'.2.2 hb.1)
  · exact RVCalc.le_trans_rv hM (Transfer.rv_mul_mem hM a'.2.1 b'.2.1)
      (Transfer.rv_mul_mem hM a.2.1 b'.2.1) (Transfer.rv_mul_mem hM a.2.1 b.2.1)
      (le_mul_right_rv (M := M) (a := a'.1) (b := a.1) (c := b'.1) a'.2.1 a.2.1 b'.2.1 b'.2.2 ha.2)
      (le_mul_left_rv (M := M) (a := b'.1) (b := b.1) (c := a.1) b'.2.1 b.2.1 a.2.1 a.2.2 hb.2)

/-- Inversion reverses `≤` on `RV ∖ {0}`. -/
theorem inv_le_inv_rv {a b : M} (ha : iRV a) (hb : iRV b) (ha0 : a ≠ iRVZero) (hb0 : b ≠ iRVZero)
    (h : iLe a b) : iLe (Transfer.iRVInv hM b) (Transfer.iRVInv hM a) := by
  have hb' : iRV (Transfer.iRVInv hM b) := Transfer.iRVInv_mem hM hb
  have hb'0 : Transfer.iRVInv hM b ≠ iRVZero := rvStar_inv_nonzero ⟨hb, hb0⟩
  have ha' : iRV (Transfer.iRVInv hM a) := Transfer.iRVInv_mem hM ha
  have ha'0 : Transfer.iRVInv hM a ≠ iRVZero := rvStar_inv_nonzero ⟨ha, ha0⟩
  have hone : iRV (iRVOne (M := M)) := Transfer.rv_one_mem hM
  -- `a ≤ b` scaled by `b⁻¹` on the right: `a·b⁻¹ ≤ 1`
  have h1 : iLe (iRVMul a (Transfer.iRVInv hM b)) iRVOne := by
    have h₁ := le_mul_right_rv (M := M) ha hb hb' hb'0 h
    rwa [Transfer.rv_mul_inv_cancel_right hM hb hb0] at h₁
  -- scaled by `a⁻¹` on the right: `b⁻¹ ≤ a⁻¹`
  have h2 : iLe (iRVMul (iRVMul a (Transfer.iRVInv hM b)) (Transfer.iRVInv hM a))
      (iRVMul iRVOne (Transfer.iRVInv hM a)) :=
    le_mul_right_rv (M := M) (Transfer.rv_mul_mem hM ha hb') hone ha' ha'0 h1
  have h3 : iRVMul (iRVMul a (Transfer.iRVInv hM b)) (Transfer.iRVInv hM a) =
      Transfer.iRVInv hM b := by
    rw [Transfer.rv_mul_assoc_of_model hM ha hb' ha',
      Transfer.rv_mul_comm_of_model hM hb' ha',
      ← Transfer.rv_mul_assoc_of_model hM ha ha' hb',
      Transfer.rv_mul_inv_cancel_right hM ha ha0,
      Transfer.rv_mul_one_any hM hb']
  have h4 : iRVMul iRVOne (Transfer.iRVInv hM a) = Transfer.iRVInv hM a :=
    Transfer.rv_mul_one_any hM ha'
  rwa [h3, h4] at h2

/-- `Cls` is compatible with `Inv`. -/
theorem clsRel_inv {a b : RVStar M} (h : ClsRel a b) : ClsRel a⁻¹ b⁻¹ :=
  ⟨inv_le_inv_rv b.2.1 a.2.1 b.2.2 a.2.2 h.2, inv_le_inv_rv a.2.1 b.2.1 a.2.2 b.2.2 h.1⟩

/-! ### The descended operations -/

/-- Multiplication on `Γ(M)`, descended along `Cls` (well-defined by `leMulCompatFull`). -/
def gammaMul (a b : GammaOf M) : GammaOf M :=
  Quotient.lift₂ (fun x y : RVStar M => gammaMk (x * y))
    (fun x y x' y' hx hy => Quotient.sound (clsRel_mul hx hy)) a b

/-- Inversion on `Γ(M)`, descended along `Cls`. -/
def gammaInv (a : GammaOf M) : GammaOf M :=
  Quotient.map (fun x : RVStar M => x⁻¹) (fun x y h => clsRel_inv h) a

instance gammaOfMul : Mul (GammaOf M) := ⟨gammaMul⟩

instance gammaOfOne : One (GammaOf M) := ⟨gammaMk 1⟩

instance gammaOfInv : Inv (GammaOf M) := ⟨gammaInv⟩

-- computation rules for the descended operations (all `rfl`)

theorem gammaMk_mul (a b : RVStar M) : gammaMk (a * b) = gammaMk a * gammaMk b := rfl

theorem gammaMk_one_eq : gammaMk (1 : RVStar M) = 1 := rfl

theorem gammaMk_inv (a : RVStar M) : gammaMk a⁻¹ = (gammaMk a)⁻¹ := rfl

/-! ### The group axioms on `Γ(M)` -/

theorem gamma_mul_assoc (a b c : GammaOf M) : a * b * c = a * (b * c) := by
  refine Quotient.inductionOn a (fun a => ?_)
  refine Quotient.inductionOn b (fun b => ?_)
  refine Quotient.inductionOn c (fun c => ?_)
  rw [← gammaMk_mul, ← gammaMk_mul, ← gammaMk_mul, ← gammaMk_mul, rvStar_mul_assoc]

theorem gamma_one_mul (a : GammaOf M) : 1 * a = a := by
  refine Quotient.inductionOn a (fun a => ?_)
  rw [← gammaMk_one_eq, ← gammaMk_mul, rvStar_one_mul]

theorem gamma_mul_one (a : GammaOf M) : a * 1 = a := by
  refine Quotient.inductionOn a (fun a => ?_)
  rw [← gammaMk_one_eq, ← gammaMk_mul, rvStar_mul_one]

theorem gamma_inv_mul_cancel (a : GammaOf M) : a⁻¹ * a = 1 := by
  refine Quotient.inductionOn a (fun a => ?_)
  rw [← gammaMk_inv, ← gammaMk_mul, rvStar_inv_mul_cancel, gammaMk_one_eq]

theorem gamma_mul_comm (a b : GammaOf M) : a * b = b * a := by
  refine Quotient.inductionOn a (fun a => ?_)
  refine Quotient.inductionOn b (fun b => ?_)
  rw [← gammaMk_mul, ← gammaMk_mul, rvStar_mul_comm]

/-- **`Γ(M)` is a commutative group.** -/
instance gammaOfCommGroup : CommGroup (GammaOf M) where
  mul_assoc := gamma_mul_assoc
  one_mul := gamma_one_mul
  mul_one := gamma_mul_one
  inv_mul_cancel := gamma_inv_mul_cancel
  mul_comm := gamma_mul_comm

instance gammaOfInhabited : Inhabited (GammaOf M) := ⟨1⟩

/-! ### The identity class is `K^×` -/

/-- The kernel of `RV ∖ {0} → Γ(M)` is exactly `K^×`: the paper's
`Γ(M) = RV(M)^× / K^×(M)`. -/
theorem gammaMk_eq_one_iff_units {a : RVStar M} : gammaMk a = 1 ↔ iUnits a.1 := by
  have h : gammaMk a = 1 ↔ ClsRel a 1 := by
    show (Quotient.mk (Cls M) a = Quotient.mk (Cls M) (1 : RVStar M)) ↔ ClsRel a 1
    exact Quotient.eq
  rw [h]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact (RVCalc.units_iff_le_one hM a.2.1 a.2.2).mpr ⟨h₂, h₁⟩
  · intro hu
    have h' := (RVCalc.units_iff_le_one hM a.2.1 a.2.2).mp hu
    exact ⟨h'.2, h'.1⟩

/-! ## 4. `Γ(M)` as a linear order

The order on the quotient is descended along `Cls`: `iLe` is invariant under replacing a
representative by a class-equal one (`iLe_congr`).  Antisymmetry is *free* from the shape of
`Cls`: two classes that are mutually `≤` are the same class by `Quotient.sound`. -/

/-- `≤` on `Γ(M)`, descended along `Cls`. -/
def gammaLe (a b : GammaOf M) : Prop :=
  Quotient.lift₂ (fun x y : RVStar M => iLe x.1 y.1)
    (fun x y x' y' hx hy => propext (iLe_congr hx hy)) a b

instance gammaOfLE : LE (GammaOf M) := ⟨gammaLe⟩

/-- The order on `Γ(M)` is `iLe` on representatives. -/
theorem gammaMk_le_iff {a b : RVStar M} : gammaMk a ≤ gammaMk b ↔ iLe a.1 b.1 := Iff.rfl

theorem gamma_le_refl (a : GammaOf M) : a ≤ a := by
  refine Quotient.inductionOn a (fun a => ?_)
  rw [gammaMk_le_iff]
  exact RVCalc.le_refl_rv hM a.2.1

theorem gamma_le_trans (a b c : GammaOf M) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  revert h₁ h₂
  refine Quotient.inductionOn a (fun a => ?_)
  refine Quotient.inductionOn b (fun b => ?_)
  refine Quotient.inductionOn c (fun c => ?_)
  intro h₁ h₂
  rw [gammaMk_le_iff] at h₁ h₂ ⊢
  exact RVCalc.le_trans_rv hM a.2.1 b.2.1 c.2.1 h₁ h₂

/-- Antisymmetry on `Γ(M)`: mutual `≤` means the same value class. -/
theorem gamma_le_antisymm (a b : GammaOf M) (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  revert h₁ h₂
  refine Quotient.inductionOn a (fun a => ?_)
  refine Quotient.inductionOn b (fun b => ?_)
  intro h₁ h₂
  rw [gammaMk_le_iff] at h₁ h₂
  exact Quotient.sound ⟨h₁, h₂⟩

/-- Totality of the order on `Γ(M)` (`leTotal` of the encoding). -/
theorem gamma_le_total (a b : GammaOf M) : a ≤ b ∨ b ≤ a := by
  refine Quotient.inductionOn a (fun a => ?_)
  refine Quotient.inductionOn b (fun b => ?_)
  rw [gammaMk_le_iff]
  exact RVCalc.le_total_rv hM a.2.1 b.2.1

instance gammaOfPreorder : Preorder (GammaOf M) where
  le_refl := gamma_le_refl
  le_trans := gamma_le_trans

instance gammaOfPartialOrder : PartialOrder (GammaOf M) where
  le_antisymm := gamma_le_antisymm

/-- **`Γ(M)` is linearly ordered.** -/
instance gammaOfLinearOrder : LinearOrder (GammaOf M) where
  le_antisymm := gamma_le_antisymm
  le_total := gamma_le_total
  toDecidableLE := fun a b => Classical.propDecidable (a ≤ b)

/-! ## 5. Order compatibility with multiplication -/

/-- Multiplication on the right preserves `≤` (`leMulCompatFull`). -/
theorem gamma_mul_le_mul_right (a b c : GammaOf M) (h : a ≤ b) : a * c ≤ b * c := by
  revert h
  refine Quotient.inductionOn a (fun a => ?_)
  refine Quotient.inductionOn b (fun b => ?_)
  refine Quotient.inductionOn c (fun c => ?_)
  intro h
  rw [gammaMk_le_iff] at h
  rw [← gammaMk_mul, ← gammaMk_mul, gammaMk_le_iff]
  exact (RVCalc.le_mul_iff hM a.2.1 b.2.1 c.2.1 c.2.2).mp h

/-- Multiplication on the left preserves `≤` (`leMulCompatFull` + commutativity). -/
theorem gamma_mul_le_mul_left (a b c : GammaOf M) (h : a ≤ b) : c * a ≤ c * b := by
  revert h
  refine Quotient.inductionOn a (fun a => ?_)
  refine Quotient.inductionOn b (fun b => ?_)
  refine Quotient.inductionOn c (fun c => ?_)
  intro h
  rw [gammaMk_le_iff] at h
  rw [← gammaMk_mul, ← gammaMk_mul, gammaMk_le_iff]
  exact le_mul_left_rv (M := M) (a := a.1) (b := b.1) (c := c.1) a.2.1 b.2.1 c.2.1 c.2.2 h

/-- Scaling is an order-embedding: `a ≤ b ↔ a·c ≤ b·c` for any `c : Γ(M)`. -/
theorem gamma_le_iff_mul_le (a b c : GammaOf M) : a ≤ b ↔ a * c ≤ b * c := by
  refine Quotient.inductionOn a (fun a => ?_)
  refine Quotient.inductionOn b (fun b => ?_)
  refine Quotient.inductionOn c (fun c => ?_)
  rw [gammaMk_le_iff, ← gammaMk_mul, ← gammaMk_mul, gammaMk_le_iff]
  exact RVCalc.le_mul_iff hM a.2.1 b.2.1 c.2.1 c.2.2

instance gammaCovariantMulLeft : CovariantClass (GammaOf M) (GammaOf M) (· * ·) (· ≤ ·) :=
  ⟨fun c a b h => gamma_mul_le_mul_left a b c h⟩

instance gammaCovariantMulRight :
    CovariantClass (GammaOf M) (GammaOf M) (Function.swap (· * ·)) (· ≤ ·) :=
  ⟨fun c a b h => gamma_mul_le_mul_right a b c h⟩

/-- **In this Mathlib version a linearly ordered commutative group is
`[CommGroup] [LinearOrder] [IsOrderedMonoid]` (`LinearOrderedCommGroup` was removed).** -/
instance gammaIsOrderedMonoid : IsOrderedMonoid (GammaOf M) where
  mul_le_mul_left a b h c := gamma_mul_le_mul_right a b c h

/-! ## 6. Deliverable: `Γ(M)` is a linearly ordered abelian group -/

/-- **Deliverable (direction d2).**  The value group `Γ(M) = RV(M)^× / K^×(M)` of any
model of `Axioms.ACVF` is a linearly ordered abelian group, with the order inherited from
`iLe` and compatible with multiplication.  Every conjunct is the corresponding field of the
`CommGroup`/`LinearOrder`/`IsOrderedMonoid` instances above. -/
theorem gamma_isLinearOrderedAbelianGroup :
    (∀ a b c : GammaOf M, (a * b) * c = a * (b * c)) ∧
      (∀ a b : GammaOf M, a * b = b * a) ∧
      (∀ a : GammaOf M, 1 * a = a) ∧
      (∀ a : GammaOf M, a * a⁻¹ = 1) ∧
      (∀ a : GammaOf M, a ≤ a) ∧
      (∀ a b c : GammaOf M, a ≤ b → b ≤ c → a ≤ c) ∧
      (∀ a b : GammaOf M, a ≤ b → b ≤ a → a = b) ∧
      (∀ a b : GammaOf M, a ≤ b ∨ b ≤ a) ∧
      (∀ a b c : GammaOf M, a ≤ b → a * c ≤ b * c) ∧
      (∀ a b c : GammaOf M, a ≤ b → c * a ≤ c * b) :=
  ⟨gamma_mul_assoc, gamma_mul_comm, gamma_one_mul, fun a => mul_inv_cancel a,
   gamma_le_refl, gamma_le_trans, gamma_le_antisymm, gamma_le_total,
   gamma_mul_le_mul_right, gamma_mul_le_mul_left⟩

/-- Trichotomy on `Γ(M)` (`<` is the strict order derived from `≤`). -/
theorem gamma_lt_trichotomy (a b : GammaOf M) : a < b ∨ a = b ∨ b < a :=
  lt_trichotomy a b

/-- The quotient map `RV ∖ {0} → Γ(M)` is order-preserving and order-reflecting. -/
theorem gammaMk_le_iff' (a b : RVStar M) : gammaMk a ≤ gammaMk b ↔ iLe a.1 b.1 :=
  gammaMk_le_iff

/-- The identity of `Γ(M)` is the class of `1`, so `gammaMk a ≤ 1` iff `rv a ≤ rv 1`. -/
theorem gammaMk_le_one_iff {a : RVStar M} : gammaMk a ≤ 1 ↔ iLe a.1 iRVOne := by
  rw [show (1 : GammaOf M) = gammaMk (1 : RVStar M) from gammaMk_one_eq.symm, gammaMk_le_iff]
  rfl


/-! ## 7. `Γ(M)` as the coset space `(RV ∖ {0}) / K^×`, and the bridge from `rv` -/

/-- **Value classes are the cosets of `K^×`.**  Two nonzero `RV`-elements have the same
value iff their quotient is a unit; this is the paper's reading of `Γ(M)` as
`RV(M)^× / K^×(M)` (with `gammaMk_eq_one_iff_units` pinning down the kernel). -/
theorem gammaMk_eq_iff_units_mul {a b : RVStar M} :
    gammaMk a = gammaMk b ↔ iUnits (a * b⁻¹).1 := by
  rw [gammaMk_eq_iff_le]
  have hconv : (a * b⁻¹).1 = iRVMul a.1 (Transfer.iRVInv hM b.1) := rfl
  rw [hconv]
  have hbI : iRV (Transfer.iRVInv hM b.1) := Transfer.iRVInv_mem hM b.2.1
  have hbI0 : Transfer.iRVInv hM b.1 ≠ iRVZero := rvStar_inv_nonzero b.2
  have hkey : iRVMul b.1 (Transfer.iRVInv hM b.1) = iRVOne :=
    Transfer.rv_mul_inv_cancel_right hM b.2.1 b.2.2
  have h1 : iLe a.1 b.1 ↔ iLe (iRVMul a.1 (Transfer.iRVInv hM b.1)) iRVOne := by
    have h := RVCalc.le_mul_iff hM a.2.1 b.2.1 hbI hbI0
    rw [hkey] at h
    exact h
  have h2 : iLe b.1 a.1 ↔ iLe iRVOne (iRVMul a.1 (Transfer.iRVInv hM b.1)) := by
    have h := RVCalc.le_mul_iff hM b.2.1 a.2.1 hbI hbI0
    rw [hkey] at h
    exact h
  rw [h1, h2]
  have hx : iRV (iRVMul a.1 (Transfer.iRVInv hM b.1)) := Transfer.rv_mul_mem hM a.2.1 hbI
  have hx0 : iRVMul a.1 (Transfer.iRVInv hM b.1) ≠ iRVZero :=
    rvStar_mul_nonzero a.2 ⟨hbI, hbI0⟩
  constructor
  · rintro ⟨h₁, h₂⟩
    exact (RVCalc.units_iff_le_one hM hx hx0).mpr ⟨h₂, h₁⟩
  · intro hu
    have h' := (RVCalc.units_iff_le_one hM hx hx0).mp hu
    exact ⟨h'.2, h'.1⟩

/-- A nonzero field element, viewed as an element of `RV ∖ {0}` via `rv`.  (Bridge used by
the valuation direction d3: `Γ(M)` receives values from the `rv` of a field element.) -/
def rvStarOf {x : M} (hx : iVF x) (hx0 : x ≠ Transfer.iVFZero) : RVStar M :=
  ⟨iRv x, Transfer.rv_mem hM hx,
    fun h => hx0 (RVCalc.vf_eq_zero_of_rv_eq_zero hM hx h)⟩

/-- **The value of a nonzero field element in `Γ(M)`**: `x ↦ [rv x]`. -/
def gammaVal {x : M} (hx : iVF x) (hx0 : x ≠ Transfer.iVFZero) : GammaOf M :=
  gammaMk (rvStarOf hx hx0)

/-- `gammaVal` is `rv` followed by the quotient map: it computes on representatives. -/
theorem gammaVal_def {x : M} (hx : iVF x) (hx0 : x ≠ Transfer.iVFZero) :
    gammaVal hx hx0 = Quotient.mk (Cls M) (rvStarOf hx hx0) := rfl

/-- Two nonzero field elements have the same value in `Γ(M)` iff their `rv`'s are mutually
`≤` — i.e. `Γ`'s order is exactly `rv`'s. -/
theorem gammaVal_eq_iff_le {x y : M} (hx : iVF x) (hy : iVF y) (hx0 : x ≠ Transfer.iVFZero)
    (hy0 : y ≠ Transfer.iVFZero) :
    gammaVal hx hx0 = gammaVal hy hy0 ↔
      (iLe (iRv x) (iRv y) ∧ iLe (iRv y) (iRv x)) :=
  gammaMk_eq_iff_le


/-! ## 8. Strict monotonicity and a triviality criterion -/

/-- Multiplication by any element is strictly order-preserving on `Γ(M)`. -/
theorem gamma_lt_iff_mul_lt (a b c : GammaOf M) : a < b ↔ a * c < b * c := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge,
    show (a ≤ b) ↔ a * c ≤ b * c from gamma_le_iff_mul_le a b c,
    show (b ≤ a) ↔ b * c ≤ a * c from gamma_le_iff_mul_le b a c]

/-- **`Γ(M)` is trivial iff every nonzero `RV`-element is a unit** — i.e. iff
`RV ∖ {0} = K^×`, so that there is only one value class. -/
theorem gamma_subsingleton_iff : Subsingleton (GammaOf M) ↔ ∀ a : RVStar M, iUnits a.1 := by
  constructor
  · intro hsub a
    have h : gammaMk a = (1 : GammaOf M) := Subsingleton.elim _ _
    rw [← gammaMk_one_eq] at h
    exact (gammaMk_eq_one_iff_units).mp h
  · intro hunit
    have hone : iRV (iRVOne (M := M)) := Transfer.rv_one_mem hM
    have hall : ∀ a b : RVStar M, ClsRel a b := by
      intro a b
      have ha := (RVCalc.units_iff_le_one hM a.2.1 a.2.2).mp (hunit a)
      have hb := (RVCalc.units_iff_le_one hM b.2.1 b.2.2).mp (hunit b)
      exact ⟨RVCalc.le_trans_rv hM a.2.1 hone b.2.1 ha.2 hb.1,
        RVCalc.le_trans_rv hM b.2.1 hone a.2.1 hb.2 ha.1⟩
    refine ⟨fun x y => ?_⟩
    refine Quotient.inductionOn x (fun a => ?_)
    refine Quotient.inductionOn y (fun b => ?_)
    exact Quotient.sound (hall a b)

end

end SpecialTransformations.Milestone0.GammaGroup

/-! ## Axiom audit (order half, d2/m2) -/

#print axioms SpecialTransformations.Milestone0.GammaGroup.gammaOfCommGroup
#print axioms SpecialTransformations.Milestone0.GammaGroup.gammaOfLinearOrder
#print axioms SpecialTransformations.Milestone0.GammaGroup.gammaCovariantMulLeft
#print axioms SpecialTransformations.Milestone0.GammaGroup.gammaCovariantMulRight
#print axioms SpecialTransformations.Milestone0.GammaGroup.gammaIsOrderedMonoid
#print axioms SpecialTransformations.Milestone0.GammaGroup.gamma_isLinearOrderedAbelianGroup
#print axioms SpecialTransformations.Milestone0.GammaGroup.gammaMk_eq_one_iff_units
#print axioms SpecialTransformations.Milestone0.GammaGroup.gamma_le_iff_mul_le
#print axioms SpecialTransformations.Milestone0.GammaGroup.gammaMk_eq_iff_units_mul
#print axioms SpecialTransformations.Milestone0.GammaGroup.gammaVal_eq_iff_le
#print axioms SpecialTransformations.Milestone0.GammaGroup.gamma_lt_iff_mul_lt
#print axioms SpecialTransformations.Milestone0.GammaGroup.gamma_subsingleton_iff

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.GammaGroup.commGroupRVStar
#print axioms SpecialTransformations.Milestone0.GammaGroup.rvStar_mul_assoc
#print axioms SpecialTransformations.Milestone0.GammaGroup.rvStar_inv_mul_cancel
#print axioms SpecialTransformations.Milestone0.GammaGroup.units_ne_zero
#print axioms SpecialTransformations.Milestone0.GammaGroup.units_exists_inv
#print axioms SpecialTransformations.Milestone0.GammaGroup.units_mul
#print axioms SpecialTransformations.Milestone0.GammaGroup.iRVInv_units
#print axioms SpecialTransformations.Milestone0.GammaGroup.KStar
#print axioms SpecialTransformations.Milestone0.GammaGroup.rvStar_mul_one
#print axioms SpecialTransformations.Milestone0.GammaGroup.rvStar_mul_comm
