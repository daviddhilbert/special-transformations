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

end

end SpecialTransformations.Milestone0.GammaGroup

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
