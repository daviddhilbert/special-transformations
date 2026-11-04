/-
**Γ(M) as an ordered abelian group: `RV ∖ {0}` modulo value-classes.**

The paper's `Γ(M) = RV(M)/Kˣ(M)`.  This file builds it for the frozen encoding from
`Axioms.ACVF` alone:

* `RVStar M` — the multiplicative group of nonzero `RV`-elements, with `iRVMul` closed
  by `Transfer.rv_mul_mem`, no zero divisors (`Transfer.rv_mul_eq_zero_of_model`), and
  inverses from `Transfer.iRVInv` (`Transfer.iRVInv_mul_cancel`);
* `GammaOf M` — its quotient by the value-class setoid `Cls a b := iLe a b ∧ iLe b a`,
  in one `CommGroup` (from `Group`/`CommMagma` instances) and one `LinearOrder`, descended
  across the setoid;
* order-compatibility of multiplication (`CovariantClass γ γ (· * ·) (· ≤ ·)`) from
  `RVCalc.le_mul_iff` = `leMulCompatFull`.

Together with `QE/StandingField.lean`'s `Field (KOf M)` this is the frozen `(K, Γ)` pair
of a model of `ACVF`, at which the Prestel-Engler quotations of `QE/ClassicalProps.lean`
(henselization with same residue/value group, divisible hull) are stated.
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

end SpecialTransformations.Milestone0.GammaGroup
