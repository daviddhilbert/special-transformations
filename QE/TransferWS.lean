/-
The QF-type (Shoenfield) assembly **over the frozen fragment**, as statements.

The unrestricted versions live in `QE/Assembly_val.lean` (`TransferAt`, `NontrivialTransfer`,
`TrivialTransfer`, `CaseSeparation`, `QFTypeDetermines`, ~lines 7663–15657) and are aimed at
`HasQE` over *all* formulas of the encoding — a statement that is false, because ill-sorted terms
like `rv (rv x)` are unconstrained by `Axioms.ACVF` (three refutations are recorded in
`QE-PLAN.md`).  This file restates the same assembly over the well-sorted fragment, which is what
the frozen target `Milestone0/Encoding.lean`'s `HasQE` is about.

The sort discipline enters in exactly three places, and nowhere else: the parameter tuples, the
variable tuples, and the formula class on both sides of each implication.

`NontrivialTransferWS` is the **sharp test** of the guard repair: pushing the equivalence through
a quantifier requires the body's truth at elements outside the sort, because
`BoundedFormula.all` ranges over the whole carrier — the `JunkTrueAt` obstruction.

Check with (`.scratch2/sec3/` holds `Enc.olean`, a compiled `Milestone0/Encoding.lean`):

    cd .scratch2/sec3 && cp ../../QE/TransferWS.lean TWS.lean &&
      LEAN_PATH=$PWD:$LEAN_PATH lean TWS.lean
-/
import Enc

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace SpecialTransformations
namespace Milestone0
open LRV

/-- The valuation is **nontrivial in the paper's sense** (the hypothesis `axNontrivial` of
`ValPM.ACVF_val`), copied from `QE/Assembly_val.lean` because the two files carry separate copies
of the encoding: some nonzero `x ∈ VF` has value strictly below the value of `1`. -/
def IsNontrivialVF (M : Type) [LRV.Structure M] : Prop :=
  ∃ x : M, iVF x ∧ x ≠ iRVZero ∧ ¬ iLe (iRv iRVOne) (iRv x)

/-- The valuation is **trivial**: every element of the `VF` sort is `0` or has the value of `1`.
Copied from `QE/Assembly_val.lean`. -/
def IsTrivialVF (M : Type) [LRV.Structure M] : Prop :=
  ∀ x : M, iVF x → x = iRVZero ∨ iRv x = iRVOne

/-- **The transfer hypothesis at a class of models `P`, over the fragment**: two models of `T` in
the class, at sort-respecting tuples, which agree on all well-sorted *quantifier-free* formulas,
agree there on every well-sorted formula. -/
def TransferAtWS (P : (M : Type) → [LRV.Structure M] → Prop) (T : LRV.Theory) : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (M : Type) [LRV.Structure M] [Nonempty M], M ⊨ T → P M →
  ∀ (N : Type) [LRV.Structure N] [Nonempty N], N ⊨ T → P N →
  ∀ (v : α → M) (xs : Fin n → M) (w : α → N) (ys : Fin n → N),
    (∀ a, sortEval (sα a) (v a)) → (∀ i, sortEval (sn i) (xs i)) →
    (∀ a, sortEval (sα a) (w a)) → (∀ i, sortEval (sn i) (ys i)) →
    (∀ ψ : LRV.BoundedFormula α n, WellSorted sα sn ψ → ψ.IsQF →
      (ψ.Realize v xs ↔ ψ.Realize w ys)) →
    ∀ φ : LRV.BoundedFormula α n, WellSorted sα sn φ →
      (φ.Realize v xs ↔ φ.Realize w ys)

/-- **The nontrivial half of the transfer, over the fragment.**  This is where the paper's §4–§5
content lands when the assembly is read over the fragment instead of over all formulas. -/
def NontrivialTransferWS (T : LRV.Theory) : Prop := TransferAtWS IsNontrivialVF T

/-- **The trivial half**, likewise (proved for `ACVF` unconditionally in the unrestricted form:
`Assembly_val`'s `trivialTransfer_ACVF`). -/
def TrivialTransferWS (T : LRV.Theory) : Prop := TransferAtWS IsTrivialVF T

/-- **Separation of the two cases by well-sorted quantifier-free types**: a sorted tuple in a
nontrivial model and a sorted tuple in a trivial model never agree on all well-sorted QF formulas.
Without this the two transfers do not compose, because each compares models within one class. -/
def CaseSeparationWS (T : LRV.Theory) : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (M : Type) [LRV.Structure M] [Nonempty M], M ⊨ T →
  ∀ (N : Type) [LRV.Structure N] [Nonempty N], N ⊨ T →
  ∀ (v : α → M) (xs : Fin n → M) (w : α → N) (ys : Fin n → N),
    (∀ a, sortEval (sα a) (v a)) → (∀ i, sortEval (sn i) (xs i)) →
    (∀ a, sortEval (sα a) (w a)) → (∀ i, sortEval (sn i) (ys i)) →
    (∀ ψ : LRV.BoundedFormula α n, WellSorted sα sn ψ → ψ.IsQF →
      (ψ.Realize v xs ↔ ψ.Realize w ys)) →
    (IsNontrivialVF M ↔ IsNontrivialVF N)

section Frozen

variable (T : LRV.Theory)

/-- **`NontrivialTransferWS` for `ACVF`** — the sharp test of the guard repair, frozen as a target.
The proof must push the equivalence through the fragment's guarded quantifiers, which needs the
body to be true at elements outside the sort. -/
theorem nontrivialTransferWS_ACVF : NontrivialTransferWS Axioms.ACVF := by
  sorry

/-- The case split needs no fragment restriction: it speaks about one model.  (Unrestricted form
proved in `Assembly_val`.) -/
theorem caseSplit_ACVF : ∀ (M : Type) [LRV.Structure M] [Nonempty M], M ⊨ Axioms.ACVF →
    IsNontrivialVF M ∨ IsTrivialVF M := by
  sorry

end Frozen
