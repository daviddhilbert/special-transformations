/-
**The sorted-context fragment** (`VFT2`/`RVT2`/`QF2`/`QFq2`) — from swarm `smw1bwjo2` m6, ported to
the repaired encoding and verified here (compiled, 0 errors, no `sorry`).  This is the base the
`qfq_cover` work needs: a quantifier-free fragment over a *sorted* context `Fin n → SortTag` with
`RV`-sorted free variables (`RVT2.rvar`), next to `QFRes`'s all-`VF` fragment in `Assembly_val`.

Why it is a separate fragment and not `QFRes`: the frozen `HasQE` quantifies over every variable
context `Fin n → SortTag`, so a cover lemma has to speak about contexts with `RV`-sorted slots.  The
guards are `Fin.snoc sn s` — the same shape as the repaired `WellSorted.all`, so no renaming is
needed — and `wellSorted_all_guarded` discharges the new `GuardTrue` field from the fragment's own
`Occurs`, which is why the port went through the guard repair unchanged.

What is here: the realization prelude the frozen encoding leaves out, the two term families with
their `val`/`Val` semantics (`val_add`, `val_mul`, `val_rv`, …), `tmSort_toLRV` for both (the sort
of every fragment term), `QF2`/`QFq2` with `toRV`, `Eval`, `realize_toRV`, `wellSorted_toRV` and
closure under the connectives, plus `VFT2.val_mem`/`RVT2.val_mem` (the sort discipline) and the junk
conventions derived from `Axioms.ACVF` alone.

**What is NOT here** and is the remaining obligation: `qf2_cover` — that a well-sorted *quantifier-free*
formula over a sorted context is, at sorted tuples, equivalent to the image `q.toRV` of a `QF2` term.
The term extraction it needs (`TmSort sn t = some .vf → VFT2`, dually for `RV`) is the place where
`QE/MulNormalForm.lean` enters: an `RV` term built from `rvMul` and `kAdd` has to be flattened into
the fragment's `RVT2`, and off `Kˣ` that is exactly cancellation, which the normal form supplies.
See `QE/QF2Cover.lean` for the statement of the target.
-/
/-
Direction d6 (swarm smw1bwjo2, member m6): a quantifier-free fragment over a *sorted* context
with `RV`-sorted free variables, ported to the **repaired** encoding (`import Enc`), plus the
realization prelude that the frozen `Milestone0/Encoding.lean` does not carry.

The fragment is `QFRes2.VFT2 sn`, `RVT2 sn`, `QF2 sn`, `QFq2 sn` of `.ultramath/smw19wtoj/m3/QF2.lean`
(member m3 of an earlier swarm, built on that session's `Assembly_val`): `RV`-sorted free variables
next to the residue symbols, and guarded quantification over the *last* variable of the context,
whose sort pattern `Fin.snoc sn s` is exactly the shape of the repaired `WellSorted.all`.  Porting it
to the repaired encoding is where the guard repair bites: `WellSorted.all` now demands `GuardTrue`,
and `Milestone0/Encoding.lean`'s `wellSorted_all_guarded` discharges it from `Occurs (Fin.last m) s η`,
which is what the fragment's guards are.

Sections:
 0. realization prelude (`iVFZero`, `iVFOne`, `iKNeg` and the `Term.realize`/`Realize` lemmas that
    `Milestone0/Encoding.lean` leaves out; written for the current encoding, no model hypothesis);
 1-6. the fragment, its image in `Bf n`, `wellSorted_toRV`, `isQF_toRV`, `Eval`, `realize_toRV`
    for both fragments, and closure under the connectives — **no hypothesis on the model**.
-/
import Enc

open Classical
open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.Transfer

/-! ## 0a. The interpretations the frozen encoding does not name -/

/-- `0` of the `VF` sort -/
def iVFZero {M : Type} [LRV.Structure M] : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfZero fun i => i.elim0

/-- `1` of the `VF` sort -/
def iVFOne {M : Type} [LRV.Structure M] : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfOne fun i => i.elim0

/-! ## 0b. Realization of the `L_RV`-term constructors -/

theorem realize_tVFZero {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M) :
    (tVFZero (n := n)).realize v = iVFZero := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfZero
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iVFZero
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem realize_tVFOne {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M) :
    (tVFOne (n := n)).realize v = iVFOne := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfOne
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iVFOne
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem realize_tVFAdd {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M)
    (a b : Tm n) : (tVFAdd a b).realize v = iVFAdd (a.realize v) (b.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfAdd
      (fun i => Term.realize (L := LRV) v (![a, b] i)) = iVFAdd (a.realize v) (b.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a, b] i)) = ![a.realize v, b.realize v] from by
    funext i
    fin_cases i <;> simp]
  rfl

theorem realize_tVFMul {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M)
    (a b : Tm n) : (tVFMul a b).realize v = iVFMul (a.realize v) (b.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfMul
      (fun i => Term.realize (L := LRV) v (![a, b] i)) = iVFMul (a.realize v) (b.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a, b] i)) = ![a.realize v, b.realize v] from by
    funext i
    fin_cases i <;> simp]
  rfl

theorem realize_tVFNeg {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M)
    (a : Tm n) : (tVFNeg a).realize v = iVFNeg (a.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfNeg
      (fun i => Term.realize (L := LRV) v (![a] i)) = iVFNeg (a.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a] i)) = ![a.realize v] from by
    funext i
    fin_cases i
    simp]
  rfl

theorem realize_tRv {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M) (a : Tm n) :
    (tRv a).realize v = iRv (a.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvMap
      (fun i => Term.realize (L := LRV) v (![a] i)) = iRv (a.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a] i)) = ![a.realize v] from by
    funext i
    fin_cases i
    simp]
  rfl

theorem realize_pLe {M : Type} [LRV.Structure M] {n : ℕ} (a b : Tm n) (v : Empty → M)
    (x : Fin n → M) :
    (pLe a b).Realize v x ↔ iLe (a.realize (Sum.elim v x)) (b.realize (Sum.elim v x)) := by
  have h : (fun i => Term.realize (L := LRV) (Sum.elim v x) (![a, b] i))
      = ![a.realize (Sum.elim v x), b.realize (Sum.elim v x)] := by
    funext i
    fin_cases i <;> simp
  show FirstOrder.Language.Structure.RelMap (L := LRV) Rel.rvLe
      (fun i => Term.realize (L := LRV) (Sum.elim v x) (![a, b] i)) ↔ iLe
        (a.realize (Sum.elim v x)) (b.realize (Sum.elim v x))
  rw [h]
  rfl

theorem realize_tv {M : Type} [LRV.Structure M] {k : ℕ} (i : Fin k) (v : Empty → M)
    (x : Fin k → M) : (tv i.1 i.2).realize (Sum.elim v x) = x i := rfl

theorem pVF_realize {M : Type} [LRV.Structure M] {k : ℕ} (t : Tm k) (v : Empty → M)
    (x : Fin k → M) : (pVF t).Realize v x ↔ iVF (t.realize (Sum.elim v x)) := by
  show FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memVF
      (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      ↔ iVF (t.realize (Sum.elim v x))
  rw [show (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      = ![t.realize (Sum.elim v x)] from by
    funext i
    fin_cases i
    simp]
  rfl

theorem pRVsort_realize {M : Type} [LRV.Structure M] {k : ℕ} (t : Tm k) (v : Empty → M)
    (x : Fin k → M) : (pRVsort t).Realize v x ↔ iRV (t.realize (Sum.elim v x)) := by
  show FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memRV
      (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      ↔ iRV (t.realize (Sum.elim v x))
  rw [show (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      = ![t.realize (Sum.elim v x)] from by
    funext i
    fin_cases i
    simp]
  rfl

theorem sortPred_realize {M : Type} [LRV.Structure M] {k : ℕ} (s : SortTag) (t : Tm k)
    (v : Empty → M) (x : Fin k → M) :
    (sortPred s t).Realize v x ↔
      (match s with
        | .vf => iVF (t.realize (Sum.elim v x))
        | .rv => iRV (t.realize (Sum.elim v x))) := by
  cases s with
  | vf => exact pVF_realize t v x
  | rv => exact pRVsort_realize t v x

theorem realize_tRVZero {M : Type} [LRV.Structure M] {k : ℕ} (v : Empty ⊕ Fin k → M) :
    (tRVZero (n := k)).realize v = iRVZero := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvZero
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iRVZero
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem realize_tRVMul {M : Type} [LRV.Structure M] {k : ℕ} (v : Empty ⊕ Fin k → M)
    (a b : Tm k) : (tRVMul a b).realize v = iRVMul (a.realize v) (b.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvMul
      (fun i => Term.realize (L := LRV) v (![a, b] i)) = iRVMul (a.realize v) (b.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a, b] i))
      = ![a.realize v, b.realize v] from by
    funext i
    fin_cases i <;> simp]
  rfl

theorem pRV_realize {M : Type} [LRV.Structure M] {k : ℕ} (t : Tm k) (v : Empty → M)
    (x : Fin k → M) : (pRV t).Realize v x ↔ t.realize (Sum.elim v x) ≠ iRVZero := by
  simp only [pRV, pEq, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    realize_tRVZero]

theorem pUnits_realize {M : Type} [LRV.Structure M] {k : ℕ} (t : Tm k) (v : Empty → M)
    (x : Fin k → M) : (pUnits t).Realize v x ↔ iUnits (t.realize (Sum.elim v x)) := by
  show FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memUnits
      (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      ↔ iUnits (t.realize (Sum.elim v x))
  rw [show (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      = ![t.realize (Sum.elim v x)] from by
    funext i
    fin_cases i
    simp]
  rfl
end SpecialTransformations.Milestone0.Transfer

/-! ## 0c. The residue-field `-`, and the `RV`-sorted term constructors -/

namespace TrivCase

variable {M : Type} [LRV.Structure M]
open SpecialTransformations.Milestone0.Transfer

/-- The interpretation of the unary residue-field `-`; the frozen encoding has no such
definition (only `iKAdd`, `iRVMul`), so it is added here. -/
def iKNeg (x : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.kNeg ![x]

theorem realize_tKAdd {n : ℕ} (v : Empty ⊕ Fin n → M) (a b : Tm n) :
    (tKAdd a b).realize v = iKAdd (a.realize v) (b.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.kAdd
      (fun i => Term.realize (L := LRV) v (![a, b] i)) = iKAdd (a.realize v) (b.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a, b] i)) = ![a.realize v, b.realize v]
    from by funext i; fin_cases i <;> simp]
  rfl

theorem realize_tKNeg {n : ℕ} (v : Empty ⊕ Fin n → M) (a : Tm n) :
    (tKNeg a).realize v = iKNeg (a.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.kNeg
      (fun i => Term.realize (L := LRV) v (![a] i)) = iKNeg (a.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a] i)) = ![a.realize v]
    from by funext i; fin_cases i; simp]
  rfl

theorem realize_tRVOne {n : ℕ} (v : Empty ⊕ Fin n → M) :
    (tRVOne (n := n)).realize v = iRVOne := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvOne
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iRVOne
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem pInK_realize {k : ℕ} (t : Tm k) (v : Empty → M) (x : Fin k → M) :
    (pInK t).Realize v x ↔
      iUnits (t.realize (Sum.elim v x)) ∨ t.realize (Sum.elim v x) = iRVZero := by
  simp only [pInK, BoundedFormula.realize_sup, pUnits_realize, pEq,
    BoundedFormula.realize_bdEqual, realize_tRVZero]

@[simp] theorem realize_tv_nat {n : ℕ} (i : ℕ) (h : i < n) (v : Empty → M) (x : Fin n → M) :
    (tv i h).realize (Sum.elim v x) = x ⟨i, h⟩ := rfl
end TrivCase

namespace RVElim

variable {M : Type} [LRV.Structure M]

theorem realize_tv_last_snoc (k : ℕ) (v : Empty → M) (x : Fin k → M) (a : M) :
    (tv k (Nat.lt_succ_self k)).realize (Sum.elim v (Fin.snoc x a)) = a := by
  rw [TrivCase.realize_tv_nat,
    show (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k from rfl, Fin.snoc_last]
end RVElim

set_option linter.unusedSimpArgs false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.Transfer
namespace QFRes2

/-! ## 1. Terms over a sorted context -/

/-- `VF`-sorted terms over the sorted context `sn`. -/
inductive VFT2 {n : ℕ} (sn : Fin n → SortTag) : Type
  | var (i : Fin n) (h : sn i = .vf) : VFT2 sn
  | zero : VFT2 sn
  | one : VFT2 sn
  | add (a b : VFT2 sn) : VFT2 sn
  | neg (a : VFT2 sn) : VFT2 sn
  | mul (a b : VFT2 sn) : VFT2 sn

/-- `RV`-sorted terms over the sorted context `sn`, with a constructor for a free `RV`-sorted
variable next to the residue symbols. -/
inductive RVT2 {n : ℕ} (sn : Fin n → SortTag) : Type
  | rvar (j : Fin n) (h : sn j = .rv) : RVT2 sn
  | one : RVT2 sn
  | zero : RVT2 sn
  | mul (a b : RVT2 sn) : RVT2 sn
  | kAdd (a b : RVT2 sn) : RVT2 sn
  | kNeg (a : RVT2 sn) : RVT2 sn
  | rv (s : VFT2 sn) : RVT2 sn

namespace VFT2

variable {n : ℕ} {sn : Fin n → SortTag}

/-- The `L_RV`-term underlying a `VF`-term. -/
def toLRV : VFT2 sn → Tm n
  | var i _ => tv i.1 i.2
  | zero => tVFZero
  | one => tVFOne
  | add a b => tVFAdd a.toLRV b.toLRV
  | neg a => tVFNeg a.toLRV
  | mul a b => tVFMul a.toLRV b.toLRV

end VFT2

namespace RVT2

variable {n : ℕ} {sn : Fin n → SortTag}

/-- The `L_RV`-term underlying an `RV`-term. -/
def toLRV : RVT2 sn → Tm n
  | rvar j _ => tv j.1 j.2
  | one => tRVOne
  | zero => tRVZero
  | mul a b => tRVMul a.toLRV b.toLRV
  | kAdd a b => tKAdd a.toLRV b.toLRV
  | kNeg a => tKNeg a.toLRV
  | rv s => tRv s.toLRV

end RVT2

/-! ## 2. The value of a term at a tuple -/

namespace VFT2

variable {n : ℕ} {sn : Fin n → SortTag} {M : Type} [LRV.Structure M]

/-- The value of a `VF`-term at a tuple. -/
noncomputable def Val (s : VFT2 sn) (x : Fin n → M) : M :=
  (s.toLRV).realize (Sum.elim (default : Empty → M) x)

theorem val_var (i : Fin n) (h : sn i = .vf) (x : Fin n → M) :
    Val (var i h) x = x i := rfl

theorem val_zero (x : Fin n → M) : Val (zero (sn := sn)) x = iVFZero :=
  realize_tVFZero _

theorem val_one (x : Fin n → M) : Val (one (sn := sn)) x = iVFOne :=
  realize_tVFOne _

theorem val_add (a b : VFT2 sn) (x : Fin n → M) :
    Val (add a b) x = iVFAdd (Val a x) (Val b x) :=
  realize_tVFAdd _ _ _

theorem val_neg (a : VFT2 sn) (x : Fin n → M) :
    Val (neg a) x = iVFNeg (Val a x) :=
  realize_tVFNeg _ _

theorem val_mul (a b : VFT2 sn) (x : Fin n → M) :
    Val (mul a b) x = iVFMul (Val a x) (Val b x) :=
  realize_tVFMul _ _ _

end VFT2

namespace RVT2

variable {n : ℕ} {sn : Fin n → SortTag} {M : Type} [LRV.Structure M]

/-- The value of an `RV`-term at a tuple. -/
noncomputable def Val (u : RVT2 sn) (x : Fin n → M) : M :=
  (u.toLRV).realize (Sum.elim (default : Empty → M) x)

theorem val_rvar (j : Fin n) (h : sn j = .rv) (x : Fin n → M) :
    Val (rvar j h) x = x j := rfl

theorem val_one (x : Fin n → M) : Val (one (sn := sn)) x = iRVOne :=
  TrivCase.realize_tRVOne _

theorem val_zero (x : Fin n → M) : Val (zero (sn := sn)) x = iRVZero :=
  realize_tRVZero _

theorem val_mul (a b : RVT2 sn) (x : Fin n → M) :
    Val (mul a b) x = iRVMul (Val a x) (Val b x) :=
  realize_tRVMul _ _ _

theorem val_kAdd (a b : RVT2 sn) (x : Fin n → M) :
    Val (kAdd a b) x = iKAdd (Val a x) (Val b x) :=
  TrivCase.realize_tKAdd _ _ _

theorem val_kNeg (a : RVT2 sn) (x : Fin n → M) :
    Val (kNeg a) x = TrivCase.iKNeg (Val a x) :=
  TrivCase.realize_tKNeg _ _

theorem val_rv (s : VFT2 sn) (x : Fin n → M) :
    Val (rv s) x = iRv (VFT2.Val s x) :=
  realize_tRv _ _

end RVT2

/-! ## 3. The sort of a term -/

namespace VFT2

variable {n : ℕ} {sn : Fin n → SortTag}

/-- A `VF`-term has sort `VF`. -/
theorem tmSort_toLRV (s : VFT2 sn) :
    TmSort (α := Empty) (fun _ => SortTag.vf) sn s.toLRV = some .vf := by
  induction s with
  | var i h => show some (sn i) = some .vf; rw [h]
  | zero => exact tmSort_vfZero (fun _ : Empty => SortTag.vf) sn
  | one => exact tmSort_vfOne (fun _ : Empty => SortTag.vf) sn
  | add a b iha ihb => exact (tmSort_vfAdd (fun _ : Empty => SortTag.vf) sn).mpr ⟨iha, ihb⟩
  | neg a iha => exact (tmSort_vfNeg (fun _ : Empty => SortTag.vf) sn).mpr iha
  | mul a b iha ihb => exact (tmSort_vfMul (fun _ : Empty => SortTag.vf) sn).mpr ⟨iha, ihb⟩

end VFT2

namespace RVT2

variable {n : ℕ} {sn : Fin n → SortTag}

/-- An `RV`-term has sort `RV`. -/
theorem tmSort_toLRV (u : RVT2 sn) :
    TmSort (α := Empty) (fun _ => SortTag.vf) sn u.toLRV = some .rv := by
  induction u with
  | rvar j h => show some (sn j) = some .rv; rw [h]
  | one => exact tmSort_rvOne (fun _ : Empty => SortTag.vf) sn
  | zero => exact tmSort_rvZero (fun _ : Empty => SortTag.vf) sn
  | mul a b iha ihb => exact (tmSort_rvMul (fun _ : Empty => SortTag.vf) sn).mpr ⟨iha, ihb⟩
  | kAdd a b iha ihb => exact (tmSort_kAdd (fun _ : Empty => SortTag.vf) sn).mpr ⟨iha, ihb⟩
  | kNeg a iha => exact (tmSort_kNeg (fun _ : Empty => SortTag.vf) sn).mpr iha
  | rv s => exact (tmSort_tRv (fun _ : Empty => SortTag.vf) sn).mpr (s.tmSort_toLRV)

end RVT2

end QFRes2
end SpecialTransformations.Milestone0.Transfer

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.Transfer
namespace QFRes2

/-! ## 4. The quantifier-free fragment -/

/-- Quantifier-free formulas of the sorted context `sn`: the atoms of `L_RV` at well-sorted terms,
and implications. -/
inductive QF2 {n : ℕ} (sn : Fin n → SortTag) : Type
  | falsum : QF2 sn
  | eqVF (a b : VFT2 sn) : QF2 sn
  | inVF (a : VFT2 sn) : QF2 sn
  | eqRV (u w : RVT2 sn) : QF2 sn
  | leRV (u w : RVT2 sn) : QF2 sn
  | unitRV (u : RVT2 sn) : QF2 sn
  | neRV (u : RVT2 sn) : QF2 sn
  | inRV (u : RVT2 sn) : QF2 sn
  | imp (a b : QF2 sn) : QF2 sn

namespace QF2

variable {n : ℕ} {sn : Fin n → SortTag}

/-- The image of the fragment in `L_RV`. -/
def toRV : QF2 sn → Bf n
  | falsum => BoundedFormula.falsum
  | eqVF a b => pEq a.toLRV b.toLRV
  | inVF a => pVF a.toLRV
  | eqRV u w => pEq u.toLRV w.toLRV
  | leRV u w => pLe u.toLRV w.toLRV
  | unitRV u => pUnits u.toLRV
  | neRV u => pRV u.toLRV
  | inRV u => pRVsort u.toLRV
  | imp a b => BoundedFormula.imp a.toRV b.toRV

/-! ### The intended meaning -/

section Semantics

variable {M : Type} [LRV.Structure M]

/-- The intended meaning of a `QF2`-formula at a tuple: the atoms are read at `iVF`, `iLe`,
`iUnits`, …, i.e. at the model's own interpretation of `L_RV`. -/
def Eval (x : Fin n → M) : QF2 sn → Prop
  | falsum => False
  | eqVF a b => VFT2.Val a x = VFT2.Val b x
  | inVF a => iVF (VFT2.Val a x)
  | eqRV u w => RVT2.Val u x = RVT2.Val w x
  | leRV u w => iLe (RVT2.Val u x) (RVT2.Val w x)
  | unitRV u => iUnits (RVT2.Val u x)
  | neRV u => RVT2.Val u x ≠ iRVZero
  | inRV u => iRV (RVT2.Val u x)
  | imp a b => Eval x a → Eval x b

/-- **The semantic contract of `toRV`**: the `L_RV`-formula realizes exactly the intended
meaning.  No hypothesis on the model. -/
theorem realize_toRV (q : QF2 sn) (x : Fin n → M) :
    (q.toRV).Realize (default : Empty → M) x ↔ q.Eval x := by
  induction q with
  | falsum => exact Iff.rfl
  | eqVF a b =>
    show ((a.toLRV).bdEqual b.toLRV).Realize (default : Empty → M) x ↔ _
    exact BoundedFormula.realize_bdEqual .. |>.trans Iff.rfl
  | inVF a =>
    show (pVF a.toLRV).Realize (default : Empty → M) x ↔ _
    exact pVF_realize a.toLRV _ x
  | eqRV u w =>
    show ((u.toLRV).bdEqual w.toLRV).Realize (default : Empty → M) x ↔ _
    exact BoundedFormula.realize_bdEqual .. |>.trans Iff.rfl
  | leRV u w =>
    show (pLe u.toLRV w.toLRV).Realize (default : Empty → M) x ↔ _
    exact realize_pLe u.toLRV w.toLRV _ x
  | unitRV u =>
    show (pUnits u.toLRV).Realize (default : Empty → M) x ↔ _
    exact pUnits_realize u.toLRV _ x
  | neRV u =>
    show (pRV u.toLRV).Realize (default : Empty → M) x ↔ _
    rw [pRV, BoundedFormula.realize_not, pEq, BoundedFormula.realize_bdEqual,
      realize_tRVZero]
    exact Iff.rfl
  | inRV u =>
    show (pRVsort u.toLRV).Realize (default : Empty → M) x ↔ _
    exact pRVsort_realize u.toLRV _ x
  | imp a b iha ihb =>
    show (BoundedFormula.imp a.toRV b.toRV).Realize (default : Empty → M) x ↔ _
    rw [BoundedFormula.realize_imp, iha, ihb]
    exact Iff.rfl

end Semantics

/-! ### Closure under the connectives -/

/-- `⊥` -/
def bot : QF2 sn := falsum

/-- `⊤` -/
def top : QF2 sn := imp falsum falsum

/-- negated formula -/
def neg (q : QF2 sn) : QF2 sn := imp q falsum

/-- conjunction -/
def inf (a b : QF2 sn) : QF2 sn := imp (imp a (imp b falsum)) falsum

/-- disjunction -/
def sup (a b : QF2 sn) : QF2 sn := imp (imp a falsum) b

section Semantics

variable {M : Type} [LRV.Structure M]

theorem eval_bot (x : Fin n → M) : ¬ (bot (sn := sn)).Eval x := fun h => h

theorem eval_top (x : Fin n → M) : (top (sn := sn)).Eval x := fun h => h

theorem eval_neg (q : QF2 sn) (x : Fin n → M) : (q.neg).Eval x ↔ ¬ q.Eval x := Iff.rfl

theorem eval_inf (a b : QF2 sn) (x : Fin n → M) :
    (inf a b).Eval x ↔ a.Eval x ∧ b.Eval x := by
  show ((a.Eval x → b.Eval x → False) → False) ↔ _
  tauto

theorem eval_sup (a b : QF2 sn) (x : Fin n → M) :
    (sup a b).Eval x ↔ a.Eval x ∨ b.Eval x := by
  show ((a.Eval x → False) → b.Eval x) ↔ _
  tauto

end Semantics

theorem toRV_bot : (bot (sn := sn)).toRV = (⊥ : Bf n) := rfl

theorem toRV_top : (top (sn := sn)).toRV = (⊤ : Bf n) := rfl

theorem toRV_neg (q : QF2 sn) : q.neg.toRV = ∼q.toRV := rfl

theorem toRV_inf (a b : QF2 sn) : (inf a b).toRV = (a.toRV ⊓ b.toRV) := rfl

theorem toRV_sup (a b : QF2 sn) : (sup a b).toRV = (a.toRV ⊔ b.toRV) := rfl

theorem toRV_imp (a b : QF2 sn) :
    (imp a b).toRV = BoundedFormula.imp a.toRV b.toRV := rfl

end QF2

end QFRes2
end SpecialTransformations.Milestone0.Transfer

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.Transfer
namespace QFRes2
namespace QF2

variable {n : ℕ} {sn : Fin n → SortTag}

/-! ## 5. The image is well-sorted -/

/-- **`QF2.toRV` is well-sorted** for the encoding's sort discipline, with no hypothesis on the
model: this is what the frozen `HasQE` asks of its witness. -/
theorem wellSorted_toRV (q : QF2 sn) :
    WellSorted (α := Empty) (fun _ => SortTag.vf) sn q.toRV := by
  induction q with
  | falsum => exact WellSorted.falsum sn
  | eqVF a b =>
    exact wellSorted_pEqG (fun _ : Empty => SortTag.vf) sn a.tmSort_toLRV b.tmSort_toLRV
  | inVF a =>
    exact wellSorted_pVFG (fun _ : Empty => SortTag.vf) sn a.tmSort_toLRV
  | eqRV u w =>
    exact wellSorted_pEqG (fun _ : Empty => SortTag.vf) sn u.tmSort_toLRV w.tmSort_toLRV
  | leRV u w =>
    exact wellSorted_pLeG (fun _ : Empty => SortTag.vf) sn u.tmSort_toLRV w.tmSort_toLRV
  | unitRV u =>
    exact wellSorted_pUnitsG (fun _ : Empty => SortTag.vf) sn u.tmSort_toLRV
  | neRV u =>
    exact WellSorted.imp sn
      (wellSorted_pEqG (fun _ : Empty => SortTag.vf) sn u.tmSort_toLRV
        (tmSort_rvZero (fun _ : Empty => SortTag.vf) sn))
      (WellSorted.falsum sn)
  | inRV u =>
    exact wellSorted_pRVG (fun _ : Empty => SortTag.vf) sn u.tmSort_toLRV
  | imp a b iha ihb => exact WellSorted.imp sn iha ihb

/-- **The quantifier-free part of the fragment is quantifier-free.** -/
theorem isQF_toRV (q : QF2 sn) : q.toRV.IsQF := by
  induction q with
  | falsum => exact BoundedFormula.IsQF.falsum
  | eqVF a b => exact (BoundedFormula.IsAtomic.equal _ _).isQF
  | inVF a => exact (BoundedFormula.IsAtomic.rel Rel.memVF ![a.toLRV]).isQF
  | eqRV u w => exact (BoundedFormula.IsAtomic.equal _ _).isQF
  | leRV u w => exact (BoundedFormula.IsAtomic.rel Rel.rvLe ![u.toLRV, w.toLRV]).isQF
  | unitRV u => exact (BoundedFormula.IsAtomic.rel Rel.memUnits ![u.toLRV]).isQF
  | neRV u => exact BoundedFormula.IsQF.not ((BoundedFormula.IsAtomic.equal _ _).isQF)
  | inRV u => exact (BoundedFormula.IsAtomic.rel Rel.memRV ![u.toLRV]).isQF
  | imp a b iha ihb => exact BoundedFormula.IsQF.imp iha ihb

end QF2

/-! ## 6. Guarded quantification over the last variable of a sorted context -/

/-- `QF2` closed under guarded quantification over the *last* variable of the context, whose sort
may be either `VF` or `RV`.  The shape `Fin.snoc sn s` is exactly the shape of the encoding's
`WellSorted.all`, so no variable renaming is needed.

The context is an index (not a parameter) because `allVF`/`allRV` change it. -/
inductive QFq2 : {n : ℕ} → (Fin n → SortTag) → Type
  | ofQF {n : ℕ} {sn : Fin n → SortTag} (q : QF2 sn) : QFq2 sn
  | imp {n : ℕ} {sn : Fin n → SortTag} (a b : QFq2 sn) : QFq2 sn
  | allVF {n : ℕ} {sn : Fin n → SortTag} (q : QFq2 (Fin.snoc sn .vf)) : QFq2 sn
  | allRV {n : ℕ} {sn : Fin n → SortTag} (q : QFq2 (Fin.snoc sn .rv)) : QFq2 sn

namespace QFq2

/-- The image of the fragment in `L_RV`. -/
def toRV {n : ℕ} {sn : Fin n → SortTag} : QFq2 sn → Bf n
  | ofQF q => QF2.toRV q
  | imp a b => BoundedFormula.imp (toRV a) (toRV b)
  | allVF q => BoundedFormula.all
      (BoundedFormula.imp (pVF (tv n (Nat.lt_succ_self n))) (toRV q))
  | allRV q => BoundedFormula.all
      (BoundedFormula.imp (pRVsort (tv n (Nat.lt_succ_self n))) (toRV q))

/-! ### The defining equations of `toRV` (with the index `n` of the *lemma*) -/

theorem toRV_ofQF {n : ℕ} {sn : Fin n → SortTag} (q : QF2 sn) :
    (ofQF q : QFq2 sn).toRV = q.toRV := rfl

theorem toRV_imp {n : ℕ} {sn : Fin n → SortTag} (a b : QFq2 sn) :
    (imp a b).toRV = BoundedFormula.imp a.toRV b.toRV := rfl

theorem toRV_allVF {n : ℕ} {sn : Fin n → SortTag} (q : QFq2 (Fin.snoc sn .vf)) :
    (allVF q).toRV
      = BoundedFormula.all (BoundedFormula.imp (pVF (tv n (Nat.lt_succ_self n))) q.toRV) := rfl

theorem toRV_allRV {n : ℕ} {sn : Fin n → SortTag} (q : QFq2 (Fin.snoc sn .rv)) :
    (allRV q).toRV
      = BoundedFormula.all (BoundedFormula.imp (pRVsort (tv n (Nat.lt_succ_self n))) q.toRV) := rfl

/-! ### The sort of the last variable -/

theorem tmSort_last_vf {n : ℕ} (sn : Fin n → SortTag) :
    TmSort (α := Empty) (fun _ => SortTag.vf) (Fin.snoc sn SortTag.vf)
      (Term.var (Sum.inr (Fin.last n))) = some SortTag.vf := by
  rw [tmSort_var_inr, Fin.snoc_last]

theorem tmSort_last_rv {n : ℕ} (sn : Fin n → SortTag) :
    TmSort (α := Empty) (fun _ => SortTag.vf) (Fin.snoc sn SortTag.rv)
      (Term.var (Sum.inr (Fin.last n))) = some SortTag.rv := by
  rw [tmSort_var_inr, Fin.snoc_last]

theorem wellSorted_pVF_last {n : ℕ} (sn : Fin n → SortTag) :
    WellSorted (α := Empty) (fun _ => SortTag.vf) (Fin.snoc sn SortTag.vf)
      (pVF (tv n (Nat.lt_succ_self n))) :=
  wellSorted_pVFG (fun _ : Empty => SortTag.vf) _ (tmSort_last_vf sn)

theorem wellSorted_pRV_last {n : ℕ} (sn : Fin n → SortTag) :
    WellSorted (α := Empty) (fun _ => SortTag.vf) (Fin.snoc sn SortTag.rv)
      (pRVsort (tv n (Nat.lt_succ_self n))) :=
  wellSorted_pRVG (fun _ : Empty => SortTag.vf) _ (tmSort_last_rv sn)

/-! ### The intended meaning -/

variable {M : Type} [LRV.Structure M]

theorem realize_pVF_last {n : ℕ} (x : Fin n → M) (a : M) :
    (pVF (tv n (Nat.lt_succ_self n))).Realize (default : Empty → M) (Fin.snoc x a)
      ↔ iVF a := by
  rw [pVF_realize, RVElim.realize_tv_last_snoc]

theorem realize_pRVsort_last {n : ℕ} (x : Fin n → M) (a : M) :
    (pRVsort (tv n (Nat.lt_succ_self n))).Realize (default : Empty → M) (Fin.snoc x a)
      ↔ iRV a := by
  rw [pRVsort_realize, RVElim.realize_tv_last_snoc]

/-- The intended meaning of a `QFq2`-formula. -/
def Eval {n : ℕ} {sn : Fin n → SortTag} (x : Fin n → M) : QFq2 sn → Prop
  | ofQF q => q.Eval x
  | imp a b => Eval x a → Eval x b
  | allVF q => ∀ a, iVF a → Eval (Fin.snoc x a) q
  | allRV q => ∀ a, iRV a → Eval (Fin.snoc x a) q

theorem eval_ofQF {n : ℕ} {sn : Fin n → SortTag} (q : QF2 sn) (x : Fin n → M) :
    (ofQF q : QFq2 sn).Eval x ↔ q.Eval x := Iff.rfl

theorem eval_imp {n : ℕ} {sn : Fin n → SortTag} (a b : QFq2 sn) (x : Fin n → M) :
    (imp a b).Eval x ↔ (a.Eval x → b.Eval x) := Iff.rfl

theorem eval_allVF {n : ℕ} {sn : Fin n → SortTag} (q : QFq2 (Fin.snoc sn .vf))
    (x : Fin n → M) :
    (allVF q).Eval x ↔ ∀ a, iVF a → q.Eval (Fin.snoc x a) := Iff.rfl

theorem eval_allRV {n : ℕ} {sn : Fin n → SortTag} (q : QFq2 (Fin.snoc sn .rv))
    (x : Fin n → M) :
    (allRV q).Eval x ↔ ∀ a, iRV a → q.Eval (Fin.snoc x a) := Iff.rfl

/-- **The semantic contract of `QFq2.toRV`**: the `L_RV`-formula realizes exactly the intended
meaning, with the sort hypotheses on the bound variables built into the guards. -/
theorem realize_toRV {n : ℕ} {sn : Fin n → SortTag} (q : QFq2 sn) :
    ∀ x : Fin n → M, (q.toRV).Realize (default : Empty → M) x ↔ q.Eval x := by
  induction q with
  | ofQF q => intro x; exact q.realize_toRV x
  | imp a b iha ihb =>
    intro x
    rw [toRV_imp, BoundedFormula.realize_imp, iha x, ihb x]
    exact Iff.rfl
  | allVF q ih =>
    intro x
    rw [toRV_allVF, BoundedFormula.realize_all]
    constructor
    · intro h a ha
      exact (ih (Fin.snoc x a)).mp
        ((BoundedFormula.realize_imp).mp (h a) ((realize_pVF_last x a).mpr ha))
    · intro h a
      exact (BoundedFormula.realize_imp).mpr
        (fun hg => (ih (Fin.snoc x a)).mpr (h a ((realize_pVF_last x a).mp hg)))
  | allRV q ih =>
    intro x
    rw [toRV_allRV, BoundedFormula.realize_all]
    constructor
    · intro h a ha
      exact (ih (Fin.snoc x a)).mp
        ((BoundedFormula.realize_imp).mp (h a) ((realize_pRVsort_last x a).mpr ha))
    · intro h a
      exact (BoundedFormula.realize_imp).mpr
        (fun hg => (ih (Fin.snoc x a)).mpr (h a ((realize_pRVsort_last x a).mp hg)))

/-! ### Closure of `QFq2` under the connectives -/

/-- `⊥` -/
def bot {n : ℕ} {sn : Fin n → SortTag} : QFq2 sn := ofQF QF2.bot

/-- `⊤` -/
def top {n : ℕ} {sn : Fin n → SortTag} : QFq2 sn := ofQF QF2.top

/-- negation -/
def neg {n : ℕ} {sn : Fin n → SortTag} (q : QFq2 sn) : QFq2 sn := imp q bot

/-- conjunction -/
def inf {n : ℕ} {sn : Fin n → SortTag} (a b : QFq2 sn) : QFq2 sn :=
  imp (imp a (imp b bot)) bot

/-- disjunction -/
def sup {n : ℕ} {sn : Fin n → SortTag} (a b : QFq2 sn) : QFq2 sn := imp (imp a bot) b

theorem eval_bot {n : ℕ} {sn : Fin n → SortTag} (x : Fin n → M) :
    ¬ (bot (n := n) (sn := sn)).Eval x := fun h => h

theorem eval_top {n : ℕ} {sn : Fin n → SortTag} (x : Fin n → M) :
    (top (n := n) (sn := sn)).Eval x := fun h => h

theorem eval_neg {n : ℕ} {sn : Fin n → SortTag} (q : QFq2 sn) (x : Fin n → M) :
    (neg q).Eval x ↔ ¬ q.Eval x := Iff.rfl

theorem eval_inf {n : ℕ} {sn : Fin n → SortTag} (a b : QFq2 sn) (x : Fin n → M) :
    (inf a b).Eval x ↔ a.Eval x ∧ b.Eval x := by
  show ((a.Eval x → b.Eval x → False) → False) ↔ _
  tauto

theorem eval_sup {n : ℕ} {sn : Fin n → SortTag} (a b : QFq2 sn) (x : Fin n → M) :
    (sup a b).Eval x ↔ a.Eval x ∨ b.Eval x := by
  show ((a.Eval x → False) → b.Eval x) ↔ _
  tauto

/-! ### The image is well-sorted -/

theorem wellSorted_allVF {n : ℕ} {sn : Fin n → SortTag} (q : QFq2 (Fin.snoc sn .vf))
    (ih : WellSorted (α := Empty) (fun _ => SortTag.vf) (Fin.snoc sn .vf) q.toRV) :
    WellSorted (α := Empty) (fun _ => SortTag.vf) sn (allVF q).toRV := by
  rw [toRV_allVF]
  refine wellSorted_all_guarded (sα := fun _ : Empty => SortTag.vf) (sn := sn) (s := .vf)
    (η := pVF (tv n (Nat.lt_succ_self n))) (ψ := q.toRV) ?_ ih ?_
  · exact wellSorted_pVF_last sn
  · exact occurs_self Empty (Fin.last n) .vf

theorem wellSorted_allRV {n : ℕ} {sn : Fin n → SortTag} (q : QFq2 (Fin.snoc sn .rv))
    (ih : WellSorted (α := Empty) (fun _ => SortTag.vf) (Fin.snoc sn .rv) q.toRV) :
    WellSorted (α := Empty) (fun _ => SortTag.vf) sn (allRV q).toRV := by
  rw [toRV_allRV]
  refine wellSorted_all_guarded (sα := fun _ : Empty => SortTag.vf) (sn := sn) (s := .rv)
    (η := pRVsort (tv n (Nat.lt_succ_self n))) (ψ := q.toRV) ?_ ih ?_
  · exact wellSorted_pRV_last sn
  · exact occurs_self Empty (Fin.last n) .rv

/-- **`QFq2.toRV` is well-sorted**: the guards are `x ∈ VF` / `x ∈ RV` at the last variable, which
is precisely the `GuardsLast` condition of `WellSorted.all`. -/
theorem wellSorted_toRV {n : ℕ} {sn : Fin n → SortTag} (q : QFq2 sn) :
    WellSorted (α := Empty) (fun _ => SortTag.vf) sn q.toRV := by
  induction q with
  | ofQF q => rw [toRV_ofQF]; exact q.wellSorted_toRV
  | imp a b iha ihb => rw [toRV_imp]; exact WellSorted.imp _ iha ihb
  | allVF q ih => exact wellSorted_allVF q ih
  | allRV q ih => exact wellSorted_allRV q ih

end QFq2

end QFRes2

end SpecialTransformations.Milestone0.Transfer

/-! ## 7. The semantic core: sort closure and the `RV` multiplicative dictionary

Everything in this section is a consequence of `Axioms.ACVF`; nothing is assumed.  It is the part
of d1 (`SortSound.lean`) that the `RV`-side of the mixed-context cover needs, kept local so that
this file is self-contained. -/

namespace SpecialTransformations.Milestone0.Transfer

variable {M : Type} [LRV.Structure M]

theorem sentence_realize {M : Type} [LRV.Structure M] {T : LRV.Theory} (hM : M ⊨ T)
    {φ : LRV.Sentence} (hmem : φ ∈ T) : M ⊨ φ :=
  hM.realize_of_mem φ hmem
/-! ### Membership of the axioms, and closure of the `VF` sort -/

theorem sortedHyps_foldr_realize {M : Type} [LRV.Structure M] {k : ℕ} (ss : Fin k → SortTag)
    (l : List (Fin k)) (v : Empty → M) (x : Fin k → M) :
    (l.foldr (fun i acc => sortPred (ss i) (tv i.1 i.2) ⊓ acc) ⊤).Realize v x
      ↔ ∀ i ∈ l, (match ss i with
          | .vf => iVF (x i)
          | .rv => iRV (x i)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, BoundedFormula.realize_inf, ih]
    have hhead : (sortPred (ss a) (tv a.1 a.2)).Realize v x
        ↔ (match ss a with | .vf => iVF (x a) | .rv => iRV (x a)) := by
      rw [sortPred_realize, realize_tv]
    rw [hhead]
    constructor
    · rintro ⟨ha, hall⟩ i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact ha
      · exact hall i hi
    · intro h
      exact ⟨h a List.mem_cons_self, fun i hi => h i (List.mem_cons_of_mem a hi)⟩

theorem sortedHyps_realize {M : Type} [LRV.Structure M] {k : ℕ} (ss : Fin k → SortTag)
    (v : Empty → M) (x : Fin k → M) :
    (sortedHyps ss).Realize v x ↔ ∀ i, (match ss i with
        | .vf => iVF (x i)
        | .rv => iRV (x i)) := by
  rw [sortedHyps, sortedHyps_foldr_realize]
  constructor
  · intro h i
    exact h i (List.mem_finRange i)
  · intro h i _
    exact h i

theorem allSorted_realize {M : Type} [LRV.Structure M] {T : LRV.Theory} (hM : M ⊨ T)
    {k : ℕ} {ss : Fin k → SortTag} {φ : Bf k} (hmem : allSorted ss φ ∈ T) :
    ∀ x : Fin k → M, (∀ i, (match ss i with
        | .vf => iVF (x i)
        | .rv => iRV (x i)))
      → @BoundedFormula.Realize LRV M _ Empty k φ (default : Empty → M) x := by
  intro x hx
  have h := hM.realize_of_mem (allSorted ss φ) hmem
  simp only [allSorted, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_imp] at h
  exact h x ((sortedHyps_realize ss (default : Empty → M) x).mpr hx)

theorem allOne_realize {M : Type} [LRV.Structure M] {T : LRV.Theory} (hM : M ⊨ T)
    {φ : Bf 1} (hmem : allOne φ ∈ T) :
    ∀ x : Fin 1 → M,
      @BoundedFormula.Realize LRV M _ Empty 1 φ (default : Empty → M) x := by
  intro x
  have h := hM.realize_of_mem (allOne φ) hmem
  simp only [allOne, Sentence.Realize, BoundedFormula.realize_alls] at h
  exact h x

theorem mem_ACVF_sortClosure {s : LRV.Sentence} (h : s ∈ Axioms.sortClosure) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.sortAxioms, Set.mem_union]
  tauto

theorem mem_ACVF_rvGroup {s : LRV.Sentence} (h : s ∈ Axioms.rvGroup) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union] at *
  tauto

theorem mem_ACVF_repairRV {s : LRV.Sentence} (h : s ∈ Axioms.repairRV) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

theorem rv_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iRV (iRv x) := by
  have hmem : allSorted ![.vf] (pRVsort (tRv &0)) ∈ Axioms.ACVF :=
    mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList, Axioms.sdRv])
  have h := allSorted_realize hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simpa only [pRVsort_realize, realize_tRv, realize_tv, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Matrix.cons_val_zero] using h

/-! ### The seven axioms for the extracted predicate -/

theorem mem_ACVF_sdRv : Axioms.sdRv ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem rv_zero_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iRV (iRVZero (M := M)) := by
  have h := sentence_realize hM (φ := Axioms.sdRVZero)
    (mem_ACVF_sortClosure (s := Axioms.sdRVZero) (by simp [Axioms.sortClosure, Axioms.ofList]))
  rw [Axioms.sdRVZero, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pRVsort_realize, realize_tRVZero] at h
  exact h

theorem realize_tRVOne_T {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M) :
    (tRVOne (n := n)).realize v = iRVOne := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvOne
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iRVOne
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem rv_one_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iRV (iRVOne (M := M)) := by
  have h := sentence_realize hM (φ := Axioms.sdRVOne)
    (mem_ACVF_sortClosure (s := Axioms.sdRVOne) (by simp [Axioms.sortClosure, Axioms.ofList]))
  rw [Axioms.sdRVOne, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pRVsort_realize, realize_tRVOne_T] at h
  exact h

theorem rv_mul_mem (hM : M ⊨ Axioms.ACVF) {a b : M} (ha : iRV a) (hb : iRV b) :
    iRV (iRVMul a b) := by
  have hmem : Axioms.sdRVMul ∈ Axioms.ACVF :=
    mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])
  have h := allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv])
    (φ := (pRVsort (tRVMul &0 &1))) hmem ![a, b] (by intro i; fin_cases i <;> simp [ha, hb])
  simpa only [Axioms.sdRVMul, pRVsort_realize, realize_tRVMul, realize_tv, Term.realize_var,
    Sum.elim_inr, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using h
end SpecialTransformations.Milestone0.Transfer

/-! ### 7a. Membership of the specific axioms used below -/

namespace SpecialTransformations.Milestone0.Transfer

theorem mem_ACVF_of_sortClosure {s : LRV.Sentence} (h : s ∈ Axioms.sortClosure) : s ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure h

theorem mem_ACVF_of_rvGroup {s : LRV.Sentence} (h : s ∈ Axioms.rvGroup) : s ∈ Axioms.ACVF :=
  mem_ACVF_rvGroup h

theorem mem_ACVF_of_repairRV {s : LRV.Sentence} (h : s ∈ Axioms.repairRV) : s ∈ Axioms.ACVF :=
  mem_ACVF_repairRV h

theorem mem_ACVF_sdRVMul : Axioms.sdRVMul ∈ Axioms.ACVF :=
  mem_ACVF_of_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_rvMulAssoc : Axioms.rvMulAssoc ∈ Axioms.ACVF :=
  mem_ACVF_of_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvMulComm : Axioms.rvMulComm ∈ Axioms.ACVF :=
  mem_ACVF_of_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvMulInfty : Axioms.rvMulInfty ∈ Axioms.ACVF :=
  mem_ACVF_of_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvMulOneRV : Axioms.rvMulOneRV ∈ Axioms.ACVF :=
  mem_ACVF_of_repairRV (by simp [Axioms.repairRV, Axioms.ofList])

theorem mem_ACVF_rvMulInvRV : Axioms.rvMulInvRV ∈ Axioms.ACVF :=
  mem_ACVF_of_repairRV (by simp [Axioms.repairRV, Axioms.ofList])

end SpecialTransformations.Milestone0.Transfer

/-! ### 7b. `RV`-multiplication is a commutative monoid with zero — from the axioms

`rvMulAssoc`, `rvMulComm`, `rvMulInfty` are in `Axioms.rvGroup`; `rvMulOneRV`, `rvMulInvRV` are the
repaired `RV^×`-group axioms of `Axioms.repairRV`.  Nothing here is assumed. -/

namespace SpecialTransformations.Milestone0.Transfer

variable {M : Type} [LRV.Structure M]

theorem rv_mul_assoc_of_model (hM : M ⊨ Axioms.ACVF) {a b c : M}
    (ha : iRV a) (hb : iRV b) (hc : iRV c) :
    iRVMul (iRVMul a b) c = iRVMul a (iRVMul b c) := by
  have h := allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv, SortTag.rv])
    (φ := (pEq (tRVMul (tRVMul &0 &1) &2) (tRVMul &0 (tRVMul &1 &2))))
    mem_ACVF_rvMulAssoc ![a, b, c] (by intro i; fin_cases i <;> simp [ha, hb, hc])
  simpa [pEq, BoundedFormula.realize_bdEqual, realize_tRVMul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] using h

theorem rv_mul_comm_of_model (hM : M ⊨ Axioms.ACVF) {a b : M} (ha : iRV a) (hb : iRV b) :
    iRVMul a b = iRVMul b a := by
  have h := allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv])
    (φ := (pEq (tRVMul &0 &1) (tRVMul &1 &0)))
    mem_ACVF_rvMulComm ![a, b] (by intro i; fin_cases i <;> simp [ha, hb])
  simpa [pEq, BoundedFormula.realize_bdEqual, realize_tRVMul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] using h

theorem rv_mul_zero_right_of_model (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) :
    iRVMul a iRVZero = iRVZero := by
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pEq (tRVMul &0 tRVInfty) tRVInfty))
    mem_ACVF_rvMulInfty ![a] (by intro i; fin_cases i; simpa using ha)
  simpa [tRVInfty, pEq, BoundedFormula.realize_bdEqual, realize_tRVMul, realize_tRVZero,
    Matrix.cons_val_zero] using h

theorem rv_mul_zero_left_of_model (hM : M ⊨ Axioms.ACVF) {b : M} (hb : iRV b) :
    iRVMul iRVZero b = iRVZero := by
  rw [rv_mul_comm_of_model hM (rv_zero_mem hM) hb, rv_mul_zero_right_of_model hM hb]

theorem rv_one_mul_of_model (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) (ha0 : a ≠ iRVZero) :
    iRVMul iRVOne a = a := by
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pRV &0 ⟹ pEq (tRVMul tRVOne &0) &0))
    mem_ACVF_rvMulOneRV ![a] (by intro i; fin_cases i; simpa using ha)
  have h' : a ≠ iRVZero → iRVMul iRVOne a = a := by
    simpa [pRV_realize, pEq, BoundedFormula.realize_bdEqual, realize_tRVMul, realize_tRVOne_T,
      Matrix.cons_val_zero] using h
  exact h' ha0

theorem rv_mul_one_of_model (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) (ha0 : a ≠ iRVZero) :
    iRVMul a iRVOne = a := by
  rw [rv_mul_comm_of_model hM ha (rv_one_mem hM), rv_one_mul_of_model hM ha ha0]

theorem rv_mul_one_any (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) :
    iRVMul iRVOne a = a := by
  by_cases h : a = iRVZero
  · subst h; exact rv_mul_zero_right_of_model hM (rv_one_mem hM)
  · exact rv_one_mul_of_model hM ha h

theorem rv_mul_one_any_right (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) :
    iRVMul a iRVOne = a := by
  by_cases h : a = iRVZero
  · subst h; exact rv_mul_zero_left_of_model hM (rv_one_mem hM)
  · exact rv_mul_one_of_model hM ha h

theorem rv_mul_inv_exists_of_model (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a)
    (ha0 : a ≠ iRVZero) :
    ∃ b : M, iRV b ∧ b ≠ iRVZero ∧ iRVMul b a = iRVOne := by
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pRV &0 ⟹ exSorted .rv (pRV &1 ⊓ pEq (tRVMul &1 &0) tRVOne)))
    mem_ACVF_rvMulInvRV ![a] (by intro i; fin_cases i; simpa using ha)
  have h' : a ≠ iRVZero → ∃ b : M, iRV b ∧ b ≠ iRVZero ∧ iRVMul b a = iRVOne := by
    simpa [pRV_realize, exSorted, sortPred, sortPred_realize, pRVsort_realize,
      BoundedFormula.realize_ex, BoundedFormula.realize_inf, pEq,
      BoundedFormula.realize_bdEqual, realize_tRVMul, realize_tRVOne_T, realize_tv,
      Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  exact h' ha0

/-- The inverse of an `RV`-element, chosen from `rvMulInvRV`; `0` is mapped to `0`. -/
noncomputable def iRVInv (hM : M ⊨ Axioms.ACVF) (a : M) : M :=
  if h : iRV a ∧ a ≠ iRVZero then Classical.choose (rv_mul_inv_exists_of_model hM h.1 h.2)
  else iRVZero

theorem iRVInv_mem (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) : iRV (iRVInv hM a) := by
  by_cases h : a = iRVZero
  · subst h
    rw [iRVInv, dif_neg (by intro hc; exact hc.2 rfl)]
    exact rv_zero_mem hM
  · rw [iRVInv, dif_pos ⟨ha, h⟩]
    exact (Classical.choose_spec (rv_mul_inv_exists_of_model hM ha h)).1

theorem iRVInv_mul_cancel (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) (ha0 : a ≠ iRVZero) :
    iRVMul (iRVInv hM a) a = iRVOne := by
  rw [iRVInv, dif_pos ⟨ha, ha0⟩]
  exact (Classical.choose_spec (rv_mul_inv_exists_of_model hM ha ha0)).2.2

theorem rv_mul_inv_cancel_right (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) (ha0 : a ≠ iRVZero) :
    iRVMul a (iRVInv hM a) = iRVOne := by
  rw [rv_mul_comm_of_model hM ha (iRVInv_mem hM ha), iRVInv_mul_cancel hM ha ha0]

/-- **No zero divisors on `RV`**: a product of `RV`-elements is `0` iff one factor is. -/
theorem rv_mul_eq_zero_of_model (hM : M ⊨ Axioms.ACVF) {a b : M} (ha : iRV a) (hb : iRV b) :
    iRVMul a b = iRVZero ↔ a = iRVZero ∨ b = iRVZero := by
  constructor
  · intro h
    by_cases ha0 : a = iRVZero
    · exact Or.inl ha0
    · refine Or.inr ?_
      calc b = iRVMul iRVOne b := (rv_mul_one_any hM hb).symm
        _ = iRVMul (iRVMul (iRVInv hM a) a) b := by rw [iRVInv_mul_cancel hM ha ha0]
        _ = iRVMul (iRVInv hM a) (iRVMul a b) := rv_mul_assoc_of_model hM (iRVInv_mem hM ha) ha hb
        _ = iRVMul (iRVInv hM a) iRVZero := by rw [h]
        _ = iRVZero := rv_mul_zero_right_of_model hM (iRVInv_mem hM ha)
  · rintro (rfl | rfl)
    · exact rv_mul_zero_left_of_model hM hb
    · exact rv_mul_zero_right_of_model hM ha

/-- **Cancellation**: on `RV` a nonzero factor can be cancelled. -/
theorem rv_mul_right_cancel_of_model (hM : M ⊨ Axioms.ACVF) {a b c : M}
    (ha : iRV a) (ha0 : a ≠ iRVZero) (hb : iRV b) (hc : iRV c)
    (h : iRVMul a b = iRVMul a c) : b = c := by
  obtain ⟨ai, hai, _, hainv⟩ := rv_mul_inv_exists_of_model hM ha ha0
  calc b = iRVMul iRVOne b := (rv_mul_one_any hM hb).symm
    _ = iRVMul (iRVMul ai a) b := by rw [hainv]
    _ = iRVMul ai (iRVMul a b) := rv_mul_assoc_of_model hM hai ha hb
    _ = iRVMul ai (iRVMul a c) := by rw [h]
    _ = iRVMul (iRVMul ai a) c := (rv_mul_assoc_of_model hM hai ha hc).symm
    _ = iRVMul iRVOne c := by rw [hainv]
    _ = c := rv_mul_one_any hM hc

theorem rv_mul_left_cancel_of_model (hM : M ⊨ Axioms.ACVF) {a b c : M}
    (ha : iRV a) (hb : iRV b) (hb0 : b ≠ iRVZero) (hc : iRV c)
    (h : iRVMul a b = iRVMul c b) : a = c := by
  rw [rv_mul_comm_of_model hM ha hb, rv_mul_comm_of_model hM hc hb] at h
  exact rv_mul_right_cancel_of_model hM hb hb0 ha hc h

/-- **The cancellation normal form of an `RV`-product, off `K` as well as on it**: the factor `b`
can be removed from a product from the right by multiplying with its inverse, without any
hypothesis on `a`, and hence a multiplicative word can be normalised by cancelling common
factors.  This is the `mul`-cancellation dictionary that
`.ultramath/smw19wtoj/m3/QF2.lean`'s `RESULTS.md` records as missing. -/
theorem rv_mul_inv_cancel_of_model (hM : M ⊨ Axioms.ACVF) {a b : M}
    (ha : iRV a) (hb : iRV b) (hb0 : b ≠ iRVZero) :
    iRVMul (iRVMul a b) (iRVInv hM b) = a := by
  by_cases ha0 : a = iRVZero
  · subst ha0
    rw [rv_mul_zero_left_of_model hM hb, rv_mul_zero_left_of_model hM (iRVInv_mem hM hb)]
  · rw [rv_mul_assoc_of_model hM ha hb (iRVInv_mem hM hb),
      rv_mul_inv_cancel_right hM hb hb0, rv_mul_one_of_model hM ha ha0]

/-- **Reduction of an `RV`-equation to an equation with `1`**: for nonzero `b`, `a = b` iff
`a · b⁻¹ = 1`.  This is how a comparison between two multiplicative words becomes a comparison of
a single word with `1`, i.e. the residual atom of the mixed-context cover. -/
theorem rv_eq_iff_mul_inv_eq_one (hM : M ⊨ Axioms.ACVF) {a b : M}
    (ha : iRV a) (hb : iRV b) (hb0 : b ≠ iRVZero) :
    (a = b) ↔ iRVMul a (iRVInv hM b) = iRVOne := by
  constructor
  · intro h; subst h; exact rv_mul_inv_cancel_right hM hb hb0
  · intro h
    calc a = iRVMul a iRVOne := (rv_mul_one_any_right hM ha).symm
      _ = iRVMul a (iRVMul (iRVInv hM b) b) := by rw [iRVInv_mul_cancel hM hb hb0]
      _ = iRVMul (iRVMul a (iRVInv hM b)) b :=
        (rv_mul_assoc_of_model hM ha (iRVInv_mem hM hb) hb).symm
      _ = iRVMul iRVOne b := by rw [h]
      _ = b := rv_mul_one_any hM hb

end SpecialTransformations.Milestone0.Transfer

/-! ### 7c. `VF`-closure, the `K → RV` bridge, and `rv` as a multiplicative map -/

namespace SpecialTransformations.Milestone0.Transfer

variable {M : Type} [LRV.Structure M]

theorem mem_ACVF_sdVFZero : Axioms.sdVFZero ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdVFOne : Axioms.sdVFOne ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdVFAdd : Axioms.sdVFAdd ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdVFNeg : Axioms.sdVFNeg ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdVFMul : Axioms.sdVFMul ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_rvAxioms {s : LRV.Sentence} (h : s ∈ Axioms.rvAxioms) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

theorem vf_zero_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iVF (iVFZero (M := M)) := by
  have h := sentence_realize hM (φ := Axioms.sdVFZero) mem_ACVF_sdVFZero
  rw [Axioms.sdVFZero, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pVF_realize, realize_tVFZero] at h
  exact h

theorem vf_one_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iVF (iVFOne (M := M)) := by
  have h := sentence_realize hM (φ := Axioms.sdVFOne) mem_ACVF_sdVFOne
  rw [Axioms.sdVFOne, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pVF_realize, realize_tVFOne] at h
  exact h

theorem vf_add_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVF (iVFAdd x y) := by
  have h := allSorted_realize hM (T := Axioms.ACVF) mem_ACVF_sdVFAdd ![x, y] (by
    intro i
    fin_cases i <;> simp [hx, hy])
  rw [pVF_realize, realize_tVFAdd] at h
  simpa using h

theorem vf_neg_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVF (iVFNeg x) := by
  have h := allSorted_realize hM (T := Axioms.ACVF) mem_ACVF_sdVFNeg ![x] (by
    intro i
    fin_cases i
    simpa using hx)
  rw [pVF_realize, realize_tVFNeg] at h
  simpa using h

theorem vf_mul_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVF (iVFMul x y) := by
  have h := allSorted_realize hM (T := Axioms.ACVF) mem_ACVF_sdVFMul ![x, y] (by
    intro i
    fin_cases i <;> simp [hx, hy])
  rw [pVF_realize, realize_tVFMul] at h
  simpa using h

/-! ### The field laws on the `VF` sort -/
theorem mem_ACVF_sdUnits' :
    allOne (pUnits (tv 0 (Nat.lt_succ_self 0)) ⟹ pRVsort (tv 0 (Nat.lt_succ_self 0)))
      ∈ Axioms.ACVF :=
  mem_ACVF_of_sortClosure (s := Axioms.sdUnits) (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_rvMulHom : Axioms.rvMulHom ∈ Axioms.ACVF :=
  mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])

/-- `K = Kˣ ∪ {0}` is inside the `RV` sort: units are `RV` by `sdUnits`, and `0` is `RV` by
`sdRVZero`. -/
theorem iRV_of_inK (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iUnits a ∨ a = iRVZero) : iRV a := by
  rcases ha with h | h
  · have h' := allOne_realize hM mem_ACVF_sdUnits' ![a]
    have h'' : iUnits a → iRV a := by
      simpa [pUnits_realize, pRVsort_realize, realize_tv, Matrix.cons_val_zero] using h'
    exact h'' h
  · subst h; exact rv_zero_mem hM

/-- **`rv` is multiplicative on `VF`** (`Axioms.rvMulHom`): `rv(x·y) = rv x · rv y`.  This is the
step that lets a factor coming from the residue field be pulled out of a product, i.e. it is the
`Kˣ`-half of the mixed-context `mul` normal form. -/
theorem rv_mul_hom_of_model (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y) :
    iRv (iVFMul x y) = iRVMul (iRv x) (iRv y) := by
  have h := allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf])
    (φ := (pEq (tRv (tVFMul &0 &1)) (tRVMul (tRv &0) (tRv &1))))
    mem_ACVF_rvMulHom ![x, y] (by intro i; fin_cases i <;> simp [hx, hy])
  simpa [pEq, BoundedFormula.realize_bdEqual, realize_tRv, realize_tVFMul, realize_tRVMul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

end SpecialTransformations.Milestone0.Transfer

/-! ### 7d. The sort discipline of the mixed fragment

At a tuple of the declared sorts, every term of the fragment lands in its own sort.  This is what
lets the `RV`-words of a mixed context be read as `RV`-elements throughout. -/

namespace SpecialTransformations.Milestone0.Transfer.QFRes2

open SpecialTransformations.Milestone0.Transfer

variable {M : Type} [LRV.Structure M] {n : ℕ} {sn : Fin n → SortTag}

theorem VFT2.val_mem (hM : M ⊨ Axioms.ACVF) (s : VFT2 sn) (x : Fin n → M)
    (hx : ∀ i, sortEval (sn i) (x i)) : iVF (s.Val x) := by
  induction s with
  | var i h =>
    rw [VFT2.val_var]
    have h1 := hx i
    rw [h] at h1
    simpa only [sortEval, iVF] using h1
  | zero => rw [VFT2.val_zero]; exact vf_zero_mem hM
  | one => rw [VFT2.val_one]; exact vf_one_mem hM
  | add a b iha ihb => rw [VFT2.val_add]; exact vf_add_mem hM iha ihb
  | neg a iha => rw [VFT2.val_neg]; exact vf_neg_mem hM iha
  | mul a b iha ihb => rw [VFT2.val_mul]; exact vf_mul_mem hM iha ihb

end SpecialTransformations.Milestone0.Transfer.QFRes2
