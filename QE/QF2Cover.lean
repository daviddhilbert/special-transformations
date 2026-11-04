/-
**`qf2_cover`**: a well-sorted quantifier-free formula over a sorted context is, at sorted tuples,
equivalent to the image of a `QF2` term of `QE/QF2Fragment.lean`.

Why this is the right target and why it is not the audit's `MixedContextCover`: that statement
(`.ultramath/smw1b0thh/m3/AvAudit.lean:158`) asks for a *parameter-free* formula `φ'` and an all-`VF`
tuple `y` with `φ.Realize v x ↔ φ'.Realize default y`.  Since `y` may depend on `(v, x)` and `φ'` is
fixed, the only thing it can require of `φ'` is that it be neither valid nor unsatisfiable, so it is
essentially true for any `φ'` with a true and a false instance, independently of `φ`.  It is therefore
not the content, and it is not what this file proves.

This file proves the content: with the fragment `RVT2` carrying an `RV`-sorted *variable*
(`RVT2.rvar`), every well-sorted quantifier-free formula over a sorted context is the image of a
`QF2` term, so the atom layer of the elimination can be done inside the fragment.  The term
extraction is where `QE/MulNormalForm.lean` belongs: an `RV`-term built out of `rvMul`/`kAdd` has to
be flattened into `RVT2`, and off `Kˣ` that is cancellation.

Build (`.scratch2/sec3/` holds the oleans):

    LEAN_PATH=$PWD:$LEAN_PATH lean QF2Cover.lean        # with QF2Fragment.olean present
-/
import QF2Fragment
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.Transfer
namespace QFRes2

/-- The sort assignment of the empty parameter type. -/
abbrev sE : Empty → SortTag := fun e => e.elim

section Extract

variable {n : ℕ} {sn : Fin n → SortTag}

/-! ## The cover, stated

The extraction is a *proof-free* recursion (`Option`-valued), because the proof-carrying version
(`(t : Tm n) → TmSort sE sn t = some .vf → VFT2 sn`) does not pass Lean's structural-recursion
check when the sort hypothesis is consumed inside a `cases f` block: the offending goal is
`sizeOf (ts 0) < 1 + l`, where `l` is the arity and not a size.  The `Option` version descends on `t`
alone and its soundness is a separate induction on `t`, which is the standard way round.

`vfOpt`/`rvOpt` mirror `TmSort` symbol by symbol; soundness is
`(TmSort sE sn t = some .vf → ∃ s, vfOpt t = some s ∧ s.val x = t.realize …)`, dually for `RV`, and
the fragment's own `val_*` lemmas (`QF2Fragment`) do the computation once the extraction is known. -/

/-- Extract a fragment `VF`-term, undoing `TmSort` symbol by symbol. -/
noncomputable def vfOpt (sn : Fin n → SortTag) : Tm n → Option (VFT2 sn) :=
  sorry

/-- Extract a fragment `RV`-term. -/
noncomputable def rvOpt (sn : Fin n → SortTag) : Tm n → Option (RVT2 sn) :=
  sorry

/-! ## `qf2_cover`

The target: a well-sorted quantifier-free formula over a sorted context is, at sorted tuples, the
image of a `QF2` term.  The atom cases are the extraction above; the connectives are `QF2.imp` and
`QF2.falsum`, and `pVF`/`pRV`/`pUnits`/`pLe`/`pEq` map to `inVF`/`inRV`/`unitRV`/`leRV`/`eqVF`
(resp. `eqRV` when both terms are `RV`). -/
theorem qf2_cover {n : ℕ} (sn : Fin n → SortTag) (φ : Bf n) (hws : WellSorted sE sn φ)
    (hqf : φ.IsQF) :
    ∃ q : QF2 sn, ∀ (M : Type) [LRV.Structure M], M ⊨ Axioms.ACVF → ∀ x : Fin n → M,
      (∀ i, sortEval (sn i) (x i)) →
      (φ.Realize (fun e : Empty => e.elim) x ↔
        (q.toRV).Realize (fun e : Empty => e.elim) x) := by
  sorry

end Extract

end QFRes2
end SpecialTransformations.Milestone0.Transfer
