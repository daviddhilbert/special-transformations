/-
**Where `NontrivialTransferWS` first fails, as a formula rather than a paragraph.**

`TransferAtWS` fixes a pair of models `M, N` of `T` and a pair of sort-respecting tuples with the
same quantifier-free type, and asks for the same *full* type there.  Its proof has to be an
induction on the `WellSorted` derivation.  The atomic and `imp` cases are immediate; the `all` case
asks, in the forward direction,

    (∀ a : M, χ.Realize v (Fin.snoc xs a))  →  (∀ b : N, χ.Realize w (Fin.snoc ys b))

and, splitting on the bound element `b : N`, needs exactly two inputs:

* `¬ sortEval s b`: **junk-truth of the body** — the `GuardTrue` field of the repaired
  `WellSorted.all`.  This is what the guard repair was for, and `all_step_forward_junk` below says
  that nothing else is needed on that branch.
* `sortEval s b`: a sorted `a : M` whose quantifier-free type over `(v, xs)` equals that of `b`
  over `(w, ys)`, so that the induction hypothesis for `χ` can fire.  That is a **realization of a
  quantifier-free type in a fixed model**, and neither `M ⊨ T` nor "the tuples `(v,xs)` and
  `(w,ys)` have the same QF type" supplies it: `all_step_forward_sorted` states it as `ext` and
  does nothing else with it.

So the transfer's remaining content is not spread over the induction: it is (i) `GuardTrue →
JunkTrueAt`, and (ii) the one-element QF-mate property — the paper's §3/§4 effectiveness of the
residue field, or a saturation/compactness substitute for it.  Note also that
`NontrivialTransfer` is *equivalent* to `HasQEb` (`Missing.nontrivialTransfer_iff_hasQEb`), so (ii)
cannot be cheap: a direct proof of the transfer is a proof of QE, and the honest decomposition is
via the extension property, not via this induction alone.

Build (`.scratch2/sec3/` holds `Enc.olean`, a compiled `Milestone0/Encoding.lean`):

    cd .scratch2/sec3 && cp ../../QE/FailProbe.lean FP.lean &&
      LEAN_PATH=$PWD:$LEAN_PATH lean FP.lean
-/
import Enc
set_option linter.unusedVariables false
open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace SpecialTransformations
namespace Milestone0
open LRV

/-!
Localization of the first failure point of `NontrivialTransferWS`.

`TransferAtWS` fixes one pair of models `M, N` and one pair of tuples with the same QF type, and
asks for the same *full* type.  Its proof must be an induction on the `WellSorted` derivation.  The
atomic and `imp` cases are immediate.  The `all` case asks, in the forward direction,

    (∀ a : M, χ.Realize v (Fin.snoc xs a))  →  (∀ b : N, χ.Realize w (Fin.snoc ys b))

and splits on the bound element `b : N`:

* `¬ sortEval s b` — junk-truth of the body (the `GuardTrue` field).  Available from the repair,
  as soon as the semantic bridge is proved;
* `sortEval s b` — the induction hypothesis for `χ` can fire only at a pair of tuples with the
  *same* QF type, so one needs a sorted `a : M` whose QF type over `(v, xs)` is that of `b` over
  `(w, ys)`.  That is a *realization of a QF type in a fixed model*, and neither `M ⊨ T` nor the
  assumption that `(v,xs)` and `(w,ys)` have the same QF type supplies it.

The two lemmas below are that split, with each half stated as the hypothesis it needs, so that the
obstruction is a formula rather than a paragraph.
-/

/-- sortedness is preserved by `Fin.snoc` -/
theorem sorted_snoc {M : Type} [LRV.Structure M] {n : ℕ} (sn : Fin n → SortTag)
    (s : SortTag) (xs : Fin n → M) (a : M) (hxs : ∀ i, sortEval (sn i) (xs i))
    (ha : sortEval s a) :
    ∀ i, sortEval ((Fin.snoc sn s : Fin (n + 1) → SortTag) i)
      ((Fin.snoc xs a : Fin (n + 1) → M) i) := by
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simpa using ha
  · intro j
    simpa using hxs j

/-- The `all` case, forward direction, at a **sorted** bound element: it needs a QF-mate. -/
theorem all_step_forward_sorted
    {M N : Type} [LRV.Structure M] [LRV.Structure N]
    {α : Type} (sα : α → SortTag) {n : ℕ} {sn : Fin n → SortTag} {s : SortTag}
    (v : α → M) (xs : Fin n → M) (w : α → N) (ys : Fin n → N)
    {χ : LRV.BoundedFormula α (n + 1)}
    -- the induction hypothesis for the body, at *any* pair of sorted tuples of equal QF type
    (IH : ∀ (xs' : Fin (n + 1) → M) (ys' : Fin (n + 1) → N),
      (∀ i, sortEval ((Fin.snoc sn s : Fin (n + 1) → SortTag) i) (xs' i)) →
      (∀ i, sortEval ((Fin.snoc sn s : Fin (n + 1) → SortTag) i) (ys' i)) →
      (∀ ψ : LRV.BoundedFormula α (n + 1), WellSorted sα (Fin.snoc sn s) ψ → ψ.IsQF →
        (ψ.Realize v xs' ↔ ψ.Realize w ys')) →
      (χ.Realize v xs' ↔ χ.Realize w ys'))
    -- the missing input, stated exactly: every sorted `b` has a sorted QF-mate `a`
    (ext : ∀ b : N, sortEval s b → ∃ a : M, sortEval s a ∧
      ∀ ψ : LRV.BoundedFormula α (n + 1), WellSorted sα (Fin.snoc sn s) ψ → ψ.IsQF →
        (ψ.Realize v (Fin.snoc xs a) ↔ ψ.Realize w (Fin.snoc ys b)))
    (hxs : ∀ i, sortEval (sn i) (xs i)) (hys : ∀ i, sortEval (sn i) (ys i))
    (hfwd : ∀ a : M, χ.Realize v (Fin.snoc xs a)) (b : N) (hb : sortEval s b) :
    χ.Realize w (Fin.snoc ys b) := by
  obtain ⟨a, ha, hQF⟩ := ext b hb
  exact (IH (Fin.snoc xs a) (Fin.snoc ys b)
    (sorted_snoc sn s xs a hxs ha) (sorted_snoc sn s ys b hys hb) hQF).1 (hfwd a)

/-- The `all` case, forward direction, at a **junk** bound element: it needs junk-truth of the
body, and nothing else. -/
theorem all_step_forward_junk
    {N : Type} [LRV.Structure N]
    {α : Type} {n : ℕ} {s : SortTag}
    (w : α → N) (ys : Fin n → N) {χ : LRV.BoundedFormula α (n + 1)}
    (hjunk : ∀ a : N, ¬ sortEval s a → χ.Realize w (Fin.snoc ys a))
    (b : N) (hb : ¬ sortEval s b) :
    χ.Realize w (Fin.snoc ys b) :=
  hjunk b hb

end Milestone0
end SpecialTransformations
