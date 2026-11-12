module

/-
**The realisation lemma for the encoding's guarded existential `exSortedG`**, which
`Milestone0/Encoding.lean` states `WellSorted`-ness for but never realises:

```
(exSortedG s ψ).Realize v xs  ↔  ∃ a, sortEval s a ∧ ψ.Realize v (Fin.snoc xs a)
```

`exSortedG s ψ` is `∃ x, (x ∈ s) ∧ ψ` written as `¬∀ x, ¬((x ∈ s) ⊓ ψ)`; the only two ingredients are
`BoundedFormula.realize_ex` and `Junk.guardAtom_realize` (`QE/JunkTrue.lean`).  It is needed wherever
a *guarded* existential has to be eliminated — in particular the pairing step of
`DefinableFun`-composition, where an intermediate tuple must be existentially quantified and
`WellSorted` admits no unguarded quantifier.

Check with `.scratch2/sec3/` (compiled `Enc` and `JunkTrue`): copy this file there and
`LEAN_PATH=$PWD:$LEAN_PATH lean` it.
-/
public import Enc
public import JunkTrue

@[expose] public section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations
namespace Milestone0

/-- **`exSortedG` realises as a guarded existential.** -/
theorem exSortedG_realize {α : Type} {k : ℕ} {M : Type} [LRV.Structure M] (s : SortTag)
    (ψ : LRV.BoundedFormula α (k + 1)) (v : α → M) (xs : Fin k → M) :
    (exSortedG s ψ).Realize v xs ↔ ∃ a : M, sortEval s a ∧ ψ.Realize v (Fin.snoc xs a) := by
  rw [exSortedG, BoundedFormula.realize_ex]
  refine exists_congr (fun a => ?_)
  rw [BoundedFormula.realize_inf]
  -- `guardAtom s i` is `sortPredG s (var i)` by definition, so this is a `change`, not a rewrite
  change (guardAtom s (Fin.last k)).Realize v (Fin.snoc xs a) ∧ ψ.Realize v (Fin.snoc xs a) ↔
    sortEval s a ∧ ψ.Realize v (Fin.snoc xs a)
  rw [Junk.guardAtom_realize, Fin.snoc_last]

end Milestone0
end SpecialTransformations
