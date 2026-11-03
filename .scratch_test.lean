import Mathlib
open FirstOrder FirstOrder.Language
open scoped FirstOrder
example {L : FirstOrder.Language} {α : Type*} {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsQF) :
    True := by
  induction h with
  | falsum => trivial
  | of_isAtomic ha => trivial
  | imp _ _ ih1 ih2 => trivial
#check @BoundedFormula.IsQF.rec
#check @BoundedFormula.IsQF.recOn
#check @BoundedFormula.IsAtomic.recOn
