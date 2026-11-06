import Mathlib.GroupTheory.Congruence.Defs
import Mathlib.Algebra.Group.Subsemigroup.Basic

/-! The additive part of Definition 4.22, with precisely the paper's
subsemigroup-of-pairs convention. Quotient structures come from AddCon. -/

namespace SpecialTransformations.Section4

variable {A : Type*} [Add A]

def additiveCongruenceGraph (c : AddCon A) : AddSubsemigroup (A × A) where
  carrier := {p | c p.1 p.2}
  add_mem' := by intro a b ha hb; exact c.add ha hb

def additiveCongruenceOfGraph (U : AddSubsemigroup (A × A))
    (heq : Equivalence (fun x y => (x, y) ∈ U)) : AddCon A where
  r x y := (x, y) ∈ U
  iseqv := heq
  add' := by intro a b c d hab hcd; exact U.add_mem hab hcd

def additiveCongruenceGraphEquiv : AddCon A ≃
    {U : AddSubsemigroup (A × A) // Equivalence (fun x y => (x, y) ∈ U)} where
  toFun c := ⟨additiveCongruenceGraph c, c.iseqv⟩
  invFun U := additiveCongruenceOfGraph U.val U.property
  left_inv c := by cases c; rfl
  right_inv U := by
    apply Subtype.ext
    ext p
    rfl

end SpecialTransformations.Section4
