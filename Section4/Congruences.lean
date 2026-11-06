import Mathlib.RingTheory.Congruence.Defs
import Mathlib.Algebra.Ring.Subsemiring.Basic

/-!
# The congruence criterion in Remark 4.23

Mathlib already supplies additive and semiring congruences and their quotient
structures. This proves the paper's one-variable stability criterion in
that API; it applies in particular to the positive Grothendieck semiring
once that semiring has been constructed.
-/

namespace SpecialTransformations.Section4

variable {R : Type*} [CommSemiring R]

/-- Definition 4.22 in the subsemiring-of-pairs description. -/
def congruenceGraph (c : RingCon R) : Subsemiring (R × R) where
  carrier := {p | c p.1 p.2}
  zero_mem' := c.refl 0
  one_mem' := c.refl 1
  add_mem' := by intro a b ha hb; exact c.add ha hb
  mul_mem' := by intro a b ha hb; exact c.mul ha hb

def congruenceOfGraph (U : Subsemiring (R × R))
    (heq : Equivalence (fun x y => (x, y) ∈ U)) : RingCon R where
  r x y := (x, y) ∈ U
  iseqv := heq
  add' := by intro a b c d hab hcd; exact U.add_mem hab hcd
  mul' := by intro a b c d hab hcd; exact U.mul_mem hab hcd

/-- The paper's definition is exactly Mathlib's semiring-congruence API. -/
def congruenceGraphEquiv : RingCon R ≃
    {U : Subsemiring (R × R) // Equivalence (fun x y => (x, y) ∈ U)} where
  toFun c := ⟨congruenceGraph c, c.iseqv⟩
  invFun U := congruenceOfGraph U.val U.property
  left_inv c := by cases c; rfl
  right_inv U := by
    apply Subtype.ext
    ext p
    rfl

/-- Remark 4.23. Translations and multiplication on the right suffice in a
commutative semiring. The equivalence relation is retained exactly. -/
def lemma_4_23 (s : Setoid R)
    (hadd : ∀ {x y}, s.r x y → ∀ z, s.r (x + z) (y + z))
    (hmul : ∀ {x y}, s.r x y → ∀ z, s.r (x * z) (y * z)) : RingCon R where
  r := s.r
  iseqv := s.iseqv
  add' := by
    intro a b c d hab hcd
    apply s.iseqv.trans (hadd hab c)
    simpa only [add_comm] using hadd hcd b
  mul' := by
    intro a b c d hab hcd
    apply s.iseqv.trans (hmul hab c)
    simpa only [mul_comm] using hmul hcd b

@[simp] theorem lemma_4_23_relation (s : Setoid R)
    (hadd : ∀ {x y}, s.r x y → ∀ z, s.r (x + z) (y + z))
    (hmul : ∀ {x y}, s.r x y → ∀ z, s.r (x * z) (y * z)) (x y : R) :
    lemma_4_23 s hadd hmul x y ↔ s.r x y := Iff.rfl

theorem congruence_iff_right_stable (s : Setoid R) :
    (∃ c : RingCon R, c.toSetoid = s) ↔
      (∀ {x y}, s.r x y → ∀ z, s.r (x + z) (y + z)) ∧
      (∀ {x y}, s.r x y → ∀ z, s.r (x * z) (y * z)) := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun h z => c.add h (c.refl z), fun h z => c.mul h (c.refl z)⟩
  · rintro ⟨hadd, hmul⟩
    exact ⟨lemma_4_23 s hadd hmul, rfl⟩

end SpecialTransformations.Section4
