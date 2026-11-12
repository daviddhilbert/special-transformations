module

public import Section4.PositivePresentation
public import Section4.Imported.GrothendieckRing

@[expose] public section

/-! Groupification of a positive scissor presentation. This uses the
attributed ring-completion port and imposes no cancellation assumption. -/

noncomputable section

namespace SpecialTransformations.Section4.PositiveGrothendieck

universe u v

variable {Obj : Type u} (P : Presentation Obj)

abbrev KRing := Algebra.GrothendieckAddGroup (KPlus P)

def completionHom : KPlus P →+* KRing P := Algebra.GrothendieckAddGroup.ofRingHom

def ringOf (a : Obj) : KRing P := completionHom P (of P a)

/-- The scissor invariants valued in a commutative ring are exactly the ring
homomorphisms from the groupification of the positive presentation. -/
def ringUniversalEquiv {R : Type v} [CommRing R] :
    Invariant P (R := R) ≃ (KRing P →+* R) :=
  (universalEquiv P).trans Algebra.GrothendieckAddGroup.liftRingHom

@[simp] theorem ringUniversalEquiv_of {R : Type v} [CommRing R]
    (f : Invariant P (R := R)) (a : Obj) :
    ringUniversalEquiv P f (ringOf P a) = f.toFun a := by
  change Algebra.GrothendieckAddGroup.liftRingHom (lift P f)
    (Algebra.GrothendieckAddGroup.of (of P a)) = f.toFun a
  rw [Algebra.GrothendieckAddGroup.liftRingHom_apply_of, lift_of]

end SpecialTransformations.Section4.PositiveGrothendieck

end
