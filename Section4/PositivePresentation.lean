import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Congruence.Hom

/-!
# Positive scissor presentations

A positive presentation is a quotient of the free commutative semiring
MvPolynomial Obj ℕ. The relations identify isomorphic objects, empty and
unit objects, products, and scissor decompositions. Its universal property
is proved over arbitrary commutative semirings, before any group completion.

This is the algebraic presentation layer. Instantiating its object and
scissor data with the VF/RV categories, and proving the description by
isomorphism classes using disjoint unions, are separate geometric tasks.
-/

noncomputable section

namespace SpecialTransformations.Section4.PositiveGrothendieck

universe u v

structure Presentation (Obj : Type u) where
  iso : Obj → Obj → Prop
  empty : Obj
  unit : Obj
  product : Obj → Obj → Obj
  scissor : Obj → Obj → Obj → Obj → Prop

variable {Obj : Type u} (P : Presentation Obj)

inductive Relation : MvPolynomial Obj ℕ → MvPolynomial Obj ℕ → Prop
  | iso {a b} : P.iso a b → Relation (MvPolynomial.X a) (MvPolynomial.X b)
  | empty : Relation (MvPolynomial.X P.empty) 0
  | unit : Relation (MvPolynomial.X P.unit) 1
  | product (a b) : Relation (MvPolynomial.X a * MvPolynomial.X b)
      (MvPolynomial.X (P.product a b))
  | scissor {a b c d} : P.scissor a b c d →
      Relation (MvPolynomial.X a + MvPolynomial.X b) (MvPolynomial.X c + MvPolynomial.X d)

def congruence : RingCon (MvPolynomial Obj ℕ) := ringConGen (Relation P)

abbrev KPlus := (congruence P).Quotient

def quotientHom : MvPolynomial Obj ℕ →+* KPlus P := (congruence P).mk'

def of (a : Obj) : KPlus P := quotientHom P (MvPolynomial.X a)

theorem quotient_relation {p q : MvPolynomial Obj ℕ} (h : Relation P p q) :
    quotientHom P p = quotientHom P q :=
  (congruence P).eq.mpr (RingConGen.Rel.of p q h)

theorem of_iso {a b : Obj} (h : P.iso a b) : of P a = of P b :=
  quotient_relation P (Relation.iso h)

@[simp] theorem of_empty : of P P.empty = 0 := by
  exact (quotient_relation P Relation.empty).trans (map_zero (quotientHom P))

@[simp] theorem of_unit : of P P.unit = 1 := by
  exact (quotient_relation P Relation.unit).trans (map_one (quotientHom P))

theorem of_product (a b : Obj) : of P (P.product a b) = of P a * of P b := by
  exact (quotient_relation P (Relation.product a b)).symm.trans (map_mul (quotientHom P) _ _)

theorem of_scissor {a b c d : Obj} (h : P.scissor a b c d) :
    of P a + of P b = of P c + of P d := by
  exact (map_add (quotientHom P) _ _).symm.trans
    ((quotient_relation P (Relation.scissor h)).trans (map_add (quotientHom P) _ _))

variable {R : Type v} [CommSemiring R]

structure Invariant where
  toFun : Obj → R
  iso : ∀ {a b}, P.iso a b → toFun a = toFun b
  empty : toFun P.empty = 0
  unit : toFun P.unit = 1
  product : ∀ a b, toFun (P.product a b) = toFun a * toFun b
  scissor : ∀ {a b c d}, P.scissor a b c d → toFun a + toFun b = toFun c + toFun d

namespace Invariant

@[ext] theorem ext {f g : Invariant P (R := R)} (h : ∀ a, f.toFun a = g.toFun a) : f = g := by
  cases f
  cases g
  congr
  exact funext h

end Invariant

def evaluate (f : Invariant P (R := R)) : MvPolynomial Obj ℕ →+* R :=
  MvPolynomial.eval₂Hom (Nat.castRingHom R) f.toFun

theorem evaluate_respects (f : Invariant P (R := R)) :
    congruence P ≤ RingCon.ker (evaluate P f) := by
  apply RingCon.ringConGen_le.mpr
  intro p q h
  change evaluate P f p = evaluate P f q
  cases h with
  | iso h => simpa only [evaluate, MvPolynomial.eval₂Hom_X'] using f.iso h
  | empty => simpa only [evaluate, MvPolynomial.eval₂Hom_X', map_zero] using f.empty
  | unit => simpa only [evaluate, MvPolynomial.eval₂Hom_X', map_one] using f.unit
  | product a b =>
    simpa only [evaluate, map_mul, MvPolynomial.eval₂Hom_X'] using (f.product a b).symm
  | scissor h =>
    simpa only [evaluate, map_add, MvPolynomial.eval₂Hom_X'] using f.scissor h

def lift (f : Invariant P (R := R)) : KPlus P →+* R :=
  (congruence P).lift (evaluate P f) (evaluate_respects P f)

@[simp] theorem lift_of (f : Invariant P (R := R)) (a : Obj) : lift P f (of P a) = f.toFun a := by
  simp only [lift, of, quotientHom, RingCon.lift_mk', evaluate, MvPolynomial.eval₂Hom_X']

theorem hom_ext {F G : KPlus P →+* R} (h : ∀ a, F (of P a) = G (of P a)) : F = G := by
  have hpoly : F.comp (quotientHom P) = G.comp (quotientHom P) := by
    apply MvPolynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · exact h
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := (congruence P).mk'_surjective z
  exact DFunLike.congr_fun hpoly p

def restrict (F : KPlus P →+* R) : Invariant P (R := R) where
  toFun a := F (of P a)
  iso h := congrArg F (of_iso P h)
  empty := by rw [of_empty, map_zero]
  unit := by rw [of_unit, map_one]
  product a b := by rw [of_product, map_mul]
  scissor h := by simpa only [map_add] using congrArg F (of_scissor P h)

/-- The universal property of the positive scissor semiring, with no
cancellation, subtraction, or group-completion premise. -/
def universalEquiv : Invariant P (R := R) ≃ (KPlus P →+* R) where
  toFun := lift P
  invFun := restrict P
  left_inv f := by apply Invariant.ext; intro a; exact lift_of P f a
  right_inv F := by apply hom_ext P; intro a; exact lift_of P (restrict P F) a

end SpecialTransformations.Section4.PositiveGrothendieck

end
