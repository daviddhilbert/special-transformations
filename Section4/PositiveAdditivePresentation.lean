module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Group.Nat.Hom
public import Mathlib.Data.Finsupp.Ext
public import Mathlib.GroupTheory.Congruence.Hom

@[expose] public section

/-!+# Positive additive scissor presentations

The fixed-degree RV categories are not closed under products. Their positive
Grothendieck objects therefore start with an additive presentation. This
module uses Mathlib's free commutative additive monoid and additive
congruences, without imposing multiplication or cancellation.

The geometric instantiation and comparison with actual isomorphism classes
remain separate obligations; this universal property alone does not prove them.
-/

open Classical

noncomputable section

namespace SpecialTransformations.Section4.PositiveAdditiveGrothendieck

universe u v

structure Presentation (Obj : Type u) where
  iso : Obj → Obj → Prop
  empty : Obj
  scissor : Obj → Obj → Obj → Obj → Prop

variable {Obj : Type u} (P : Presentation Obj)

def generator (a : Obj) : Obj →₀ ℕ := Finsupp.single a 1

inductive Relation : (Obj →₀ ℕ) → (Obj →₀ ℕ) → Prop
  | iso {a b} : P.iso a b → Relation (generator a) (generator b)
  | empty : Relation (generator P.empty) 0
  | scissor {a b c d} : P.scissor a b c d →
      Relation (generator a + generator b) (generator c + generator d)

def congruence : AddCon (Obj →₀ ℕ) := addConGen (Relation P)

abbrev KPlus := (congruence P).Quotient

def quotientHom : (Obj →₀ ℕ) →+ KPlus P := (congruence P).mk'

def of (a : Obj) : KPlus P := quotientHom P (generator a)

theorem quotient_relation {p q : Obj →₀ ℕ} (h : Relation P p q) :
    quotientHom P p = quotientHom P q :=
  (congruence P).eq.mpr (AddConGen.Rel.of p q h)

theorem of_iso {a b : Obj} (h : P.iso a b) : of P a = of P b :=
  quotient_relation P (Relation.iso h)

@[simp] theorem of_empty : of P P.empty = 0 :=
  (quotient_relation P Relation.empty).trans (map_zero (quotientHom P))

theorem of_scissor {a b c d : Obj} (h : P.scissor a b c d) :
    of P a + of P b = of P c + of P d :=
  (map_add (quotientHom P) _ _).symm.trans
    ((quotient_relation P (Relation.scissor h)).trans (map_add (quotientHom P) _ _))

variable {A : Type v} [AddCommMonoid A]

structure Invariant where
  toFun : Obj → A
  iso : ∀ {a b}, P.iso a b → toFun a = toFun b
  empty : toFun P.empty = 0
  scissor : ∀ {a b c d}, P.scissor a b c d → toFun a + toFun b = toFun c + toFun d

namespace Invariant

@[ext] theorem ext {f g : Invariant P (A := A)} (h : ∀ a, f.toFun a = g.toFun a) : f = g := by
  cases f
  cases g
  congr
  exact funext h

end Invariant

def evaluate (f : Invariant P (A := A)) : (Obj →₀ ℕ) →+ A :=
  Finsupp.liftAddHom (fun a => multiplesHom A (f.toFun a))

@[simp] theorem evaluate_generator (f : Invariant P (A := A)) (a : Obj) :
    evaluate P f (generator a) = f.toFun a := by
  simp only [evaluate, generator, Finsupp.liftAddHom_apply_single, multiplesHom_apply, one_nsmul]

theorem evaluate_respects (f : Invariant P (A := A)) :
    congruence P ≤ AddCon.ker (evaluate P f) := by
  apply AddCon.addConGen_le.mpr
  intro p q h
  change evaluate P f p = evaluate P f q
  cases h with
  | iso h => simpa only [evaluate_generator] using f.iso h
  | empty => simpa only [evaluate_generator, map_zero] using f.empty
  | scissor h => simpa only [map_add, evaluate_generator] using f.scissor h

def lift (f : Invariant P (A := A)) : KPlus P →+ A :=
  (congruence P).lift (evaluate P f) (evaluate_respects P f)

@[simp] theorem lift_of (f : Invariant P (A := A)) (a : Obj) :
    lift P f (of P a) = f.toFun a := by
  simp only [lift, of, quotientHom, AddCon.lift_mk', evaluate_generator]

theorem hom_ext {F G : KPlus P →+ A} (h : ∀ a, F (of P a) = G (of P a)) : F = G := by
  have hfree : F.comp (quotientHom P) = G.comp (quotientHom P) := by
    apply Finsupp.addHom_ext'
    intro a
    apply AddMonoidHom.ext_nat
    exact h a
  apply AddMonoidHom.ext
  intro z
  obtain ⟨p, rfl⟩ := (congruence P).mk'_surjective z
  exact DFunLike.congr_fun hfree p

def restrict (F : KPlus P →+ A) : Invariant P (A := A) where
  toFun a := F (of P a)
  iso h := congrArg F (of_iso P h)
  empty := by rw [of_empty, map_zero]
  scissor h := by simpa only [map_add] using congrArg F (of_scissor P h)

/-- The positive additive scissor universal property, valid before any
group completion and without a cancellation premise. -/
def universalEquiv : Invariant P (A := A) ≃ (KPlus P →+ A) where
  toFun := lift P
  invFun := restrict P
  left_inv f := by apply Invariant.ext; intro a; exact lift_of P f a
  right_inv F := by apply hom_ext P; intro a; exact lift_of P (restrict P F) a

end SpecialTransformations.Section4.PositiveAdditiveGrothendieck

end
