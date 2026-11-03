/-
  **Prime models over substructures for the theory of fields** in the language of rings.

  Johnson's Definition 2.1.1 for `T₀ = Theory.field`: every substructure `S` of a model of
  `Theory.field` (that is, every integral domain presented as a `Language.ring`-structure that
  embeds into a field) has a prime model over it, namely its fraction field.

  The construction avoids transferring ring instances to the abstract `S`: instead of `Frac(S)`
  the file uses `Frac (FreeCommRing S ⧸ ker ψ)`, where `ψ = FreeCommRing.lift e` is the evaluation
  of polynomials along the embedding `e : S ↪ M`.  The whole content is that two embeddings of the
  same `S` have the same polynomial relations —
  `ker (FreeCommRing.lift e) = ker (FreeCommRing.lift f)` — which is proved by converting a
  polynomial into a *term* (`Ring.termOfFreeCommRing`) and using that embeddings commute with
  term evaluation.

  What is proved here: the polynomial relations of an abstract `S` are the same in every field
  it embeds into (`ker_lift_eq`), and the dictionary between ring homomorphisms and
  `Language.ring`-embeddings.  What is *not* yet proved here: the remaining assembly of the
  fraction field of the coordinate ring, the embedding `S ↪ Frac`, and the universal property
  (`IsFractionRing.lift`).  See `NOTES.md`.

  Only import: Mathlib.
-/
import Mathlib

open FirstOrder FirstOrder.Language
open FirstOrder.Ring
open Polynomial
open scoped FirstOrder

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace PrimeModels

universe u

/-! ## 1. Ring homomorphisms and `Language.ring`-embeddings -/

section Conversions

variable {A B : Type*} [CommRing A] [CommRing B] [CompatibleRing A] [CompatibleRing B]

theorem ringHom_map_fun (f : A →+* B) {n : ℕ} (g : Language.ring.Functions n)
    (x : Fin n → A) : f (Structure.funMap g x) = Structure.funMap g (f ∘ x) := by
  cases g <;> simp

/-- An injective ring homomorphism is an embedding for the language of rings. -/
def embeddingOfInjectiveRingHom (f : A →+* B) (hf : Function.Injective f) :
    A ↪[Language.ring] B where
  toFun := f
  inj' := hf
  map_fun' := ringHom_map_fun f
  map_rel' := by intro n R; exact isEmptyElim R

end Conversions

/-! ## 2. Two embeddings of one structure have the same polynomial relations -/

section Kernel

variable {S : Type u} [Language.ring.Structure S]
variable {M : Type u} [CommRing M] [CompatibleRing M]
variable {N : Type u} [CommRing N] [CompatibleRing N]

/-- `FreeCommRing.lift (fun s => e s) p` only depends on the term that `p` represents. -/
theorem lift_eq_apply_term (e : S ↪[Language.ring] M) (p : FreeCommRing S) :
    FreeCommRing.lift (fun s => e s) p
      = e (Term.realize (fun s => s) (Ring.termOfFreeCommRing p)) := by
  rw [← Ring.realize_termOfFreeCommRing p (fun s => e s)]
  exact HomClass.realize_term (g := e) (v := fun s => s)

/-- The zero of `S`, described intrinsically (as the value of the zero term), so that no ring
structure on `S` is needed. -/
def zeroTerm : Language.ring.Term S :=
  Term.func (FirstOrder.Ring.zeroFunc) (fun i => (i.elim0 : Language.ring.Term S))

theorem apply_zeroTerm {R : Type u} [CommRing R] [CompatibleRing R] (g : S ↪[Language.ring] R) :
    g (Term.realize (fun s => s) (zeroTerm (S := S))) = 0 := by
  rw [zeroTerm, Term.realize_func]
  rw [g.map_fun (FirstOrder.Ring.zeroFunc)]
  exact CompatibleRing.funMap_zero _

theorem apply_eq_zero_iff {R : Type u} [CommRing R] [CompatibleRing R]
    (g : S ↪[Language.ring] R) (w : S) :
    g w = 0 ↔ w = Term.realize (fun s => s) (zeroTerm (S := S)) := by
  constructor
  · intro h
    apply g.injective
    rw [h, apply_zeroTerm]
  · intro h
    rw [h, apply_zeroTerm]

/-- **The polynomial relations of an abstract structure are the same in every field it embeds
into.** -/
theorem ker_lift_eq (e : S ↪[Language.ring] M) (f : S ↪[Language.ring] N) :
    RingHom.ker (FreeCommRing.lift (fun s => e s))
      = RingHom.ker (FreeCommRing.lift (fun s => f s)) := by
  ext p
  rw [RingHom.mem_ker, RingHom.mem_ker, lift_eq_apply_term e, lift_eq_apply_term f,
    apply_eq_zero_iff e, apply_eq_zero_iff f]

end Kernel


#print axioms PrimeModels.ker_lift_eq
#print axioms PrimeModels.lift_eq_apply_term

end PrimeModels
