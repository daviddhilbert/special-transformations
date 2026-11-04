/-
**The quoted classical statements Theorem 2.3's route consumes.**

Author rulings of 2026-11-04, binding for this project:

* **Marker ruling**: model theory in Dave Marker's book may be taken as given — statements only.
* **Prestel-Engler ruling**: general valuation theory in Prestel-Engler likewise.

This file is the one place those statements are transcribed for reuse, each as a named `Prop`
with the book's content in its docstring.  Downstream files cite them; nothing here is proved.
The discipline is in `MILESTONES.md`.

The valuation-theoretic statements are at the abstract level of a field with a Mathlib
`Valuation`, which the frozen `ACVF` supplies on its `VF` sort by
`QE/VFValued.lean`'s `exists_valuation_predV`.
-/
import Mathlib

open Polynomial

namespace ClassicalProps

variable {K Γ Γ' : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-! ### Henselization (Prestel-Engler, *Valued Fields*)

Every valued field `K` has a **henselization** `K^h`: a henselian valued extension characterized
by the universal property for extensions into henselian fields — and the henselization has the
**same residue field** and the **same value group** as the base:

* `K(K^h) = K(K)` — every unit of `K^h` is approximated by a base element to within the maximal
  ideal;
* `Γ(K^h) = Γ(K)` — every element of `K^h` has the value of an element of the base;
* any embedding of `K` into a henselian valued field factors through `K^h`.

The Prestel-Engler theorem, as a quotation; never proved here. -/

/-- **A henselization of a valued field, packaged.**  The Prestel-Engler properties at an
extension `(L, w)` of `(K, v)`: henselian, same value group, same residue field, and the
universal factorization property into henselian valued fields extending the base. -/
structure HenselizationOf {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) where
  /-- the henselization field -/
  L : Type
  /-- its field structure -/
  fieldL : Field L
  /-- the embedding -/
  emb : K →+* L
  /-- the henselization field's value group and valuation, *with the same value group as `v`* -/
  w : Valuation L Γ
  /-- it extends `v` -/
  spec : ∀ x : K, w (emb x) = v x
  /-- it is henselian -/
  henselian : HenselianLocalRing w.integer
  /-- **same residue field**: every unit of `L` is approximated, to within the maximal ideal, by
  a unit of the base -/
  same_residue : ∀ u : L, w u = 1 → ∃ k : K, w (emb k) = 1 ∧ w (emb k - u) < 1
  /-- **same value group**: every nonzero element of `L` has the value of an element of the base
  (together with `spec`, the value groups coincide) -/
  same_value : ∀ x : L, x ≠ 0 → ∃ k : K, v k = w x
  /-- **universal property**: an embedding into a henselian valued field factors through the
  henselization -/
  universal : ∀ {L2 : Type} [Field L2]
    (w₂ : Valuation L2 Γ) (_ : HenselianLocalRing w₂.integer)
    (j : K →+* L2) (_ : ∀ x : K, w₂ (j x) = v x),
    ∃ l : L →+* L2, (∀ x : K, l (emb x) = j x) ∧ (∀ y : L, w₂ (l y) = w y)

/-- **Prestel-Engler**: every valued field has a henselization. -/
def HenselizationExists : Prop :=
  ∀ {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ),
    Nonempty (HenselizationOf v)

/-! ### The divisible hull of an ordered abelian group

An ordered abelian group `G` admits a **divisible hull** `G^(1/n)`: a divisible ordered abelian
group containing `G`, initial with this property — every divisible ordered abelian group
receiving a monotone embedding of `G` receives the hull uniquely, and every element of the hull
has a positive multiple lying in the image of `G`.  Prestel-Engler, *Valued Fields*, as a
quotation; never proved here.  In the encoding `Γ = RV/Kˣ` is no sort, so this is the group-side
fact the `Γ(S*)`-divisible step of Lemma 3.3 consumes. -/

/-- **The divisible hull quotation.**  Every element `h` of the hull has a positive multiple
`n • h` in the image of the original group. -/
def DivisibleHullExists : Prop :=
  ∀ (G : Type) [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G], ∃ (H : Type) (_ : AddCommGroup H) (_ : LinearOrder H) (_ : IsOrderedAddMonoid H)
    (_ : DivisibleBy H ℕ) (j : G →+ H), Function.Injective j ∧ Monotone j ∧
      (∀ h : H, ∃ n : ℕ, 0 < n ∧ ∃ g : G, n • h = j g)

/-! ### ACF extension of embeddings (Marker)

*Marker*: an embedding of an algebraically closed field into an algebraically closed field
extends along an *algebraic* extension of its domain.  (This is the field homomorphism
`K(M) → K(N)` at Lemma 3.3's step (i), the size hypotheses supplying transcendence bases.)
Mathlib states the same content as `IsAlgClosed.lift`; under the ruling it is a quotation. -/
def ACFExtendsAlgebraicEmbeddings : Prop :=
  ∀ {K E F : Type} [Field K] [Field E] [Field F] [Algebra K E] [IsAlgClosed F]
    (_ : Algebra.IsAlgebraic K E) (j : K →+* F), ∃ l : E →+* F, ∀ x : K, l (algebraMap K E x) = j x

end ClassicalProps
