module

/-
Saturation and monster models, in the shape of Marker's *Model Theory: An Introduction*
(GTM 217): types over a parameter set, `κ`-saturation ("every type over fewer than `κ`
parameters is realized"), strong `κ`-homogeneity ("every partial elementary map on fewer than
`κ` parameters extends to an automorphism"), and a `MonsterModel` bundling a model of a theory
with a cardinal at which it has both properties.

This is the interface the paper's Sections 3-8 are stated over: the author's ruling
(`Milestone0/DECISION.md`, "Saturation") is that saturation enters as a genuine notion of this
shape, **not** as a list of stated consequences, so that the paper's own lemmas about the
monster model have to be *proved* from it rather than assumed alongside it.

Nothing about `ACVF` is used below: the definitions are for Mathlib's general
`FirstOrder.Language`, and the instantiation is the abbreviation `MonsterACVF` at the end.
Check this file with

    cp Milestone0/Encoding.lean .scratch2/sec3/Enc.lean
    (cd .scratch2/sec3 && LEAN_PATH=$PWD:$LEAN_PATH lean -o Enc.olean Enc.lean)
    cd .scratch2/sec3 && cp ../../Milestone0/Saturation.lean Sat.lean &&
      LEAN_PATH=$PWD:$LEAN_PATH lean Sat.lean

(It imports `Enc`, a compiled `Milestone0/Encoding.lean`, exactly like `QE/Sec3_frozen.lean`;
the encoding is 115 kB of definitions and copying it again as a standalone snapshot would add a
third divergent copy of the frozen statements.)
-/
public import Enc

@[expose] public section

open FirstOrder FirstOrder.Language
open scoped FirstOrder

universe u w w'

namespace SpecialTransformations
namespace Milestone0
namespace Sat

/-! ## 1. Types over a parameter set (Marker, types over `A`)

A type over the parameters `v : A → M` in `n` free variables is a set of formulas with
parameters from `A`; it is *finitely satisfiable* in `M` if every finite subset has a common
solution in `M`.  These are Marker's `tp^M(a/A)` and "`p` is finitely satisfiable in `M`", with
the parameter set given by its indexing map (a subset of `M` is an injective `v`). -/

variable {L : Language.{u}} {M : Type w} {N : Type w} [L.Structure M] [L.Structure N]

/-- The type of the tuple `a : Fin n → M` over the parameters `v : A → M`. -/
def typeOf {A : Type w'} {n : ℕ} (v : A → M) (a : Fin n → M) : Set (L.BoundedFormula A n) :=
  {φ | φ.Realize v a}

@[simp]
theorem mem_typeOf {A : Type w'} {n : ℕ} {v : A → M} {a : Fin n → M}
    {φ : L.BoundedFormula A n} : φ ∈ typeOf v a ↔ φ.Realize v a :=
  Iff.rfl

/-- `p` is finitely satisfiable under the parameters `v`: every finite list of members of `p`
has a common solution. -/
def FinitelySatisfiable {A : Type w'} {n : ℕ} (v : A → M)
    (p : Set (L.BoundedFormula A n)) : Prop :=
  ∀ l : List (L.BoundedFormula A n), (∀ φ ∈ l, φ ∈ p) →
    ∃ xs : Fin n → M, ∀ φ ∈ l, φ.Realize v xs

/-- The type of an actual tuple is finitely satisfiable. -/
theorem finitelySatisfiable_typeOf {A : Type w'} {n : ℕ} (v : A → M) (a : Fin n → M) :
    FinitelySatisfiable (L := L) v (typeOf (L := L) v a) := by
  intro l hl
  exact ⟨a, fun φ hφ => (mem_typeOf (L := L)).1 (hl φ hφ)⟩

/-! ## 2. `κ`-saturation

Marker's definition, kept in the "finitely satisfiable" form, which is the form the compactness
argument in the paper's §4 uses: `N` is `κ`-saturated if every finitely satisfiable type over
fewer than `κ` parameters is realized in `N`. -/

/-- **`κ`-saturation**: every finitely satisfiable type over fewer than `κ` parameters is
realized. -/
def Saturated (N : Type w) [L.Structure N] (κ : Cardinal.{w'}) : Prop :=
  ∀ (A : Type w') (v : A → N), Cardinal.mk A < κ →
    ∀ {n : ℕ} (p : Set (L.BoundedFormula A n)), FinitelySatisfiable (M := N) v p →
      ∃ xs : Fin n → N, ∀ φ ∈ p, φ.Realize v xs

/-- Saturation is monotone in the cardinal: `κ'`-saturated implies `κ`-saturated for `κ ≤ κ'`
(there are fewer types to realize). -/
theorem Saturated.anti {κ κ' : Cardinal.{w'}} (h : Saturated (L := L) N κ') (hle : κ ≤ κ') :
    Saturated (L := L) N κ := by
  intro A v hA
  exact h A v (lt_of_lt_of_le hA hle)

/-- The elimination rule of `Saturated`, named for use at the paper's `κ = |M|⁺`. -/
theorem Saturated.realizes {κ : Cardinal.{w'}} (h : Saturated (L := L) N κ) {A : Type w'}
    (v : A → N) (hA : Cardinal.mk A < κ) {n : ℕ} {p : Set (L.BoundedFormula A n)}
    (hp : FinitelySatisfiable v p) :
    ∃ xs : Fin n → N, ∀ φ ∈ p, φ.Realize v xs :=
  h A v hA p hp

/-! ## 3. Partial elementary maps and homogeneity

A *partial elementary map* is an injective map on a parameter set that preserves every formula;
it is presented by the pair `(v, w)` of its values on the two sides, `v : A → M` (typically the
inclusion of a subset) and `w : A → N` (its image). -/

/-- `(v, w)` is a partial elementary map: every formula with parameters from `A` has the same
truth value at a tuple drawn from `A` on the two sides. -/
def PartialElementary (v : A → M) (w : A → N) : Prop :=
  ∀ {n : ℕ} (φ : L.BoundedFormula A n) (as : Fin n → A),
    φ.Realize v (fun i => v (as i)) ↔ φ.Realize w (fun i => w (as i))

/-- **Strong `κ`-homogeneity** (the monster-model condition): every partial elementary map on
fewer than `κ` parameters extends to an automorphism. -/
def StronglyHomogeneous (M : Type w) [L.Structure M] (κ : Cardinal.{w'}) : Prop :=
  ∀ (A : Type w') (v w : A → M), Cardinal.mk A < κ → PartialElementary (L := L) v w →
    ∃ e : M ≃[L] M, ∀ a, e (v a) = w a

/-! ## 4. Monster models

A monster model of a theory is a model that is `κ`-saturated and strongly `κ`-homogeneous for a
`κ` at least countable and larger than every parameter set the paper's arguments use.
"Small" means `< κ`.  The existence of such models is model theory that the author has ruled
may be taken as given (`Milestone0/DECISION.md`, "Saturation"); it enters as the *data* of this
structure, so that every statement which uses it mentions `𝕄.κ` and the hypothesis `|A| < 𝕄.κ`
explicitly, and no paper lemma is assumed alongside it. -/

/-- A monster model: a model `M` of `T`, a cardinal `κ ≥ ℵ₀`, `κ`-saturation and strong
`κ`-homogeneity of `M`. -/
structure MonsterModel (L : Language.{u}) (T : L.Theory) where
  /-- the carrier of the monster model -/
  M : Type w
  /-- the `L`-structure on the carrier -/
  [str : L.Structure M]
  /-- the carrier is nonempty -/
  [ne : Nonempty M]
  /-- the saturation cardinal (`κ` "larger than everything small" in the paper) -/
  κ : Cardinal.{w'}
  /-- the carrier is a model of `T` -/
  isModel : M ⊨ T
  /-- `κ`-saturation -/
  saturated : Saturated (L := L) M κ
  /-- strong `κ`-homogeneity -/
  homogeneous : StronglyHomogeneous (L := L) M κ
  /-- `κ` is at least countable, so every finite parameter set is small -/
  aleph0_le : Cardinal.aleph0 ≤ κ

attribute [instance] MonsterModel.str MonsterModel.ne

namespace MonsterModel

variable {L : Language.{u}} {T : L.Theory} (𝕄 : MonsterModel L T)

/-- A small set of parameters: `|A| < κ`. -/
def Small (A : Type w') : Prop := Cardinal.mk A < 𝕄.κ

/-- **Types over small parameter sets are realized.**  This is the property a *positive*
existential use needs (e.g. "a type all of whose finite subsets are consistent has a solution"). -/
theorem realizes {A : Type w'} (v : A → 𝕄.M) (hA : 𝕄.Small A) {n : ℕ}
    {p : Set (L.BoundedFormula A n)} (hp : FinitelySatisfiable (M := 𝕄.M) v p) :
    ∃ xs : Fin n → 𝕄.M, ∀ φ ∈ p, φ.Realize v xs :=
  𝕄.saturated A v hA p hp

/-- The type of an element of a monster model is realized in it (no smallness needed). -/
theorem realizes_typeOf {A : Type w'} (v : A → 𝕄.M) (a : Fin 1 → 𝕄.M) :
    ∃ xs : Fin 1 → 𝕄.M, ∀ (φ : L.BoundedFormula A 1), φ ∈ typeOf (L := L) v a →
      φ.Realize v xs :=
  ⟨a, fun _ hφ => (mem_typeOf (L := L)).1 hφ⟩

/-- **Homogeneity**: a partial elementary map on a small parameter set extends to an
automorphism.  This is the property every "we may assume, after an automorphism, that ..." step
in the paper's §3 uses. -/
theorem exists_automorphism {A : Type w'} {v w : A → 𝕄.M} (hA : 𝕄.Small A)
    (h : PartialElementary (L := L) v w) :
    ∃ e : 𝕄.M ≃[L] 𝕄.M, ∀ a, e (v a) = w a :=
  𝕄.homogeneous A v w hA h

/-- Every finite parameter set is small in a monster model. -/
theorem mk_fin_lt (n : ℕ) : Cardinal.mk (Fin n) < 𝕄.κ := by
  rw [Cardinal.mk_fin]
  exact lt_of_lt_of_le Cardinal.natCast_lt_aleph0 𝕄.aleph0_le

/-- The empty parameter set is small. -/
theorem mk_empty_lt : Cardinal.mk (Empty : Type) < 𝕄.κ := by
  simpa using 𝕄.mk_fin_lt 0

/-- Every finite parameter set is small — in particular the sorted pair of tuples that every §3
statement has as its parameters. -/
theorem small_of_finite {A : Type w'} [Finite A] : 𝕄.Small A := by
  rw [Small]
  exact lt_of_lt_of_le (Cardinal.lt_aleph0_of_finite A) 𝕄.aleph0_le

end MonsterModel

/-! ## 5. The instantiation at the frozen encoding

The paper's Sections 3-8 work in a monster model of `ACVF` (`Milestone0/Encoding.lean`), with
`S` a small substructure.  The abbreviation below is the type those statements quantify over;
`MonsterModel.isModel` gives `𝕄.M ⊨ Axioms.ACVF`, so every axiom of the frozen theory is
available inside the monster model at no extra cost. -/

/-- A monster model of the frozen theory `ACVF` of `L_RV`. -/
abbrev MonsterACVF : Type _ := MonsterModel LRV Axioms.ACVF

/-- The frozen theory holds in a monster model of it. -/
theorem MonsterACVF.model (𝕄 : MonsterACVF) : 𝕄.M ⊨ Axioms.ACVF := 𝕄.isModel

end Sat
end Milestone0
end SpecialTransformations
