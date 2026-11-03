/-
Milestone 0 for: Yimu Yin, "Special transformations in algebraically closed valued fields",
Annals of Pure and Applied Logic (2010), arXiv:1006.2467.

The paper's language `L_RV` (Definition 2.1), the theory `ACVF` (Definition 2.2), the
theory `ACVF_S(0,0)`, and the statements of quantifier elimination (Theorem 2.3) and
C-minimality (Theorem 2.8), encoded in Mathlib's one-sorted first-order model theory by
putting the sorts of `L_RV` on a single tagged carrier with unary sort predicates.

This file is self-contained: its only import is `Mathlib`.  Check it with

    lean RepairedTheory.lean

It contains no `sorry` and no `axiom`.  Parts 0–5 are the encoding and the axioms,
the interpretation of the symbols follows, and an appended section (`namespace Fixed`)
extracts the axioms used by this repository's earlier inconsistency argument and records
what the author's ruling on `0` and `∞` does to that argument.  The paper's `0` and `∞`
of the `RV` sort are ONE element (`rv(0) = 0` is the absorbing element, `∞` is another
name for it): the language has the single constant `rvZero`, and `tRVInfty` is a
definition of `tRVZero`.
-/
import Mathlib

/-!
## Reading guide

* Part 0  the paper's `RV` sort, copied verbatim (conventions) from
          `SpecialTransformations/Basic.lean` of this repository.
* Part 1  the sorts of `L_RV`, as a tag type, and the symbols of `L_RV` with their
          sort signatures (Definition 2.1).
* Part 2  term/formula constructors for the encoded language.
* Part 3  the axioms of `ACVF` (Definition 2.2), item by item, and of `ACVF(0,0)`.
* Part 4  the value-group sort `Γ` as an extra tag (the paper treats `Γ` as an
          imaginary sort; `Γ` is needed for the substructure `S`) and the expansion
          `L_RV^Γ` together with the axioms linking `Γ` to `RV`.
* Part 5  `ACVF_S(0,0)`: the theory `ACVF(0,0)` together with the atomic diagram of a
          substructure `S`.
* Part 6  the interpretation of the symbols in a model, for use in the statements
          (the two target theorems, Theorem 2.3 and Theorem 2.8, are stated in
          `Milestone0/Encoding.lean`, which is where they are proved).
* appended: `namespace Fixed`, the extraction of the axioms used by the earlier
          inconsistency argument, and what the ruling `0 = ∞` does to that argument.
-/

open FirstOrder FirstOrder.Language

namespace SpecialTransformations
namespace Milestone0

/-! ## Part 0. The paper's `RV` sort (conventions of `SpecialTransformations/Basic.lean`) -/

/- The algebraic layer of the paper, as it exists in the repository: `RV^× = Kˣ/(1+M)`,
`RV = RV^× ∪ {∞}`, `RV₀ = RV ∪ {0}` and `rv : K → RV`. -/
namespace Valued

open Valuation

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀)

/-- `RV× = Kˣ / (1 + M)`, the multiplicative RV sort. -/
abbrev RVUnit : Type _ := Kˣ ⧸ v.valuationSubring.principalUnitGroup

/-- The RV sort with the point at infinity: `RV = RV× ∪ {∞}`.  `none` is `∞`. -/
abbrev RV : Type _ := Option (RVUnit v)

/-- `RV0 = RV ∪ {0}`.  The outer `none` is the added `0`. -/
abbrev RV0 : Type _ := Option (RV v)

/-- The quotient map `rv : K → RV`, with `rv 0 = ∞`. -/
noncomputable def rv (x : K) : RV v := by
  classical
  exact if h : x = 0 then none else some (QuotientGroup.mk (Units.mk0 x h))

end Valued

/-! ## Part 1. The sorts and the symbols of `L_RV` (Definition 2.1)

Definition 2.1 of the paper gives a language with two sorts:

* a `VF`-sort with the language of rings `L_R = {0, 1, +, -, ×}`;
* an `RV`-sort with the group language `{1, ×}`, two constants `0` and `∞`, a unary
  predicate `Kˣ`, a binary function `+ : K² → K` and a unary function `- : K → K`
  (where `K = Kˣ ∪ {0}`), and a binary relation `≤`;
* a function symbol `rv` from the `VF`-sort into the `RV`-sort.

### Encoding

Mathlib's `FirstOrder.Language` is one-sorted: `Language.Functions n` and
`Language.Relations n` are the `n`-ary symbols of a language over *one* carrier type.
We therefore use a single carrier `M` with a tag `SortTag` for the sorts, plus a unary
sort predicate for each sort.  The *names* of the function symbols record their sort
signature: `vfAdd` is the addition of the ring language of the `VF` sort, `kAdd` is the
addition of `K = Kˣ ∪ {0}` inside the `RV` sort, and so on.
-/

/-- The sorts of `L_RV`, as tags on the single carrier. -/
inductive SortTag where
  | vf
  | rv
  deriving DecidableEq, Repr

/-- Function symbols of `L_RV`, tagged by arity. -/
inductive Fn : ℕ → Type where
  /-- `0` of the ring language of the `VF` sort -/
  | vfZero : Fn 0
  /-- `1` of the ring language of the `VF` sort -/
  | vfOne : Fn 0
  /-- `+` of the ring language of the `VF` sort -/
  | vfAdd : Fn 2
  /-- `-` of the ring language of the `VF` sort -/
  | vfNeg : Fn 1
  /-- `×` of the ring language of the `VF` sort -/
  | vfMul : Fn 2
  /-- `1` of the group language of the `RV` sort -/
  | rvOne : Fn 0
  /-- the constant `0` of the `RV` sort: the residue field's zero, which is also `rv(0)` and
  the absorbing element of `RV`.  The paper writes this element both as `0` and as `∞`; it is
  one element, so the language has one constant. -/
  | rvZero : Fn 0
  /-- `×` of the `RV` sort -/
  | rvMul : Fn 2
  /-- `+ : K² → K` of the `RV` sort -/
  | kAdd : Fn 2
  /-- `- : K → K` of the `RV` sort -/
  | kNeg : Fn 1
  /-- the projection `rv : VF → RV` -/
  | rvMap : Fn 1

/-- Relation symbols of `L_RV`, tagged by arity.  The first two are the sort predicates
of the encoding (they are not part of the paper's signature); the last two are the
paper's unary predicate `Kˣ` and its preorder `≤`. -/
inductive Rel : ℕ → Type where
  /-- encoding: the `VF` sort -/
  | memVF : Rel 1
  /-- encoding: the `RV` sort -/
  | memRV : Rel 1
  /-- the paper's unary predicate `Kˣ` -/
  | memUnits : Rel 1
  /-- the paper's preorder `≤` on `RV` -/
  | rvLe : Rel 2

/-- **The language `L_RV` of Definition 2.1**, in the tagged one-sorted encoding. -/
abbrev LRV : Language := ⟨Fn, Rel⟩

namespace LRV

/-! ### Terms and formulas of `L_RV` with variables among `Fin n` and no parameters -/

/-- Terms of `L_RV` whose (free) variables are indexed by `Fin n`. -/
abbrev Tm (n : ℕ) : Type := LRV.Term (Empty ⊕ Fin n)

/-- Bounded formulas of `L_RV` with `n` variables in scope and no free parameters. -/
abbrev Bf (n : ℕ) : Type := LRV.BoundedFormula Empty n

variable {n : ℕ}

/-! #### Term constructors -/

/-- `0` of the `VF` sort -/
def tVFZero : Tm n := Term.func Fn.vfZero fun i => i.elim0
/-- `1` of the `VF` sort -/
def tVFOne : Tm n := Term.func Fn.vfOne fun i => i.elim0
/-- `+` of the `VF` sort -/
def tVFAdd (t u : Tm n) : Tm n := Term.func Fn.vfAdd ![t, u]
/-- `-` of the `VF` sort -/
def tVFNeg (t : Tm n) : Tm n := Term.func Fn.vfNeg ![t]
/-- `×` of the `VF` sort -/
def tVFMul (t u : Tm n) : Tm n := Term.func Fn.vfMul ![t, u]
/-- `1` of the `RV` sort -/
def tRVOne : Tm n := Term.func Fn.rvOne fun i => i.elim0
/-- `0` of the `RV` sort -/
def tRVZero : Tm n := Term.func Fn.rvZero fun i => i.elim0
/-- The paper's `∞` is `rv(0)`, i.e. the absorbing element `rvZero` of the `RV` sort: the paper's
two symbols `0` and `∞` name one element.  Kept as a definition so that the axioms can be read
in the paper's notation. -/
def tRVInfty : Tm n := tRVZero
/-- `×` of the `RV` sort -/
def tRVMul (t u : Tm n) : Tm n := Term.func Fn.rvMul ![t, u]
/-- `+ : K² → K` of the `RV` sort -/
def tKAdd (t u : Tm n) : Tm n := Term.func Fn.kAdd ![t, u]
/-- `- : K → K` of the `RV` sort -/
def tKNeg (t : Tm n) : Tm n := Term.func Fn.kNeg ![t]
/-- the projection `rv : VF → RV` -/
def tRv (t : Tm n) : Tm n := Term.func Fn.rvMap ![t]

/-- the bound variable of index `i < n` -/
def tv (i : ℕ) (h : i < n) : Tm n := Term.var (Sum.inr ⟨i, h⟩)

/-- the numeral `k · 1` of the `VF` sort -/
def tVFNumeral : ℕ → Tm n
  | 0 => tVFZero
  | k + 1 => tVFAdd (tVFNumeral k) tVFOne

/-- `t ^ k`, in the `VF` sort -/
def tVFPow (t : Tm n) : ℕ → Tm n
  | 0 => tVFOne
  | k + 1 => tVFMul (tVFPow t k) t

/-- `t ^ k`, in the `RV` sort -/
def tRVPow (t : Tm n) : ℕ → Tm n
  | 0 => tRVOne
  | k + 1 => tRVMul (tRVPow t k) t

/-! #### Formula constructors -/

/-- `t ∈ VF`, the encoding's sort predicate for the `VF` sort -/
def pVF (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memVF t
/-- `t ∈ RV`, the encoding's sort predicate for the `RV` sort -/
def pRVsort (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memRV t
/-- the paper's unary predicate `Kˣ` -/
def pUnits (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memUnits t
/-- the paper's preorder `≤` -/
def pLe (t u : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₂ Rel.rvLe t u
/-- `t = u` -/
def pEq (t u : Tm n) : Bf n := t =' u
/-- the paper's `RV = RV-sort ∖ {0}` -/
def pRV (t : Tm n) : Bf n := ∼(pEq t tRVZero)
/-- the paper's `K = RV-sort ∖ {∞}`.  Since `∞ = rv(0) = 0` this is the same predicate as
`pRV`; it is kept as a separate name so that statements read as in the paper. -/
def pK (t : Tm n) : Bf n := ∼(pEq t tRVInfty)
/-- the paper's `RV₀ = RV ∪ {0}`, i.e. the whole `RV` sort -/
def pRV0 (_t : Tm n) : Bf n := ⊤
/-- the strict order `t > 1` of the `RV` sort -/
def pGtOne (t : Tm n) : Bf n := pLe tRVOne t ⊓ ∼(pLe t tRVOne)
/-- `t ∈ K = K^× ∪ {0}`, the residue field inside the `RV` sort.

Not the same as `t ≠ 0`: when `Γ` is nontrivial the elements of `RV ∖ {0}` of value `≠ 1`
are not in `K`, and the residue-field operations are junk there.  Definition 2.1(d)
defines `K` as `K^× ∪ {0}`, with `K^×` the predicate, i.e. axiom (4)'s class of `1`.  The
`0` here is `rv(0)`, the absorbing element of `RV`. -/
def pInK (t : Tm n) : Bf n := pUnits t ⊔ pEq t tRVZero

end LRV

/-! ## Part 2 is below; the enclosing namespaces stay open to the end of the file. -/

namespace LRV

/-! ## Part 2. Guarded quantifiers

Since the carrier of a model of the encoding holds both sorts, every axiom of the paper
has to say which sort its variables range over.  `allSorted ss φ` is the sentence
`∀ x̄, (⋀ i, x_i ∈ s_i) → φ`, and `exSorted s φ` is the formula `∃ x ∈ s, φ`. -/

/-- the sort predicate of the sort `s`, as a formula -/
def sortPred (s : SortTag) (t : Tm n) : Bf n :=
  match s with
  | .vf => pVF t
  | .rv => pRVsort t

/-- `⋀ i, x_i ∈ s_i`, for the variables `x_i` of index `i` -/
def sortedHyps {k : ℕ} (ss : Fin k → SortTag) : Bf k :=
  (List.finRange k).foldr (fun i acc => sortPred (ss i) (tv i.val i.isLt) ⊓ acc) ⊤

/-- the guarded universal sentence `∀ x̄, (⋀ i, x_i ∈ s_i) → φ` -/
def allSorted {k : ℕ} (ss : Fin k → SortTag) (φ : Bf k) : LRV.Sentence :=
  BoundedFormula.alls (sortedHyps ss ⟹ φ)

/-- the guarded existential formula `∃ x ∈ s, φ`, where `x` is the variable of index `k` -/
def exSorted {k : ℕ} (s : SortTag) (φ : Bf (k + 1)) : Bf k :=
  BoundedFormula.ex (sortPred s (tv k (Nat.lt_succ_self k)) ⊓ φ)

/-! ### Quantification over the residue field `K = K^× ∪ {0}`

The `RV` sort's carrier holds the residue zero `0`, the multiplicative group `K^×`, *and* the
point `∞`.  The paper's field `K = K^× ∪ {0}` is therefore the *definable* subset
`RV-sort ∖ {∞}` — the constant `∞` is the marker of "not in `K`".  Axioms about the field `K`
must be relativised to it: with the sort predicate alone they would also be asserted at `∞`,
where `×` is absorbing (`t × ∞ = ∞`), and the field axiom "every nonzero element is
invertible" would then force `0 = ∞`. -/

/-- `⋀ i < k, x_i ≠ ∞`: the tuple lies in `K = RV-sort ∖ {∞}` -/
def kHyps {k : ℕ} : Bf k :=
  (List.finRange k).foldr (fun i acc => pInK (tv i.val i.isLt) ⊓ acc) ⊤

/-- the universal sentence `∀ x̄ ∈ s̄ ∩ K, φ` -/
def allSortedK {k : ℕ} (ss : Fin k → SortTag) (φ : Bf k) : LRV.Sentence :=
  BoundedFormula.alls ((sortedHyps ss ⊓ kHyps) ⟹ φ)

/-- the guarded existential formula `∃ x ∈ s ∩ K, φ`, with `x` the variable of index `k` -/
def exSortedK {k : ℕ} (s : SortTag) (φ : Bf (k + 1)) : Bf k :=
  BoundedFormula.ex (sortPred s (tv k (Nat.lt_succ_self k)) ⊓
    pInK (tv k (Nat.lt_succ_self k)) ⊓ φ)

/-- the universal closure of a formula in a single variable -/
def allOne (φ : Bf 1) : LRV.Sentence := BoundedFormula.alls φ

/-- Horner form `x^k + a_{k-1} x^{k-1} + ⋯ + a_0` of the monic polynomial of degree `k`
whose coefficients are the variables `0, …, k-1` and whose variable is the variable `k`.

The leading term is `x ^ k`, so `acfScheme` quantifies over *all* monic polynomials of
degree `k`.  (An earlier version started the Horner fold at `x` instead of at `x + a_{k-1}`,
which silently produced `x^{k+1} + a_{k-1}x^{k-1} + ⋯ + a_0` — a monic polynomial of degree
`k+1` with zero `x^k` coefficient, so the scheme covered only a proper subclass and did not
give algebraic closedness.)  For `k = 0` the value is immaterial: `acfScheme` is only used
with `1 ≤ k`. -/
def hornerPoly {k : ℕ} (add mul : {n : ℕ} → Tm n → Tm n → Tm n) : Tm (k + 1) :=
  match k with
  | 0 => tv 0 Nat.zero_lt_one
  | (n + 1) =>
    let x : Tm (n + 1 + 1) := tv (n + 1) (by omega)
    (List.finRange n).reverse.foldl
      (fun acc i => add (mul acc x) (tv i.val (by omega)))
      (add x (tv n (by omega)))

/-- Sanity check on the Horner form: at `k = 1` it is the monic linear `x + a₀`. -/
theorem hornerPoly_one :
    hornerPoly (k := 1) tKAdd tRVMul = tKAdd (tv 1 Nat.one_lt_two) (tv 0 Nat.zero_lt_two) := rfl

/-- Sanity check on the Horner form: at `k = 2` it is the monic quadratic `x² + a₁x + a₀`
(the `x²` coefficient is `1`, not `0`). -/
theorem hornerPoly_two :
    hornerPoly (k := 2) tKAdd tRVMul =
      tKAdd (tRVMul (tKAdd (tv 2 (Nat.lt_succ_self 2)) (tv 1 (Nat.one_lt_succ_succ 1)))
        (tv 2 (Nat.lt_succ_self 2))) (tv 0 (Nat.zero_lt_succ 2)) := rfl

end LRV

namespace Axioms

open LRV

/-- The sentences of a finite list, as a theory. -/
def ofList (l : List LRV.Sentence) : LRV.Theory := {s | s ∈ l}

/-! ### 3.1 The sort discipline of the encoding

These sentences are not part of the paper's Definition 2.2: they are what makes a
one-sorted structure behave like a two-sorted one.  They say that the carrier is the
disjoint union of the two sorts, and that each sort is closed under its own symbols. -/

/-- the carrier is covered by the two sorts -/
def sdCover : LRV.Sentence := allOne (pVF &0 ⊔ pRVsort &0)
/-- the two sorts are disjoint -/
def sdDisjoint : LRV.Sentence := allOne (∼(pVF &0 ⊓ pRVsort &0))
/-- `0` of the ring language lies in the `VF` sort -/
def sdVFZero : LRV.Sentence := pVF tVFZero
/-- `1` of the ring language lies in the `VF` sort -/
def sdVFOne : LRV.Sentence := pVF tVFOne
/-- the `VF` sort is closed under `+` -/
def sdVFAdd : LRV.Sentence := allSorted ![.vf, .vf] (pVF (tVFAdd &0 &1))
/-- the `VF` sort is closed under `-` -/
def sdVFNeg : LRV.Sentence := allSorted ![.vf] (pVF (tVFNeg &0))
/-- the `VF` sort is closed under `×` -/
def sdVFMul : LRV.Sentence := allSorted ![.vf, .vf] (pVF (tVFMul &0 &1))
/-- `rv` maps the `VF` sort into the `RV` sort -/
def sdRv : LRV.Sentence := allSorted ![.vf] (pRVsort (tRv &0))
/-- `0` of the `RV` sort lies in the `RV` sort -/
def sdRVZero : LRV.Sentence := pRVsort tRVZero
/-- `∞` lies in the `RV` sort -/
def sdRVInfty : LRV.Sentence := pRVsort tRVInfty
/-- `1` of the `RV` sort lies in the `RV` sort -/
def sdRVOne : LRV.Sentence := pRVsort tRVOne
/-- the `RV` sort is closed under `×` -/
def sdRVMul : LRV.Sentence := allSorted ![.rv, .rv] (pRVsort (tRVMul &0 &1))
/-- The predicate `Kˣ` holds only of elements of the `RV` sort.

Its actual content is axiom (4)'s `leClassOne`, which makes `Kˣ` the class of `1` — a
*proper* subgroup of the multiplicative group `RV ∖ {0}` whenever `Γ` is nontrivial.
Identifying `Kˣ` with all of `RV ∖ {0}` puts every `x ≠ 0` in the class of `1`, hence
`1 ≤ x ≤ 1`, hence makes the preorder trivial and `Γ` trivial — contradicting the paper's
standing hypothesis that `Γ(S)` is nontrivial. -/
def sdUnits : LRV.Sentence := allOne (pUnits &0 ⟹ pRVsort &0)
/-- `K = Kˣ ∪ {0}` is closed under `+` -/
def sdKAdd : LRV.Sentence :=
  allSorted ![.rv, .rv] (pInK &0 ⟹ (pInK &1 ⟹ pInK (tKAdd &0 &1)))
/-- `K` is closed under unary `-` -/
def sdKNeg : LRV.Sentence := allSorted ![.rv] (pInK &0 ⟹ pInK (tKNeg &0))
/-- `K` is closed under `×`: the paper's `K = K^× ∪ {0}` is a field, so the product of two
elements of `K` is in `K` and not `∞`.  Without this the field axioms of `kField` (which are
guarded by `pK`) constrain only the products that happen to land in `K`. -/
def sdKMul : LRV.Sentence :=
  allSorted ![.rv, .rv] (pInK &0 ⟹ (pInK &1 ⟹ pInK (tRVMul &0 &1)))

/-- The closure part of the sort discipline: each sort is closed under its own symbols,
and the two sorts are related through the symbols that cross them. -/
def sortClosure : LRV.Theory :=
  ofList [sdVFZero, sdVFOne, sdVFAdd, sdVFNeg, sdVFMul, sdRv,
    sdRVZero, sdRVInfty, sdRVOne, sdRVMul, sdUnits, sdKAdd, sdKNeg, sdKMul]

/-- the sort discipline of the encoding, as a theory -/
def sortAxioms : LRV.Theory := sortClosure ∪ ofList [sdCover, sdDisjoint]

/-! ### 3.2 Fields

The field axioms of Definition 2.2 items 1 and 3 are the same list of sentences read in
the two sorts, so they are generated from the sort tag and that sort's symbols. -/

/-- the field axioms for the sort `s`, with that sort's `0`, `1`, `+`, `-`, `×` -/
def fieldAxioms (s : SortTag) (zero one : {n : ℕ} → Tm n)
    (add mul : {n : ℕ} → Tm n → Tm n → Tm n) (neg : {n : ℕ} → Tm n → Tm n) :
    List LRV.Sentence :=
  [ /- associativity of `+` -/
    allSorted ![s, s, s] (pEq (add (add &0 &1) &2) (add &0 (add &1 &2))),
    /- commutativity of `+` -/
    allSorted ![s, s] (pEq (add &0 &1) (add &1 &0)),
    /- `0` is neutral for `+` -/
    allSorted ![s] (pEq (add &0 zero) &0),
    /- additive inverses -/
    allSorted ![s] (pEq (add &0 (neg &0)) zero),
    /- associativity of `×` -/
    allSorted ![s, s, s] (pEq (mul (mul &0 &1) &2) (mul &0 (mul &1 &2))),
    /- commutativity of `×` -/
    allSorted ![s, s] (pEq (mul &0 &1) (mul &1 &0)),
    /- `1` is neutral for `×` -/
    allSorted ![s] (pEq (mul &0 one) &0),
    /- distributivity -/
    allSorted ![s, s, s] (pEq (mul &0 (add &1 &2)) (add (mul &0 &1) (mul &0 &2))),
    /- `0 ≠ 1` -/
    ∼(pEq zero one),
    /- every nonzero element is invertible: the language has no inverse symbol -/
    allSorted ![s] (pEq &0 zero ⊔ exSorted s (pEq (mul &0 &1) one)) ]

/-- the algebraic-closedness scheme for the sort `s`:
`∀ a₀ … a_{k-1} ∃ x, x^k + a_{k-1} x^{k-1} + ⋯ + a₀ = 0` -/
def acfScheme (s : SortTag) (zero : {n : ℕ} → Tm n)
    (add mul : {n : ℕ} → Tm n → Tm n → Tm n) (k : ℕ) : LRV.Sentence :=
  allSorted (fun _ : Fin k => s) (exSorted s (pEq (hornerPoly add mul) zero))

/-- Definition 2.2 item 1: `(VF, 0, 1, +, -, ×)` is an algebraically closed field. -/
def vfField : LRV.Theory :=
  ofList (fieldAxioms .vf tVFZero tVFOne tVFAdd tVFMul tVFNeg)
/-- algebraic closedness of the `VF` sort -/
def vfAlgClosed : LRV.Theory := {s | ∃ k, 1 ≤ k ∧ s = acfScheme .vf tVFZero tVFAdd tVFMul k}

/-- Definition 2.2 item 3: `(K, 0, 1, +, -, ×)` is an algebraically closed field, where
`K = K^× ∪ {0} = RV-sort ∖ {∞}`.

Every quantifier is relativised to `K` (`allSortedK`, `exSortedK`), not merely to the `RV`
sort.  This is not cosmetic: the `RV` sort's carrier also contains `∞`, where `×` is
absorbing, so asserting the field axioms — in particular "every nonzero element is
invertible" — at `∞` forces `0 = ∞` and destroys the theory. -/
def kField : LRV.Theory :=
  ofList
    [ /- associativity of `+` -/
      allSortedK ![.rv, .rv, .rv] (pEq (tKAdd (tKAdd &0 &1) &2) (tKAdd &0 (tKAdd &1 &2))),
      /- commutativity of `+` -/
      allSortedK ![.rv, .rv] (pEq (tKAdd &0 &1) (tKAdd &1 &0)),
      /- `0` is neutral for `+` -/
      allSortedK ![.rv] (pEq (tKAdd &0 tRVZero) &0),
      /- additive inverses -/
      allSortedK ![.rv] (pEq (tKAdd &0 (tKNeg &0)) tRVZero),
      /- associativity of `×` -/
      allSortedK ![.rv, .rv, .rv] (pEq (tRVMul (tRVMul &0 &1) &2) (tRVMul &0 (tRVMul &1 &2))),
      /- commutativity of `×` -/
      allSortedK ![.rv, .rv] (pEq (tRVMul &0 &1) (tRVMul &1 &0)),
      /- `1` is neutral for `×` -/
      allSortedK ![.rv] (pEq (tRVMul &0 tRVOne) &0),
      /- distributivity -/
      allSortedK ![.rv, .rv, .rv]
        (pEq (tRVMul &0 (tKAdd &1 &2)) (tKAdd (tRVMul &0 &1) (tRVMul &0 &2))),
      /- `0 ≠ 1` -/
      ∼(pEq tRVZero tRVOne),
      /- every nonzero element of `K` is invertible -/
      allSortedK ![.rv] (pEq &0 tRVZero ⊔ exSortedK .rv (pEq (tRVMul &0 &1) tRVOne)) ]

/-- the algebraic-closedness scheme for `K = K^× ∪ {0}`: coefficients and root in `K` -/
def acfSchemeK (k : ℕ) : LRV.Sentence :=
  allSortedK (fun _ : Fin k => .rv)
    (exSortedK .rv (pEq (hornerPoly tKAdd tRVMul) tRVZero))

/-- algebraic closedness of `K = K^× ∪ {0}` -/
def kAlgClosed : LRV.Theory := {s | ∃ k, 1 ≤ k ∧ s = acfSchemeK k}

/-! ### 3.3 The multiplicative structure of the `RV` sort (Definition 2.2 items 2 and 4) -/

/-- `1 ∈ Kˣ` -/
def rvOneMem : LRV.Sentence := pUnits tRVOne
/-- `Kˣ` is closed under `×` -/
def rvMulMem : LRV.Sentence := allSorted ![.rv, .rv] (pUnits &0 ⟹ (pUnits &1 ⟹ pUnits (tRVMul &0 &1)))
/-- `×` is associative on `RV` -/
def rvMulAssoc : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv] (pEq (tRVMul (tRVMul &0 &1) &2) (tRVMul &0 (tRVMul &1 &2)))
/-- `×` is commutative on `RV` -/
def rvMulComm : LRV.Sentence := allSorted ![.rv, .rv] (pEq (tRVMul &0 &1) (tRVMul &1 &0))
/-- `1` is neutral for `×` on `Kˣ` -/
def rvMulOne : LRV.Sentence := allSorted ![.rv] (pUnits &0 ⟹ pEq (tRVMul tRVOne &0) &0)
/-- every element of `Kˣ` is invertible in `Kˣ` -/
def rvMulInv : LRV.Sentence :=
  allSorted ![.rv] (pUnits &0 ⟹ exSorted .rv (pUnits &1 ⊓ pEq (tRVMul &1 &0) tRVOne))
/-- divisibility of `Kˣ`: for every `k ≥ 1`, `∀ x ∈ Kˣ ∃ y ∈ Kˣ, y^k = x` -/
def rvDivisible (k : ℕ) : LRV.Sentence :=
  allSorted ![.rv] (pUnits &0 ⟹ exSorted .rv (pUnits &1 ⊓ pEq (tRVPow &1 k) &0))
/-- `t × 0 = 0` for `t ∈ K` -/
def rvMulZeroK : LRV.Sentence := allSorted ![.rv] (pInK &0 ⟹ pEq (tRVMul &0 tRVZero) tRVZero)
/-- `t × ∞ = ∞` for `t ∈ RV₀`, i.e. for every `t` of the `RV` sort -/
def rvMulInfty : LRV.Sentence := allSorted ![.rv] (pEq (tRVMul &0 tRVInfty) tRVInfty)

/-- Definition 2.2 item 2: `(RV^×, 1, ×)` is a divisible abelian group, with `×`
augmented by `t × 0 = 0` and `t × ∞ = ∞`. -/
def rvGroup : LRV.Theory :=
  ofList [rvOneMem, rvMulMem, rvMulAssoc, rvMulComm, rvMulOne, rvMulInv, rvMulZeroK,
      rvMulInfty] ∪
    {s | ∃ k, 1 ≤ k ∧ s = rvDivisible k}

/-! ### 3.4 The preorder on `RV` (Definition 2.2 item 4) -/

/-- `≤` is reflexive on `RV` -/
def leRefl : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pLe &0 &0)
/-- `≤` is transitive on `RV` -/
def leTrans : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pRV &2 ⟹ (pLe &0 &1 ⟹ (pLe &1 &2 ⟹ pLe &0 &2)))))
/-- `≤` is total on `RV` -/
def leTotal : LRV.Sentence := allSorted ![.rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pLe &0 &1 ⊔ pLe &1 &0)))
/-- `∞` is the top element of `RV` -/
def leTop : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pLe &0 tRVInfty)
/-- `∞ ≤ x` forces `x = ∞`, i.e. `∞` is alone in its class -/
def leInftyEq : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ (pLe tRVInfty &0 ⟹ pEq &0 tRVInfty))
/-- `Kˣ` is the equivalence class of `1` -/
def leClassOne : LRV.Sentence :=
  allSorted ![.rv] (pRV &0 ⟹ (pUnits &0 ⇔ (pLe tRVOne &0 ⊓ pLe &0 tRVOne)))
/-- `≤` is compatible with `×` on the left, i.e. the induced order on `RV/Kˣ` is a
translation-invariant order -/
def leMulCompat : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pRV &2 ⟹ (pUnits &2 ⟹ (pLe &0 &1 ⟹ pLe (tRVMul &0 &2) (tRVMul &1 &2))))))

/-- Definition 2.2 item 4: `≤` is a preorder on `RV` with `∞` the top element and `Kˣ`
the equivalence class of `1`. -/
def preorderRV : LRV.Theory :=
  ofList [leRefl, leTrans, leTotal, leTop, leInftyEq, leClassOne, leMulCompat]

/-! ### 3.5 The projection `rv` (Definition 2.2 item 6) -/

/-- `rv(0) = ∞` -/
def rvZeroEq : LRV.Sentence := pEq (tRv tVFZero) tRVInfty
/-- `rv(x) = ∞` forces `x = 0` -/
def rvEqInfty : LRV.Sentence := allSorted ![.vf] (pEq (tRv &0) tRVInfty ⟹ pEq &0 tVFZero)
/-- `rv` is a group homomorphism on `VF^×` -/
def rvMulHom : LRV.Sentence :=
  allSorted ![.vf, .vf] (pEq (tRv (tVFMul &0 &1)) (tRVMul (tRv &0) (tRv &1)))
/-- **`rv` is surjective**: every element of the `RV` sort other than `rv(0)` is `rv(x)` for
some `x ∈ VF`.  (Definition 2.2(6): `rv : VF^× → RV^×` is surjective, augmented by
`rv(0) = ∞ = 0`.  With `RV^× = RV ∖ {0}` this says: `RV = rv(VF) ∪ {0}`, so there are no
`RV`-elements outside the image of `rv`.) -/
def rvSurj : LRV.Sentence :=
  allSorted ![.rv] (∼(pEq &0 tRVZero) ⟹ exSorted .vf (pEq (tRv &1) &0))
/-- the ultrametric inequality for `vv = vrv ∘ rv`: `vv(x+y) ≥ min(vv x, vv y)` -/
def rvUltrametric : LRV.Sentence :=
  allSorted ![.vf, .vf] (pLe (tRv &0) (tRv (tVFAdd &0 &1)) ⊔ pLe (tRv &1) (tRv (tVFAdd &0 &1)))

/-- Definition 2.2 item 6: `rv : VF^× → RV^×` is a surjective group homomorphism
augmented by `rv(0) = ∞`, and `vv = vrv ∘ rv` is a valuation.  (The valuation ring
`O = rv⁻¹(RV^{≥1})` and the maximal ideal `M = rv⁻¹(RV^{>1})` are *defined* from `rv`,
so — exactly as in the paper — they need no symbols of their own.) -/
def rvAxioms : LRV.Theory :=
  ofList [rvZeroEq, rvEqInfty, rvMulHom, rvSurj, rvUltrametric]

/-! ### 3.6 `ACVF` and `ACVF(0,0)` -/

/-- the paper's own content of `ACVF`: Definition 2.2, items 1–6 -/
def ACVFpaper : LRV.Theory :=
  vfField ∪ vfAlgClosed ∪ rvGroup ∪ kField ∪ kAlgClosed ∪ preorderRV ∪ rvAxioms

/-- **The theory `ACVF` of Definition 2.2**, in the tagged encoding: items 1–6 plus the
sort discipline of the encoding. -/
def ACVF : LRV.Theory := sortAxioms ∪ ACVFpaper

/-- characteristic zero of the `VF` sort -/
def charZeroVF (k : ℕ) : LRV.Sentence := ∼(pEq (tVFNumeral (k + 1)) tVFZero)

/-- residue characteristic zero: for each prime `p`, `p · 1` is a unit of the valuation
ring, i.e. `¬ (1 < rv(p·1))` -/
def residueCharZero (p : ℕ) : LRV.Sentence := ∼(pGtOne (tRv (tVFNumeral p)))

/-- the paper's content of `ACVF(0,0)`: `ACVF` together with pure characteristic `0` -/
def ACVF00paper : LRV.Theory :=
  ACVFpaper ∪ {s | ∃ k, s = charZeroVF k} ∪ {s | ∃ p, p.Prime ∧ s = residueCharZero p}

/-- **The theory `ACVF(0,0)`**: `ACVF` with pure characteristic `0`, i.e. characteristic
`0` for the valued field and characteristic `0` for its residue field. -/
def ACVF00 : LRV.Theory := ACVF ∪ {s | ∃ k, s = charZeroVF k} ∪ {s | ∃ p, p.Prime ∧ s = residueCharZero p}

end Axioms

/-! ## Part 4. The value-group sort `Γ`

The paper has two sorts; `Γ` is treated semantically: "we shall treat `Γ` as an
imaginary sort and write `RV_Γ` for `RV ∪ Γ`; syntactically any reference to `Γ` may be
eliminated in the usual way" (Section 2, after Definition 2.2).

The substructure `S` of `ACVF_S(0,0)` is `(VF, Γ)`-generated, so `Γ` is genuinely used
in the theory `ACVF_S(0,0)`.  We therefore provide a *third tag* with its own language
`LΓ`, the expansion `L_RV^Γ = L_RV ∪ LΓ`, and the axioms which make `Γ` the quotient
`RV/Kˣ` with the order and the group operation induced by `≤` and `×`.  `Γ` is
definable from `RV` in `L_RV` (`Γ` is the quotient of `RV` by the definable equivalence
relation `x ~ y ⟺ ∃u ∈ Kˣ, x = u·y`), so `ACVF` and Theorems 2.3 and 2.8 are stated in
`L_RV` itself; `L_RV^Γ` is a definitional expansion of it. -/

namespace Gamma

open Axioms LRV

/- Function symbols of the `Γ` sort: the group language `{1, ×}` of the value group,
`{0, +, -}`, the top element `⊤` (the image of `∞`), and the quotient map `vrv`. -/
inductive FnΓ : ℕ → Type where
  /-- `0` of the value group -/
  | zero : FnΓ 0
  /-- `1` of the value group -/
  | one : FnΓ 0
  /-- the top element, the image of `∞` -/
  | top : FnΓ 0
  /-- `+` of the value group -/
  | add : FnΓ 2
  /-- `-` of the value group -/
  | neg : FnΓ 1
  /-- the quotient map `vrv : RV → Γ ∪ {∞}` of Definition 2.2 item 5 -/
  | vrv : FnΓ 1

/-- Relation symbols of the `Γ` sort. -/
inductive RelΓ : ℕ → Type where
  /-- encoding: the `Γ` sort -/
  | memGamma : RelΓ 1
  /-- the order of the value group -/
  | le : RelΓ 2

/-- the language of the value-group sort -/
def LΓ : Language := ⟨FnΓ, RelΓ⟩

/-- **`L_RV^Γ`**: the paper's `L_RV` together with the value-group sort `Γ` -/
def LRVΓ : Language := LRV.sum LΓ

/-- `L_RV` as a fragment of `L_RV^Γ` -/
def inc : LRV →ᴸ LRVΓ := LHom.sumInl

/-- terms of `L_RV^Γ` with variables among `Fin n` -/
abbrev TmΓ (n : ℕ) : Type := LRVΓ.Term (Empty ⊕ Fin n)

/-- bounded formulas of `L_RV^Γ` with `n` variables in scope -/
abbrev BfΓ (n : ℕ) : Type := LRVΓ.BoundedFormula Empty n

variable {n : ℕ}

/-! ### 4.1 The symbols of `L_RV` inside `L_RV^Γ` -/

/-- `0` of the `VF` sort -/
def uVFZero : TmΓ n := Term.func (Sum.inl Fn.vfZero) fun i => i.elim0
/-- `1` of the `VF` sort -/
def uVFOne : TmΓ n := Term.func (Sum.inl Fn.vfOne) fun i => i.elim0
/-- `+` of the `VF` sort -/
def uVFAdd (t u : TmΓ n) : TmΓ n := Term.func (Sum.inl Fn.vfAdd) ![t, u]
/-- `-` of the `VF` sort -/
def uVFNeg (t : TmΓ n) : TmΓ n := Term.func (Sum.inl Fn.vfNeg) ![t]
/-- `×` of the `VF` sort -/
def uVFMul (t u : TmΓ n) : TmΓ n := Term.func (Sum.inl Fn.vfMul) ![t, u]
/-- `1` of the `RV` sort -/
def uRVOne : TmΓ n := Term.func (Sum.inl Fn.rvOne) fun i => i.elim0
/-- `0` of the `RV` sort -/
def uRVZero : TmΓ n := Term.func (Sum.inl Fn.rvZero) fun i => i.elim0
/-- The paper's `∞`, i.e. `rv(0) = 0` -/
def uRVInfty : TmΓ n := uRVZero
/-- `×` of the `RV` sort -/
def uRVMul (t u : TmΓ n) : TmΓ n := Term.func (Sum.inl Fn.rvMul) ![t, u]
/-- the projection `rv` -/
def uRv (t : TmΓ n) : TmΓ n := Term.func (Sum.inl Fn.rvMap) ![t]
/-- `t ∈ VF` -/
def uVF (t : TmΓ n) : BfΓ n := BoundedFormula.rel (Sum.inl Rel.memVF) ![t]
/-- `t ∈ RV` (the encoding's sort predicate) -/
def uRVsort (t : TmΓ n) : BfΓ n := BoundedFormula.rel (Sum.inl Rel.memRV) ![t]
/-- the paper's unary predicate `Kˣ` -/
def uUnits (t : TmΓ n) : BfΓ n := BoundedFormula.rel (Sum.inl Rel.memUnits) ![t]
/-- the paper's preorder `≤` -/
def uLe (t u : TmΓ n) : BfΓ n := BoundedFormula.rel (Sum.inl Rel.rvLe) ![t, u]
/-- the paper's `RV = RV-sort ∖ {0}` -/
def uRV (t : TmΓ n) : BfΓ n := ∼(t =' uRVZero)

/-! ### 4.2 The symbols of the `Γ` sort -/

/-- `0` of the value group -/
def gZero : TmΓ n := Term.func (Sum.inr FnΓ.zero) fun i => i.elim0
/-- `1` of the value group -/
def gOne : TmΓ n := Term.func (Sum.inr FnΓ.one) fun i => i.elim0
/-- the top element -/
def gTop : TmΓ n := Term.func (Sum.inr FnΓ.top) fun i => i.elim0
/-- `+` of the value group -/
def gAdd (t u : TmΓ n) : TmΓ n := Term.func (Sum.inr FnΓ.add) ![t, u]
/-- `-` of the value group -/
def gNeg (t : TmΓ n) : TmΓ n := Term.func (Sum.inr FnΓ.neg) ![t]
/-- the quotient map `vrv` -/
def gVrv (t : TmΓ n) : TmΓ n := Term.func (Sum.inr FnΓ.vrv) ![t]
/-- the order of the value group -/
def pgLe (t u : TmΓ n) : BfΓ n := BoundedFormula.rel (Sum.inr RelΓ.le) ![t, u]
/-- the encoding's sort predicate for `Γ ∪ {⊤}` -/
def pMemGamma (t : TmΓ n) : BfΓ n := BoundedFormula.rel (Sum.inr RelΓ.memGamma) ![t]
/-- equality of `L_RV^Γ`-terms -/
def gEq (t u : TmΓ n) : BfΓ n := t =' u
/-- a bound variable of `L_RV^Γ` -/
def tvg (i : ℕ) (h : i < n) : TmΓ n := Term.var (Sum.inr ⟨i, h⟩)
/-- `k · t` in the value group -/
def gNSmul {n : ℕ} (t : TmΓ n) : ℕ → TmΓ n
  | 0 => gZero
  | k + 1 => gAdd (gNSmul t k) t

/-! ### 4.3 Guarded quantifiers for `L_RV^Γ` -/

/-- the universal closure of a formula in a single variable -/
def close1 (φ : BfΓ 1) : LRVΓ.Sentence := BoundedFormula.alls φ
/-- the universal closure of a formula in two variables -/
def close2 (φ : BfΓ 2) : LRVΓ.Sentence := BoundedFormula.alls φ
/-- `∀ x̄, h → φ` -/
def allG (k : ℕ) (h φ : BfΓ k) : LRVΓ.Sentence := BoundedFormula.alls (h ⟹ φ)
/-- `⋀ i, x_i ∈ Γ` -/
def gHyp (k : ℕ) : BfΓ k :=
  (List.finRange k).foldr (fun i acc => pMemGamma (tvg i.val i.isLt) ⊓ acc) ⊤
/-- `∀ x̄ ∈ Γ, φ` -/
def allGamma (k : ℕ) (φ : BfΓ k) : LRVΓ.Sentence := allG k (gHyp k) φ
/-- `∃ x ∈ Γ, φ` -/
def exGamma {k : ℕ} (φ : BfΓ (k + 1)) : BfΓ k :=
  BoundedFormula.ex (pMemGamma (tvg k (Nat.lt_succ_self k)) ⊓ φ)
/-- `∃ x ∈ RV, φ` -/
def exRV {k : ℕ} (φ : BfΓ (k + 1)) : BfΓ k :=
  BoundedFormula.ex (uRV (tvg k (Nat.lt_succ_self k)) ⊓ φ)

/-! ### 4.4 The axioms of the `Γ` sort -/

/-- the carrier is covered by the three sorts -/
def cover3 : LRVΓ.Sentence := close1 (uVF (&0) ⊔ (uRVsort (&0) ⊔ pMemGamma (&0)))
/-- the `VF` and `RV` sorts are disjoint -/
def disjVF_RV : LRVΓ.Sentence := close1 (∼(uVF (&0) ⊓ uRVsort (&0)))
/-- the `VF` and `Γ` sorts are disjoint -/
def disjVF_G : LRVΓ.Sentence := close1 (∼(uVF (&0) ⊓ pMemGamma (&0)))
/-- the `RV` and `Γ` sorts are disjoint -/
def disjRV_G : LRVΓ.Sentence := close1 (∼(uRVsort (&0) ⊓ pMemGamma (&0)))
/-- `0 ∈ Γ` -/
def gMemZero : LRVΓ.Sentence := pMemGamma gZero
/-- `⊤` is not an element of the value group -/
def gTopNotMem : LRVΓ.Sentence := ∼(pMemGamma gTop)
/-- `Γ` is closed under `+` -/
def gMemAdd : LRVΓ.Sentence := allGamma 2 (pMemGamma (gAdd (&0) (&1)))
/-- `Γ` is closed under `-` -/
def gMemNeg : LRVΓ.Sentence := allGamma 1 (pMemGamma (gNeg (&0)))
/-- `vrv` maps `RV` into `Γ ∪ {⊤}` -/
def gVrvMem : LRVΓ.Sentence :=
  allG 1 (uRV (&0)) (pMemGamma (gVrv (&0)) ⊔ gEq (gVrv (&0)) gTop)
/-- `+` is associative on `Γ` -/
def gAddAssoc : LRVΓ.Sentence :=
  allGamma 3 (gEq (gAdd (gAdd (&0) (&1)) (&2)) (gAdd (&0) (gAdd (&1) (&2))))
/-- `+` is commutative on `Γ` -/
def gAddComm : LRVΓ.Sentence := allGamma 2 (gEq (gAdd (&0) (&1)) (gAdd (&1) (&0)))
/-- `0` is neutral for `+` on `Γ` -/
def gAddZero : LRVΓ.Sentence := allGamma 1 (gEq (gAdd (&0) gZero) (&0))
/-- additive inverses in `Γ` -/
def gAddNeg : LRVΓ.Sentence := allGamma 1 (gEq (gAdd (&0) (gNeg (&0))) gZero)
/-- `≤` is reflexive on `Γ` -/
def gLeRefl : LRVΓ.Sentence := allGamma 1 (pgLe (&0) (&0))
/-- `≤` is transitive on `Γ` -/
def gLeTrans : LRVΓ.Sentence :=
  allGamma 3 (pgLe (&0) (&1) ⟹ (pgLe (&1) (&2) ⟹ pgLe (&0) (&2)))
/-- `≤` is total on `Γ` -/
def gLeTotal : LRVΓ.Sentence := allGamma 2 (pgLe (&0) (&1) ⊔ pgLe (&1) (&0))
/-- `≤` is antisymmetric on `Γ` -/
def gLeAntisym : LRVΓ.Sentence :=
  allGamma 2 (pgLe (&0) (&1) ⟹ (pgLe (&1) (&0) ⟹ gEq (&0) (&1)))
/-- `≤` is translation invariant on `Γ` -/
def gLeAdd : LRVΓ.Sentence :=
  allGamma 3 (pgLe (&0) (&1) ⟹ pgLe (gAdd (&0) (&2)) (gAdd (&1) (&2)))
/-- `⊤` is the top element -/
def gLeTop : LRVΓ.Sentence := allGamma 1 (pgLe (&0) gTop)
/-- divisibility of `Γ`: for every `k ≥ 1`, `∀ x ∃ y, k·y = x` -/
def gDivisible (k : ℕ) : LRVΓ.Sentence :=
  allGamma 1 (exGamma (gEq (gNSmul (tvg 1 (Nat.lt_succ_self 1)) k) (&0)))
/-- `vrv(∞) = ⊤` -/
def gVrvTop : LRVΓ.Sentence := gEq (gVrv uRVInfty) gTop
/-- `vrv` is a group homomorphism on `Kˣ` -/
def gVrvMul : LRVΓ.Sentence :=
  allG 2 (uUnits (&0) ⊓ uUnits (&1))
    (gEq (gVrv (uRVMul (&0) (&1))) (gAdd (gVrv (&0)) (gVrv (&1))))
/-- `Γ ∪ {⊤}` *is* the quotient `RV/Kˣ`: two elements of `RV` have the same value iff
they differ by an element of `Kˣ` -/
def gVrvEq : LRVΓ.Sentence :=
  allG 2 (uRV (&0) ⊓ uRV (&1))
    (gEq (gVrv (&0)) (gVrv (&1)) ⇔ exRV (uUnits (&2) ⊓ gEq (&0) (uRVMul (&2) (&0))))
/-- the order of `Γ` is induced by the preorder of `RV` -/
def gLeVrv : LRVΓ.Sentence :=
  allG 2 (uRV (&0) ⊓ uRV (&1)) (pgLe (gVrv (&0)) (gVrv (&1)) ⇔ uLe (&0) (&1))

/-- **Definition 2.2 item 5**: the quotient `RV/Kˣ` (written `Γ ∪ {∞}`) is a divisible
ordered abelian group with a top element, and the ordering and the group operation are
induced by `≤` and `×`. -/
def gammaAxioms : LRVΓ.Theory :=
  {s | s ∈ [gMemZero, gTopNotMem, gMemAdd, gMemNeg, gVrvMem, gAddAssoc, gAddComm,
      gAddZero, gAddNeg, gLeRefl, gLeTrans, gLeTotal, gLeAntisym, gLeAdd, gLeTop,
      gVrvTop, gVrvMul, gVrvEq, gLeVrv]} ∪ {s | ∃ k, 1 ≤ k ∧ s = gDivisible k}

/-- the sort discipline of the three-sorted encoding -/
def sortAxiomsΓ : LRVΓ.Theory :=
  inc.onTheory sortClosure ∪ {s | s ∈ [cover3, disjVF_RV, disjVF_G, disjRV_G]}

/-- **`ACVF(0,0)` in the `Γ`-expansion `L_RV^Γ`** -/
def ACVF00Γ : LRVΓ.Theory :=
  sortAxiomsΓ ∪ inc.onTheory ACVF00paper ∪ gammaAxioms

end Gamma

/-! ## Part 5. The theory `ACVF_S(0,0)`

`ACVF_S(0,0)` is `ACVF(0,0)` together with the atomic diagram of a small substructure `S`
of a model (Section 2, after Definition 2.4).  In Lean, `S` is a Mathlib
`FirstOrder.Language.Substructure` of a model `M`, and the atomic diagram is the set of
atomic and negated atomic `L_RV`-sentences with parameters in `S` that hold in `M`. -/

namespace SubstructureTheory

open Axioms

variable {M : Type*} [LRV.Structure M]

/-- atomic formulas: equalities of terms and applications of relation symbols -/
def IsAtomic {L : FirstOrder.Language} {α : Type*} : L.BoundedFormula α 0 → Prop
  | .equal _ _ => True
  | .rel _ _ => True
  | _ => False

/-- the atomic diagram of a substructure `S`: the atomic and negated atomic
`L_RV`-sentences with parameters in `S` that hold in `M` -/
def atomicDiagram (S : LRV.Substructure M) : LRV[[(S : Set M)]].Theory :=
  {φ | IsAtomic φ ∧ (M ⊨ φ)} ∪
    {φ | ∃ ψ, IsAtomic ψ ∧ φ = BoundedFormula.not ψ ∧ ¬ (M ⊨ ψ)}

/-- **`ACVF_S(0,0)`**: `ACVF(0,0)` together with the atomic diagram of `S` -/
def ACVF_S (S : LRV.Substructure M) : LRV[[(S : Set M)]].Theory :=
  (LRV.lhomWithConstants (S : Set M)).onTheory ACVF00 ∪ atomicDiagram S

end SubstructureTheory

/-! ## Part 6. The two target theorems, stated -/

open Axioms

/-- A theory `T` of `L_RV` **admits quantifier elimination**: every formula is
`T`-equivalent to a quantifier-free formula.  This is the paper's Theorem 2.3
("the theory `ACVF` admits quantifier elimination"). -/
def HasQE (T : LRV.Theory) : Prop :=
  ∀ (α : Type) (φ : LRV.Formula α), ∃ ψ : LRV.Formula α,
    FirstOrder.Language.BoundedFormula.IsQF ψ ∧ T ⊨ᵇ (φ ⇔ ψ)

/-! ### 6.1 The interpretation of the symbols in a model, for use in the statements -/

variable {M : Type*} [LRV.Structure M]

/-- `x` lies in the `VF` sort -/
def iVF (x : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memVF ![x]

/-- `x` lies in the `RV` sort -/
def iRV (x : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memRV ![x]

/-- `x ∈ Kˣ`, i.e. `x` satisfies the paper's unary predicate `Kˣ` -/
def iUnits (x : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memUnits ![x]

/-- the preorder `≤` of the `RV` sort -/
def iLe (x y : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.rvLe ![x, y]

/-- the interpretation of `+` of the `VF` sort -/
def iVFAdd (x y : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfAdd ![x, y]

/-- the interpretation of `-` of the `VF` sort -/
def iVFNeg (x : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfNeg ![x]

/-- the interpretation of `×` of the `VF` sort -/
def iVFMul (x y : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfMul ![x, y]

/-- the interpretation of `+ : K² → K` of the `RV` sort -/
def iKAdd (x y : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.kAdd ![x, y]

/-- the interpretation of `×` of the `RV` sort -/
def iRVMul (x y : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvMul ![x, y]

/-- the interpretation of the projection `rv : VF → RV` -/
def iRv (x : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvMap ![x]

/-- the interpretation of `0` of the `RV` sort -/
def iRVZero : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvZero fun i => i.elim0

/-- The interpretation of the paper's `∞`, which is the interpretation of `0` of the `RV` sort -/
def iRVInfty : M := iRVZero (M := M)

/-- the interpretation of `1` of the `RV` sort -/
def iRVOne : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvOne fun i => i.elim0

end Milestone0
end SpecialTransformations

/-!
# The repaired `ACVF`: what the author's ruling does to the old inconsistency argument

Appended to a copy of `Milestone0/Encoding.lean` (the version with the two-layer `RV` sort),
lines 1–872, with `LRV` as an `abbrev` (so `LRV.Relations` reduces and `simp`/`rw` can
rewrite the realised axioms).  Nothing else of the encoding part is changed.

## The ruling

The paper's two symbols `0` and `∞` of the `RV` sort name ONE element: `rv(0) = 0` is the
absorbing element of `RV`, `∞` is another name for it, and `RV^× = RV ∖ {∞} = RV ∖ {0}`.
The language therefore has one constant, `rvZero` — the constructor `rvInfty` is deleted —
and `tRVInfty`, `uRVInfty`, `iRVInfty`, `pK` are *definitions* of `tRVZero`, `uRVZero`,
`iRVZero`, `pRV`.

## What changed and why the old argument cannot be repeated

The old argument (`ACVFInconsistent.lean`, aimed at commit `f0b6a84`) had three steps:

1. `sdUnits` was `Kˣ ↔ (x ≠ 0 ∧ x ≠ ∞)`, which together with `rvOneMem` gave `1 ≠ ∞`.
   The current `sdUnits` is `allOne (pUnits &0 ⟹ pRVsort &0)`, i.e. only
   **`Kˣ` lies in the `RV` sort** (`sdUnits_mem` below): `1 ≠ ∞` is no longer available.
2. `kField`'s multiplicative-inverse axiom was asserted at every element of the `RV` sort,
   in particular at `∞`.  The current `kField` guards all its quantifiers by the paper's
   residue field `K = K^× ∪ {0}` (`allSortedK`, `exSortedK` with `pInK`), so the axiom is
   not available outside `K` (`kAlgClosed_lin_rel` below is the linear instance).
3. `hornerPoly` folded from `x`, so `acfScheme k` was the degree-`k+1` polynomial
   `x^{k+1} + a_{k-1}x^{k-1} + ⋯`; the `k = 1` instance gave `∀ a, ∃ x, x·x + a = 0`.
   The current `hornerPoly` (with the repository's own `hornerPoly_one`) gives `x + a₀`:
   `acfSchemeK 1` is `∀ a ∈ K, ∃ x ∈ K, x + a = 0` (`kAlgClosed_lin_rel` below).

Steps 1–3 are gone.  The old file's final theorem was

    zero_ne_infty : (iRVZero : M) ≠ iRVInfty

derived from `kAlgClosed`'s linear instance together with `sdKAdd`.  Under the ruling the two
sides are the *same* element: `iRVInfty` is definitionally `iRVZero`, so that statement is
now **false** (it is the negation of the convention that has been adopted).  Together with
`zero_eq_infty_imp_false`, which packaged the old inconsistency argument, it is therefore
**removed, not weakened** — no proof of it exists, and its subject matter no longer exists.
In its place this file records the identity as `zero_eq_infty` (`rfl`), and keeps the two
extraction lemmas on which the old argument rested, restated with the paper's guard
`K = K^× ∪ {0}`:

* `sdKAdd_rel` : `K` is closed under `+` (the old form, `x + y ≠ ∞`, is the *wrong* statement
  once `∞ = 0`: closure of `K` means `iInK (iKAdd x y)`, i.e. the disjunction
  `K^× ∪ {0}`, not `≠ 0`);
* `kAlgClosed_lin_rel` : `∀ a ∈ K, ∃ x ∈ K, x + a = 0`.

The old contradiction needed `x + 1 ≠ 0` and `x + 1 = 0` simultaneously.  With `0 = ∞` the
solution `x + 1 = 0` satisfies `sdKAdd` through the second disjunct of `K = K^× ∪ {0}`
(`kAlgClosed_lin_unit` below), so the pair of axioms is consistent on this point.  Keeping
the `pK` (`x ≠ ∞`) guards of an earlier version would *not* be consistent: `kAlgClosed`'s
linear instance at `a = 1` gives `x ≠ 0` with `x + 1 = 0`, and `pK`-guarded `sdKAdd` gives
`x + 1 ≠ ∞ = 0`.  That is why the guards of `K` are `pInK`, as in `pInK`'s own definition.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0

namespace Fixed

/-! ## Normal forms for the tuples that `BoundedFormula.Realize` produces -/

variable {M : Type*} [LRV.Structure M]

theorem fin0_fun_eq (f : Fin 0 → M) : f = ![] := Matrix.empty_eq f

theorem fin1_fun_eq (x : M) : (fun _ : Fin 1 => x) = ![x] := by
  funext i; fin_cases i; rfl

theorem snoc_fin2 (x y : M) : Fin.snoc (fun _ : Fin 1 => x) y = ![x, y] := by
  rw [show (fun _ : Fin 1 => x) = ![x] from fin1_fun_eq x]
  simp

theorem evalVec1 (xs : Fin 1 → M) :
    (fun i : Fin 1 => Term.realize (Sum.elim (default : Empty → M) xs)
      ((![Term.var (Sum.inr (0 : Fin 1))] : Fin 1 → LRV.Term (Empty ⊕ Fin 1)) i)) = xs := by
  funext i; fin_cases i; simp [Term.realize_func, fin0_fun_eq, fin1_fun_eq]

theorem evalVec2 (xs : Fin 2 → M) :
    (fun i : Fin 2 => Term.realize (Sum.elim (default : Empty → M) xs)
      ((![Term.var (Sum.inr (0 : Fin 2)), Term.var (Sum.inr (1 : Fin 2))] :
        Fin 2 → LRV.Term (Empty ⊕ Fin 2)) i)) = xs := by
  funext i; fin_cases i <;> simp [Term.realize_func, fin0_fun_eq, fin1_fun_eq]

theorem evalVec2swap (xs : Fin 2 → M) :
    (fun i : Fin 2 => Term.realize (Sum.elim (default : Empty → M) xs)
      ((![Term.var (Sum.inr (1 : Fin 2)), Term.var (Sum.inr (0 : Fin 2))] :
        Fin 2 → LRV.Term (Empty ⊕ Fin 2)) i)) = ![xs 1, xs 0] := by
  funext i; fin_cases i <;> simp [Term.realize_func, fin0_fun_eq, fin1_fun_eq]

theorem realize_tRVZero {n : ℕ} (xs : Fin n → M) :
    Term.realize (Sum.elim (default : Empty → M) xs) (LRV.tRVZero : LRV.Term (Empty ⊕ Fin n))
      = iRVZero := by
  rw [LRV.tRVZero, iRVZero]
  exact congrArg (FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvZero)
    (Subsingleton.elim _ _)

/-- The paper's `∞` and its `0` are one element, so the term `∞` realises as `iRVZero`. -/
theorem realize_tRVInfty {n : ℕ} (xs : Fin n → M) :
    Term.realize (Sum.elim (default : Empty → M) xs) (LRV.tRVInfty : LRV.Term (Empty ⊕ Fin n))
      = iRVInfty := by
  rw [LRV.tRVInfty, iRVInfty]
  exact realize_tRVZero xs


/-! ## The two extracted axioms, with the paper's `K = K^× ∪ {0}` guard -/

/-- The paper's residue field `K = K^× ∪ {0}` inside the carrier, as a predicate on the
model: `pInK`'s semantics.  `0` here is `rv(0)`, the absorbing element of `RV`. -/
def iInK (x : M) : Prop := iUnits x ∨ x = iRVZero

/-- the current `sdUnits`: only that `Kˣ` lies in the `RV` sort -/
theorem sdUnits_mem (h : M ⊨ Axioms.sdUnits) : ∀ x : M, iUnits x → iRV x := by
  have h2 := h
  simp [Axioms.sdUnits, LRV.allOne, LRV.pUnits, LRV.pRVsort, Sentence.Realize, fin0_fun_eq,
    Term.realize] at h2
  intro x hx
  exact h2 (fun _ => x) hx

theorem sdUnits_mem_ACVF : Axioms.sdUnits ∈ Axioms.ACVF := by
  simp [Axioms.ACVF, Axioms.sortAxioms, Axioms.sortClosure, Axioms.ofList]

theorem sdKAdd_mem_ACVF : Axioms.sdKAdd ∈ Axioms.ACVF := by
  simp [Axioms.ACVF, Axioms.sortAxioms, Axioms.sortClosure, Axioms.ofList]

theorem sdRVOne_mem_ACVF : Axioms.sdRVOne ∈ Axioms.ACVF := by
  simp [Axioms.ACVF, Axioms.sortAxioms, Axioms.sortClosure, Axioms.ofList]

/-- `K = K^× ∪ {0}` is closed under `+` (`sdKAdd`, read in the model).

The old version of this lemma concluded `iKAdd x y ≠ iRVInfty`, which was the right reading of
`sdKAdd` when `K` was the complement of `∞`; with `∞ = 0` closure of `K` in the paper's sense
is membership `iInK`, whose second disjunct is exactly `= 0`. -/
theorem sdKAdd_rel (h : M ⊨ Axioms.sdKAdd) :
    ∀ x y : M, iRV x → iRV y → iInK x → iInK y → iInK (iKAdd x y) := by
  have h2 := h
  simp [Axioms.sdKAdd, LRV.allSorted, LRV.sortedHyps, LRV.sortPred, LRV.pRVsort, LRV.pInK,
    LRV.pUnits, LRV.pEq, LRV.tKAdd, LRV.tv, Sentence.Realize, List.finRange, realize_tRVZero,
    Term.realize] at h2
  intro x y hx hy hxK hyK
  have hxK' : iUnits x ∨ x = iRVZero := by
    simpa [iInK, iUnits, iRVZero, realize_tRVZero] using hxK
  have hyK' : iUnits y ∨ y = iRVZero := by
    simpa [iInK, iUnits, iRVZero, realize_tRVZero] using hyK
  have key := h2 ![x, y] hx hy (by simpa [iUnits, iRVZero, realize_tRVZero] using hxK')
    (by simpa [iUnits, iRVZero, realize_tRVZero] using hyK')
  simpa [iInK, iUnits, iKAdd, iRVZero, realize_tRVZero, evalVec2, fin0_fun_eq, fin1_fun_eq]
    using key

theorem sdRVOne_mem (h : M ⊨ Axioms.sdRVOne) : iRV (iRVOne : M) := by
  have h2 := h
  simp only [Axioms.sdRVOne, LRV.pRVsort, Sentence.Realize] at h2
  simp only [Formula.Realize, BoundedFormula.realize_rel₁, LRV.tRVOne, Term.realize_func,
    fin0_fun_eq, fin1_fun_eq] at h2
  simpa [iRV, iRVOne, fin0_fun_eq, fin1_fun_eq] using h2

/-- the `kField` sentence `0 ≠ 1` -/
def sKZeroNeOne : LRV.Sentence := ∼(LRV.pEq LRV.tRVZero LRV.tRVOne)

theorem sKZeroNeOne_mem : sKZeroNeOne ∈ Axioms.ACVF := by
  simp [sKZeroNeOne, Axioms.ACVF, Axioms.ACVFpaper, Axioms.kField, Axioms.ofList]

theorem zero_ne_one_rel (h : M ⊨ sKZeroNeOne) : (iRVZero : M) ≠ iRVOne := by
  have h2 := h
  simp only [sKZeroNeOne, Sentence.Realize] at h2
  simp only [Formula.Realize, BoundedFormula.realize_bdEqual, LRV.pEq, LRV.tRVZero, LRV.tRVOne,
    Term.realize_func, fin0_fun_eq, fin1_fun_eq] at h2
  simpa [iRVZero, iRVOne, fin0_fun_eq, fin1_fun_eq] using h2

/-- `1 ∈ Kˣ` (`rvOneMem`): the witness that `1` lies in the paper's residue field `K`. -/
theorem rvOneMem_mem_ACVF : Axioms.rvOneMem ∈ Axioms.ACVF := by
  simp [Axioms.ACVF, Axioms.ACVFpaper, Axioms.rvGroup, Axioms.ofList]

theorem rvOneMem_rel (h : M ⊨ Axioms.rvOneMem) : iUnits (iRVOne : M) := by
  have h2 := h
  simp only [Axioms.rvOneMem, LRV.pUnits, Sentence.Realize] at h2
  simp only [Formula.Realize, BoundedFormula.realize_rel₁, LRV.tRVOne, Term.realize_func,
    fin0_fun_eq, fin1_fun_eq] at h2
  simpa [iUnits, iRVOne, fin0_fun_eq, fin1_fun_eq] using h2

/-- the linear instance of the repaired `kAlgClosed`: `∀ a ∈ K, ∃ x ∈ K, x + a = 0`.

(`hornerPoly` at `k = 1` is the monic *linear* polynomial `x + a₀`, the repository's
own `hornerPoly_one`; the guards are the paper's `K = K^× ∪ {0}`.) -/
theorem kAlgClosed_lin_rel (h : M ⊨ Axioms.acfSchemeK 1) :
    ∀ a : M, iRV a → iInK a → ∃ x : M, iRV x ∧ iInK x ∧ iKAdd x a = iRVZero := by
  have h2 := h
  simp [Axioms.acfSchemeK, LRV.allSortedK, LRV.exSortedK, LRV.sortedHyps, LRV.kHyps,
    LRV.sortPred, LRV.pRVsort, LRV.pInK, LRV.pUnits, LRV.pEq, LRV.tv, LRV.hornerPoly_one,
    LRV.tKAdd, LRV.tRVZero, Sentence.Realize, List.finRange, realize_tRVZero, Term.realize,
    BoundedFormula.realize_ex] at h2
  intro a hRV haK
  have haK' : (FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memUnits ![a] ∨
      a = FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvZero
        (fun i : Fin 0 => Term.realize (Sum.elim (default : Empty → M) (fun _ => a))
          (i.elim0 : LRV.Term (Empty ⊕ Fin 1)))) := by
    rcases haK with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (realize_tRVZero (xs := fun _ => a)).symm)
  obtain ⟨x, hxrest⟩ := h2 (fun _ => a) hRV haK'
  have hsnoc : (Fin.snoc (fun _ : Fin 1 => a) x : Fin 2 → M) (1 : Fin 2) = x := by
    simp [snoc_fin2]
  have hzero : (Fin.snoc (fun _ : Fin 1 => a) x : Fin 2 → M) (0 : Fin 2) = a := by
    simp [snoc_fin2]
  have hxRV : iRV x := by
    have h := hxrest.1.1
    rwa [hsnoc] at h
  refine ⟨x, hxRV, ?_, ?_⟩
  · rcases hxrest.1.2 with h | h
    · rw [hsnoc] at h
      exact Or.inl h
    · rw [hsnoc] at h
      exact Or.inr (h.trans (realize_tRVZero (xs := Fin.snoc (fun _ : Fin 1 => a) x)))
  · have h' := hxrest.2
    have hL : (fun i : Fin 2 => Term.realize (Sum.elim (default : Empty → M)
        (Fin.snoc (fun _ : Fin 1 => a) x))
          ((![Term.var (Sum.inr (1 : Fin 2)), Term.var (Sum.inr (0 : Fin 2))] :
            Fin 2 → LRV.Term (Empty ⊕ Fin 2)) i)) = ![x, a] := by
      funext i
      fin_cases i
      · simpa [hsnoc, fin0_fun_eq, fin1_fun_eq] using congrArg (fun f : Fin 2 → M => f 1) hsnoc
      · simpa [hzero, fin0_fun_eq, fin1_fun_eq] using congrArg (fun f : Fin 2 → M => f 0) hzero
    rw [hL] at h'
    exact h'.trans (realize_tRVZero (xs := Fin.snoc (fun _ : Fin 1 => a) x))

theorem kAlgClosed_lin_mem : Axioms.acfSchemeK 1 ∈ Axioms.ACVF := by
  have hmem : Axioms.acfSchemeK 1 ∈ Axioms.kAlgClosed := ⟨1, le_rfl, rfl⟩
  simp [Axioms.ACVF, Axioms.ACVFpaper, hmem]


/-! ## What the reversal of the convention does to the old obstruction -/

/-- **The paper's `0` and `∞` are one element**: in the repaired encoding the two names have
the same interpretation, definitionally.  This replaces the old `zero_ne_infty`, whose
statement is now false. -/
theorem zero_eq_infty : (iRVZero : M) = iRVInfty := rfl

/-- In every model of `ACVF` the residue field has a solution of `x + 1 = 0`, and it lies in
`K`.  This is the step that used to give the contradiction `0 = ∞`: `sdKAdd` now allows
`x + 1 = 0` as an element of `K` through the disjunct `K = K^× ∪ {0}`, so nothing
inconsistent follows. -/
theorem kAlgClosed_lin_unit (h : M ⊨ Axioms.ACVF) :
    ∃ x : M, iInK x ∧ iKAdd x (iRVOne : M) = iRVZero := by
  have hunit : iUnits (iRVOne : M) := rvOneMem_rel (h.realize_of_mem _ rvOneMem_mem_ACVF)
  have hRV : iRV (iRVOne : M) := sdRVOne_mem (h.realize_of_mem _ sdRVOne_mem_ACVF)
  obtain ⟨x, -, hxK, hEq⟩ :=
    kAlgClosed_lin_rel (h.realize_of_mem _ kAlgClosed_lin_mem) (iRVOne : M) hRV (Or.inl hunit)
  exact ⟨x, hxK, hEq⟩

#print axioms zero_eq_infty
#print axioms kAlgClosed_lin_rel
#print axioms sdKAdd_rel
#print axioms kAlgClosed_lin_unit

end Fixed
