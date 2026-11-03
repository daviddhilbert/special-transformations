import Mathlib
/-!
## A model of the theory `ACVF` of `Milestone0/Encoding.lean` at the trivial valuation

This file contains:

* Parts 0–3 of `Milestone0/Encoding.lean` at the current commit `d608de6`, verbatim except
  that `LRV` is declared as an `abbrev` instead of a `def` (same term, definitionally the same
  language; the change only lets the elaborator unfold `LRV.Functions`/`LRV.Relations` while
  rewriting).  In particular the residue-field guard is the current one,
  `pInK t = pUnits t ⊔ pEq t tRVZero`, i.e. `K = K^× ∪ {0}` (commit `dfef4ca` used
  `pK t = ∼(pEq t tRVInfty)` instead);
* an `LRV.Structure` on the carrier `K ⊕ RV`, where `K` is an algebraically closed field of
  characteristic zero and `RV = Option Kˣ = Kˣ ∪ {rv 0}` is the `RV` of the *trivial*
  valuation (`RVUnit = Kˣ ⧸ (1+𝔪) = Kˣ` since `𝔪 = ⊥`); `Sum.inr none` is `rv 0`, the residue
  zero, the absorbing element and the paper's `∞` — ONE element;
* the semantic counterpart `InK` of the guard `pInK`.  On `RV`-sorted elements `pInK` is
  vacuous in this carrier (`0 = ∞`), so `InK (mkRV t)` holds for *every* `t : RV`;
* proofs that this structure satisfies every sentence of `ACVF` and of `ACVF(0,0)`, and the
  corollary that `ACVF` has a model.

**Conversion (author's ruling: the paper's `0` and `∞` are ONE element).**  `Fn.rvInfty` is
deleted, `tRVInfty`/`iRVInfty` are definitions of `rvZero`/`iRVZero`, `rvSurj` is the paper's
unguarded surjectivity `t ≠ rv(0) → ∃ x, rv x = t`, `sdRVInfty`/`rvMulInfty`/`leTop`/
`leInftyEq` are stated at `tRVZero`, and the carrier of the model is the **two-layer**
`RV = Kˣ ∪ {rv 0} = Option Kˣ` (`none` is `rv 0`, which is the residue zero *and* `∞`).
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
/-- The paper's `∞` is `rv(0)`, i.e. the absorbing element `rvZero` of the `RV` sort: the
paper's two symbols `0` and `∞` name one element.  Kept as a definition so that the axioms can
be read in the paper's notation. -/
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

Not the same as `t ≠ ∞`: when `Γ` is nontrivial the elements of `RV ∖ {0, ∞}` of value
`≠ 1` are not in `K`, and the residue-field operations are junk there.  Definition 2.1(d)
defines `K` as `K^× ∪ {0}`, with `K^×` the predicate, i.e. axiom (4)'s class of `1`. -/
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
/-- `∞`, i.e. `rv(0) = 0`, lies in the `RV` sort -/
def sdRVInfty : LRV.Sentence := pRVsort tRVZero
/-- `1` of the `RV` sort lies in the `RV` sort -/
def sdRVOne : LRV.Sentence := pRVsort tRVOne
/-- the `RV` sort is closed under `×` -/
def sdRVMul : LRV.Sentence := allSorted ![.rv, .rv] (pRVsort (tRVMul &0 &1))
/-- The predicate `Kˣ` holds only of elements of the `RV` sort.

Its actual content is axiom (4)'s `leClassOne`, which makes `Kˣ` the class of `1` — a
*proper* subgroup of the multiplicative group `RV ∖ {0, ∞}` whenever `Γ` is nontrivial.
Identifying `Kˣ` with all of `RV ∖ {0, ∞}` (as an earlier version did) puts every
`x ∉ {0, ∞}` in the class of `1`, hence `1 ≤ x ≤ 1`, hence makes the preorder trivial and
`Γ` trivial — contradicting the paper's standing hypothesis that `Γ(S)` is nontrivial. -/
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
def rvMulInfty : LRV.Sentence := allSorted ![.rv] (pEq (tRVMul &0 tRVZero) tRVZero)

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
/-- `∞ = rv(0) = 0` is the top element of `RV` -/
def leTop : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pLe &0 tRVZero)
/-- `∞ ≤ x` forces `x = ∞`, i.e. `∞` is alone in its class -/
def leInftyEq : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ (pLe tRVZero &0 ⟹ pEq &0 tRVZero))
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
some `x ∈ VF`.  (With `RV^× = RV ∖ {0}` this is `RV = rv(VF^×) ∪ {0}`.) -/
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

end Milestone0
end SpecialTransformations

/-! ## The model at the trivial valuation

`K` is a field (we later assume `IsAlgClosed` and `CharZero`).  The carrier is `K ⊕ RV₀` with
`RV₀ = Option (Option Kˣ)` — literally the paper's `RV₀ = RV ∪ {0} = (RV^× ∪ {∞}) ∪ {0}` for
the *trivial* valuation `v = 1`, where `RV^× = Kˣ ⧸ (1 + 𝔪) = Kˣ` because `𝔪 = ⊥`.

* `Sum.inl x` is the `VF` element `x`;
* `Sum.inr none` is the residue-field zero `0`;
* `Sum.inr (some none)` is `∞ = rv 0`;
* `Sum.inr (some (some u))` is the `RV` element of the unit `u`.
-/

namespace SpecialTransformations
namespace Milestone0
namespace TrivialModel

open FirstOrder FirstOrder.Language

/-- The `RV` sort at the trivial valuation, with **two** layers as in the paper:
`RV = Kˣ ∪ {rv 0}`, i.e. `Option Kˣ`.  `none` is `rv 0`, which is the residue field's zero,
the absorbing element of `RV`, *and* the paper's top element `∞`: one element, not three. -/
abbrev RV (K : Type*) [Field K] : Type _ := Option Kˣ

/-- The carrier of the model: the disjoint union of the `VF` sort and the `RV` sort. -/
abbrev M (K : Type*) [Field K] : Type _ := K ⊕ RV K

variable {K : Type*} [Field K]

/-- the `VF`-tag -/
def mkVF (x : K) : M K := Sum.inl x
/-- the `RV`-tag -/
def mkRV (t : RV K) : M K := Sum.inr t
/-- the residue-field zero, i.e. `rv 0`, i.e. the paper's `∞` -/
def cZero : M K := Sum.inr none
/-- the paper's `∞ = rv 0`: the *same* carrier element as `0` -/
def cInfty : M K := Sum.inr none
/-- the paper's `1` in the `RV` sort -/
def cOneRV : M K := Sum.inr (some 1)
/-- an element of `Kˣ`, i.e. of `RV ∖ {0}` -/
def cUnit (u : Kˣ) : M K := Sum.inr (some u)

/-- Read an element of the `RV` sort as an element of the residue field `K = Kˣ ∪ {0}`;
`∞ = rv 0` reads as `0`. -/
def toK : RV K → K
  | none => 0
  | some u => (u : K)

/-- The inverse of `toK` on `K = Kˣ ∪ {0}`: `0 ↦ rv 0`, `x ≠ 0 ↦` the unit `x`. -/
noncomputable def fromK (x : K) : RV K := by
  classical
  exact if h : x = 0 then none else some (Units.mk0 x h)

@[simp] theorem toK_none : toK (none : RV K) = 0 := rfl
/-- `toK` at `∞ = rv 0`, which is `0` itself -/
@[simp] theorem toK_infty : toK (none : RV K) = 0 := rfl
@[simp] theorem toK_unit (u : Kˣ) : toK (some u) = (u : K) := rfl

@[simp] theorem fromK_zero : fromK (K := K) 0 = none := by
  rw [fromK, dif_pos rfl]

theorem fromK_of_ne {x : K} (h : x ≠ 0) : fromK x = some (Units.mk0 x h) := by
  rw [fromK, dif_neg h]

/-- `fromK x ≠ rv 0` for `x ≠ 0`.  (The old `fromK_ne_infty : fromK x ≠ none` said that
`fromK` never takes the value `∞`; with `∞ = rv 0` that is false at `x = 0`, and the useful
statement is this one.) -/
theorem fromK_ne_none {x : K} (h : x ≠ 0) : fromK (K := K) x ≠ none := by
  rw [fromK_of_ne h]; simp

@[simp] theorem toK_fromK (x : K) : toK (fromK x) = x := by
  rw [fromK]; split_ifs with h
  · rw [h]; rfl
  · rw [toK_unit]; rfl

theorem fromK_toK (t : RV K) : fromK (toK t) = t := by
  cases t with
  | none => simp [fromK]
  | some u =>
    have hu : (u : K) ≠ 0 := u.ne_zero
    rw [toK_unit, fromK_of_ne hu, Units.mk0_val]

theorem fromK_injective : Function.Injective (fromK (K := K)) := by
  intro x y h
  have := congrArg toK h
  simpa using this

theorem fromK_eq_none_iff {x : K} : fromK x = none ↔ x = 0 := by
  constructor
  · intro h
    have := congrArg toK h
    simpa using this
  · intro h; subst h; simp

theorem toK_eq_zero_iff {t : RV K} (_h : t ≠ none) : toK t = 0 ↔ t = none := by
  cases t with
  | none => simp
  | some u => simp [toK, u.ne_zero]

theorem toK_ne_zero {t : RV K} (h0 : t ≠ none) (h1 : t ≠ none) : toK t ≠ 0 := by
  intro h
  exact h0 ((toK_eq_zero_iff h1).mp h)

/-- The `vrv`-decoration of the `RV` sort at the trivial valuation: `∞ ↦ 0`, units `↦ 1`
(the junk value at the residue zero is `0`).  It induces the preorder of Definition 2.2.4 by
`t ≤ s ⟺ vrv s ≤ vrv t`. -/
def vval : RV K → ℕ
  | none => 0
  | some _ => 1

/-- The preorder `≤` of the `RV` sort: `t ≤ s ⟺ vval s ≤ vval t`. -/
def vle (t s : RV K) : Prop := vval s ≤ vval t

/-- `vval` at `∞ = rv 0`, the same element as `0` -/
@[simp] theorem vval_infty : vval (K := K) none = 0 := rfl
@[simp] theorem vval_zero : vval (K := K) none = 0 := rfl
@[simp] theorem vval_unit (u : Kˣ) : vval (K := K) (some u) = 1 := rfl

theorem vval_eq_zero_iff {t : RV K} (_h : t ≠ none) : vval t = 0 ↔ t = none := by
  cases t with
  | none => simp
  | some u => simp

/-- Multiplication on the `RV` sort: transported from the field `K` along `toK`/`fromK`.
With `0 = ∞ = rv 0` one element, the old case distinction "`∞` absorbing, else the group law"
collapses into `fromK (0 * x) = fromK 0 = rv 0`, so this is the residue field's multiplication
on the whole of `RV = Kˣ ∪ {0}`, and the group law on `Kˣ`. -/
noncomputable def rvMul (t s : RV K) : RV K := fromK (toK t * toK s)

/-- Addition on `K = Kˣ ∪ {0}`, transported from the field `K`; there is no junk value left,
because `K` is now the whole `RV` sort. -/
noncomputable def kAdd (t s : RV K) : RV K := fromK (toK t + toK s)

/-- Negation on `K = Kˣ ∪ {0}`, transported from the field `K`. -/
noncomputable def kNeg (t : RV K) : RV K := fromK (-(toK t))

/-- the map `rv : VF → RV`, the tautological `x ↦ fromK x` (so `0 ↦ rv 0 = ∞ = 0`) -/
noncomputable def rvMap (x : K) : RV K := fromK x

@[simp] theorem rvMap_zero : rvMap (K := K) 0 = none := by rw [rvMap, fromK_zero]

theorem rvMap_of_ne {x : K} (_h : x ≠ 0) : rvMap x = fromK x := rfl

theorem rvMap_eq_infty_iff {x : K} : rvMap x = none ↔ x = 0 := fromK_eq_none_iff

/-- `rv x ≠ rv 0` for `x ≠ 0` (the old `rvMap_ne_none x : rvMap x ≠ none` is false at `x = 0`
now that `rv 0 = ∞` is the residue zero itself). -/
theorem rvMap_ne_none {x : K} (h : x ≠ 0) : rvMap (K := K) x ≠ none := fromK_ne_none h

theorem toK_rvMap {x : K} (_h : x ≠ 0) : toK (rvMap x) = x := by
  rw [rvMap, toK_fromK]

theorem rvMap_injective : Function.Injective (rvMap (K := K)) := by
  intro x y h
  by_cases hx : x = 0
  · subst hx
    have : rvMap y = none := h.symm ▸ rvMap_zero
    exact (rvMap_eq_infty_iff.mp this).symm
  · by_cases hy : y = 0
    · subst hy
      have : rvMap x = none := h ▸ rvMap_zero
      exact absurd (rvMap_eq_infty_iff.mp this) hx
    · rw [rvMap_of_ne hx, rvMap_of_ne hy] at h
      exact fromK_injective h

/-- The interpretation of the twelve function symbols.  Junk values: the two partial
symbols of the residue field (`kAdd`, `kNeg`) and the `VF` operations take the junk value
`∞` off their intended domain (`Milestone0/Partiality.lean`). -/
noncomputable def fMap : {n : ℕ} → Fn n → (Fin n → M K) → M K
  | _, .vfZero, _ => mkVF 0
  | _, .vfOne, _ => mkVF 1
  | _, .vfAdd, xs => match xs 0, xs 1 with
      | Sum.inl a, Sum.inl b => mkVF (a + b)
      | _, _ => cInfty
  | _, .vfNeg, xs => match xs 0 with
      | Sum.inl a => mkVF (-a)
      | _ => cInfty
  | _, .vfMul, xs => match xs 0, xs 1 with
      | Sum.inl a, Sum.inl b => mkVF (a * b)
      | _, _ => cInfty
  | _, .rvOne, _ => cOneRV
  | _, .rvZero, _ => cZero
  | _, .rvMul, xs => match xs 0, xs 1 with
      | Sum.inr t, Sum.inr s => mkRV (rvMul t s)
      | _, _ => cInfty
  | _, .kAdd, xs => match xs 0, xs 1 with
      | Sum.inr t, Sum.inr s => mkRV (kAdd t s)
      | _, _ => cInfty
  | _, .kNeg, xs => match xs 0 with
      | Sum.inr t => mkRV (kNeg t)
      | _ => cInfty
  | _, .rvMap, xs => match xs 0 with
      | Sum.inl a => mkRV (rvMap a)
      | _ => cInfty

/-- **The preorder of the `RV` sort at the trivial valuation**, as a total relation on the
carrier: `∞` is the top, the residue zero `0` is the bottom, and every unit is below every
element of the `RV` sort.  On `RV ∖ {0}` this is `t ≤ s ⟺ vrv s ≤ vrv t` for the trivial
valuation (`vrv` sends units to `1` and `∞` to `0`); it is stated in this *direct* form, with
no existential over representatives, so that the axioms of `preorderRV` are case splits. -/
def rvLeC (x y : M K) : Prop := y = cInfty ∨ ∃ u : Kˣ, x = cUnit u

/-- The interpretation of the four relation symbols. -/
def rMap : {n : ℕ} → Rel n → (Fin n → M K) → Prop
  | _, .memVF, xs => ∃ x : K, xs 0 = mkVF x
  | _, .memRV, xs => ∃ t : RV K, xs 0 = mkRV t
  | _, .memUnits, xs => ∃ u : Kˣ, xs 0 = cUnit u
  | _, .rvLe, xs => rvLeC (xs 0) (xs 1)

/-- **The `L_RV`-structure on `K ⊕ RV₀` at the trivial valuation.** -/
noncomputable instance instStructure : LRV.Structure (M K) where
  funMap := fMap
  RelMap := rMap

end TrivialModel
end Milestone0
end SpecialTransformations

/-! ## Unfolding toolkit for the structure

These lemmas turn `M ⊨ <guarded sentence>` into its semantic content on the carrier
`K ⊕ RV₀`. -/

namespace SpecialTransformations.Milestone0.TrivialModel

open FirstOrder FirstOrder.Language

variable {K : Type*} [Field K]

/-- the (unique) empty assignment -/
abbrev dflt : Empty → M K := fun e => e.elim

@[simp] theorem RelMap_def {n : ℕ} (r : Rel n) (xs : Fin n → M K) :
    (Structure.RelMap (L := LRV) (M := M K) r xs) = rMap r xs := rfl

@[simp] theorem funMap_def {n : ℕ} (f : Fn n) (xs : Fin n → M K) :
    (Structure.funMap (L := LRV) (M := M K) f xs) = fMap f xs := rfl

/-! ### The residue-field guard `pInK` on the carrier

`pInK` is the guard `K = K^× ∪ {0}` of the encoding: on `RV`-sorted elements it is the test
`t ≠ ∞` that the previous version of the encoding used, but *literally* it says that the value
is the residue-field zero or a unit.  The two differ on `VF`-sorted elements of the carrier,
which are not in `K` at all; so the semantic counterpart of `pInK` is `InK` below. -/

/-- The residue field `K = K^× ∪ {0}` inside the carrier, as a predicate. -/
def InK (z : M K) : Prop := (∃ u : Kˣ, z = cUnit u) ∨ z = cZero

/-- `∞ = rv 0 = 0` and the residue zero are one carrier element, so `0` and `∞` are not
distinct; the old `cZero_ne_cInfty` is false and is replaced by `cZero_eq_cInfty`. -/
theorem cZero_eq_cInfty : (cZero : M K) = cInfty := rfl

theorem cUnit_ne_cInfty (u : Kˣ) : (cUnit u : M K) ≠ cInfty := fun h => nomatch Sum.inr.inj h

/-- every `RV`-sorted element satisfies the guard `pInK = pUnits ⊔ (t = 0)`: in the two-layer
carrier the residue zero *is* `∞`, so `pInK` is now vacuous on the `RV` sort -/
theorem InK_mkRV (s : RV K) : InK (mkRV s) := by
  cases s with
  | none => exact Or.inr rfl
  | some u => exact Or.inl ⟨u, rfl⟩

theorem InK_mkRV_iff {s : RV K} : InK (mkRV s) ↔ True := by
  cases s with
  | none => simp [InK, mkRV, cZero]
  | some u => simp [InK, mkRV, cUnit]

/-- the guard `pInK`, unfolded to the carrier predicate `InK` -/
theorem realize_pInK {m : ℕ} (t : LRV.Tm m) (xs : Fin m → M K) :
    (LRV.pInK t).Realize (dflt) xs ↔ InK (Term.realize (Sum.elim dflt xs) t) := by
  simp only [LRV.pInK, LRV.pUnits, LRV.pEq, LRV.tRVZero, Relations.boundedFormula₁,
    BoundedFormula.realize_sup, BoundedFormula.realize_rel, BoundedFormula.realize_bdEqual,
    RelMap_def, rMap, Term.realize_func, funMap_def, fMap, Matrix.cons_val_fin_one,
    Matrix.empty_eq, Function.comp_apply, InK]

/-- the value of a variable under the empty assignment -/
theorem realize_tv_val' {m : ℕ} (xs : Fin m → M K) (i : Fin m) :
    Term.realize (Sum.elim dflt xs) (LRV.tv i.val i.isLt) = xs i := by
  simp [LRV.tv, Term.realize_var]

/-- `M ⊨ φ.alls` unfolds to the universally quantified bounded formula. -/
theorem model_alls {k : ℕ} (φ : LRV.BoundedFormula Empty k) :
    ((M K) ⊨ φ.alls) ↔ ∀ xs : Fin k → M K, φ.Realize (dflt) xs := by
  rw [Sentence.Realize, BoundedFormula.realize_alls]
  refine forall_congr' (fun xs => ?_)
  exact iff_of_eq (congrArg (fun w => φ.Realize w xs) (Subsingleton.elim _ _))

/-- the `VF` sort predicate at a variable, in terms of the carrier -/
theorem realize_sortPred_vf {n : ℕ} (i : Fin n) (xs : Fin n → M K) :
    (LRV.sortPred .vf (LRV.tv i.val i.isLt)).Realize (dflt) xs ↔ ∃ x : K, xs i = mkVF x := by
  simp only [LRV.sortPred, LRV.pVF, LRV.tv, BoundedFormula.realize_rel₁, RelMap_def, rMap,
    Matrix.cons_val_fin_one, Term.realize_var, Sum.elim_inr, Fin.eta]

/-- the `RV` sort predicate at a variable, in terms of the carrier -/
theorem realize_sortPred_rv {n : ℕ} (i : Fin n) (xs : Fin n → M K) :
    (LRV.sortPred .rv (LRV.tv i.val i.isLt)).Realize (dflt) xs ↔
      ∃ t : RV K, xs i = mkRV t := by
  simp only [LRV.sortPred, LRV.pRVsort, LRV.tv, BoundedFormula.realize_rel₁, RelMap_def, rMap,
    Matrix.cons_val_fin_one, Term.realize_var, Sum.elim_inr, Fin.eta]

/-- realizing a `foldr` of conjunctions -/
theorem realize_foldr_inf {ι : Type*} {n : ℕ} (l : List ι)
    (f : ι → LRV.BoundedFormula Empty n) (xs : Fin n → M K) :
    (l.foldr (fun i acc => f i ⊓ acc) ⊤).Realize (dflt) xs ↔
      ∀ i ∈ l, (f i).Realize (dflt) xs := by
  induction l with
  | nil => simp [BoundedFormula.realize_top]
  | cons a l ih =>
    simp only [List.foldr_cons, BoundedFormula.realize_inf, ih, List.mem_cons]
    exact ⟨fun ⟨h1, h2⟩ i hi => hi.elim (fun e => e ▸ h1) (h2 i),
      fun h => ⟨h a (Or.inl rfl), fun i hi => h i (Or.inr hi)⟩⟩

theorem realize_sortedHyps {k : ℕ} (ss : Fin k → SortTag) (xs : Fin k → M K) :
    (LRV.sortedHyps ss).Realize (dflt) xs ↔
      ∀ i : Fin k, ((ss i = .vf → ∃ x : K, xs i = mkVF x) ∧
        (ss i = .rv → ∃ t : RV K, xs i = mkRV t)) := by
  rw [LRV.sortedHyps, realize_foldr_inf]
  constructor
  · intro h i
    have hi := h i (List.mem_finRange i)
    cases hss : ss i with
    | vf =>
      rw [hss] at hi
      rw [realize_sortPred_vf] at hi
      exact ⟨fun _ => hi, fun hh => by simp at hh⟩
    | rv =>
      rw [hss] at hi
      rw [realize_sortPred_rv] at hi
      exact ⟨fun hh => by simp at hh, fun _ => hi⟩
  · intro h φ _
    rcases h φ with ⟨hvf, hrv⟩
    cases hss : ss φ with
    | vf => rw [realize_sortPred_vf]; exact hvf hss
    | rv => rw [realize_sortPred_rv]; exact hrv hss

/-- **the guarded universal sentence, unfolded** -/
theorem model_allSorted {k : ℕ} (ss : Fin k → SortTag) (φ : LRV.BoundedFormula Empty k) :
    ((M K) ⊨ LRV.allSorted ss φ) ↔
      ∀ xs : Fin k → M K, (∀ i : Fin k, ((ss i = .vf → ∃ x : K, xs i = mkVF x) ∧
        (ss i = .rv → ∃ t : RV K, xs i = mkRV t))) →
        φ.Realize (dflt) xs := by
  rw [LRV.allSorted, model_alls]
  refine forall_congr' (fun xs => ?_)
  rw [BoundedFormula.realize_imp]
  exact ⟨fun h hg => h ((realize_sortedHyps ss xs).mpr hg),
    fun h hg => h ((realize_sortedHyps ss xs).mp hg)⟩

/-- `K`-guarded hypotheses: every entry of the tuple lies in `K = K^× ∪ {0}` -/
theorem realize_kHyps {k : ℕ} (xs : Fin k → M K) :
    (LRV.kHyps (k := k)).Realize (dflt) xs ↔ ∀ i : Fin k, InK (xs i) := by
  have hdef : LRV.kHyps (k := k) =
      (List.finRange k).foldr (fun i acc => LRV.pInK (LRV.tv i.val i.isLt) ⊓ acc) ⊤ := rfl
  rw [hdef, realize_foldr_inf]
  constructor
  · intro h i
    have hi := h i (List.mem_finRange i)
    rwa [realize_pInK, realize_tv_val'] at hi
  · intro h i _
    rw [realize_pInK, realize_tv_val']
    exact h i

/-- **the `K`-guarded universal sentence, unfolded**: the guard hypothesis is membership
in `K = K^× ∪ {0}` (on `RV`-sorted entries this is the same as `≠ ∞`) -/
theorem model_allSortedK {k : ℕ} (ss : Fin k → SortTag) (φ : LRV.BoundedFormula Empty k) :
    ((M K) ⊨ LRV.allSortedK ss φ) ↔
      ∀ xs : Fin k → M K, (∀ i : Fin k, ((ss i = .vf → ∃ x : K, xs i = mkVF x) ∧
        (ss i = .rv → ∃ t : RV K, xs i = mkRV t))) →
        (∀ i : Fin k, InK (xs i)) → φ.Realize (dflt) xs := by
  rw [LRV.allSortedK, model_alls]
  refine forall_congr' (fun xs => ?_)
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  constructor
  · intro h hg hk
    exact h ⟨(realize_sortedHyps ss xs).mpr hg, (realize_kHyps xs).mpr hk⟩
  · intro h hh
    exact h ((realize_sortedHyps ss xs).mp hh.1) ((realize_kHyps xs).mp hh.2)

macro "prep" : tactic => `(tactic|
  (simp only [FirstOrder.Language.BoundedFormula.realize_rel₁,
    FirstOrder.Language.BoundedFormula.realize_rel₂,
    FirstOrder.Language.BoundedFormula.realize_rel,
    FirstOrder.Language.BoundedFormula.realize_imp,
    FirstOrder.Language.BoundedFormula.realize_inf,
    FirstOrder.Language.BoundedFormula.realize_sup,
    FirstOrder.Language.BoundedFormula.realize_not,
    FirstOrder.Language.BoundedFormula.realize_bdEqual,
    FirstOrder.Language.BoundedFormula.realize_top,
    FirstOrder.Language.BoundedFormula.realize_bot,
    FirstOrder.Language.BoundedFormula.realize_iff,
    FirstOrder.Language.BoundedFormula.realize_all,
    FirstOrder.Language.BoundedFormula.realize_ex,
    FirstOrder.Language.BoundedFormula.realize_exs,
    FirstOrder.Language.BoundedFormula.realize_alls,
    FirstOrder.Language.Term.realize_func, FirstOrder.Language.Term.realize_var,
    FirstOrder.Language.Relations.boundedFormula₁, FirstOrder.Language.Relations.boundedFormula₂,
    Function.comp_apply,
    LRV.allOne, LRV.sortedHyps, LRV.kHyps, LRV.sortPred, LRV.tv, LRV.exSorted,
    LRV.exSortedK, LRV.allSortedK, LRV.allSorted,
    LRV.pVF, LRV.pRVsort, LRV.pUnits, LRV.pLe, LRV.pEq, LRV.pRV, LRV.pK, LRV.pRV,
    LRV.pGtOne, LRV.tVFZero, LRV.tVFOne, LRV.tVFAdd, LRV.tVFNeg, LRV.tVFMul,
    LRV.tRVOne, LRV.tRVZero, LRV.tRVInfty, LRV.tRVMul, LRV.tKAdd, LRV.tKNeg, LRV.tRv,
    RelMap_def, funMap_def, rMap, fMap, mkVF, mkRV, cInfty, cZero, cOneRV, cUnit,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.empty_eq, Fin.snoc_zero, Fin.snoc_castSucc,
    Fin.snoc_last, Fin.forall_fin_one, Fin.forall_fin_two, Fin.forall_fin_zero, Fin.ext_iff,
    Fin.zero_eta, Sum.elim_inl, Sum.elim_inr,
    FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize]))

/-! ### Basic shape lemmas for the carrier -/

@[simp] theorem mkVF_eq_mkVF {x y : K} : mkVF x = mkVF (K := K) y ↔ x = y :=
  ⟨fun h => Sum.inl.inj h, fun h => by rw [h]⟩

theorem mkVF_ne_mkRV (x : K) (t : RV K) : mkVF x ≠ mkRV t := by simp [mkVF, mkRV]
theorem mkRV_ne_mkVF (t : RV K) (x : K) : mkRV t ≠ mkVF x := by simp [mkVF, mkRV]
theorem mkRV_inj {t s : RV K} : mkRV t = mkRV s ↔ t = s := ⟨fun h => Sum.inr.inj h, fun h => by rw [h]⟩

theorem exists_mkVF_iff {z : M K} : (∃ x : K, z = mkVF x) ↔ ∃ x, z = Sum.inl x := Iff.rfl
theorem exists_mkRV_iff {z : M K} : (∃ t : RV K, z = mkRV t) ↔ ∃ t, z = Sum.inr t := Iff.rfl

/-! ### The sort discipline of the encoding -/

section SortDiscipline

theorem model_sdVFZero : (M K) ⊨ Axioms.sdVFZero := by
  simp only [Axioms.sdVFZero]; prep
  exact ⟨0, rfl⟩

theorem model_sdVFOne : (M K) ⊨ Axioms.sdVFOne := by
  simp only [Axioms.sdVFOne]; prep
  exact ⟨1, rfl⟩

theorem model_sdVFAdd : (M K) ⊨ Axioms.sdVFAdd := by
  simp only [Axioms.sdVFAdd]; rw [model_allSorted]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  obtain ⟨b, hb⟩ := (h 1).1 rfl
  rw [ha, hb]
  exact ⟨a + b, rfl⟩

theorem model_sdVFNeg : (M K) ⊨ Axioms.sdVFNeg := by
  simp only [Axioms.sdVFNeg]; rw [model_allSorted]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  rw [ha]
  exact ⟨-a, rfl⟩

theorem model_sdVFMul : (M K) ⊨ Axioms.sdVFMul := by
  simp only [Axioms.sdVFMul]; rw [model_allSorted]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  obtain ⟨b, hb⟩ := (h 1).1 rfl
  rw [ha, hb]
  exact ⟨a * b, rfl⟩

theorem model_sdRv : (M K) ⊨ Axioms.sdRv := by
  simp only [Axioms.sdRv]; rw [model_allSorted]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  rw [ha]
  exact ⟨rvMap a, rfl⟩

theorem model_sdRVZero : (M K) ⊨ Axioms.sdRVZero := by
  simp only [Axioms.sdRVZero]; prep
  exact ⟨none, rfl⟩

theorem model_sdRVOne : (M K) ⊨ Axioms.sdRVOne := by
  simp only [Axioms.sdRVOne]; prep
  exact ⟨some (1), rfl⟩

theorem model_sdRVInfty : (M K) ⊨ Axioms.sdRVInfty := by
  simp only [Axioms.sdRVInfty]; prep
  exact ⟨none, rfl⟩

theorem model_sdRVMul : (M K) ⊨ Axioms.sdRVMul := by
  simp only [Axioms.sdRVMul]; rw [model_allSorted]; intro xs h; prep
  obtain ⟨s, hs⟩ := (h 0).2 rfl
  obtain ⟨t, ht⟩ := (h 1).2 rfl
  rw [hs, ht]
  exact ⟨rvMul s t, rfl⟩

theorem model_sdUnits : (M K) ⊨ Axioms.sdUnits := by
  simp only [Axioms.sdUnits, LRV.allOne]
  rw [model_alls]
  intro xs
  prep
  rintro ⟨u, hu⟩
  rw [hu]
  exact ⟨some (u), rfl⟩

theorem model_sdCover : (M K) ⊨ Axioms.sdCover := by
  simp only [Axioms.sdCover, LRV.allOne]
  rw [model_alls]
  intro xs
  prep
  rcases xs 0 with x | t
  · exact Or.inl ⟨x, rfl⟩
  · exact Or.inr ⟨t, rfl⟩

theorem model_sdDisjoint : (M K) ⊨ Axioms.sdDisjoint := by
  simp only [Axioms.sdDisjoint, LRV.allOne]
  rw [model_alls]
  intro xs
  prep
  rintro ⟨⟨x, hx⟩, ⟨t, ht⟩⟩
  rw [hx] at ht
  exact nomatch ht

theorem model_sdKAdd : (M K) ⊨ Axioms.sdKAdd := by
  simp only [Axioms.sdKAdd]; rw [model_allSorted]; intro xs h; prep
  obtain ⟨s, hs⟩ := (h 0).2 rfl
  obtain ⟨t, ht⟩ := (h 1).2 rfl
  intro _ _
  rw [realize_pInK]
  simp only [LRV.tKAdd, Term.realize_func, funMap_def, fMap, Term.realize_var, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, hs, ht, mkRV]
  exact InK_mkRV _

theorem model_sdKNeg : (M K) ⊨ Axioms.sdKNeg := by
  simp only [Axioms.sdKNeg]; rw [model_allSorted]; intro xs h; prep
  obtain ⟨s, hs⟩ := (h 0).2 rfl
  intro _
  rw [realize_pInK]
  simp only [LRV.tKNeg, Term.realize_func, funMap_def, fMap, Term.realize_var, Sum.elim_inr,
    Matrix.cons_val_zero, hs, mkRV]
  exact InK_mkRV _

theorem model_sdKMul : (M K) ⊨ Axioms.sdKMul := by
  simp only [Axioms.sdKMul]; rw [model_allSorted]; intro xs h; prep
  obtain ⟨s, hs⟩ := (h 0).2 rfl
  obtain ⟨t, ht⟩ := (h 1).2 rfl
  intro _ _
  rw [realize_pInK]
  simp only [LRV.tRVMul, Term.realize_func, funMap_def, fMap, Term.realize_var, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, hs, ht, mkRV]
  exact InK_mkRV _

end SortDiscipline

/-! ### The residue field and the preorder: basic lemmas -/

section Axioms

variable {K : Type*} [Field K]

@[simp] theorem fromK_one : fromK (K := K) 1 = some (1) := by
  rw [fromK_of_ne one_ne_zero]
  exact congrArg (fun u => some (u)) (Units.ext rfl)

theorem fromK_coe_unit (u : Kˣ) : fromK (K := K) (u : K) = some (u) := by
  rw [fromK_of_ne u.ne_zero]
  exact congrArg (fun w => some (w)) (Units.mk0_val u u.ne_zero)

theorem fromK_add (a b : K) : kAdd (fromK a) (fromK b) = fromK (a + b) := by
  rw [kAdd, toK_fromK, toK_fromK]

theorem fromK_mul (a b : K) : rvMul (fromK a) (fromK b) = fromK (a * b) := by
  rw [rvMul, toK_fromK, toK_fromK]

theorem fromK_neg (a : K) : kNeg (fromK a) = fromK (-a) := by
  rw [kNeg, toK_fromK]

theorem rvMul_infty_any (t : RV K) : rvMul t (none) = none := by
  rw [rvMul, toK_none, mul_zero, fromK_zero]

theorem rvMul_infty_any' (t : RV K) : rvMul (none) t = none := by
  rw [rvMul, toK_none, zero_mul, fromK_zero]

theorem rvMul_eq_fromK {t s : RV K} (_ht : t ≠ none) (_hs : s ≠ none) :
    rvMul t s = fromK (toK t * toK s) := rfl

theorem rvMul_unit (u v : Kˣ) :
    rvMul (some (u)) (some (v)) = some ((u * v)) := by
  rw [rvMul, toK_unit, toK_unit, fromK_of_ne (mul_ne_zero u.ne_zero v.ne_zero)]
  exact congrArg some (Units.ext rfl)

theorem kAdd_unit_toK {t s : RV K} (_ht : t ≠ none) (_hs : s ≠ none) :
    kAdd t s = fromK (toK t + toK s) := rfl

theorem kNeg_toK {t : RV K} (_ht : t ≠ none) : kNeg t = fromK (-(toK t)) := rfl

/-! ### `rv`-side arithmetic -/

theorem rvMul_comm (t s : RV K) : rvMul t s = rvMul s t := by
  rw [rvMul, rvMul, mul_comm]

theorem rvMul_assoc (t s r : RV K) : rvMul (rvMul t s) r = rvMul t (rvMul s r) := by
  simp only [rvMul, toK_fromK, mul_assoc]


theorem rvMul_one_left (u : Kˣ) : rvMul (some (1)) (some (u)) = some (u) := by
  rw [rvMul_unit, one_mul]

theorem rvMul_inv_left (u : Kˣ) :
    rvMul (some (u⁻¹)) (some (u)) = some (1) := by
  rw [rvMul_unit, inv_mul_cancel]

end Axioms

/-! ### The polynomial bridge from the Horner fold to `IsAlgClosed`

The term `hornerPoly` is a `List.foldl` over `(List.finRange n).reverse`.  We mirror that
fold on `K[X]`; evaluating the mirror at `r` gives the value of the `K`-level fold at `r`,
and the mirror is monic of `natDegree n+1`, so `IsAlgClosed` supplies a root. -/

section Horner

open Polynomial

variable {K : Type*} [Field K]

/-- one step of the polynomial fold: `P ↦ P * X + C a` -/
theorem monic_step {A : K[X]} (hA : A.Monic) (a : K) : (A * X + C a).Monic := by
  have hAX : (A * X).Monic := hA.mul monic_X
  have hdeg : (A * X).degree = ((A.natDegree : ℕ) : WithBot ℕ) + 1 := by
    rw [degree_mul, degree_eq_natDegree hA.ne_zero, degree_X]
  refine Monic.add_of_left hAX ?_
  refine lt_of_le_of_lt degree_C_le ?_
  rw [hdeg]
  exact WithBot.coe_lt_coe.mpr (Nat.zero_lt_succ _)

theorem natDegree_step {A : K[X]} (hA : A.Monic) (a : K) :
    (A * X + C a).natDegree = A.natDegree + 1 := by
  have hAX : (A * X).Monic := hA.mul monic_X
  have hdeg : (A * X).natDegree = A.natDegree + 1 := by
    rw [Monic.natDegree_mul hA monic_X, natDegree_X]
  rw [natDegree_add_eq_left_of_natDegree_lt, hdeg]
  rw [natDegree_C]
  omega

theorem monic_foldl {ι : Type*} (c : ι → K) (l : List ι) (A : K[X]) (hA : A.Monic) :
    (l.foldl (fun P i => P * X + C (c i)) A).Monic := by
  induction l generalizing A with
  | nil => simpa using hA
  | cons a l ih =>
    simp only [List.foldl_cons]
    exact ih _ (monic_step hA (c a))

theorem natDegree_foldl {ι : Type*} (c : ι → K) (l : List ι) (A : K[X]) (hA : A.Monic) :
    (l.foldl (fun P i => P * X + C (c i)) A).natDegree = A.natDegree + l.length := by
  induction l generalizing A with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih _ (monic_step hA (c a)), natDegree_step hA (c a)]
    omega

theorem eval_foldl {ι : Type*} (c : ι → K) (l : List ι) (A : K[X]) (α r : K)
    (hA : A.eval r = α) :
    (l.foldl (fun P i => P * X + C (c i)) A).eval r =
      l.foldl (fun a i => a * r + c i) α := by
  induction l generalizing A α with
  | nil => simpa using hA
  | cons a l ih =>
    simp only [List.foldl_cons]
    refine ih _ _ ?_
    rw [eval_add, eval_mul, eval_X, eval_C, hA]

/-- the polynomial mirror of the Horner fold of `hornerPoly` -/
noncomputable def Qpoly (c : ℕ → K) (n : ℕ) : K[X] :=
  (List.finRange n).reverse.foldl (fun P i => P * X + C (c i.val)) (X + C (c n))

theorem start_monic (a : K) : (X + C a : K[X]).Monic :=
  Monic.add_of_left monic_X (lt_of_le_of_lt degree_C_le (by rw [degree_X]; exact zero_lt_one))

theorem natDegree_X_add_C (a : K) : (X + C a : K[X]).natDegree = 1 := by
  rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X]
  rw [natDegree_C, natDegree_X]
  exact Nat.zero_lt_one

theorem Qpoly_monic (c : ℕ → K) (n : ℕ) : (Qpoly c n).Monic := by
  rw [Qpoly]
  exact monic_foldl (fun (i : Fin n) => c i.val) _ _ (start_monic (c n))

theorem Qpoly_natDegree (c : ℕ → K) (n : ℕ) : (Qpoly c n).natDegree = n + 1 := by
  rw [Qpoly]
  rw [natDegree_foldl (fun (i : Fin n) => c i.val) _ _ (start_monic (c n)), natDegree_X_add_C,
    List.length_reverse, List.length_finRange]
  omega

theorem Qpoly_eval (c : ℕ → K) (n : ℕ) (r : K) :
    (Qpoly c n).eval r =
      (List.finRange n).reverse.foldl (fun a i => a * r + c i.val) (r + c n) := by
  rw [Qpoly]
  exact eval_foldl (fun (i : Fin n) => c i.val) _ _ (r + c n) r (by simp)

/-- **The Horner fold has a root**: for every `c : ℕ → K` and every `n` there is `r : K`
with the Horner value `r^(n+1) + c n r^n + ⋯ + c 0` equal to `0`. -/
theorem exists_root_foldl [IsAlgClosed K] (c : ℕ → K) (n : ℕ) :
    ∃ r : K, (List.finRange n).reverse.foldl (fun a i => a * r + c i.val) (r + c n) = 0 := by
  have hmonic : (Qpoly c n).Monic := Qpoly_monic c n
  have hdeg : (Qpoly c n).degree ≠ 0 := by
    have h := Qpoly_natDegree c n
    have hne : (Qpoly c n) ≠ 0 := hmonic.ne_zero
    rw [degree_eq_natDegree hne, h]
    exact_mod_cast Nat.succ_ne_zero n
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (Qpoly c n) hdeg
  refine ⟨r, ?_⟩
  rw [← Qpoly_eval c n r]
  exact hr

end Horner

/-! ### Term realization for the Horner fold -/

section TermRealize

variable {K : Type*} [Field K]

theorem realize_tv {m : ℕ} (xs : Fin m → M K) (i : ℕ) (h : i < m) :
    Term.realize (Sum.elim dflt xs) (LRV.tv i h) = xs ⟨i, h⟩ := by
  simp [LRV.tv, Term.realize_var]

@[simp] theorem realize_tv_val {m : ℕ} (xs : Fin m → M K) (i : Fin m) :
    Term.realize (Sum.elim dflt xs) (LRV.tv i.val i.isLt) = xs i :=
  realize_tv xs i.val i.isLt

theorem realize_tVFAdd {m : ℕ} (xs : Fin m → M K) (A B : LRV.Tm m) (a b : K)
    (hA : Term.realize (Sum.elim dflt xs) A = mkVF a)
    (hB : Term.realize (Sum.elim dflt xs) B = mkVF b) :
    Term.realize (Sum.elim dflt xs) (LRV.tVFAdd A B) = mkVF (a + b) := by
  simp only [LRV.tVFAdd, Term.realize_func, funMap_def, fMap, mkVF, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
  rw [hA, hB]
  simp [mkVF]

theorem realize_tVFMul {m : ℕ} (xs : Fin m → M K) (A B : LRV.Tm m) (a b : K)
    (hA : Term.realize (Sum.elim dflt xs) A = mkVF a)
    (hB : Term.realize (Sum.elim dflt xs) B = mkVF b) :
    Term.realize (Sum.elim dflt xs) (LRV.tVFMul A B) = mkVF (a * b) := by
  simp only [LRV.tVFMul, Term.realize_func, funMap_def, fMap, mkVF, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
  rw [hA, hB]
  simp [mkVF]

theorem realize_tKAdd {m : ℕ} (xs : Fin m → M K) (A B : LRV.Tm m) (a b : K)
    (hA : Term.realize (Sum.elim dflt xs) A = mkRV (fromK a))
    (hB : Term.realize (Sum.elim dflt xs) B = mkRV (fromK b)) :
    Term.realize (Sum.elim dflt xs) (LRV.tKAdd A B) = mkRV (fromK (a + b)) := by
  simp only [LRV.tKAdd, Term.realize_func, funMap_def, fMap, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [hA, hB]
  simp only [mkRV]
  rw [fromK_add]

theorem realize_tRVMul {m : ℕ} (xs : Fin m → M K) (A B : LRV.Tm m) (a b : K)
    (hA : Term.realize (Sum.elim dflt xs) A = mkRV (fromK a))
    (hB : Term.realize (Sum.elim dflt xs) B = mkRV (fromK b)) :
    Term.realize (Sum.elim dflt xs) (LRV.tRVMul A B) = mkRV (fromK (a * b)) := by
  simp only [LRV.tRVMul, Term.realize_func, funMap_def, fMap, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [hA, hB]
  simp only [mkRV]
  rw [fromK_mul]

/-- the shared `List.foldl` shape of `hornerPoly` at `k = n+1` -/
theorem hornerPoly_succ_unfold {n : ℕ} (add mul : {m : ℕ} → LRV.Tm m → LRV.Tm m → LRV.Tm m) :
    LRV.hornerPoly (k := n + 1) add mul =
      (List.finRange n).reverse.foldl
        (fun acc i => add (mul acc (LRV.tv (n + 1) (by omega))) (LRV.tv i.val (by omega)))
        (add (LRV.tv (n + 1) (by omega)) (LRV.tv n (by omega))) := rfl

/-- realizing the Horner fold of the `VF` sort -/
theorem realize_hornerPoly_vf {n : ℕ} (c : ℕ → K) (r : K) (xs : Fin (n + 1 + 1) → M K)
    (hx : xs ⟨n + 1, by omega⟩ = mkVF r)
    (hc : ∀ i : ℕ, ∀ (h : i < n + 1), xs ⟨i, by omega⟩ = mkVF (c i)) :
    ∀ (l : List (Fin n)) (A : LRV.Tm (n + 1 + 1)) (α : K),
      Term.realize (Sum.elim dflt xs) A = mkVF α →
      Term.realize (Sum.elim dflt xs)
        (l.foldl (fun acc i => LRV.tVFAdd (LRV.tVFMul acc (LRV.tv (n + 1) (by omega)))
          (LRV.tv i.val (by omega))) A) =
        mkVF (l.foldl (fun a i => a * r + c i.val) α) := by
  intro l
  induction l with
  | nil => intro A α h; simpa using h
  | cons a l ih =>
    intro A α h
    simp only [List.foldl_cons]
    refine ih _ _ ?_
    rw [realize_tVFAdd _ _ _ _ _ (realize_tVFMul _ _ _ _ _ h (by
      rw [realize_tv]; exact hx)) (by rw [realize_tv]; exact hc a.val (by omega))]

/-- realizing the Horner fold of the `RV` sort (the residue field `K = Kˣ ∪ {0}`) -/
theorem realize_hornerPoly_rv {n : ℕ} (c : ℕ → K) (r : K) (xs : Fin (n + 1 + 1) → M K)
    (hx : xs ⟨n + 1, by omega⟩ = mkRV (fromK r))
    (hc : ∀ i : ℕ, ∀ (h : i < n + 1), xs ⟨i, by omega⟩ = mkRV (fromK (c i))) :
    ∀ (l : List (Fin n)) (A : LRV.Tm (n + 1 + 1)) (α : K),
      Term.realize (Sum.elim dflt xs) A = mkRV (fromK α) →
      Term.realize (Sum.elim dflt xs)
        (l.foldl (fun acc i => LRV.tKAdd (LRV.tRVMul acc (LRV.tv (n + 1) (by omega)))
          (LRV.tv i.val (by omega))) A) =
        mkRV (fromK (l.foldl (fun a i => a * r + c i.val) α)) := by
  intro l
  induction l with
  | nil => intro A α h; simpa using h
  | cons a l ih =>
    intro A α h
    simp only [List.foldl_cons]
    refine ih _ _ ?_
    rw [realize_tKAdd _ _ _ _ _ (realize_tRVMul _ _ _ _ _ h (by
      rw [realize_tv]; exact hx)) (by rw [realize_tv]; exact hc a.val (by omega))]

end TermRealize

/-! ### The algebraic-closedness schemes -/

section Schemes

variable {K : Type*} [Field K]

/-- the coefficient of the `i`-th variable of a `VF`-sorted coefficient tuple -/
noncomputable def coefOf {n : ℕ} (xs : Fin (n + 1) → M K)
    (h : ∀ i : Fin (n + 1), ∃ a : K, xs i = mkVF a) (i : ℕ) : K :=
  if hi : i < n + 1 then (h ⟨i, hi⟩).choose else 0

theorem coefOf_spec {n : ℕ} (xs : Fin (n + 1) → M K)
    (h : ∀ i : Fin (n + 1), ∃ a : K, xs i = mkVF a) {i : ℕ}
    (hi : i < n + 1) : xs ⟨i, hi⟩ = mkVF (coefOf xs h i) := by
  rw [coefOf, dif_pos hi]
  exact (h ⟨i, hi⟩).choose_spec

/-- the coefficient of the `i`-th variable of a `K`-sorted coefficient tuple -/
noncomputable def coefOfRV {n : ℕ} (xs : Fin (n + 1) → M K)
    (h : ∀ i : Fin (n + 1), ∃ t : RV K, xs i = mkRV t)
    (i : ℕ) : K :=
  if hi : i < n + 1 then toK ((h ⟨i, hi⟩).choose) else 0

theorem coefOfRV_spec {n : ℕ} (xs : Fin (n + 1) → M K)
    (h : ∀ i : Fin (n + 1), ∃ t : RV K, xs i = mkRV t)
    {i : ℕ} (hi : i < n + 1) : xs ⟨i, hi⟩ = mkRV (fromK (coefOfRV xs h i)) := by
  have hspec := (h ⟨i, hi⟩).choose_spec
  have hc : coefOfRV xs h i = toK (h ⟨i, hi⟩).choose := by
    rw [coefOfRV, dif_pos hi]
  rw [hc, fromK_toK]
  exact hspec

theorem realize_hornerPoly_vf_snoc {n : ℕ} (c : ℕ → K) (r : K) (xs : Fin (n + 1) → M K)
    (hc : ∀ i : ℕ, ∀ (h : i < n + 1), xs ⟨i, h⟩ = mkVF (c i)) :
    Term.realize (Sum.elim dflt (Fin.snoc xs (mkVF r)))
        (LRV.hornerPoly (k := n + 1) LRV.tVFAdd LRV.tVFMul) =
      mkVF ((List.finRange n).reverse.foldl (fun a i => a * r + c i.val) (r + c n)) := by
  rw [hornerPoly_succ_unfold]
  refine realize_hornerPoly_vf c r (Fin.snoc xs (mkVF r)) ?_ ?_ (List.finRange n).reverse _ _ ?_
  · rw [show (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)) = Fin.last (n + 1) from Fin.ext rfl,
      Fin.snoc_last]
  · intro i hi
    rw [show (⟨i, by omega⟩ : Fin (n + 1 + 1)) = Fin.castSucc ⟨i, hi⟩ from Fin.ext rfl,
      Fin.snoc_castSucc]
    exact hc i hi
  · refine realize_tVFAdd _ _ _ _ _ ?_ ?_
    · rw [realize_tv]
      rw [show (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)) = Fin.last (n + 1) from Fin.ext rfl,
        Fin.snoc_last]
    · rw [realize_tv]
      rw [show (⟨n, by omega⟩ : Fin (n + 1 + 1)) = Fin.castSucc ⟨n, by omega⟩ from Fin.ext rfl,
        Fin.snoc_castSucc]
      exact hc n (by omega)

theorem realize_hornerPoly_rv_snoc {n : ℕ} (c : ℕ → K) (r : K) (xs : Fin (n + 1) → M K)
    (hc : ∀ i : ℕ, ∀ (h : i < n + 1), xs ⟨i, h⟩ = mkRV (fromK (c i))) :
    Term.realize (Sum.elim dflt (Fin.snoc xs (mkRV (fromK r))))
        (LRV.hornerPoly (k := n + 1) LRV.tKAdd LRV.tRVMul) =
      mkRV (fromK ((List.finRange n).reverse.foldl (fun a i => a * r + c i.val) (r + c n))) := by
  rw [hornerPoly_succ_unfold]
  refine realize_hornerPoly_rv c r (Fin.snoc xs (mkRV (fromK r))) ?_ ?_ (List.finRange n).reverse _ _
    ?_
  · rw [show (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)) = Fin.last (n + 1) from Fin.ext rfl,
      Fin.snoc_last]
  · intro i hi
    rw [show (⟨i, by omega⟩ : Fin (n + 1 + 1)) = Fin.castSucc ⟨i, hi⟩ from Fin.ext rfl,
      Fin.snoc_castSucc]
    exact hc i hi
  · refine realize_tKAdd _ _ _ _ _ ?_ ?_
    · rw [realize_tv]
      rw [show (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)) = Fin.last (n + 1) from Fin.ext rfl,
        Fin.snoc_last]
    · rw [realize_tv]
      rw [show (⟨n, by omega⟩ : Fin (n + 1 + 1)) = Fin.castSucc ⟨n, by omega⟩ from Fin.ext rfl,
        Fin.snoc_castSucc]
      exact hc n (by omega)

/-- algebraic closedness of the `VF` sort at the trivial-valuation structure -/
theorem model_acfScheme_vf [IsAlgClosed K] (n : ℕ) :
    (M K) ⊨ Axioms.acfScheme .vf LRV.tVFZero LRV.tVFAdd LRV.tVFMul (n + 1) := by
  simp only [Axioms.acfScheme]
  rw [model_allSorted]
  intro xs h
  prep
  have hcoe : ∀ i : Fin (n + 1), ∃ a : K, xs i = mkVF a := by
    intro i
    exact (h i).1 rfl
  obtain ⟨r, hr⟩ := exists_root_foldl (K := K) (coefOf (n := n) xs hcoe) n
  refine ⟨mkVF r, ⟨r, ?_⟩, ?_⟩
  · rw [show (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)) = Fin.last (n + 1) from Fin.ext rfl,
      Fin.snoc_last]
    rfl
  · rw [realize_hornerPoly_vf_snoc (coefOf (n := n) xs hcoe) r xs
      (fun i hi => coefOf_spec (n := n) xs hcoe hi), hr]
    rfl

/-- algebraic closedness of `K = Kˣ ∪ {0}` at the trivial-valuation structure -/
theorem model_acfScheme_k [IsAlgClosed K] (n : ℕ) :
    (M K) ⊨ Axioms.acfSchemeK (n + 1) := by
  simp only [Axioms.acfSchemeK]
  rw [model_allSortedK]
  intro xs h hne
  prep
  have hcoe : ∀ i : Fin (n + 1), ∃ t : RV K, xs i = mkRV t := fun i => (h i).2 rfl
  obtain ⟨r, hr⟩ := exists_root_foldl (K := K) (coefOfRV (n := n) xs hcoe) n
  refine ⟨mkRV (fromK r), ⟨⟨fromK r, ?_⟩, ?_⟩, ?_⟩
  · rw [show (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)) = Fin.last (n + 1) from Fin.ext rfl,
      Fin.snoc_last]
    rfl
  · rw [realize_pInK]
    simp only [Term.realize_var, Sum.elim_inr]
    rw [show (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)) = Fin.last (n + 1) from Fin.ext rfl,
      Fin.snoc_last]
    exact InK_mkRV _
  · rw [realize_hornerPoly_rv_snoc (coefOfRV (n := n) xs hcoe) r xs
      (fun i hi => coefOfRV_spec (n := n) xs hcoe hi), hr]
    rw [fromK_zero]
    rfl

end Schemes

/-! ### The remaining axioms of `ACVF` -/

section RemainingAxioms

open Polynomial

variable {K : Type*} [Field K]

/-- an `RV`-element of the `K`-sort, read as `mkRV (fromK a)` -/
theorem rvK_rep {m : ℕ} {xs : Fin m → M K} {i : Fin m}
    (h : ∃ t : RV K, xs i = mkRV t) (_hK : InK (xs i)) :
    ∃ a : K, xs i = mkRV (fromK a) := by
  obtain ⟨t, ht⟩ := h
  cases t with
  | none => exact ⟨0, by rw [ht, fromK_zero]⟩
  | some u => exact ⟨toK (some u), by rw [ht, fromK_toK]⟩

theorem rvMul_zero_right {t : RV K} (_ht : t ≠ none) : rvMul t none = none :=
  rvMul_infty_any t

/-! #### the field axioms of the `VF` sort -/

theorem model_vfField : (M K) ⊨ Axioms.vfField := by
  rw [Theory.model_iff]; intro s hs
  simp only [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms, List.mem_cons, List.mem_nil_iff,
    or_false] at hs
  obtain rfl | h2 := hs
  · rw [model_allSorted]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl; obtain ⟨b, hb⟩ := (h 1).1 rfl; obtain ⟨c, hc⟩ := (h 2).1 rfl
    rw [ha, hb, hc]; exact congrArg mkVF (add_assoc a b c)
  obtain rfl | h3 := h2
  · rw [model_allSorted]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl; obtain ⟨b, hb⟩ := (h 1).1 rfl
    rw [ha, hb]; exact congrArg mkVF (add_comm a b)
  obtain rfl | h4 := h3
  · rw [model_allSorted]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl
    rw [ha]; exact congrArg mkVF (add_zero a)
  obtain rfl | h5 := h4
  · rw [model_allSorted]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl
    rw [ha]; exact congrArg mkVF (add_neg_cancel a)
  obtain rfl | h6 := h5
  · rw [model_allSorted]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl; obtain ⟨b, hb⟩ := (h 1).1 rfl; obtain ⟨c, hc⟩ := (h 2).1 rfl
    rw [ha, hb, hc]; exact congrArg mkVF (mul_assoc a b c)
  obtain rfl | h7 := h6
  · rw [model_allSorted]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl; obtain ⟨b, hb⟩ := (h 1).1 rfl
    rw [ha, hb]; exact congrArg mkVF (mul_comm a b)
  obtain rfl | h8 := h7
  · rw [model_allSorted]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl
    rw [ha]; exact congrArg mkVF (mul_one a)
  obtain rfl | h9 := h8
  · rw [model_allSorted]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl; obtain ⟨b, hb⟩ := (h 1).1 rfl; obtain ⟨c, hc⟩ := (h 2).1 rfl
    rw [ha, hb, hc]; exact congrArg mkVF (mul_add a b c)
  obtain rfl | h10 := h9
  · prep
    intro hh
    exact zero_ne_one (Sum.inl.inj hh)
  · obtain rfl := by simpa using h10
    rw [model_allSorted]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl
    rw [ha]
    rcases eq_or_ne a 0 with rfl | ha0
    · exact Or.inl rfl
    · refine Or.inr ⟨mkVF a⁻¹, ⟨a⁻¹, rfl⟩, ?_⟩
      have h1' : (1 : Fin 2) = Fin.last 1 := rfl
      have h0' : (0 : Fin 2) = Fin.castSucc (0 : Fin 1) := rfl
      rw [h1', h0', Fin.snoc_castSucc, Fin.snoc_last, ha, mkVF]
      exact congrArg Sum.inl (mul_inv_cancel₀ ha0)

/-! #### the field axioms of the residue field `K = Kˣ ∪ {0}` -/

theorem kAdd_self_kNeg (a : K) : kAdd (fromK a) (kNeg (fromK a)) = none := by
  rw [fromK_neg, fromK_add, add_neg_cancel, fromK_zero]

theorem model_kField : (M K) ⊨ Axioms.kField := by
  rw [Theory.model_iff]; intro s hs
  simp only [Axioms.kField, Axioms.ofList, List.mem_cons, List.mem_nil_iff, or_false,
    Function.comp_apply] at hs
  obtain rfl | h2 := hs
  · rw [model_allSortedK]; intro xs h hne; prep
    obtain ⟨a, ha⟩ := rvK_rep ((h 0).2 rfl) (hne 0)
    obtain ⟨b, hb⟩ := rvK_rep ((h 1).2 rfl) (hne 1)
    obtain ⟨c, hc⟩ := rvK_rep ((h 2).2 rfl) (hne 2)
    simp only [mkRV, ha, hb, hc, fromK_add, add_assoc]
  obtain rfl | h3 := h2
  · rw [model_allSortedK]; intro xs h hne; prep
    obtain ⟨a, ha⟩ := rvK_rep ((h 0).2 rfl) (hne 0)
    obtain ⟨b, hb⟩ := rvK_rep ((h 1).2 rfl) (hne 1)
    simp only [mkRV, ha, hb, fromK_add, add_comm]
  obtain rfl | h4 := h3
  · rw [model_allSortedK]; intro xs h hne; prep
    obtain ⟨a, ha⟩ := rvK_rep ((h 0).2 rfl) (hne 0)
    simp only [mkRV, ha, ← fromK_zero, fromK_add, add_zero]
  obtain rfl | h5 := h4
  · rw [model_allSortedK]; intro xs h hne; prep
    obtain ⟨a, ha⟩ := rvK_rep ((h 0).2 rfl) (hne 0)
    simp only [mkRV, ha, kAdd_self_kNeg]
  obtain rfl | h6 := h5
  · rw [model_allSortedK]; intro xs h hne; prep
    obtain ⟨a, ha⟩ := rvK_rep ((h 0).2 rfl) (hne 0)
    obtain ⟨b, hb⟩ := rvK_rep ((h 1).2 rfl) (hne 1)
    obtain ⟨c, hc⟩ := rvK_rep ((h 2).2 rfl) (hne 2)
    simp only [mkRV, ha, hb, hc, fromK_mul, mul_assoc]
  obtain rfl | h7 := h6
  · rw [model_allSortedK]; intro xs h hne; prep
    obtain ⟨a, ha⟩ := rvK_rep ((h 0).2 rfl) (hne 0)
    obtain ⟨b, hb⟩ := rvK_rep ((h 1).2 rfl) (hne 1)
    simp only [mkRV, ha, hb, fromK_mul, mul_comm]
  obtain rfl | h8 := h7
  · rw [model_allSortedK]; intro xs h hne; prep
    obtain ⟨a, ha⟩ := rvK_rep ((h 0).2 rfl) (hne 0)
    simp only [mkRV, ha, ← fromK_one, fromK_mul, mul_one]
  obtain rfl | h9 := h8
  · rw [model_allSortedK]; intro xs h hne; prep
    obtain ⟨a, ha⟩ := rvK_rep ((h 0).2 rfl) (hne 0)
    obtain ⟨b, hb⟩ := rvK_rep ((h 1).2 rfl) (hne 1)
    obtain ⟨c, hc⟩ := rvK_rep ((h 2).2 rfl) (hne 2)
    simp only [mkRV, ha, hb, hc, fromK_add, fromK_mul, mul_add]
  obtain rfl | h10 := h9
  · prep
    intro hh
    exact nomatch (Sum.inr.inj hh)
  · obtain rfl := by simpa using h10
    rw [model_allSortedK]; intro xs h hne; prep
    obtain ⟨a, ha⟩ := rvK_rep ((h 0).2 rfl) (hne 0)
    rcases eq_or_ne a 0 with rfl | ha0
    · left
      rw [ha, fromK_zero]
      rfl
    · right
      refine ⟨mkRV (fromK a⁻¹), ⟨⟨fromK a⁻¹, rfl⟩, ?_⟩, ?_⟩
      · rw [realize_pInK]
        simp only [Term.realize_var, Sum.elim_inr, Fin.snoc_last]
        exact InK_mkRV _
      · have h1' : (1 : Fin 2) = Fin.last 1 := rfl
        have h0' : (0 : Fin 2) = Fin.castSucc (0 : Fin 1) := rfl
        rw [h1', h0', Fin.snoc_castSucc, Fin.snoc_last, ha]
        simp only [mkRV, fromK_mul, mul_inv_cancel₀ ha0, fromK_one]

end RemainingAxioms

/-! ### the multiplicative structure of the `RV` sort and the preorder -/

section RVGroupPreorder

variable {K : Type*} [Field K]

/-- powers in the `RV` sort -/
noncomputable def rvpow (s : RV K) : ℕ → RV K
  | 0 => some (1)
  | k + 1 => rvMul (rvpow s k) s

theorem rvpow_unit (u : Kˣ) : ∀ k : ℕ, rvpow (some (u)) k = some ((u ^ k))
  | 0 => by simp [rvpow]
  | k + 1 => by
    rw [rvpow, rvpow_unit u k, rvMul_unit, pow_succ]

theorem realize_tRVMul' {m : ℕ} (xs : Fin m → M K) (A B : LRV.Tm m) (s t : RV K)
    (hA : Term.realize (Sum.elim dflt xs) A = mkRV s)
    (hB : Term.realize (Sum.elim dflt xs) B = mkRV t) :
    Term.realize (Sum.elim dflt xs) (LRV.tRVMul A B) = mkRV (rvMul s t) := by
  simp only [LRV.tRVMul, Term.realize_func, funMap_def, fMap, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [hA, hB]
  simp only [mkRV]

theorem realize_tRVPow {m : ℕ} (xs : Fin m → M K) (i : ℕ) (hi : i < m) (s : RV K)
    (hs : xs ⟨i, hi⟩ = mkRV s) (k : ℕ) :
    Term.realize (Sum.elim dflt xs) (LRV.tRVPow (LRV.tv i hi) k) = mkRV (rvpow s k) := by
  induction k with
  | zero => simp [LRV.tRVPow, rvpow, mkRV, LRV.tRVOne, funMap_def, fMap, cOneRV]
  | succ k ih =>
    rw [show LRV.tRVPow (LRV.tv i hi) (k + 1) =
      LRV.tRVMul (LRV.tRVPow (LRV.tv i hi) k) (LRV.tv i hi) from rfl]
    rw [realize_tRVMul' xs _ _ _ _ ih (by rw [realize_tv]; exact hs)]
    rfl

theorem model_rvOneMem : (M K) ⊨ Axioms.rvOneMem := by
  simp only [Axioms.rvOneMem]; prep
  exact ⟨1, rfl⟩

theorem model_rvMulMem : (M K) ⊨ Axioms.rvMulMem := by
  simp only [Axioms.rvMulMem]; rw [model_allSorted]; intro xs h; prep
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  refine ⟨u * v, ?_⟩
  rw [hu, hv]
  simp only [mkRV, rvMul_unit]

theorem model_rvMulAssoc : (M K) ⊨ Axioms.rvMulAssoc := by
  simp only [Axioms.rvMulAssoc]; rw [model_allSorted]; intro xs h; prep
  obtain ⟨s, hs⟩ := (h 0).2 rfl
  obtain ⟨t, ht⟩ := (h 1).2 rfl
  obtain ⟨r, hr⟩ := (h 2).2 rfl
  simp only [hs, ht, hr, mkRV, rvMul_assoc]

theorem model_rvMulComm : (M K) ⊨ Axioms.rvMulComm := by
  simp only [Axioms.rvMulComm]; rw [model_allSorted]; intro xs h; prep
  obtain ⟨s, hs⟩ := (h 0).2 rfl
  obtain ⟨t, ht⟩ := (h 1).2 rfl
  simp only [hs, ht, mkRV, rvMul_comm]

theorem model_rvMulOne : (M K) ⊨ Axioms.rvMulOne := by
  simp only [Axioms.rvMulOne]; rw [model_allSorted]; intro xs h; prep
  rintro ⟨u, hu⟩
  rw [hu]
  simp only [mkRV, rvMul_unit, one_mul]

theorem model_rvMulInv : (M K) ⊨ Axioms.rvMulInv := by
  simp only [Axioms.rvMulInv]; rw [model_allSorted]; intro xs h; prep
  rintro ⟨u, hu⟩
  refine ⟨mkRV (some (u⁻¹)), ⟨some (u⁻¹), ?_⟩, ⟨u⁻¹, ?_⟩, ?_⟩
  · rw [show (⟨1, Nat.one_lt_two⟩) = Fin.last 1 from Fin.ext rfl, Fin.snoc_last]
    rfl
  · rw [show (1 : Fin 2) = Fin.last 1 from Fin.ext rfl, Fin.snoc_last]
    rfl
  · rw [show (1 : Fin 2) = Fin.last 1 from Fin.ext rfl,
      show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) from Fin.ext rfl, Fin.snoc_last,
      Fin.snoc_castSucc, hu]
    simp only [mkRV, rvMul_unit, inv_mul_cancel]

theorem model_rvMulZeroK : (M K) ⊨ Axioms.rvMulZeroK := by
  simp only [Axioms.rvMulZeroK]; rw [model_allSorted]; intro xs h; prep
  obtain ⟨s, hs⟩ := (h 0).2 rfl
  intro _
  simp only [LRV.tRVMul, LRV.tRVZero, Term.realize_func, funMap_def, fMap,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_eq, hs, mkRV]
  rw [rvMul_infty_any]

theorem model_rvMulInfty : (M K) ⊨ Axioms.rvMulInfty := by
  simp only [Axioms.rvMulInfty]; rw [model_allSorted]; intro xs h; prep
  obtain ⟨s, hs⟩ := (h 0).2 rfl
  rw [hs]
  simp only [mkRV]
  rw [rvMul_infty_any]

/-! #### the preorder -/

theorem le_of_rel {s t : RV K}
    (h : ∃ a b : RV K, (Sum.inr s : M K) = Sum.inr a ∧ (Sum.inr t : M K) = Sum.inr b ∧ vle a b) :
    vle s t := by
  obtain ⟨a, b, e1, e2, hv⟩ := h
  simp only [Sum.inr.injEq] at e1 e2
  subst e1
  subst e2
  exact hv

theorem vval_rvMap_zero : vval (rvMap (K := K) 0) = 0 := by
  rw [rvMap_zero]; rfl

theorem vval_rvMap_of_ne {x : K} (h : x ≠ 0) : vval (rvMap x) = 1 := by
  rw [rvMap_of_ne h, fromK_of_ne h]; rfl


/-! ### Assembly: which theories of `Milestone0/Encoding.lean` hold at `M` -/

section Assembly

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

theorem model_sortClosure : (M K) ⊨ Axioms.sortClosure := by
  rw [Theory.model_iff]
  intro s hs
  simp only [Axioms.sortClosure, Axioms.ofList, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact model_sdVFZero
  · exact model_sdVFOne
  · exact model_sdVFAdd
  · exact model_sdVFNeg
  · exact model_sdVFMul
  · exact model_sdRv
  · exact model_sdRVZero
  · exact model_sdRVInfty
  · exact model_sdRVOne
  · exact model_sdRVMul
  · exact model_sdUnits
  · exact model_sdKAdd
  · exact model_sdKNeg
  · exact model_sdKMul

theorem model_sortAxioms : (M K) ⊨ Axioms.sortAxioms := by
  rw [Axioms.sortAxioms, Theory.model_union_iff]
  refine ⟨model_sortClosure, ?_⟩
  rw [Theory.model_iff]
  intro s hs
  simp only [Axioms.ofList, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl
  · exact model_sdCover
  · exact model_sdDisjoint

theorem model_vfAlgClosed : (M K) ⊨ Axioms.vfAlgClosed := by
  rw [Theory.model_iff]
  intro s hs
  obtain ⟨k, hk, rfl⟩ := hs
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact model_acfScheme_vf n

theorem model_kAlgClosed : (M K) ⊨ Axioms.kAlgClosed := by
  rw [Theory.model_iff]
  intro s hs
  obtain ⟨k, hk, rfl⟩ := hs
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact model_acfScheme_k n

/-- the fragment of `ACVF` verified unconditionally at `M`: items 1 and 3 (fields), their
algebraic closedness, and the sort discipline of the encoding -/
theorem model_ACVF_partial :
    (M K) ⊨ (Axioms.sortAxioms ∪ Axioms.vfField ∪ Axioms.vfAlgClosed ∪ Axioms.kField ∪
      Axioms.kAlgClosed) := by
  rw [Theory.model_union_iff]
  refine ⟨?_, model_kAlgClosed⟩
  rw [Theory.model_union_iff]
  refine ⟨?_, model_kField⟩
  rw [Theory.model_union_iff]
  refine ⟨?_, model_vfAlgClosed⟩
  rw [Theory.model_union_iff]
  exact ⟨model_sortAxioms, model_vfField⟩

/-- `rvGroup` without the divisibility scheme -/
theorem model_rvGroup_list : (M K) ⊨ Axioms.ofList [Axioms.rvOneMem, Axioms.rvMulMem,
    Axioms.rvMulAssoc, Axioms.rvMulComm, Axioms.rvMulOne, Axioms.rvMulInv,
    Axioms.rvMulZeroK, Axioms.rvMulInfty] := by
  rw [Theory.model_iff]
  intro s hs
  simp only [Axioms.ofList, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact model_rvOneMem
  · exact model_rvMulMem
  · exact model_rvMulAssoc
  · exact model_rvMulComm
  · exact model_rvMulOne
  · exact model_rvMulInv
  · exact model_rvMulZeroK
  · exact model_rvMulInfty

end Assembly

/-! ### The preorder of the `RV` sort

With `rvLeC` written directly on the carrier, each axiom of `preorderRV` is a case split on
the shape of its arguments. -/

section Preorder

variable {K : Type*} [Field K]

theorem rvLeC_refl_mk {t : RV K} (_h : t ≠ none) : rvLeC (mkRV t) (mkRV t) := by
  cases t with
  | none => exact Or.inl rfl
  | some u => exact Or.inr ⟨u, rfl⟩

theorem rvLeC_top_mk (t : RV K) : rvLeC (mkRV t) (cInfty) := Or.inl rfl

theorem cInfty_ne_cUnit (u : Kˣ) : (cInfty : M K) ≠ cUnit u := fun h => nomatch (Sum.inr.inj h)

theorem cOneRV_ne_cInfty : (cOneRV : M K) ≠ cInfty := fun h => nomatch (Sum.inr.inj h)

theorem mkRV_ne_cZero {t : RV K} (h : t ≠ none) : (mkRV t : M K) ≠ cZero :=
  fun hh => h (Sum.inr.inj hh)

/-- `∞ ≤ x` forces `x = ∞`: the first disjunct of `rvLeC` is the only way to be below `∞` -/
theorem rvLeC_infty_mk {t : RV K} (h : rvLeC cInfty (mkRV t)) : mkRV t = cInfty := by
  rcases h with h | ⟨u, hu⟩
  · exact h
  · exact absurd hu (cInfty_ne_cUnit u)

theorem rvLeC_trans_mk {t s r : RV K} (ht : t ≠ none)
    (_h1 : rvLeC (mkRV t) (mkRV s)) (_h2 : rvLeC (mkRV s) (mkRV r)) :
    rvLeC (mkRV t) (mkRV r) := by
  cases t with
  | none => exact absurd rfl ht
  | some u => exact Or.inr ⟨u, rfl⟩

theorem rvLeC_total_mk {t s : RV K} (ht : t ≠ none) :
    rvLeC (mkRV t) (mkRV s) ∨ rvLeC (mkRV s) (mkRV t) := by
  cases t with
  | none => exact absurd rfl ht
  | some u => exact Or.inl (Or.inr ⟨u, rfl⟩)

theorem rvLeC_one_iff_unit {t : RV K} (_ht : t ≠ none) :
    (∃ u : Kˣ, mkRV t = cUnit u) ↔ (rvLeC cOneRV (mkRV t) ∧ rvLeC (mkRV t) cOneRV) := by
  constructor
  · rintro ⟨u, hu⟩
    rw [hu]
    exact ⟨Or.inr ⟨1, rfl⟩, Or.inr ⟨u, rfl⟩⟩
  · rintro ⟨_h1, h2⟩
    rcases h2 with h | h
    · exact absurd h cOneRV_ne_cInfty
    · exact h

theorem rvMul_zero_unit (u : Kˣ) : rvMul (none : RV K) (some (u)) = none :=
  rvMul_infty_any' _

theorem rvLeC_mulCompat_mk {t s : RV K} (h : rvLeC (mkRV t) (mkRV s)) (u : Kˣ) :
    rvLeC (mkRV (rvMul t (some (u)))) (mkRV (rvMul s (some (u)))) := by
  cases t with
  | none =>
    have hs : s = none := by
      rcases h with h | ⟨w, hw⟩
      · exact Sum.inr.inj h
      · exact absurd hw (fun hh => nomatch hh)
    subst hs
    refine Or.inl ?_
    show mkRV (rvMul (none) (some (u))) = cInfty
    rw [rvMul_zero_unit]
    rfl
  | some w =>
    refine Or.inr ⟨w * u, ?_⟩
    show mkRV (rvMul (some (w)) (some (u))) = cUnit (w * u)
    rw [rvMul_unit]
    rfl

theorem model_leRefl : (M K) ⊨ Axioms.leRefl := by
  simp only [Axioms.leRefl]; rw [model_allSorted]; intro xs h; prep
  intro hne
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  have ht' : t ≠ none := fun hh => hne (by rw [ht, hh]; rfl)
  rw [ht]
  exact rvLeC_refl_mk ht'

theorem model_leTrans : (M K) ⊨ Axioms.leTrans := by
  simp only [Axioms.leTrans]; rw [model_allSorted]; intro xs h; prep
  intro hne1 hne2 hne3 h12 h23
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  obtain ⟨r, hr⟩ := (h 2).2 rfl
  have ht' : t ≠ none := fun hh => hne1 (by rw [ht, hh]; rfl)
  rw [ht, hs] at h12
  rw [hs, hr] at h23
  rw [ht, hr]
  exact rvLeC_trans_mk ht' h12 h23

theorem model_leTotal : (M K) ⊨ Axioms.leTotal := by
  simp only [Axioms.leTotal]; rw [model_allSorted]; intro xs h; prep
  intro hne1 hne2
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  have ht' : t ≠ none := fun hh => hne1 (by rw [ht, hh]; rfl)
  rw [ht, hs]
  rcases rvLeC_total_mk (s := s) ht' with hle | hle
  · exact Or.inl hle
  · exact Or.inr hle

theorem model_leTop : (M K) ⊨ Axioms.leTop := by
  simp only [Axioms.leTop]; rw [model_allSorted]; intro xs h; prep
  intro hne
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht]
  exact rvLeC_top_mk t

theorem model_leInftyEq : (M K) ⊨ Axioms.leInftyEq := by
  simp only [Axioms.leInftyEq]; rw [model_allSorted]; intro xs h; prep
  intro hne hle
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht] at hle ⊢
  exact rvLeC_infty_mk hle

theorem model_leClassOne : (M K) ⊨ Axioms.leClassOne := by
  simp only [Axioms.leClassOne]; rw [model_allSorted]; intro xs h; prep
  intro hne
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  have ht' : t ≠ none := fun hh => hne (by rw [ht, hh]; rfl)
  rw [ht]
  exact rvLeC_one_iff_unit ht'

theorem model_leMulCompat : (M K) ⊨ Axioms.leMulCompat := by
  simp only [Axioms.leMulCompat]; rw [model_allSorted]; intro xs h; prep
  intro hne1 hne2 hne3 hunit hle
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  obtain ⟨r, hr⟩ := (h 2).2 rfl
  obtain ⟨w, hw⟩ := hunit
  rw [ht, hs] at hle
  have hw' : mkRV r = cUnit w := by rw [← hr]; exact hw
  rw [ht, hs, hr, hw']
  simp only [mkRV, cUnit]
  exact rvLeC_mulCompat_mk hle w

theorem model_preorderRV : (M K) ⊨ Axioms.preorderRV := by
  rw [Theory.model_iff]
  intro s hs
  simp only [Axioms.preorderRV, Axioms.ofList, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact model_leRefl
  · exact model_leTrans
  · exact model_leTotal
  · exact model_leTop
  · exact model_leInftyEq
  · exact model_leClassOne
  · exact model_leMulCompat

end Preorder

/-! ### Divisibility of `Kˣ`, the `rv`-axioms, and the assembly -/

section Finishing

variable {K : Type*} [Field K]

theorem model_rvDivisible [IsAlgClosed K] (n : ℕ) (hn : 1 ≤ n) :
    (M K) ⊨ Axioms.rvDivisible n := by
  simp only [Axioms.rvDivisible]; rw [model_allSorted]; intro xs h; prep
  intro hunit
  obtain ⟨u, hu⟩ := hunit
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (k := K) (n := n) (u : K)
    (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hr0 : r ≠ 0 := by
    intro hh
    rw [hh, zero_pow (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn))] at hr
    exact u.ne_zero hr.symm
  have hkey : (Units.mk0 r hr0 : Kˣ) ^ n = u := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact hr
  refine ⟨mkRV (some ((Units.mk0 r hr0))), ⟨some ((Units.mk0 r hr0)), ?_⟩,
    ⟨Units.mk0 r hr0, ?_⟩, ?_⟩
  · rw [show (⟨1, Nat.one_lt_two⟩) = Fin.last 1 from Fin.ext rfl, Fin.snoc_last]
    rfl
  · rw [show (1 : Fin 2) = Fin.last 1 from Fin.ext rfl, Fin.snoc_last]
    rfl
  · have hpt : (Fin.snoc xs (mkRV (some ((Units.mk0 r hr0)))) : Fin 2 → M K) ⟨1, Nat.one_lt_two⟩ =
        mkRV (some ((Units.mk0 r hr0))) := by
      rw [show (⟨1, Nat.one_lt_two⟩) = Fin.last 1 from Fin.ext rfl, Fin.snoc_last]
    have hpow := realize_tRVPow (Fin.snoc xs (mkRV (some ((Units.mk0 r hr0)))) :
      Fin 2 → M K) 1 Nat.one_lt_two (some ((Units.mk0 r hr0))) hpt n
    rw [show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) from Fin.ext rfl, Fin.snoc_castSucc, hu]
    refine hpow.trans ?_
    rw [rvpow_unit, hkey]
    rfl

theorem model_rvGroup [IsAlgClosed K] [CharZero K] : (M K) ⊨ Axioms.rvGroup := by
  rw [Theory.model_iff]; intro s hs
  rcases hs with hs | hs
  · haveI : (M K) ⊨ Axioms.ofList [Axioms.rvOneMem, Axioms.rvMulMem, Axioms.rvMulAssoc,
      Axioms.rvMulComm, Axioms.rvMulOne, Axioms.rvMulInv, Axioms.rvMulZeroK,
      Axioms.rvMulInfty] := model_rvGroup_list
    exact (Theory.model_iff (T := Axioms.ofList [Axioms.rvOneMem, Axioms.rvMulMem,
      Axioms.rvMulAssoc, Axioms.rvMulComm, Axioms.rvMulOne, Axioms.rvMulInv,
      Axioms.rvMulZeroK, Axioms.rvMulInfty])).mp model_rvGroup_list s hs
  · obtain ⟨k, hk, rfl⟩ := hs
    exact model_rvDivisible k hk

/-! #### the projection `rv` -/

theorem model_rvZeroEq : (M K) ⊨ Axioms.rvZeroEq := by
  simp only [Axioms.rvZeroEq]; prep
  rw [rvMap_zero]

theorem model_rvEqInfty : (M K) ⊨ Axioms.rvEqInfty := by
  simp only [Axioms.rvEqInfty]; rw [model_allSorted]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  rw [ha]
  simp only [mkVF]
  intro h
  have h' : rvMap a = none := Sum.inr.inj h
  rw [rvMap_eq_infty_iff] at h'
  rw [h']

theorem model_rvMulHom : (M K) ⊨ Axioms.rvMulHom := by
  simp only [Axioms.rvMulHom]; rw [model_allSorted]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  obtain ⟨b, hb⟩ := (h 1).1 rfl
  rw [ha, hb]
  simp only [mkVF]
  by_cases ha0 : a = 0
  · subst ha0
    rw [zero_mul, rvMap_zero, rvMul_infty_any']
  by_cases hb0 : b = 0
  · subst hb0
    rw [mul_zero, rvMap_zero, rvMul_infty_any]
  · rw [rvMap_of_ne (mul_ne_zero ha0 hb0), rvMap_of_ne ha0, rvMap_of_ne hb0, fromK_mul]

theorem model_rvSurj : (M K) ⊨ Axioms.rvSurj := by
  simp only [Axioms.rvSurj]; rw [model_allSorted]; intro xs h; prep
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  intro hne
  have ht0 : t ≠ none := fun hh => hne (by rw [ht, hh]; rfl)
  refine ⟨mkVF (toK t), ⟨toK t, rfl⟩, ?_⟩
  rw [show (1 : Fin 2) = Fin.last 1 from Fin.ext rfl, Fin.snoc_last,
    show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) from Fin.ext rfl, Fin.snoc_castSucc, ht]
  simp only [mkVF, rvMap]
  exact congrArg Sum.inr (fromK_toK t)

theorem model_rvUltrametric : (M K) ⊨ Axioms.rvUltrametric := by
  simp only [Axioms.rvUltrametric]; rw [model_allSorted]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  obtain ⟨b, hb⟩ := (h 1).1 rfl
  rw [ha, hb]
  simp only [mkVF]
  by_cases hab : a + b = 0
  · refine Or.inl ?_
    rw [hab, rvMap_zero]
    exact Or.inl rfl
  · by_cases ha0 : a = 0
    · refine Or.inr ?_
      subst ha0
      rw [zero_add]
      exact rvLeC_refl_mk (fun hh => hab (by rw [zero_add]; exact rvMap_eq_infty_iff.mp hh))
    · refine Or.inl ?_
      rw [rvMap_of_ne ha0]
      exact Or.inr ⟨Units.mk0 a ha0, by rw [cUnit, fromK_of_ne ha0]⟩

theorem model_rvAxioms : (M K) ⊨ Axioms.rvAxioms := by
  rw [Theory.model_iff]
  intro s hs
  simp only [Axioms.rvAxioms, Axioms.ofList, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact model_rvZeroEq
  · exact model_rvEqInfty
  · exact model_rvMulHom
  · exact model_rvSurj
  · exact model_rvUltrametric

end Finishing

/-! ### `M ⊨ ACVF`, `M ⊨ ACVF(0,0)`, and a model of `ACVF` -/

section Final

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

theorem model_ACVFpaper : (M K) ⊨ Axioms.ACVFpaper := by
  rw [Axioms.ACVFpaper, Theory.model_union_iff]
  refine ⟨?_, model_rvAxioms⟩
  rw [Theory.model_union_iff]
  refine ⟨?_, model_preorderRV⟩
  rw [Theory.model_union_iff]
  refine ⟨?_, model_kAlgClosed⟩
  rw [Theory.model_union_iff]
  refine ⟨?_, model_kField⟩
  rw [Theory.model_union_iff]
  refine ⟨?_, model_rvGroup⟩
  rw [Theory.model_union_iff]
  exact ⟨model_vfField, model_vfAlgClosed⟩

/-- **`M` is a model of the theory `ACVF` of Definition 2.2** -/
theorem model_ACVF : (M K) ⊨ Axioms.ACVF := by
  rw [Axioms.ACVF, Theory.model_union_iff]
  exact ⟨model_sortAxioms, model_ACVFpaper⟩

/-- `realize_tVFAdd` with an arbitrary assignment -/
theorem realize_tVFAdd_v {m : ℕ} (v : Empty ⊕ Fin m → M K) (A B : LRV.Tm m) (a b : K)
    (hA : Term.realize v A = mkVF a) (hB : Term.realize v B = mkVF b) :
    Term.realize v (LRV.tVFAdd A B) = mkVF (a + b) := by
  simp only [LRV.tVFAdd, Term.realize_func, funMap_def, fMap, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [hA, hB]
  simp [mkVF]

theorem realize_tVFNumeral {m : ℕ} (v : Empty ⊕ Fin m → M K) (n : ℕ) :
    Term.realize v (LRV.tVFNumeral n) = mkVF (n : K) := by
  induction n with
  | zero => simp [LRV.tVFNumeral, LRV.tVFZero, funMap_def, fMap, mkVF]
  | succ n ih =>
    have hone : Term.realize v LRV.tVFOne = mkVF (1 : K) := by
      simp [LRV.tVFOne, funMap_def, fMap, mkVF]
    rw [show LRV.tVFNumeral (n + 1) = LRV.tVFAdd (LRV.tVFNumeral n) LRV.tVFOne from rfl,
      realize_tVFAdd_v _ _ _ _ _ ih hone, Nat.cast_add, Nat.cast_one]

theorem model_charZeroVF (k : ℕ) : (M K) ⊨ Axioms.charZeroVF k := by
  simp only [Axioms.charZeroVF]; prep
  rw [realize_tVFNumeral]
  simp only [mkVF]
  intro h
  have h1 : ((k + 1 : ℕ) : K) = 0 := by simpa using h
  exact Nat.succ_ne_zero k (Nat.cast_eq_zero.mp h1)

theorem model_residueCharZero {p : ℕ} (hp : p.Prime) :
    (M K) ⊨ Axioms.residueCharZero p := by
  simp only [Axioms.residueCharZero, LRV.pGtOne]
  prep
  rw [realize_tVFNumeral]
  simp only [mkVF]
  intro h
  refine h.2 ?_
  have hp0 : ((p : ℕ) : K) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  rw [rvMap_of_ne hp0]
  exact Or.inr ⟨Units.mk0 ((p : ℕ) : K) hp0, by rw [cUnit, fromK_of_ne hp0]⟩

/-- **`M` is a model of `ACVF(0,0)`** (pure characteristic zero) -/
theorem model_ACVF00 : (M K) ⊨ Axioms.ACVF00 := by
  rw [Axioms.ACVF00, Theory.model_union_iff]
  refine ⟨?_, ?_⟩
  · rw [Theory.model_union_iff]
    exact ⟨model_ACVF, by
      rw [Theory.model_iff]
      intro s hs
      obtain ⟨k, rfl⟩ := hs
      exact model_charZeroVF k⟩
  · rw [Theory.model_iff]
    intro s hs
    obtain ⟨p, hp, rfl⟩ := hs
    exact model_residueCharZero hp

end Final

/-! ### The non-vacuity corollary: `ACVF` has a model -/

/-- **`ACVF` is consistent**: the trivial-valuation structure on `ℂ ⊕ RV₀` is a model. -/
theorem exists_model_ACVF : ∃ (M : Type) (_ : LRV.Structure M), M ⊨ Axioms.ACVF :=
  ⟨M ℂ, instStructure (K := ℂ), model_ACVF (K := ℂ)⟩

/-- **`ACVF` has a model**, so Theorems 2.3 and 2.8 of the paper are not vacuous. -/
theorem exists_model_ACVF00 : ∃ (M : Type) (_ : LRV.Structure M), M ⊨ Axioms.ACVF00 :=
  ⟨M ℂ, instStructure (K := ℂ), model_ACVF00 (K := ℂ)⟩

#print axioms exists_model_ACVF
#print axioms exists_model_ACVF00
#print axioms model_ACVF
#print axioms model_ACVF00
