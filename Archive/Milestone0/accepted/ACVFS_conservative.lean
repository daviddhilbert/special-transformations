module

/-
Milestone 0 for: Yimu Yin, "Special transformations in algebraically closed valued fields",
Annals of Pure and Applied Logic (2010), arXiv:1006.2467.

The paper's language `L_RV` (Definition 2.1), the theory `ACVF` (Definition 2.2), the
theory `ACVF_S(0,0)`, and the statements of quantifier elimination (Theorem 2.3) and
C-minimality (Theorem 2.8), encoded in Mathlib's one-sorted first-order model theory by
putting the sorts of `L_RV` on a single tagged carrier with unary sort predicates.

This file is self-contained: its only import is `Mathlib`.  Check it with

    lean Milestone0.lean

The last part of the file (Part 6) contains the two target theorems.  They are stated
with `sorry`, which is the only `sorry` in the file; all definitions are complete.
-/
public import Mathlib

@[expose] public section

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
* Part 6  quantifier elimination (Theorem 2.3) and C-minimality (Theorem 2.8), as
          targets.
* Part 7  a worked example showing that the encoding supports the paper's definable
          subsets of `VF^n × RV^m` and their coordinate projections (Notation 2.10).
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
def LRV : Language := ⟨Fn, Rel⟩

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
  (List.finRange k).foldr (fun i acc => pK (tv i.val i.isLt) ⊓ acc) ⊤

/-- the universal sentence `∀ x̄ ∈ s̄ ∩ K, φ` -/
def allSortedK {k : ℕ} (ss : Fin k → SortTag) (φ : Bf k) : LRV.Sentence :=
  BoundedFormula.alls ((sortedHyps ss ⊓ kHyps) ⟹ φ)

/-- the guarded existential formula `∃ x ∈ s ∩ K, φ`, with `x` the variable of index `k` -/
def exSortedK {k : ℕ} (s : SortTag) (φ : Bf (k + 1)) : Bf k :=
  BoundedFormula.ex (sortPred s (tv k (Nat.lt_succ_self k)) ⊓
    pK (tv k (Nat.lt_succ_self k)) ⊓ φ)

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
def sdKAdd : LRV.Sentence := allSorted ![.rv, .rv] (pK &0 ⟹ (pK &1 ⟹ pK (tKAdd &0 &1)))
/-- `K` is closed under unary `-` -/
def sdKNeg : LRV.Sentence := allSorted ![.rv] (pK &0 ⟹ pK (tKNeg &0))
/-- `K` is closed under `×`: the paper's `K = K^× ∪ {0}` is a field, so the product of two
elements of `K` is in `K` and not `∞`.  Without this the field axioms of `kField` (which are
guarded by `pK`) constrain only the products that happen to land in `K`. -/
def sdKMul : LRV.Sentence := allSorted ![.rv, .rv] (pK &0 ⟹ (pK &1 ⟹ pK (tRVMul &0 &1)))

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
def rvMulZeroK : LRV.Sentence := allSorted ![.rv] (pK &0 ⟹ pEq (tRVMul &0 tRVZero) tRVZero)
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
`rv(0) = ∞ = 0`.  With `RV^× = RV ∖ {0}` this says: `RV = rv(VF^×) ∪ {0}`, so there are no
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

/-- `b` is a **closed ball** in the sense of Definition 2.6: there are `a ∈ VF` and a
radius `γ = vrv(t)` — i.e. an `RV`-element `t ≠ 0`, since the preorder is only defined on
`RV = RV ∖ {0}` — such that `b = {x ∈ VF : t ≤ rv(x - a)}`.  With `t = ∞` this is the
degenerate ball `{a}`. -/
def IsClosedBall (b : Set M) : Prop :=
  ∃ a t : M, iVF a ∧ iRV t ∧ t ≠ iRVZero ∧
    b = {x | iVF x ∧ iLe t (iRv (iVFAdd x (iVFNeg a)))}

/-- `b` is an **open ball**: `{x ∈ VF : t < rv(x - a)}` for a radius `t ≠ 0`, together
with the paper's convention `O(a, ∞) = C(a, ∞) = {a}`. -/
def IsOpenBall (b : Set M) : Prop :=
  (∃ a t : M, iVF a ∧ iRV t ∧ t ≠ iRVZero ∧
      b = {x | iVF x ∧ iLe t (iRv (iVFAdd x (iVFNeg a))) ∧
        ¬ iLe (iRv (iVFAdd x (iVFNeg a))) t}) ∨
    ∃ a : M, iVF a ∧ b = {x | iVF x ∧ x = a}

/-- **A ball** in the sense of Definition 2.6: `VF` itself (the ball of radius `-∞`), a
closed ball, or an open ball. -/
def IsBall (b : Set M) : Prop :=
  b = {x | iVF x} ∨ IsClosedBall b ∨ IsOpenBall b

/-- the Boolean algebra generated by a family of subsets -/
inductive IsBoolComb (B : Set (Set M)) : Set M → Prop
  /-- a member of the family -/
  | basic {b : Set M} : b ∈ B → IsBoolComb B b
  /-- the whole carrier -/
  | univ : IsBoolComb B Set.univ
  /-- complements -/
  | compl {s : Set M} : IsBoolComb B s → IsBoolComb B sᶜ
  /-- finite unions -/
  | union {s t : Set M} : IsBoolComb B s → IsBoolComb B t → IsBoolComb B (s ∪ t)

/-- **C-minimality** (Definition 2.7): every parametrically definable subset of the
`VF` sort is a Boolean combination of balls. -/
def IsCMinimal (M : Type*) [LRV.Structure M] : Prop :=
  ∀ (A : Set M) (s : Set M), A.Definable₁ LRV s → IsBoolComb {b | IsBall b} s

/- The two target theorems of `Milestone0/Encoding.lean` are NOT restated or proved here: this
file is about the substructure theory `ACVF_S(0,0)` of Part 5.  This file has no `sorry`. -/

/-! ## Part 7. Definable subsets of `VF^n × RV^m`

The paper's Notation 2.10 indexes the coordinates of a subset of `VF^n × RV^m` by
`I_n ⊎ I_m`.  In the encoding that disjoint union is the type `Fin n ⊕ Fin m`, which is
exactly Mathlib's index type for `Definable`-sets of tuples: no translation is needed. -/

namespace Downstream

variable {M : Type*} [LRV.Structure M]

/-- The set of tuples of `VF^n × RV^m` inside the carrier `M`, indexed by `Fin n ⊕ Fin m`
as in Notation 2.10. -/
def sortedTuples (n m : ℕ) : Set (Fin n ⊕ Fin m → M) :=
  {p | (∀ i, iVF (p (Sum.inl i))) ∧ ∀ j, iRV (p (Sum.inr j))}

/-- A subset of `VF^n × RV^m` is definable over `A` when its membership is given by an
`L_RV`-formula with parameters in `A`. -/
def MixedDefinable (A : Set M) (n m : ℕ) (s : Set (Fin n ⊕ Fin m → M)) : Prop :=
  A.Definable LRV s

/-- The `VF`-dimension `n` of the ambient product `VF^n × RV^m` of a mixed definable set
(the paper's `dimVF`; see Section 4 of the paper). -/
def dimVF {n m : ℕ} (_s : Set (Fin n ⊕ Fin m → M)) : ℕ := n

/-- The `RV`-dimension `m` of the ambient product `VF^n × RV^m` of a mixed definable set
(the paper's `dimRV`). -/
def dimRV {n m : ℕ} (_s : Set (Fin n ⊕ Fin m → M)) : ℕ := m

def projRV (n m : ℕ) (s : Set (Fin n ⊕ Fin m → M)) : Set (Fin m → M) :=
  {t | ∃ q : Fin n → M, (fun k => match k with | Sum.inl i => q i | Sum.inr j => t j) ∈ s}

/-- the fiber of `s ⊆ VF^n × RV^m` over the `RV`-coordinates `t` (Notation 2.10) -/
def fib (n m : ℕ) (s : Set (Fin n ⊕ Fin m → M)) (t : Fin m → M) : Set (Fin n → M) :=
  {q | (fun k => match k with | Sum.inl i => q i | Sum.inr j => t j) ∈ s}

/-- the `rv`-polydisc of a tuple of `VF^n × RV^m`: `rv⁻¹(rv ā) × {t̄}` (Definition 2.6) -/
def rvPolydisc {n m : ℕ} (p : Fin n ⊕ Fin m → M) : Set (Fin n ⊕ Fin m → M) :=
  {q | (∀ i, iVF (q (Sum.inl i)) ∧ iRv (q (Sum.inl i)) = iRv (p (Sum.inl i))) ∧
    ∀ j, q (Sum.inr j) = p (Sum.inr j)}

/-- the `RV`-hull of a set: the union of the `rv`-polydiscs that meet it (Section 5) -/
def rvHull {n m : ℕ} (s : Set (Fin n ⊕ Fin m → M)) : Set (Fin n ⊕ Fin m → M) :=
  {q | ∃ p ∈ s, q ∈ rvPolydisc p}

/-- an `RV`-pullback: a set equal to its `RV`-hull (Section 5) -/
def IsRVPullback {n m : ℕ} (s : Set (Fin n ⊕ Fin m → M)) : Prop := rvHull s = s

end Downstream

end Milestone0
end SpecialTransformations

/- === M4-D9-START === -/

namespace SpecialTransformations.Milestone0.M4
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.Axioms
open SpecialTransformations.Milestone0.SubstructureTheory

variable {M : Type*} [LRV.Structure M]

/-! ## `ACVF_S(0,0)`: the atomic diagram is a conservative extension

`SubstructureTheory.ACVF_S S` is `ACVF(0,0)` together with the atomic diagram of a substructure
`S`.  The paper's Convention 2.5 works in `ACVF_S(0,0)` throughout, so it matters that adding the
diagram neither destroys satisfiability nor adds `L_RV`-consequences.  Both are proved below. -/

/-- The encoding's `IsAtomic` really is "equality or a relation symbol": for a sentence of any
one-sorted language it holds exactly of the atomic formulas.  (Checked because
`atomicDiagram`'s content depends on this predicate.) -/
theorem isAtomic_iff {L : FirstOrder.Language} {α : Type*} (φ : L.BoundedFormula α 0) :
    SubstructureTheory.IsAtomic φ ↔
      (∃ t u : L.Term (α ⊕ Fin 0), φ = t =' u) ∨
      (∃ (n : ℕ) (R : L.Relations n) (ts : Fin n → L.Term (α ⊕ Fin 0)),
        φ = BoundedFormula.rel R ts) := by
  cases φ with
  | falsum =>
      refine iff_of_false (by simp [SubstructureTheory.IsAtomic]) ?_
      rintro (⟨t, u, h⟩ | ⟨n, R, ts, h⟩) <;> cases h
  | equal t u =>
      refine iff_of_true (by simp [SubstructureTheory.IsAtomic]) ?_
      exact Or.inl ⟨t, u, rfl⟩
  | rel R ts =>
      refine iff_of_true (by simp [SubstructureTheory.IsAtomic]) ?_
      exact Or.inr ⟨_, R, ts, rfl⟩
  | imp f g =>
      refine iff_of_false (by simp [SubstructureTheory.IsAtomic]) ?_
      rintro (⟨t, u, h⟩ | ⟨n, R, ts, h⟩) <;> cases h
  | all f =>
      refine iff_of_false (by simp [SubstructureTheory.IsAtomic]) ?_
      rintro (⟨t, u, h⟩ | ⟨n, R, ts, h⟩) <;> cases h

/-- The structure `M` realizes its own atomic diagram: every atomic sentence with parameters in
`S` that holds in `M` is in the diagram, and every negated atomic sentence whose body fails
likewise. -/
theorem realize_atomicDiagram (S : LRV.Substructure M) :
    M ⊨ SubstructureTheory.atomicDiagram S := by
  refine ⟨fun φ hφ => ?_⟩
  rcases hφ with ⟨-, h⟩ | ⟨ψ, -, rfl, h⟩
  · exact h
  · simpa using h

/-- Every true atomic `L_RV[[S]]`-sentence lies in the diagram. -/
theorem mem_atomicDiagram {S : LRV.Substructure M} {φ : LRV[[(S : Set M)]].Sentence}
    (hAt : SubstructureTheory.IsAtomic φ) (h : M ⊨ φ) :
    φ ∈ SubstructureTheory.atomicDiagram S :=
  Or.inl ⟨hAt, h⟩

/-- Every model of `ACVF_S(0,0)` realizes the diagram. -/
theorem model_diagram_of_model_ACVF_S (S : LRV.Substructure M)
    (h : M ⊨ SubstructureTheory.ACVF_S S) : M ⊨ SubstructureTheory.atomicDiagram S :=
  Theory.Model.mono h Set.subset_union_right

/-- **The diagram is never the source of a contradiction**: every model of `ACVF(0,0)`, expanded
by constants for the elements of any substructure `S`, is a model of `ACVF_S(0,0)`. -/
theorem model_ACVF_S (h : M ⊨ Axioms.ACVF00) (S : LRV.Substructure M) :
    M ⊨ SubstructureTheory.ACVF_S S := by
  have h1 : M ⊨ (LRV.lhomWithConstants (S : Set M)).onTheory Axioms.ACVF00 :=
    (LHom.onTheory_model (LRV.lhomWithConstants (S : Set M)) (T := Axioms.ACVF00)).mpr h
  exact Theory.model_union_iff.mpr ⟨h1, realize_atomicDiagram S⟩

/-- **Conservativity, converse direction**: a model of `ACVF_S(0,0)` has an `L_RV`-reduct which
is a model of `ACVF(0,0)`.  So the diagram constrains only the new constants, never `L_RV`. -/
theorem model_ACVF00_of_model_ACVF_S (S : LRV.Substructure M)
    (h : M ⊨ SubstructureTheory.ACVF_S S) : M ⊨ Axioms.ACVF00 := by
  have h1 : M ⊨ (LRV.lhomWithConstants (S : Set M)).onTheory Axioms.ACVF00 :=
    Theory.Model.mono h Set.subset_union_left
  exact (LHom.onTheory_model (LRV.lhomWithConstants (S : Set M)) (T := Axioms.ACVF00)).mp h1

/-! ### Convention 2.5 of the paper: parameters versus named constants

Convention 2.5 defines "definable" as *0-definable in `ACVF_S(0,0)`*, i.e. parameters are
replaced by the constants of the expansion.  The encoding states definability with parameters
(`Downstream.MixedDefinable A n m s := A.Definable LRV s`); below is the machine-checked
identification of the two readings, so that the paper's convention can be used with the
encoding's targets. -/

/-- **Convention 2.5**: definability with parameters in `A` in `L_RV` is the same as
0-definability in the constant expansion `L_RV[[A]]`. -/
theorem definable_iff_definable_expansion (A : Set M) {ι : Type*} (s : Set (ι → M)) :
    A.Definable LRV s ↔ (∅ : Set M).Definable (LRV[[A]]) s :=
  Set.definable_iff_empty_definable_with_params

/-- The same for the encoding's mixed definable sets `VF^n × RV^m` (Notation 2.10). -/
theorem mixedDefinable_iff_expansion (A : Set M) {n m : ℕ}
    (s : Set (Fin n ⊕ Fin m → M)) :
    Downstream.MixedDefinable A n m s ↔ (∅ : Set M).Definable (LRV[[A]]) s :=
  Set.definable_iff_empty_definable_with_params

/-- **Theorem 2.8's statement in the paper's own form**: `M` is `C`-minimal iff every set
definable with parameters is 0-definable in the corresponding constant expansion and is a Boolean
combination of balls.  (The two readings of "definable" are exchanged by
`definable_iff_definable_expansion`.) -/
theorem isCMinimal_iff_expansion :
    IsCMinimal M ↔ ∀ (A : Set M) (s : Set M),
      (∅ : Set M).Definable (LRV[[A]]) {x : Fin 1 → M | x 0 ∈ s} → IsBoolComb {b | IsBall b} s := by
  constructor
  · intro h A s hs
    exact h A s ((definable_iff_definable_expansion A _).mpr hs)
  · intro h A s hs
    exact h A s ((definable_iff_definable_expansion A _).mp hs)

/-- Sentences of `L_RV` keep their truth value under the constant expansion. -/
theorem realize_onSentence (S : LRV.Substructure M) (φ : LRV.Sentence) :
    M ⊨ ((LRV.lhomWithConstants (S : Set M)).onSentence φ) ↔ M ⊨ φ :=
  FirstOrder.Language.LHom.realize_onSentence (L := LRV) (L' := LRV[[(S : Set M)]])
    (M := M) (LRV.lhomWithConstants (S : Set M)) φ

/-- **Conservativity at the level of theories**: `ACVF_S(0,0)` contains the image of
`ACVF(0,0)`, and its extra sentences are exactly the diagram, which only speaks about the new
constants.  Nothing is added to `L_RV`. -/
theorem onTheory_subset_ACVF_S (S : LRV.Substructure M) :
    (LRV.lhomWithConstants (S : Set M)).onTheory Axioms.ACVF00 ⊆
      SubstructureTheory.ACVF_S S :=
  Set.subset_union_left

/-- `ACVF_S(0,0)` adds no consistency strength: a model of it has an `L_RV`-reduct which is a
model of `ACVF(0,0)`.  (`ACVF(0,0)` and `ACVF_S(0,0)` are theories of `LRV`, a language in
`Type 0`, so the satisfiability statement is made for carriers in `Type`.) -/
theorem isSatisfiable_of_model_ACVF_S (X : Type) [LRV.Structure X] [Nonempty X]
    (S : LRV.Substructure X) (h : X ⊨ SubstructureTheory.ACVF_S S) :
    Axioms.ACVF00.IsSatisfiable :=
  ⟨(model_ACVF00_of_model_ACVF_S S h).bundled⟩

/-- Conversely every model of `ACVF(0,0)` expands to a model of `ACVF_S(0,0)` for the trivial
substructure.  So `ACVF(0,0)` and `ACVF_S(0,0)` are equiconsistent, and the paper's
Convention 2.5 setting is non-vacuous exactly when `ACVF(0,0)` is. -/
theorem isSatisfiable_ACVF_S_bot (h : Axioms.ACVF00.IsSatisfiable) :
    (SubstructureTheory.ACVF_S (⊥ : LRV.Substructure h.some)).IsSatisfiable :=
  ⟨(model_ACVF_S h.some.is_model (⊥ : LRV.Substructure h.some)).bundled⟩

end SpecialTransformations.Milestone0.M4

namespace SpecialTransformations.Milestone0.M4
#print axioms definable_iff_definable_expansion
#print axioms mixedDefinable_iff_expansion
#print axioms isCMinimal_iff_expansion
#print axioms isAtomic_iff
#print axioms realize_atomicDiagram
#print axioms model_ACVF_S
#print axioms model_ACVF00_of_model_ACVF_S
#print axioms realize_onSentence
#print axioms onTheory_subset_ACVF_S
#print axioms isSatisfiable_of_model_ACVF_S
#print axioms isSatisfiable_ACVF_S_bot
end SpecialTransformations.Milestone0.M4
