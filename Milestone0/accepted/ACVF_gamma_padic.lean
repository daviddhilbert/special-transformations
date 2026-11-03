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
  /-- the constant `0` of the `RV` sort (an element of `K`) -/
  | rvZero : Fn 0
  /-- the constant `∞` of the `RV` sort -/
  | rvInfty : Fn 0
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
/-- `∞` of the `RV` sort -/
def tRVInfty : Tm n := Term.func Fn.rvInfty fun i => i.elim0
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
/-- the paper's `K = RV-sort ∖ {∞}` -/
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
/-- `∞` lies in the `RV` sort -/
def sdRVInfty : LRV.Sentence := pRVsort tRVInfty
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
/-- `rv : VF^× → RV^×` is surjective -/
def rvSurj : LRV.Sentence :=
  allSorted ![.rv] (pUnits &0 ⟹ exSorted .vf (pEq (tRv &1) &0))
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

end Milestone0
end SpecialTransformations
namespace SpecialTransformations
namespace RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

section Basics

variable (v : Valuation K Γ₀)

/-- `RV× = Kˣ / (1 + M)`, the multiplicative RV sort. -/
abbrev RVUnit : Type _ := Kˣ ⧸ v.valuationSubring.principalUnitGroup

/-- The RV sort with the point at infinity: `RV = RV× ∪ {∞}`.  `none` is `∞`. -/
abbrev RV : Type _ := Option (RVUnit v)

/-- `RV0 = RV ∪ {0}`.  The outer `none` is the added `0` (zero of the residue field). -/
abbrev RV0 : Type _ := Option (RV v)

/-- The quotient map `rv : K → RV`, with `rv 0 = ∞`. -/
noncomputable def rv (x : K) : RV v := by
  classical
  exact if h : x = 0 then none else some (QuotientGroup.mk' _ (Units.mk0 x h))

/-- The paper's `∞`, i.e. `rv 0`. -/
abbrev rvInfty : RV v := none

/-- The paper's `1`, i.e. `rv 1`, the identity of `RV^×`. -/
noncomputable abbrev rvOne : RV v := rv v 1

variable {v}

@[simp] theorem rv_zero : rv v 0 = (none : RV v) := by
  rw [rv]; exact dif_pos rfl

theorem rv_of_ne {x : K} (h : x ≠ 0) :
    rv v x = some (QuotientGroup.mk' _ (Units.mk0 x h)) := by
  rw [rv]; exact dif_neg h

theorem rv_eq_none_iff {x : K} : rv v x = none ↔ x = 0 := by
  unfold rv
  split_ifs with h
  · simp [h]
  · simp [h]

/-- `rv` is onto `RV ∖ {∞}`: the paper's "`rv : VF^× → RV^×` is surjective". -/
theorem rv_surjective {t : RV v} (h : t ≠ none) : ∃ x : K, x ≠ 0 ∧ rv v x = t := by
  cases t with
  | none => exact absurd rfl h
  | some q =>
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (v.valuationSubring.principalUnitGroup) q
    refine ⟨(u : K), Units.ne_zero u, ?_⟩
    rw [rv_of_ne (Units.ne_zero u)]
    congr 2
    exact Units.ext rfl

/-- Multiplication of the `RV`-sort: the group law on `RV^×`, with `∞` absorbing
(axiom 2 of Definition 2.2: `t × ∞ = ∞`).  On `RV` (i.e. away from the residue-field
zero) this is determined by the axioms. -/
def rvMul : RV v → RV v → RV v
  | none, _ => none
  | some _, none => none
  | some a, some b => some (a * b)

@[simp] theorem rvMul_infty (t : RV v) : rvMul t none = none := by cases t <;> rfl

@[simp] theorem rvMul_infty' (t : RV v) : rvMul none t = none := by cases t <;> rfl

@[simp] theorem rvMul_some_some (a b : RVUnit v) : rvMul (some a) (some b) = some (a * b) :=
  rfl

/-- The paper's `1` in the `RV`-sort is the identity of `RV^× = Kˣ/(1+M)`. -/
theorem rvOne_eq : rvOne v = some (1 : RVUnit v) := by
  rw [rvOne, rv_of_ne one_ne_zero]
  congr 1
  rw [show Units.mk0 (1 : K) one_ne_zero = (1 : Kˣ) from Units.ext rfl, map_one]

theorem rvMul_comm (t s : RV v) : rvMul t s = rvMul s t := by
  cases t with
  | none => cases s <;> simp
  | some a =>
    cases s with
    | none => simp
    | some b =>
      induction a using Quotient.inductionOn with
      | _ x =>
        induction b using Quotient.inductionOn with
        | _ y =>
          simp only [rvMul_some_some, ← QuotientGroup.mk_mul, mul_comm]

theorem rvMul_assoc (t s r : RV v) : rvMul (rvMul t s) r = rvMul t (rvMul s r) := by
  cases t with
  | none => simp
  | some a =>
    cases s with
    | none => simp
    | some b =>
      cases r with
      | none => simp
      | some c =>
        induction a using Quotient.inductionOn with
        | _ x =>
          induction b using Quotient.inductionOn with
          | _ y =>
            induction c using Quotient.inductionOn with
            | _ z =>
              simp only [rvMul_some_some, ← QuotientGroup.mk_mul, mul_assoc]

/-- `1` is the identity of `RV^×` and `∞ × 1 = ∞`. -/
theorem rvMul_one (t : RV v) : rvMul t (rvOne v) = t := by
  cases t with
  | none => simp
  | some a =>
    rw [rvOne_eq, rvMul_some_some]
    exact congrArg some (mul_one a)

/-- `rv` is multiplicative (axiom 6 of Definition 2.2). -/
theorem rv_mul (x y : K) : rv v (x * y) = rvMul (rv v x) (rv v y) := by
  by_cases hx : x = 0
  · subst hx; simp [rv_zero]
  by_cases hy : y = 0
  · subst hy; simp [rv_zero]
  rw [rv_of_ne hx, rv_of_ne hy, rv_of_ne (mul_ne_zero hx hy), rvMul_some_some,
    show Units.mk0 (x * y) (mul_ne_zero hx hy) = Units.mk0 x hx * Units.mk0 y hy from
      Units.ext rfl,
    map_mul]

/-- The fibre of `rv` over `1` is `1 + M`, i.e. the principal units. -/
theorem rv_eq_one_iff (u : Kˣ) :
    rv v (u : K) = rvOne v ↔ u ∈ v.valuationSubring.principalUnitGroup := by
  rw [rv_of_ne (Units.ne_zero u), rvOne, rv_of_ne one_ne_zero,
    show Units.mk0 ((u : K)) (Units.ne_zero u) = u from Units.ext rfl,
    show Units.mk0 (1 : K) one_ne_zero = (1 : Kˣ) from Units.ext rfl,
    map_one, Option.some_inj, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

end Basics

section Vrv

variable (v : Valuation K Γ₀)

/-- The valuation, viewed as a monoid homomorphism on the units of `K`. -/
noncomputable def vUnits : Kˣ →* Γ₀ˣ where
  toFun u := Units.mk0 (v (u : K)) (by
    rw [Valuation.ne_zero_iff]
    exact Units.ne_zero u)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [Valuation.map_mul]

@[simp] theorem vUnits_apply (u : Kˣ) : ((vUnits v u : Γ₀ˣ) : Γ₀) = v (u : K) := rfl

theorem vUnits_ker : v.valuationSubring.principalUnitGroup ≤ (vUnits v).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, Units.ext_iff, vUnits_apply]
  exact (Valuation.mem_unitGroup_iff K v x).1 (v.valuationSubring.principal_units_le_units hx)

/-- The map `RV^× → Γ` induced by the valuation, i.e. the paper's `vrv` restricted to
the group part of the `RV`-sort.  Well defined because `v` is trivial on `1 + M`. -/
noncomputable def vrvUnit : RVUnit v →* Γ₀ˣ :=
  QuotientGroup.lift _ (vUnits v) (vUnits_ker v)

@[simp] theorem vrvUnit_mk (u : Kˣ) :
    vrvUnit v (QuotientGroup.mk' _ u) = vUnits v u := rfl

/-- The paper's `vrv : RV → Γ ∪ {∞}`: the map induced by the valuation on `RV^×`,
extended by `vrv ∞ = 0`.  (Mathlib's `Γ₀ = WithZero Γ` is ordered so that `0` is the
bottom; the paper's order on `Γ ∪ {∞}` is the reverse, cf. `le_iff`.) -/
noncomputable def vrv : RV v → Γ₀
  | none => 0
  | some q => (vrvUnit v q : Γ₀)

@[simp] theorem vrv_none : vrv v (none : RV v) = 0 := rfl

@[simp] theorem vrv_some (q : RVUnit v) : vrv v (some q) = (vrvUnit v q : Γ₀) := rfl

theorem vrv_mk (u : Kˣ) : vrv v (some (QuotientGroup.mk' _ u)) = v (u : K) := rfl

/-- `vv = vrv ∘ rv` (axiom 6): the projection commutes with the valuation. -/
theorem vrv_rv (x : K) : vrv v (rv v x) = v x := by
  by_cases h : x = 0
  · subst h; simp [rv_zero]
  · rw [rv_of_ne h, vrv_mk]
    rfl

/-- `vrv` is multiplicative. -/
theorem vrv_mul (t s : RV v) : vrv v (rvMul t s) = vrv v t * vrv v s := by
  cases t with
  | none => simp
  | some a =>
    cases s with
    | none => simp
    | some b => simp

/-- `vrv` and `v` have the same range: `vrv` maps `RV` *onto* the value group. -/
theorem vrv_range (γ : Γ₀) :
    (∃ t : RV v, vrv v t = γ) ↔ (∃ x : K, v x = γ) := by
  constructor
  · rintro ⟨t, rfl⟩
    cases t with
    | none => exact ⟨0, by simp⟩
    | some q =>
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (v.valuationSubring.principalUnitGroup) q
      exact ⟨(u : K), by rw [← vrv_mk]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨rv v x, vrv_rv v x⟩

/-- The kernel of `vrv` is the predicate `K^×` of Definition 2.1: the equivalence class
of `1`, i.e. the image of the units of the valuation ring
(`(𝒪 ∖ 𝔪)/(1+𝔪) ≅ k^×`). -/
theorem vrv_kernel (t : RV v) :
    vrv v t = 1 ↔ ∃ u : v.valuationSubring.unitGroup,
      some (QuotientGroup.mk' _ (u : Kˣ)) = t := by
  constructor
  · intro ht
    cases t with
    | none => simp at ht
    | some q =>
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (v.valuationSubring.principalUnitGroup) q
      refine ⟨⟨u, ?_⟩, rfl⟩
      have h := ht
      rw [vrv_mk] at h
      exact (Valuation.mem_unitGroup_iff K v u).2 h
  · rintro ⟨u, rfl⟩
    rw [vrv_mk]
    exact (Valuation.mem_unitGroup_iff K v (u : Kˣ)).1 u.2

end Vrv

section Order

variable (v : Valuation K Γ₀)

/-- The paper's preorder on `RV`: `t ≤ s` iff `vrv t ≥ vrv s` in the value monoid
ordered so that `𝒪 = {x : v x ≤ 1}`.  Then `∞` is the top element and the
equivalence class of `1` is `K^×` (axiom 4 of Definition 2.2). -/
def rvLe (t s : RV v) : Prop := vrv v s ≤ vrv v t

instance : Preorder (RV v) where
  le := rvLe v
  lt t s := rvLe v t s ∧ ¬ rvLe v s t
  le_refl := fun _ => le_rfl
  le_trans _ _ _ h₁ h₂ := le_trans h₂ h₁
  lt_iff_le_not_ge _ _ := Iff.rfl

theorem le_iff {t s : RV v} : t ≤ s ↔ vrv v s ≤ vrv v t := Iff.rfl

theorem lt_iff {t s : RV v} : t < s ↔ vrv v s < vrv v t := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge]
  exact Iff.rfl

/-- `∞` is the top element. -/
theorem le_infty (t : RV v) : t ≤ (none : RV v) := by
  rw [le_iff]; simp

/-- The equivalence class of `1` is `K^×` (axiom 4). -/
theorem le_class_of_one_iff {t : RV v} : (rvOne v ≤ t ∧ t ≤ rvOne v) ↔ vrv v t = 1 := by
  have h1 : vrv v (rvOne v) = 1 := by rw [rvOne, vrv_rv, Valuation.map_one]
  rw [le_iff, le_iff, h1]
  exact ⟨fun ⟨h1, h2⟩ => le_antisymm h1 h2, fun h => ⟨le_of_eq h, le_of_eq h.symm⟩⟩

/-- Axiom 6, first half: `𝒪 = rv⁻¹(RV^{≥1})` where `RV^{≥1} = {x : 1 ≤ x}`. -/
theorem valuationSubring_eq (x : K) :
    x ∈ v.valuationSubring ↔ rvOne v ≤ rv v x := by
  rw [le_iff, vrv_rv, rvOne, vrv_rv, Valuation.map_one, Valuation.mem_valuationSubring_iff]

/-- Axiom 6, second half: `𝔪 = rv⁻¹(RV^{>1})` where `RV^{>1} = {x : 1 < x}`. -/
theorem maximalIdeal_eq (x : K) : v x < 1 ↔ rvOne v < rv v x := by
  rw [lt_iff, vrv_rv, rvOne, vrv_rv, Valuation.map_one]

/-- `RV^×` is divisible when `K` is algebraically closed (axiom 2 of Definition 2.2). -/
theorem rvUnit_divisible [IsAlgClosed K] (n : ℕ) (hn : n ≠ 0) (t : RVUnit v) :
    ∃ s : RVUnit v, s ^ n = t := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (v.valuationSubring.principalUnitGroup) t
  have hu : (u : K) ≠ 0 := Units.ne_zero u
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (u : K) (n := n) (Nat.pos_of_ne_zero hn)
  have hw0 : w ≠ 0 := by rintro rfl; rw [zero_pow hn] at hw; exact hu hw.symm
  have hpow : (Units.mk0 w hw0 : Kˣ) ^ n = u := by
    ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, hw]
  refine ⟨QuotientGroup.mk' _ (Units.mk0 w hw0), ?_⟩
  rw [← map_pow, hpow]

end Order

section Extra
variable (v : Valuation K Γ₀)
/-- An admissible reading of the paper's multiplication on `RV_0 = RV ∪ {0}`: the group law
on `RV^×`, `∞` absorbing, `0` absorbing on `K`.  (The axioms do not determine `t × 0` for
`t ∈ RV^× ∖ K^×`, so this is one faithful choice.) -/
def rv0Mul : RV0 v → RV0 v → RV0 v
  | some none, _ => some none
  | _, some none => some none
  | none, _ => none
  | some (some _), none => none
  | some (some a), some (some b) => some (some (a * b))

/-- The paper's `≤` on the whole sort `RV_0`: the residue-field zero is the bottom, `∞` the
top, and on `RV` it is the order induced by `vrv` (`le_iff`). -/
def le0 : RV0 v → RV0 v → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => rvLe v a b

/-- `K^×` as a subset of the whole sort `RV_0`: the class of `1`, i.e. the residue field's
units (axiom 4). -/
def Kx0 : Set (RV0 v) := {t | ∃ q : RVUnit v, t = some (some q) ∧ vrv v (some q) = 1}

@[simp] theorem rv0Mul_infty (t : RV0 v) : rv0Mul v t (some none) = some none := by
  match t with
  | none => rfl
  | some t => cases t <;> rfl

theorem rv0Mul_some_rv (x y : K) :
    rv0Mul v (some (rv v x)) (some (rv v y)) = some (rv v (x * y)) := by
  rw [rv_mul x y]
  match hx : rv v x, hy : rv v y with
  | none, _ => rfl
  | some _, none => rfl
  | some a, some b => rfl

/-- `b : RV` is not `∞`. -/
theorem rv_shape {b : RV v} (hb : b ≠ none) : ∃ c : RVUnit v, b = some c := by
  match b, hb with
  | none, h => exact absurd rfl h
  | some c, _ => exact ⟨c, rfl⟩

/-- The group law of `RV^×` at the level of `RVUnit`. -/
theorem rvUnit_mul_comm (a b : RVUnit v) : a * b = b * a := mul_comm a b

theorem rvUnit_mul_assoc (a b c : RVUnit v) : a * b * c = a * (b * c) := mul_assoc a b c

theorem rvUnit_mul_one (a : RVUnit v) : a * 1 = a := mul_one a

theorem rvUnit_inv (a : RVUnit v) : ∃ c : RVUnit v, a * c = 1 := ⟨a⁻¹, mul_inv_cancel a⟩

theorem rv0Mul_some_some (a b : RVUnit v) :
    rv0Mul v (some (some a)) (some (some b)) = some (some (a * b)) := rfl

theorem le0_refl (t : RV0 v) : le0 v t t := by
  match t with
  | none => trivial
  | some none => exact le_infty v none
  | some (some q) => exact le_rfl

theorem le0_total (t s : RV0 v) : le0 v t s ∨ le0 v s t := by
  match t, s with
  | none, _ => exact Or.inl trivial
  | some _, none => exact Or.inr trivial
  | some a, some b =>
    rcases le_total (vrv v a) (vrv v b) with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem le0_trans {t s r : RV0 v} (h1 : le0 v t s) (h2 : le0 v s r) : le0 v t r := by
  match t, s, r with
  | none, _, _ => trivial
  | some _, none, _ => exact absurd h1 (by simp [le0])
  | some _, some _, none => exact absurd h2 (by simp [le0])
  | some a, some b, some c =>
    exact le_trans (show vrv v c ≤ vrv v b from h2) (show vrv v b ≤ vrv v a from h1)

theorem le0_infty (t : RV0 v) : le0 v t (some none) := by
  match t with
  | none => trivial
  | some none => exact le_infty v none
  | some (some q) => exact le_infty v (some q)
end Extra
end RVM
end SpecialTransformations

namespace SpecialTransformations
namespace Milestone0
namespace IModel

open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-- The carrier of the intended `L_RV`-structure of the valued field `(K, v)`:
`M = VF ⊕ RV₀` with `VF = K` and `RV₀ = Option (Option (Kˣ ⧸ (1+𝔪)))`. -/
abbrev C : Type _ := K ⊕ RVM.RV0 v

/-- the `VF`-tag -/
def mkVF (x : K) : C v := Sum.inl x
/-- the `RV`-tag -/
def mkRV (t : RVM.RV0 v) : C v := Sum.inr t

/-- the paper's `0` (the residue field's zero) -/
def cKZero : C v := Sum.inr none
/-- the paper's `∞ = rv 0` -/
def cInfty : C v := Sum.inr (some none)
/-- an element of `RV^×`, i.e. the class of a unit -/
def cUnit (q : RVM.RVUnit v) : C v := Sum.inr (some (some q))
/-- the paper's `1` in the `RV` sort -/
noncomputable def cRVOne : C v := Sum.inr (some (RVM.rvOne v))

/-- The interpretation of the twelve function symbols.  The junk value for the partial
symbols is `∞` (`Milestone0/Partiality.lean`) off the intended sort; `kAdd`, `kNeg` (the
residue field's `+`/`-`) take the junk value `0` here, so that they stay inside
`K = RV₀ ∖ {∞}` on the whole of `K` (the sort-closure sentences `sdKAdd`, `sdKNeg`).  The
field axioms for `K` itself (`kField`, `kAlgClosed`) are proved only in the trivially
valued case, where `K` *is* the residue field. -/
noncomputable def fMap : {n : ℕ} → Fn n → (Fin n → C v) → C v
  | _, .vfZero, _ => mkVF v 0
  | _, .vfOne, _ => mkVF v 1
  | _, .vfAdd, xs => match xs 0, xs 1 with
      | Sum.inl a, Sum.inl b => mkVF v (a + b)
      | _, _ => cInfty v
  | _, .vfNeg, xs => match xs 0 with
      | Sum.inl a => mkVF v (-a)
      | _ => cInfty v
  | _, .vfMul, xs => match xs 0, xs 1 with
      | Sum.inl a, Sum.inl b => mkVF v (a * b)
      | _, _ => cInfty v
  | _, .rvOne, _ => cRVOne v
  | _, .rvZero, _ => cKZero v
  | _, .rvInfty, _ => cInfty v
  | _, .rvMul, xs => match xs 0, xs 1 with
      | Sum.inr t, Sum.inr s => mkRV v (RVM.rv0Mul v t s)
      | _, _ => cInfty v
  | _, .kAdd, _ => cKZero v
  | _, .kNeg, _ => cKZero v
  | _, .rvMap, xs => match xs 0 with
      | Sum.inl a => mkRV v (some (RVM.rv v a))
      | _ => cInfty v

/-- The interpretation of the four relation symbols. -/
noncomputable def rMap : {n : ℕ} → Rel n → (Fin n → C v) → Prop
  | _, .memVF, xs => ∃ x : K, xs 0 = mkVF v x
  | _, .memRV, xs => ∃ t : RVM.RV0 v, xs 0 = mkRV v t
  | _, .memUnits, xs => ∃ q : RVM.RVUnit v, xs 0 = cUnit v q ∧ RVM.vrv v (some q) = 1
  | _, .rvLe, xs => ∃ t s : RVM.RV0 v, xs 0 = mkRV v t ∧ xs 1 = mkRV v s ∧ RVM.le0 v t s

noncomputable instance instStructure : LRV.Structure (C v) where
  funMap := fMap v
  RelMap := rMap v

end IModel
end Milestone0
end SpecialTransformations
set_option linter.unusedSimpArgs false
open FirstOrder FirstOrder.Language
namespace SpecialTransformations.Milestone0.IModel
open SpecialTransformations.Milestone0

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-- the (unique) empty assignment -/
abbrev dflt (v : Valuation K Γ₀) : Empty → C v := fun e => e.elim

@[simp] theorem RelMap_def {n : ℕ} (r : Rel n) (xs : Fin n → C v) :
    (Structure.RelMap (L := LRV) (M := C v) r xs) = rMap v r xs := rfl

@[simp] theorem funMap_def {n : ℕ} (f : Fn n) (xs : Fin n → C v) :
    (Structure.funMap (L := LRV) (M := C v) f xs) = fMap v f xs := rfl

/-- `M ⊨ φ.alls` unfolds to the universally quantified bounded formula. -/
theorem model_alls {k : ℕ} (φ : LRV.BoundedFormula Empty k) :
    ((C v) ⊨ φ.alls) ↔ ∀ xs : Fin k → C v, φ.Realize (dflt v) xs := by
  rw [Sentence.Realize, BoundedFormula.realize_alls]
  refine forall_congr' (fun xs => ?_)
  exact iff_of_eq (congrArg (fun w => φ.Realize w xs) (Subsingleton.elim _ _))

/-- the `VF` sort predicate at a variable, in terms of the carrier -/
theorem realize_sortPred_vf {n : ℕ} (i : Fin n) (xs : Fin n → C v) :
    (LRV.sortPred .vf (LRV.tv i.val i.isLt)).Realize (dflt v) xs ↔ ∃ x : K, xs i = mkVF v x := by
  simp only [LRV.sortPred, LRV.pVF, LRV.tv, BoundedFormula.realize_rel₁, RelMap_def, rMap,
    Matrix.cons_val_fin_one, Term.realize_var, Sum.elim_inr, Fin.eta]

/-- the `RV` sort predicate at a variable, in terms of the carrier -/
theorem realize_sortPred_rv {n : ℕ} (i : Fin n) (xs : Fin n → C v) :
    (LRV.sortPred .rv (LRV.tv i.val i.isLt)).Realize (dflt v) xs ↔
      ∃ t : RVM.RV0 v, xs i = mkRV v t := by
  simp only [LRV.sortPred, LRV.pRVsort, LRV.tv, BoundedFormula.realize_rel₁, RelMap_def, rMap,
    Matrix.cons_val_fin_one, Term.realize_var, Sum.elim_inr, Fin.eta]

/-- realizing a `foldr` of conjunctions -/
theorem realize_foldr_inf {ι : Type*} {n : ℕ} (l : List ι)
    (f : ι → LRV.BoundedFormula Empty n) (xs : Fin n → C v) :
    (l.foldr (fun i acc => f i ⊓ acc) ⊤).Realize (dflt v) xs ↔
      ∀ i ∈ l, (f i).Realize (dflt v) xs := by
  induction l with
  | nil => simp [BoundedFormula.realize_top]
  | cons a l ih =>
    simp only [List.foldr_cons, BoundedFormula.realize_inf, ih, List.mem_cons]
    exact ⟨fun ⟨h1, h2⟩ i hi => hi.elim (fun e => e ▸ h1) (h2 i),
      fun h => ⟨h a (Or.inl rfl), fun i hi => h i (Or.inr hi)⟩⟩

theorem realize_sortedHyps {k : ℕ} (ss : Fin k → SortTag) (xs : Fin k → C v) :
    (LRV.sortedHyps ss).Realize (dflt v) xs ↔
      ∀ i : Fin k, ((ss i = .vf → ∃ x : K, xs i = mkVF v x) ∧
        (ss i = .rv → ∃ t : RVM.RV0 v, xs i = mkRV v t)) := by
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

/-- **the guarded universal sentence, unfolded at the intended model** -/
theorem model_allSorted {k : ℕ} (ss : Fin k → SortTag) (φ : LRV.BoundedFormula Empty k) :
    ((C v) ⊨ LRV.allSorted ss φ) ↔
      ∀ xs : Fin k → C v, (∀ i : Fin k, ((ss i = .vf → ∃ x : K, xs i = mkVF v x) ∧
        (ss i = .rv → ∃ t : RVM.RV0 v, xs i = mkRV v t))) →
        φ.Realize (dflt v) xs := by
  rw [LRV.allSorted, model_alls v]
  refine forall_congr' (fun xs => ?_)
  rw [BoundedFormula.realize_imp]
  exact ⟨fun h hg => h ((realize_sortedHyps v ss xs).mpr hg),
    fun h hg => h ((realize_sortedHyps v ss xs).mp hg)⟩

macro "prep" : tactic => `(tactic|
  simp only [FirstOrder.Language.BoundedFormula.realize_rel₁, FirstOrder.Language.BoundedFormula.realize_rel₂,
    FirstOrder.Language.BoundedFormula.realize_rel, FirstOrder.Language.BoundedFormula.realize_imp,
    FirstOrder.Language.BoundedFormula.realize_inf, FirstOrder.Language.BoundedFormula.realize_sup,
    FirstOrder.Language.BoundedFormula.realize_not, FirstOrder.Language.BoundedFormula.realize_bdEqual,
    FirstOrder.Language.BoundedFormula.realize_top, FirstOrder.Language.BoundedFormula.realize_bot,
    FirstOrder.Language.BoundedFormula.realize_iff, FirstOrder.Language.BoundedFormula.realize_all,
    FirstOrder.Language.BoundedFormula.realize_ex, FirstOrder.Language.BoundedFormula.realize_exs,
    FirstOrder.Language.BoundedFormula.realize_alls,
    FirstOrder.Language.Term.realize_func, FirstOrder.Language.Term.realize_var,
    FirstOrder.Language.Relations.boundedFormula₁, FirstOrder.Language.Relations.boundedFormula₂,
    Function.comp_apply,
    SpecialTransformations.Milestone0.LRV.allOne, SpecialTransformations.Milestone0.LRV.sortedHyps,
    SpecialTransformations.Milestone0.LRV.sortPred,
    SpecialTransformations.Milestone0.LRV.tv, SpecialTransformations.Milestone0.LRV.exSorted,
    SpecialTransformations.Milestone0.LRV.pVF, SpecialTransformations.Milestone0.LRV.pRVsort,
    SpecialTransformations.Milestone0.LRV.pUnits, SpecialTransformations.Milestone0.LRV.pLe,
    SpecialTransformations.Milestone0.LRV.pEq, SpecialTransformations.Milestone0.LRV.pRV,
    SpecialTransformations.Milestone0.LRV.pK, SpecialTransformations.Milestone0.LRV.pInK,
    SpecialTransformations.Milestone0.LRV.pRV0,
    SpecialTransformations.Milestone0.LRV.pGtOne,
    SpecialTransformations.Milestone0.LRV.tVFZero, SpecialTransformations.Milestone0.LRV.tVFOne,
    SpecialTransformations.Milestone0.LRV.tVFAdd, SpecialTransformations.Milestone0.LRV.tVFNeg,
    SpecialTransformations.Milestone0.LRV.tVFMul, SpecialTransformations.Milestone0.LRV.tRVOne,
    SpecialTransformations.Milestone0.LRV.tRVZero, SpecialTransformations.Milestone0.LRV.tRVInfty,
    SpecialTransformations.Milestone0.LRV.tRVMul, SpecialTransformations.Milestone0.LRV.tKAdd,
    SpecialTransformations.Milestone0.LRV.tKNeg, SpecialTransformations.Milestone0.LRV.tRv,
    RelMap_def, funMap_def, rMap, fMap, mkVF, mkRV, cInfty, cKZero, cRVOne,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.empty_eq, Fin.snoc_zero, Fin.snoc_castSucc,
    Fin.snoc_last, Fin.forall_fin_one, Fin.forall_fin_two, Fin.forall_fin_zero, Fin.ext_iff,
    Fin.zero_eta, Sum.elim_inl, Sum.elim_inr,
    FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize])

/-! ### the sort discipline of the encoding (except the two residue-arithmetic sentences) -/

theorem model_sdVFZero : (C v) ⊨ Axioms.sdVFZero := by
  simp only [Axioms.sdVFZero]; prep
  exact ⟨0, rfl⟩

theorem model_sdVFOne : (C v) ⊨ Axioms.sdVFOne := by
  simp only [Axioms.sdVFOne]; prep
  exact ⟨1, rfl⟩

theorem model_sdVFAdd : (C v) ⊨ Axioms.sdVFAdd := by
  simp only [Axioms.sdVFAdd]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  obtain ⟨b, hb⟩ := (h 1).1 rfl
  rw [ha, hb]
  exact ⟨a + b, rfl⟩

theorem model_sdVFNeg : (C v) ⊨ Axioms.sdVFNeg := by
  simp only [Axioms.sdVFNeg]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  rw [ha]
  exact ⟨-a, rfl⟩

theorem model_sdVFMul : (C v) ⊨ Axioms.sdVFMul := by
  simp only [Axioms.sdVFMul]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  obtain ⟨b, hb⟩ := (h 1).1 rfl
  rw [ha, hb]
  exact ⟨a * b, rfl⟩

theorem model_sdRv : (C v) ⊨ Axioms.sdRv := by
  simp only [Axioms.sdRv]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  rw [ha]
  exact ⟨some (RVM.rv v a), rfl⟩

theorem model_sdRVZero : (C v) ⊨ Axioms.sdRVZero := by
  simp only [Axioms.sdRVZero]; prep
  exact ⟨none, rfl⟩

theorem model_sdRVOne : (C v) ⊨ Axioms.sdRVOne := by
  simp only [Axioms.sdRVOne]; prep
  exact ⟨some (RVM.rvOne v), rfl⟩

theorem model_sdRVInfty : (C v) ⊨ Axioms.sdRVInfty := by
  simp only [Axioms.sdRVInfty]; prep
  exact ⟨some none, rfl⟩

theorem model_sdRVMul : (C v) ⊨ Axioms.sdRVMul := by
  simp only [Axioms.sdRVMul]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨s, hs⟩ := (h 0).2 rfl
  obtain ⟨t, ht⟩ := (h 1).2 rfl
  rw [hs, ht]
  exact ⟨RVM.rv0Mul v s t, rfl⟩

theorem model_sdCover : (C v) ⊨ Axioms.sdCover := by
  simp only [Axioms.sdCover, LRV.allOne]
  rw [model_alls v]
  intro xs
  prep
  rcases xs 0 with x | t
  · exact Or.inl ⟨x, rfl⟩
  · exact Or.inr ⟨t, rfl⟩

theorem model_sdDisjoint : (C v) ⊨ Axioms.sdDisjoint := by
  simp only [Axioms.sdDisjoint, LRV.allOne]
  rw [model_alls v]
  intro xs
  prep
  rintro ⟨⟨x, hx⟩, ⟨t, ht⟩⟩
  rw [hx] at ht
  exact nomatch ht


/-! ### the field axioms of the `VF` sort (Definition 2.2 item 1) -/

theorem model_vfField : (C v) ⊨ Axioms.vfField := by
  rw [Theory.model_iff]; intro s hs
  simp only [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms, List.mem_cons, List.mem_nil_iff,
    or_false] at hs
  obtain rfl | h2 := hs
  · rw [model_allSorted v]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl; obtain ⟨b, hb⟩ := (h 1).1 rfl; obtain ⟨c, hc⟩ := (h 2).1 rfl
    rw [ha, hb, hc]; exact congrArg (mkVF v) (add_assoc a b c)
  obtain rfl | h3 := h2
  · rw [model_allSorted v]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl; obtain ⟨b, hb⟩ := (h 1).1 rfl
    rw [ha, hb]; exact congrArg (mkVF v) (add_comm a b)
  obtain rfl | h4 := h3
  · rw [model_allSorted v]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl
    rw [ha]; exact congrArg (mkVF v) (add_zero a)
  obtain rfl | h5 := h4
  · rw [model_allSorted v]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl
    rw [ha]; exact congrArg (mkVF v) (add_neg_cancel a)
  obtain rfl | h6 := h5
  · rw [model_allSorted v]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl; obtain ⟨b, hb⟩ := (h 1).1 rfl; obtain ⟨c, hc⟩ := (h 2).1 rfl
    rw [ha, hb, hc]; exact congrArg (mkVF v) (mul_assoc a b c)
  obtain rfl | h7 := h6
  · rw [model_allSorted v]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl; obtain ⟨b, hb⟩ := (h 1).1 rfl
    rw [ha, hb]; exact congrArg (mkVF v) (mul_comm a b)
  obtain rfl | h8 := h7
  · rw [model_allSorted v]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl
    rw [ha]; exact congrArg (mkVF v) (mul_one a)
  obtain rfl | h9 := h8
  · rw [model_allSorted v]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl; obtain ⟨b, hb⟩ := (h 1).1 rfl; obtain ⟨c, hc⟩ := (h 2).1 rfl
    rw [ha, hb, hc]; exact congrArg (mkVF v) (mul_add a b c)
  obtain rfl | h10 := h9
  · prep
    intro hh
    exact zero_ne_one (Sum.inl.inj hh)
  · obtain rfl := by simpa using h10
    rw [model_allSorted v]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl
    rw [ha]
    rcases eq_or_ne a 0 with rfl | ha0
    · exact Or.inl rfl
    · refine Or.inr ⟨mkVF v a⁻¹, ⟨a⁻¹, rfl⟩, ?_⟩
      have h1' : (1 : Fin 2) = Fin.last 1 := rfl
      have h0' : (0 : Fin 2) = Fin.castSucc (0 : Fin 1) := rfl
      rw [h1', h0', Fin.snoc_castSucc, Fin.snoc_last, ha, mkVF]
      exact congrArg Sum.inl (mul_inv_cancel₀ ha0)


/-! ### the projection `rv` (Definition 2.2 item 6) -/

theorem model_rvZeroEq : (C v) ⊨ Axioms.rvZeroEq := by
  simp only [Axioms.rvZeroEq]; prep
  rw [RVM.rv_zero]

theorem model_rvEqInfty : (C v) ⊨ Axioms.rvEqInfty := by
  simp only [Axioms.rvEqInfty]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  rw [ha]
  intro hh
  have h1 : RVM.rv v a = none := by
    have h2 : some (RVM.rv v a) = (some (none : Option (RVM.RVUnit v))) := by
      simpa [mkVF, fMap] using hh
    exact Option.some.inj h2
  rw [RVM.rv_eq_none_iff] at h1
  rw [h1]
  rfl

theorem model_rvMulHom : (C v) ⊨ Axioms.rvMulHom := by
  simp only [Axioms.rvMulHom]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  obtain ⟨b, hb⟩ := (h 1).1 rfl
  rw [ha, hb]
  show Sum.inr (some (RVM.rv v (a * b))) = Sum.inr (RVM.rv0Mul v (some (RVM.rv v a)) (some (RVM.rv v b)))
  rw [RVM.rv0Mul_some_rv]

theorem model_rvSurj : (C v) ⊨ Axioms.rvSurj := by
  simp only [Axioms.rvSurj]; rw [model_allSorted v]; intro xs h; prep
  rintro ⟨q, hq, -⟩
  obtain ⟨x, -, hxq⟩ := RVM.rv_surjective (v := v) (t := some q) (by simp)
  refine ⟨mkVF v x, ⟨x, rfl⟩, ?_⟩
  show Sum.inr (some (RVM.rv v x)) = xs 0
  rw [hxq, hq]
  rfl

theorem le0_rv_add (a b : K) :
    RVM.le0 v (some (RVM.rv v a)) (some (RVM.rv v (a + b))) ∨
      RVM.le0 v (some (RVM.rv v b)) (some (RVM.rv v (a + b))) := by
  simp only [show ∀ x y : K, RVM.le0 v (some (RVM.rv v x)) (some (RVM.rv v y)) =
      (RVM.vrv v (RVM.rv v y) ≤ RVM.vrv v (RVM.rv v x)) from fun x y => rfl, RVM.vrv_rv]
  exact Valuation.map_add' v a b

theorem model_rvUltrametric : (C v) ⊨ Axioms.rvUltrametric := by
  simp only [Axioms.rvUltrametric]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  obtain ⟨b, hb⟩ := (h 1).1 rfl
  rw [ha, hb]
  rcases le0_rv_add v a b with h | h
  · exact Or.inl ⟨some (RVM.rv v a), some (RVM.rv v (a + b)), rfl, rfl, h⟩
  · exact Or.inr ⟨some (RVM.rv v b), some (RVM.rv v (a + b)), rfl, rfl, h⟩


/-! ### the multiplicative monoid of the `RV` sort (Definition 2.2 item 2), partial -/

theorem rv0Mul_comm (t s : RVM.RV0 v) : RVM.rv0Mul v t s = RVM.rv0Mul v s t := by
  rcases t with _ | (_ | a) <;> rcases s with _ | (_ | b) <;> simp only [RVM.rv0Mul] <;>
    (first | rfl | rw [mul_comm a b])

theorem rv0Mul_assoc (t s r : RVM.RV0 v) :
    RVM.rv0Mul v (RVM.rv0Mul v t s) r = RVM.rv0Mul v t (RVM.rv0Mul v s r) := by
  rcases t with _ | (_ | a) <;> rcases s with _ | (_ | b) <;> rcases r with _ | (_ | c) <;>
    simp only [RVM.rv0Mul] <;> (first | rfl | rw [mul_assoc a b c])

theorem model_rvOneMem : (C v) ⊨ Axioms.rvOneMem := by
  simp only [Axioms.rvOneMem]; prep
  refine ⟨1, ?_, ?_⟩
  · simp [cRVOne, cUnit, RVM.rvOne_eq]
  · simp [RVM.vrv_some]

theorem model_rvMulMem : (C v) ⊨ Axioms.rvMulMem := by
  simp only [Axioms.rvMulMem]; rw [model_allSorted v]; intro xs h; prep
  rintro ⟨q1, hq1, hv1⟩ ⟨q2, hq2, hv2⟩
  rw [hq1, hq2]
  refine ⟨q1 * q2, ?_, ?_⟩
  · simp only [cUnit, RVM.rv0Mul_some_some]
  · rw [← RVM.rvMul_some_some, RVM.vrv_mul, hv1, hv2, mul_one]

theorem model_rvMulComm : (C v) ⊨ Axioms.rvMulComm := by
  simp only [Axioms.rvMulComm]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  rw [ht, hs]
  exact congrArg (fun x => mkRV v x) (rv0Mul_comm v t s)

theorem model_rvMulAssoc : (C v) ⊨ Axioms.rvMulAssoc := by
  simp only [Axioms.rvMulAssoc]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  obtain ⟨r, hr⟩ := (h 2).2 rfl
  rw [ht, hs, hr]
  exact congrArg (fun x => mkRV v x) (rv0Mul_assoc v t s r)

theorem model_rvMulOne : (C v) ⊨ Axioms.rvMulOne := by
  simp only [Axioms.rvMulOne]; rw [model_allSorted v]; intro xs h; prep
  rintro ⟨q, hq, -⟩
  rw [hq]
  simp only [cUnit, RVM.rvOne_eq, RVM.rv0Mul_some_some, mul_one, mkRV, Sum.inr.injEq,
    Option.some.injEq]
  exact one_mul q

theorem model_rvMulZeroK : (C v) ⊨ Axioms.rvMulZeroK := by
  simp only [Axioms.rvMulZeroK]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  intro hpK
  rw [ht] at hpK ⊢
  rcases hpK with ⟨q, hq, -⟩ | hzero
  · rw [hq]; simp [cUnit, cKZero, RVM.rv0Mul]
  · rw [hzero]; simp [cKZero, RVM.rv0Mul]

/-- **`sdUnits` holds at the intended structure**: the predicate `K^×` is borne by
`RV`-sort elements (its actual content is `leClassOne`, i.e. `K^× = ker vrv`). -/
theorem models_sdUnits : (C v) ⊨ Axioms.sdUnits := by
  simp only [Axioms.sdUnits, LRV.allOne]
  rw [model_alls v]
  intro xs
  prep
  rintro ⟨q, hq, -⟩
  exact ⟨some (some q), hq⟩

/-! ### the preorder on `RV` (Definition 2.2 item 4) -/

theorem le0_mkRV_iff {t s : RVM.RV0 v} :
    (∃ a b : RVM.RV0 v, mkRV v t = mkRV v a ∧ mkRV v s = mkRV v b ∧ RVM.le0 v a b) ↔
      RVM.le0 v t s := by
  constructor
  · rintro ⟨a, b, h1, h2, h3⟩
    simp only [mkRV, Sum.inr.injEq] at h1 h2
    rw [← h1, ← h2] at h3
    exact h3
  · intro h; exact ⟨t, s, rfl, rfl, h⟩

theorem model_leRefl : (C v) ⊨ Axioms.leRefl := by
  simp only [Axioms.leRefl]; rw [model_allSorted v]; intro xs h; prep
  intro _
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht]
  exact ⟨t, t, rfl, rfl, RVM.le0_refl v t⟩

theorem model_leTotal : (C v) ⊨ Axioms.leTotal := by
  simp only [Axioms.leTotal]; rw [model_allSorted v]; intro xs h; prep
  intro _ _
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  rw [ht, hs]
  rcases RVM.le0_total v t s with h' | h'
  · exact Or.inl ⟨t, s, rfl, rfl, h'⟩
  · exact Or.inr ⟨s, t, rfl, rfl, h'⟩

theorem model_leTop : (C v) ⊨ Axioms.leTop := by
  simp only [Axioms.leTop]; rw [model_allSorted v]; intro xs h; prep
  intro _
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht]
  exact ⟨t, some none, rfl, rfl, RVM.le0_infty v t⟩

theorem model_leInftyEq : (C v) ⊨ Axioms.leInftyEq := by
  simp only [Axioms.leInftyEq]; rw [model_allSorted v]; intro xs h; prep
  intro _ hle
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht] at hle ⊢
  obtain ⟨a, b, ha, hb, hab⟩ := hle
  simp only [mkRV, Sum.inr.injEq] at ha hb
  subst ha
  rw [hb]
  rcases b with _ | _ | q
  · exact absurd hab (by simp [RVM.le0])
  · rfl
  · exfalso
    have hne : RVM.vrv v (some q) ≠ 0 := by simp [RVM.vrv_some]
    have h0 : RVM.vrv v (some q) = 0 := le_antisymm hab zero_le
    exact hne h0

/-! ### the residue-arithmetic sort-closure sentences -/

theorem model_sdKAdd : (C v) ⊨ Axioms.sdKAdd := by
  simp only [Axioms.sdKAdd]; rw [model_allSorted v]; intro xs h; prep
  intro _ _
  simp [fMap, cKZero, cInfty]

theorem model_sdKNeg : (C v) ⊨ Axioms.sdKNeg := by
  simp only [Axioms.sdKNeg]; rw [model_allSorted v]; intro xs h; prep
  intro _
  simp [fMap, cKZero, cInfty]

theorem model_sdKMul : (C v) ⊨ Axioms.sdKMul := by
  simp only [Axioms.sdKMul]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  intro h1 h2
  rw [ht] at h1 ⊢
  rw [hs] at h2 ⊢
  simp only [mkRV, cUnit, cKZero, Sum.inr.injEq] at h1 h2
  rcases h1 with ⟨q, rfl, hq⟩ | rfl
  · rcases h2 with ⟨q', rfl, hq'⟩ | rfl
    · refine Or.inl ⟨q * q', ?_, ?_⟩
      · rfl
      · rw [← RVM.rvMul_some_some, RVM.vrv_mul, hq, hq', mul_one]
    · refine Or.inr ?_
      simp only [mkRV, cKZero, RVM.rv0Mul]
  · rcases h2 with ⟨q', rfl, hq'⟩ | rfl
    · refine Or.inr ?_
      simp only [mkRV, cKZero, RVM.rv0Mul]
    · refine Or.inr ?_
      simp only [mkRV, cKZero, RVM.rv0Mul]

/-! ### the assembly: which axioms of the encoded `ACVF` hold at the intended structure -/

theorem model_ofList {l : List LRV.Sentence} (h : ∀ s ∈ l, (C v) ⊨ s) :
    (C v) ⊨ Axioms.ofList l := by
  rw [Theory.model_iff]; intro s hs; exact h s hs

/-- every sentence of the sort discipline holds at the intended structure -/
theorem model_sortClosure_all (s : LRV.Sentence) (hs : s ∈ Axioms.sortClosure) :
    (C v) ⊨ s := by
  simp only [Axioms.sortClosure, Axioms.ofList, List.mem_cons, List.mem_nil_iff, or_false] at hs
  obtain rfl | h4 := hs
  · exact model_sdVFZero v
  obtain rfl | h5 := h4
  · exact model_sdVFOne v
  obtain rfl | h6 := h5
  · exact model_sdVFAdd v
  obtain rfl | h7 := h6
  · exact model_sdVFNeg v
  obtain rfl | h8 := h7
  · exact model_sdVFMul v
  obtain rfl | h9 := h8
  · exact model_sdRv v
  obtain rfl | h10 := h9
  · exact model_sdRVZero v
  obtain rfl | h11 := h10
  · exact model_sdRVInfty v
  obtain rfl | h12 := h11
  · exact model_sdRVOne v
  obtain rfl | h13 := h12
  · exact model_sdRVMul v
  obtain rfl | h14 := h13
  · exact models_sdUnits v
  obtain rfl | h15 := h14
  · exact model_sdKAdd v
  obtain rfl | h16 := h15
  · exact model_sdKNeg v
  obtain rfl := by simpa using h16
  exact model_sdKMul v

/-- the sort discipline of the encoded `ACVF` holds at the intended structure -/
theorem model_sortAxioms_all : (C v) ⊨ Axioms.sortAxioms := by
  rw [Theory.model_iff]; intro s hs
  simp only [Axioms.sortAxioms, Set.mem_union, Set.mem_ofPred_eq, Axioms.ofList, List.mem_cons,
    List.mem_nil_iff, or_false] at hs
  rcases hs with hs | hs | hs
  · exact model_sortClosure_all v s hs
  · rw [show s = Axioms.sdCover from hs]; exact model_sdCover v
  · rw [show s = Axioms.sdDisjoint from hs]; exact model_sdDisjoint v

/-- `preorderRV` minus transitivity, `K^×` = class of 1, and compatibility with `×` -/
theorem model_preorderRV_easy (s : LRV.Sentence) (hs : s ∈ Axioms.preorderRV)
    (h1 : s ≠ Axioms.leTrans) (h2 : s ≠ Axioms.leClassOne) (h3 : s ≠ Axioms.leMulCompat) :
    (C v) ⊨ s := by
  revert h1 h2 h3
  simp only [Axioms.preorderRV, Axioms.ofList, List.mem_cons, List.mem_nil_iff, or_false] at hs
  obtain rfl | h4 := hs
  · intro _ _ _; exact model_leRefl v
  obtain rfl | h5 := h4
  · intro h1 _ _; exact absurd rfl h1
  obtain rfl | h6 := h5
  · intro _ _ _; exact model_leTotal v
  obtain rfl | h7 := h6
  · intro _ _ _; exact model_leTop v
  obtain rfl | h8 := h7
  · intro _ _ _; exact model_leInftyEq v
  obtain rfl | h9 := h8
  · intro _ h2 _; exact absurd rfl h2
  obtain rfl := by simpa using h9
  · intro _ _ h3; exact absurd rfl h3

/-- the `rv`-axioms of Definition 2.2(6) hold at the intended structure -/
theorem model_rvAxioms_all : (C v) ⊨ Axioms.rvAxioms := by
  rw [Theory.model_iff]; intro s hs
  simp only [Axioms.rvAxioms, Axioms.ofList, List.mem_cons, List.mem_nil_iff, or_false] at hs
  obtain rfl | h2 := hs
  · exact model_rvZeroEq v
  obtain rfl | h3 := h2
  · exact model_rvEqInfty v
  obtain rfl | h4 := h3
  · exact model_rvMulHom v
  obtain rfl | h5 := h4
  · exact model_rvSurj v
  obtain rfl := by simpa using h5
  exact model_rvUltrametric v

/-! ## Part 6 helpers: the interpretation of the symbols, for the milestone statements -/

namespace SpecialTransformations.Milestone0
open Axioms
variable {M : Type*} [LRV.Structure M]

/-- `x` lies in the `VF` sort -/
def iVF (x : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memVF ![x]
/-- `x` lies in the `RV` sort -/
def iRV (x : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memRV ![x]
/-- `x ∈ Kˣ` -/
def iUnits (x : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memUnits ![x]
/-- the preorder `≤` of the `RV` sort -/
def iLe (x y : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.rvLe ![x, y]
/-- the interpretation of `0` of the `RV` sort -/
def iRVZero : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvZero fun i => i.elim0
/-- the interpretation of `∞` -/
def iRVInfty : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvInfty fun i => i.elim0
/-- the interpretation of `1` of the `RV` sort -/
def iRVOne : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvOne fun i => i.elim0

end SpecialTransformations.Milestone0

/-! ## The last two sentences of `rvGroup`: inverses and divisibility of `Kˣ` -/

namespace SpecialTransformations.Milestone0.Ob.RVGroup

open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.IModel

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

theorem vrv_cUnit_one : RVM.vrv v (some (1 : RVM.RVUnit v)) = 1 := by
  rw [← RVM.rvOne_eq]
  simpa using RVM.vrv_rv (v := v) (1 : K)

theorem vrv_cUnit_pow (a : RVM.RVUnit v) (k : ℕ) :
    RVM.vrv v (some (a ^ k)) = RVM.vrv v (some a) ^ k := by
  induction k with
  | zero => simpa using vrv_cUnit_one v
  | succ k ih =>
    rw [pow_succ, pow_succ, ← RVM.rvMul_some_some (v := v), RVM.vrv_mul, ih]

theorem eq_one_of_pow_eq_one {x : Γ₀} {k : ℕ} (hk : k ≠ 0) (h : x ^ k = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with h' | h' | h'
  · have hlt : x ^ k < 1 := (pow_lt_one_iff hk).mpr h'
    rw [h] at hlt
    exact absurd hlt (lt_irrefl 1)
  · exact h'
  · have hlt : 1 < x ^ k := (one_lt_pow_iff hk).mpr h'
    rw [h] at hlt
    exact absurd hlt (lt_irrefl 1)

/-- `Fin.snoc` at the last index, in the `Fin 2` form produced by `exSorted` -/
theorem snoc_last_fin2 {Y : Type*} (f : Fin 1 → Y) (a : Y) :
    @Fin.snoc 1 (fun _ => Y) f a (1 : Fin 2) = a := by
  show @Fin.snoc 1 (fun _ => Y) f a (Fin.last 1) = a
  simp only [Fin.snoc_last]

/-- `Fin.snoc` at index `0`, in the `Fin 2` form produced by `exSorted` -/
theorem snoc_zero_fin2 {Y : Type*} (f : Fin 1 → Y) (a : Y) :
    @Fin.snoc 1 (fun _ => Y) f a (0 : Fin 2) = f 0 := by
  show @Fin.snoc 1 (fun _ => Y) f a ((0 : Fin 1).castSucc) = f 0
  simp only [Fin.snoc_castSucc]

/-- the term `tRVPow` at a `Kˣ`-element of the assignment realizes to the power in `RV^×` -/
theorem realize_tRVPow_cUnit (xs : Fin 1 → C v) (c : RVM.RVUnit v) (k : ℕ) :
    Term.realize (Sum.elim (dflt v) (@Fin.snoc 1 (fun _ => C v) xs (cUnit v c)))
      (LRV.tRVPow (Term.var (L := LRV) (Sum.inr (1 : Fin 2))) k) = cUnit v (c ^ k) := by
  induction k with
  | zero =>
    simp only [LRV.tRVPow, LRV.tRVOne, Term.realize_func, funMap_def, fMap, cRVOne, cUnit,
      RVM.rvOne_eq, pow_zero]
  | succ k ih =>
    simp only [LRV.tRVPow, LRV.tRVMul]
    simp only [Term.realize_func]
    simp only [funMap_def]
    have hx : Term.realize (Sum.elim (dflt v) (@Fin.snoc 1 (fun _ => C v) xs (cUnit v c)))
        (Term.var (L := LRV) (Sum.inr (1 : Fin 2))) = cUnit v c := by
      simp only [Term.realize_var (L := LRV), Sum.elim_inr, snoc_last_fin2]
    have hmat : (fun i : Fin 2 =>
        Term.realize (Sum.elim (dflt v) (@Fin.snoc 1 (fun _ => C v) xs (cUnit v c)))
          (![LRV.tRVPow (Term.var (L := LRV) (Sum.inr (1 : Fin 2))) k,
            Term.var (L := LRV) (Sum.inr (1 : Fin 2))] i)) =
        ![cUnit v (c ^ k), cUnit v c] := by
      funext i
      fin_cases i
      · exact ih
      · exact hx
    rw [hmat]
    simp only [fMap, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, cUnit,
      mkRV, RVM.rv0Mul_some_some, pow_succ]
/-- the last `rvGroup` sentence: every element of `Kˣ` is invertible in `Kˣ` -/
theorem model_rvMulInv : (C v) ⊨ Axioms.rvMulInv := by
  simp only [Axioms.rvMulInv]; rw [model_allSorted v]; intro xs h; prep
  rintro ⟨q, hq, hq1⟩
  refine ⟨Sum.inr (some (some q⁻¹)), ⟨some (some q⁻¹), snoc_last_fin2 xs _⟩,
    ⟨q⁻¹, snoc_last_fin2 xs _, ?_⟩, ?_⟩
  · have h : RVM.vrv v (some q) * RVM.vrv v (some q⁻¹) = 1 := by
      rw [← RVM.vrv_mul, RVM.rvMul_some_some (v := v), mul_inv_cancel, vrv_cUnit_one v]
    rw [hq1, one_mul] at h
    exact h
  · rw [snoc_last_fin2, snoc_zero_fin2, hq]
    simp only [cUnit, RVM.rv0Mul_some_some, mul_comm q⁻¹ q, mul_inv_cancel, RVM.rvOne_eq]

/-- divisibility of `Kˣ`, which needs `K` algebraically closed -/
theorem model_rvDivisible [IsAlgClosed K] (k : ℕ) (hk : 1 ≤ k) :
    (C v) ⊨ Axioms.rvDivisible k := by
  simp only [Axioms.rvDivisible]; rw [model_allSorted v]; intro xs h; prep
  rintro ⟨q, hq, hq1⟩
  have hk0 : k ≠ 0 := by omega
  obtain ⟨c, hc⟩ := RVM.rvUnit_divisible (v := v) k hk0 q
  refine ⟨Sum.inr (some (some c)), ⟨some (some c), snoc_last_fin2 xs _⟩,
    ⟨c, snoc_last_fin2 xs _, ?_⟩, ?_⟩
  · have h : RVM.vrv v (some c) ^ k = 1 := by
      rw [← vrv_cUnit_pow v c k, hc, hq1]
    exact eq_one_of_pow_eq_one (Γ₀ := Γ₀) hk0 h
  · rw [show (Sum.inr (some (some c)) : C v) = cUnit v c from rfl, realize_tRVPow_cUnit,
      snoc_zero_fin2, hc, hq]

end SpecialTransformations.Milestone0.Ob.RVGroup

#print axioms SpecialTransformations.Milestone0.Ob.RVGroup.model_rvMulInv
#print axioms SpecialTransformations.Milestone0.Ob.RVGroup.model_rvDivisible
#print axioms SpecialTransformations.Milestone0.Ob.RVGroup.realize_tRVPow_cUnit

/-! ### completing `preorderRV` (the three sentences `IntendedModel.lean` leaves out)

These are m7's proofs (finding f2, `.ultramath/smw06c8tw/m7/Body.lean`), restated here so
that this file is self-contained. -/

theorem mkRV_inj {t s : RVM.RV0 v} (h : mkRV v t = Sum.inr s) : t = s := by
  simpa [mkRV] using h

theorem exists_mkRV_of_le0 {t s : RVM.RV0 v} (h : RVM.le0 v t s) :
    ∃ a b : RVM.RV0 v, mkRV v t = mkRV v a ∧ mkRV v s = mkRV v b ∧ RVM.le0 v a b :=
  ⟨t, s, rfl, rfl, h⟩

theorem le0_of_exists_mkRV {t s : RVM.RV0 v}
    (h : ∃ a b : RVM.RV0 v, mkRV v t = mkRV v a ∧ mkRV v s = mkRV v b ∧ RVM.le0 v a b) :
    RVM.le0 v t s := by
  obtain ⟨a, b, h1, h2, h3⟩ := h
  simp only [mkRV, Sum.inr.injEq] at h1 h2
  rw [← h1, ← h2] at h3
  exact h3

theorem model_leTrans : (C v) ⊨ Axioms.leTrans := by
  simp only [Axioms.leTrans]; rw [model_allSorted v]; intro xs h; prep
  intro _ _ _ h01 h12
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  obtain ⟨r, hr⟩ := (h 2).2 rfl
  rw [ht, hs] at h01
  rw [hs, hr] at h12
  rw [ht, hr]
  exact exists_mkRV_of_le0 v
    (RVM.le0_trans v (le0_of_exists_mkRV v h01) (le0_of_exists_mkRV v h12))

/-- multiplying on the right by an element of `K^×` preserves `≤` -/
theorem le0_mul_unit_right (t s : RVM.RV0 v) (q : RVM.RVUnit v)
    (hq : RVM.vrv v (some q) = 1) (h : RVM.le0 v t s) :
    RVM.le0 v (RVM.rv0Mul v t (some (some q))) (RVM.rv0Mul v s (some (some q))) := by
  have key : ∀ a : RVM.RV v,
      RVM.rv0Mul v (some a) (some (some q)) = some (RVM.rvMul a (some q)) := by
    intro a; cases a <;> rfl
  match t, s with
  | none, _ => exact trivial
  | some a, none => exact absurd h (by simp [RVM.le0])
  | some a, some b =>
    rw [key a, key b]
    show RVM.vrv v (RVM.rvMul b (some q)) ≤ RVM.vrv v (RVM.rvMul a (some q))
    rw [RVM.vrv_mul v, RVM.vrv_mul v, hq, mul_one, mul_one]
    exact h

theorem model_leClassOne : (C v) ⊨ Axioms.leClassOne := by
  simp only [Axioms.leClassOne]; rw [model_allSorted v]; intro xs h; prep
  intro _
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht]
  constructor
  · rintro ⟨q, hq, hq1⟩
    have htq : t = some (some q) := mkRV_inj v hq
    subst htq
    have hcl := (RVM.le_class_of_one_iff v (t := some q)).mpr hq1
    exact ⟨⟨some (RVM.rvOne v), some (some q), rfl, rfl, hcl.1⟩,
      ⟨some (some q), some (RVM.rvOne v), rfl, rfl, hcl.2⟩⟩
  · rintro ⟨⟨a1, b1, ha1, hb1, hl1⟩, ⟨a2, b2, ha2, hb2, hl2⟩⟩
    simp only [mkRV, Sum.inr.injEq] at ha1 hb1 ha2 hb2
    rw [← ha1, ← hb1] at hl1
    rw [← ha2, ← hb2] at hl2
    cases t with
    | none => exact absurd hl1 (by simp [RVM.le0])
    | some b =>
      cases b with
      | none =>
        exact absurd ((RVM.le_class_of_one_iff v (t := none)).mp ⟨hl1, hl2⟩) (by simp [RVM.vrv])
      | some q =>
        exact ⟨q, rfl, (RVM.le_class_of_one_iff v (t := some q)).mp ⟨hl1, hl2⟩⟩

theorem model_leMulCompat : (C v) ⊨ Axioms.leMulCompat := by
  simp only [Axioms.leMulCompat]; rw [model_allSorted v]; intro xs h; prep
  intro _ _ _ hunit hle
  obtain ⟨t0, ht0⟩ := (h 0).2 rfl
  obtain ⟨t1, ht1⟩ := (h 1).2 rfl
  obtain ⟨t2, ht2⟩ := (h 2).2 rfl
  obtain ⟨q, hq, hq1⟩ := hunit
  rw [ht2] at hq
  have ht2q : t2 = some (some q) := mkRV_inj v hq
  subst ht2q
  rw [ht0, ht1] at hle
  rw [ht0, ht1, ht2]
  exact ⟨RVM.rv0Mul v t0 (some (some q)), RVM.rv0Mul v t1 (some (some q)), rfl, rfl,
    le0_mul_unit_right v t0 t1 q hq1 (le0_of_exists_mkRV v hle)⟩

/-- **`preorderRV` holds at the intended structure** (Definition 2.2 item 4) -/
theorem model_preorderRV : (C v) ⊨ Axioms.preorderRV := by
  rw [Theory.model_iff]; intro s hs
  simp only [Axioms.preorderRV, Axioms.ofList, List.mem_cons, List.mem_nil_iff,
    or_false] at hs
  obtain rfl | h2 := hs
  · exact model_leRefl v
  obtain rfl | h3 := h2
  · exact model_leTrans v
  obtain rfl | h4 := h3
  · exact model_leTotal v
  obtain rfl | h5 := h4
  · exact model_leTop v
  obtain rfl | h6 := h5
  · exact model_leInftyEq v
  obtain rfl | h7 := h6
  · exact model_leClassOne v
  obtain rfl := by simpa using h7
  exact model_leMulCompat v

/-! ### the whole `rvGroup` block -/

theorem model_rvMulInfty : (C v) ⊨ Axioms.rvMulInfty := by
  simp only [Axioms.rvMulInfty]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht]
  exact congrArg (fun z => mkRV v z) (RVM.rv0Mul_infty v t)

/-- **`rvGroup` holds at the intended structure** (Definition 2.2 item 2) -/
theorem model_rvGroup [IsAlgClosed K] : (C v) ⊨ Axioms.rvGroup := by
  rw [Theory.model_iff]; intro s hs
  simp only [Axioms.rvGroup, Set.mem_union, Set.mem_setOf_eq, Axioms.ofList, List.mem_cons,
    List.mem_nil_iff, or_false] at hs
  rcases hs with h | ⟨k, hk, rfl⟩
  · obtain rfl | h2 := h
    · exact model_rvOneMem v
    obtain rfl | h3 := h2
    · exact model_rvMulMem v
    obtain rfl | h4 := h3
    · exact model_rvMulAssoc v
    obtain rfl | h5 := h4
    · exact model_rvMulComm v
    obtain rfl | h6 := h5
    · exact model_rvMulOne v
    obtain rfl | h7 := h6
    · exact SpecialTransformations.Milestone0.Ob.RVGroup.model_rvMulInv v
    obtain rfl | h8 := h7
    · exact model_rvMulZeroK v
    obtain rfl := by simpa using h8
    exact model_rvMulInfty v
  · exact SpecialTransformations.Milestone0.Ob.RVGroup.model_rvDivisible v k hk

/-! ### the assembled fragment -/

theorem model_of_mem {T : LRV.Theory} (h : (C v) ⊨ T) {s : LRV.Sentence} (hs : s ∈ T) :
    (C v) ⊨ s := by
  rw [Theory.model_iff] at h
  exact h s hs

/-- **the largest fragment of `ACVF` verified here**: everything except `kField`,
`kAlgClosed` and `vfAlgClosed` (Definition 2.2 items 1 partially, 2, 4, 6, plus the sort
discipline of the encoding) -/
theorem model_ACVF_fragment [IsAlgClosed K] :
    (C v) ⊨ (Axioms.sortAxioms ∪ Axioms.vfField ∪ Axioms.rvGroup ∪ Axioms.preorderRV ∪
      Axioms.rvAxioms) := by
  rw [Theory.model_iff]; intro s hs
  simp only [Set.mem_union] at hs
  rcases hs with (((hs | hs) | hs) | hs) | hs
  · exact model_of_mem v (model_sortAxioms_all v) hs
  · exact model_of_mem v (model_vfField v) hs
  · exact model_of_mem v (model_rvGroup v) hs
  · exact model_of_mem v (model_preorderRV v) hs
  · exact model_of_mem v (model_rvAxioms_all v) hs

end SpecialTransformations.Milestone0.IModel

/-! ### the `p`-adic instantiation of the fragment -/

namespace SpecialTransformations.Milestone0.Ob.Fragment

open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.IModel
open SpecialTransformations.Milestone0.IModel.SpecialTransformations.Milestone0
open scoped NNReal

/-- the fragment holds at `K = ℂ_[p]`, `v = (PadicComplex.valued p).v` -/
theorem model_ACVF_fragment_padic (p : ℕ) [Fact (Nat.Prime p)] :
    (C ((PadicComplex.valued p).v)) ⊨
      (Axioms.sortAxioms ∪ Axioms.vfField ∪ Axioms.rvGroup ∪ Axioms.preorderRV ∪
        Axioms.rvAxioms) :=
  model_ACVF_fragment _

end SpecialTransformations.Milestone0.Ob.Fragment

#print axioms SpecialTransformations.Milestone0.IModel.model_preorderRV
#print axioms SpecialTransformations.Milestone0.IModel.model_rvGroup
#print axioms SpecialTransformations.Milestone0.IModel.model_ACVF_fragment
#print axioms SpecialTransformations.Milestone0.Ob.Fragment.model_ACVF_fragment_padic

/-! ### `vfAlgClosed` at the intended structure `C v`

`accepted/VFAlgClosed.lean` proves this for a different `LRV.Structure` on the same carrier
(junk `Sum.inr none` everywhere off `VF`, `rvLe` interpreted as equality), so its
`realize_hornerPoly`/`acfScheme_vf` do not apply here; the polynomial machinery
(`hornerPolyK` and its monic/natDegree/eval lemmas) is structure-independent and is copied
from it. -/

namespace SpecialTransformations.Milestone0.Ob.VFAC

open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.IModel
open Polynomial

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- the monic polynomial `x^{n+1} + a_n x^n + ⋯ + a_0` in the Horner shape of
`LRV.hornerPoly` -/
noncomputable def hornerPolyK (a : ℕ → K) : ℕ → K[X]
  | 0 => 0
  | (n + 1) =>
    (List.finRange n).reverse.foldl (fun acc i => acc * X + Polynomial.C (a i.val))
      (X + Polynomial.C (a n))

theorem degree_C_lt_X (c : K) : (Polynomial.C c).degree < (X : K[X]).degree := by
  rw [Polynomial.degree_X]
  calc (Polynomial.C c).degree ≤ 0 := Polynomial.degree_C_le
    _ < 1 := by rw [← WithBot.coe_zero, ← WithBot.coe_one, WithBot.coe_lt_coe]; omega

theorem monic_X_add_C (c : K) : (X + Polynomial.C c : K[X]).Monic :=
  Polynomial.monic_X.add_of_left (degree_C_lt_X c)

theorem natDegree_X_add_C (c : K) : (X + Polynomial.C c : K[X]).natDegree = 1 := by
  rw [Polynomial.natDegree_add_eq_left_of_degree_lt (degree_C_lt_X c),
    Polynomial.natDegree_X]

theorem monic_mul_X_add_C (a : ℕ → K) {y : K[X]} (hy : y.Monic) (c : ℕ) :
    (y * X + Polynomial.C (a c)).Monic := by
  have hy0 : y ≠ 0 := hy.ne_zero
  have h1 : (y * X).degree = ((y.natDegree + 1 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_mul, Polynomial.degree_X, Polynomial.degree_eq_natDegree hy0]
    simp
  have hdeg : (Polynomial.C (a c)).degree < (y * X).degree := by
    rw [h1]
    calc (Polynomial.C (a c)).degree ≤ 0 := Polynomial.degree_C_le
      _ < ((y.natDegree + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.succ_pos y.natDegree
  exact (hy.mul Polynomial.monic_X).add_of_left hdeg

theorem natDegree_mul_X_add_C (a : ℕ → K) {y : K[X]} (hy : y.Monic) (c : ℕ) :
    (y * X + Polynomial.C (a c)).natDegree = y.natDegree + 1 := by
  have hy0 : y ≠ 0 := hy.ne_zero
  have h1 : (y * X).natDegree = y.natDegree + 1 := by
    rw [Polynomial.natDegree_mul hy0 Polynomial.X_ne_zero, Polynomial.natDegree_X]
  rw [← h1]
  refine Polynomial.natDegree_add_eq_left_of_degree_lt ?_
  rw [Polynomial.degree_eq_natDegree (mul_ne_zero hy0 Polynomial.X_ne_zero), h1]
  calc (Polynomial.C (a c)).degree ≤ 0 := Polynomial.degree_C_le
    _ < ((y.natDegree + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.succ_pos y.natDegree

theorem fold_monic {n : ℕ} (a : ℕ → K) (y : K[X]) (hy : y.Monic) (l : List (Fin n)) :
    (l.foldl (fun acc i => acc * X + Polynomial.C (a i.val)) y).Monic := by
  induction l generalizing y with
  | nil => simpa using hy
  | cons i l ih =>
    rw [List.foldl_cons]
    exact ih _ (monic_mul_X_add_C a hy i.val)

theorem fold_natDegree {n : ℕ} (a : ℕ → K) (y : K[X]) (hy : y.Monic) (l : List (Fin n)) :
    (l.foldl (fun acc i => acc * X + Polynomial.C (a i.val)) y).natDegree
      = y.natDegree + l.length := by
  induction l generalizing y with
  | nil => simp
  | cons i l ih =>
    rw [List.foldl_cons, ih _ (monic_mul_X_add_C a hy i.val),
      natDegree_mul_X_add_C a hy i.val]
    simp only [List.length_cons]
    omega

theorem fold_congr {m : ℕ} (f g : K[X] → Fin m → K[X]) (h : ∀ acc i, f acc i = g acc i)
    (l : List (Fin m)) (y : K[X]) : l.foldl f y = l.foldl g y := by
  induction l generalizing y with
  | nil => rfl
  | cons i l ih => rw [List.foldl_cons, List.foldl_cons, h, ih]

theorem fold_eval {n : ℕ} (a : ℕ → K) (y : K[X]) (x : K) (l : List (Fin n)) :
    Polynomial.eval x (l.foldl (fun acc i => acc * X + Polynomial.C (a i.val)) y)
      = l.foldl (fun v i => v * x + a i.val) (Polynomial.eval x y) := by
  induction l generalizing y with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    simp

theorem hornerPolyK_monic {n : ℕ} (a : ℕ → K) : (hornerPolyK a (n + 1)).Monic := by
  rw [hornerPolyK]
  exact fold_monic a _ (monic_X_add_C (a n)) _

theorem hornerPolyK_natDegree {n : ℕ} (a : ℕ → K) :
    (hornerPolyK a (n + 1)).natDegree = n + 1 := by
  rw [hornerPolyK, fold_natDegree a _ (monic_X_add_C (a n)) _, natDegree_X_add_C]
  simp only [List.length_reverse, List.length_finRange]
  omega

theorem hornerPolyK_eval {n : ℕ} (a : ℕ → K) (x : K) :
    Polynomial.eval x (hornerPolyK a (n + 1))
      = (List.finRange n).reverse.foldl (fun v i => v * x + a i.val) (x + a n) := by
  rw [hornerPolyK, fold_eval]
  have h : Polynomial.eval x (X + Polynomial.C (a n) : K[X]) = x + a n := by
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [h]

/-! #### term evaluation in the `C v` structure -/

variable (v : Valuation K Γ₀)

/-- the value of a variable -/
theorem ev_tv {N : ℕ} (xs : Fin N → C v) (j : Fin N) :
    Term.realize (Sum.elim (dflt v) xs) (LRV.tv j.val j.isLt) = xs j := by
  simp only [LRV.tv, Term.realize_var, Sum.elim_inr, Fin.eta]

/-- `+` of the `VF` sort -/
theorem ev_vfAdd {N : ℕ} (w : Empty ⊕ Fin N → C v) (t u : LRV.Tm N) :
    Term.realize w (LRV.tVFAdd t u) =
      (match Term.realize w t, Term.realize w u with
        | Sum.inl a, Sum.inl b => Sum.inl (a + b)
        | _, _ => cInfty v) := rfl

/-- `×` of the `VF` sort -/
theorem ev_vfMul {N : ℕ} (w : Empty ⊕ Fin N → C v) (t u : LRV.Tm N) :
    Term.realize w (LRV.tVFMul t u) =
      (match Term.realize w t, Term.realize w u with
        | Sum.inl a, Sum.inl b => Sum.inl (a * b)
        | _, _ => cInfty v) := rfl

/-- the value of the variable `j`, from its value in `K` -/
theorem ev_tv_of {N : ℕ} (xs : Fin N → C v) (a : ℕ → K)
    (ha : ∀ i : Fin N, xs i = Sum.inl (a i.val)) (j : Fin N) :
    Term.realize (Sum.elim (dflt v) xs) (LRV.tv j.val j.isLt) = Sum.inl (a j.val) := by
  rw [ev_tv v]
  exact ha j

/-- the value of the Horner fold -/
theorem ev_fold {n N : ℕ} (hn : n ≤ N) (xs : Fin N → C v) (xT : LRV.Tm N) (xc : K)
    (hx : Term.realize (Sum.elim (dflt v) xs) xT = Sum.inl xc) (a : ℕ → K)
    (ha : ∀ i : Fin N, xs i = Sum.inl (a i.val)) (l : List (Fin n))
    (accT : LRV.Tm N) (acc : K)
    (hacc : Term.realize (Sum.elim (dflt v) xs) accT = Sum.inl acc) :
    Term.realize (Sum.elim (dflt v) xs)
      (l.foldl (fun acc i => LRV.tVFAdd (LRV.tVFMul acc xT) (LRV.tv i.val (by omega))) accT)
      = Sum.inl (l.foldl (fun v i => v * xc + a i.val) acc) := by
  induction l generalizing accT acc with
  | nil => simpa using hacc
  | cons i l ih =>
    rw [List.foldl_cons, List.foldl_cons]
    refine ih _ _ ?_
    rw [ev_vfAdd, ev_vfMul, hacc, hx, ev_tv_of v xs a ha ⟨i.val, by omega⟩]

/-- **the load-bearing term-evaluation lemma**: `hornerPoly tVFAdd tVFMul` (with `k = n+1`
coefficients) evaluates to the Horner value of the coefficients -/
theorem realize_hornerPoly {n : ℕ} (xs : Fin (n + 1 + 1) → C v) (a : ℕ → K)
    (ha : ∀ i : Fin (n + 1 + 1), xs i = Sum.inl (a i.val)) :
    Term.realize (Sum.elim (dflt v) xs) (LRV.hornerPoly LRV.tVFAdd LRV.tVFMul (k := n + 1))
      = Sum.inl ((List.finRange n).reverse.foldl
          (fun v i => v * a (n + 1) + a i.val) (a (n + 1) + a n)) := by
  have hpoly : LRV.hornerPoly LRV.tVFAdd LRV.tVFMul (k := n + 1)
      = (List.finRange n).reverse.foldl
          (fun acc i => LRV.tVFAdd (LRV.tVFMul acc (LRV.tv (n + 1) (by omega)))
            (LRV.tv i.val (by omega)))
          (LRV.tVFAdd (LRV.tv (n + 1) (by omega)) (LRV.tv n (by omega))) := rfl
  rw [hpoly]
  refine ev_fold v (n := n) (N := n + 1 + 1) (by omega) xs _ (a (n + 1)) ?_ a ha
    (List.finRange n).reverse _ (a (n + 1) + a n) ?_
  · exact ev_tv_of v xs a ha ⟨n + 1, by omega⟩
  · rw [ev_vfAdd, ev_tv_of v xs a ha ⟨n + 1, by omega⟩,
      ev_tv_of v xs a ha ⟨n, by omega⟩]

/-! #### `vfAlgClosed` -/

theorem acfScheme_vf [IsAlgClosed K] {k : ℕ} (hk : 1 ≤ k) :
    (C v) ⊨ Axioms.acfScheme .vf LRV.tVFZero LRV.tVFAdd LRV.tVFMul k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  simp only [Axioms.acfScheme]
  rw [model_allSorted v]
  intro xs hxs
  have hxs' : ∀ i : Fin (n + 1), ∃ x : K, xs i = mkVF v x := fun i => (hxs i).1 rfl
  let a : ℕ → K := fun i => if h : i < n + 1 then Classical.choose (hxs' ⟨i, h⟩) else 0
  have ha : ∀ i : Fin (n + 1), xs i = Sum.inl (a i.val) := by
    intro i
    have h1 : a i.val = Classical.choose (hxs' ⟨i.val, i.isLt⟩) := dif_pos i.isLt
    rw [h1]
    have h2 := Classical.choose_spec (hxs' ⟨i.val, i.isLt⟩)
    rwa [mkVF] at h2
  have hmonic : (hornerPolyK a (n + 1)).Monic := hornerPolyK_monic a
  have hdeg : (hornerPolyK a (n + 1)).degree ≠ 0 := by
    refine ne_of_gt ?_
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hornerPolyK_natDegree]
    omega
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (hornerPolyK a (n + 1)) hdeg
  prep
  refine ⟨Sum.inl x, ⟨x, ?_⟩, ?_⟩
  · show @Fin.snoc (n + 1) (fun _ => C v) xs (Sum.inl x) (Fin.last (n + 1)) = Sum.inl x
    simp only [Fin.snoc_last]
  · set a' : ℕ → K := Function.update a (n + 1) x with ha'_def
    have ha'_last : a' (n + 1) = x := Function.update_self (n + 1) x a
    have ha'_prev : ∀ i, i < n + 1 → a' i = a i := by
      intro i hi
      exact Function.update_of_ne (show i ≠ n + 1 by omega) x a
    have hs : ∀ i : Fin (n + 1 + 1),
        (@Fin.snoc (n + 1) (fun _ => C v) xs (Sum.inl x)) i = (Sum.inl (a' i.val) : C v) := by
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hj
      · subst hj
        rw [Fin.snoc_castSucc]
        simp only [Fin.val_castSucc]
        rw [ha'_prev j.val j.isLt]
        exact ha j
      · subst hj
        rw [Fin.snoc_last]
        simp only [Fin.val_last]
        rw [ha'_last]
    rw [realize_hornerPoly v (xs := @Fin.snoc (n + 1) (fun _ => C v) xs (Sum.inl x))
      (a := a') hs]
    have hpoly : hornerPolyK a' (n + 1) = hornerPolyK a (n + 1) := by
      rw [hornerPolyK, hornerPolyK, ha'_prev n (by omega)]
      exact fold_congr _ _ (fun acc i => by rw [ha'_prev i.val (by omega)]) _ _
    have hx' : Polynomial.eval x (hornerPolyK a' (n + 1)) = 0 := by
      rw [hpoly]
      exact hx
    have hgoal : (List.finRange n).reverse.foldl
          (fun v i => v * a' (n + 1) + a' i.val) (a' (n + 1) + a' n)
        = Polynomial.eval x (hornerPolyK a' (n + 1)) := by
      rw [hornerPolyK_eval]
      simp only [ha'_last]
    rw [hgoal, hx']

/-- **`vfAlgClosed` holds at the intended structure `C v`** (the `acfScheme .vf` scheme of
Definition 2.2 item 1), for algebraically closed `K` and any valuation -/
theorem model_vfAlgClosed [IsAlgClosed K] : (C v) ⊨ Axioms.vfAlgClosed where
  realize_of_mem φ hφ := by
    obtain ⟨k, hk, rfl⟩ := hφ
    exact acfScheme_vf v hk

end SpecialTransformations.Milestone0.Ob.VFAC

#print axioms SpecialTransformations.Milestone0.Ob.VFAC.realize_hornerPoly
#print axioms SpecialTransformations.Milestone0.Ob.VFAC.acfScheme_vf
#print axioms SpecialTransformations.Milestone0.Ob.VFAC.model_vfAlgClosed

namespace SpecialTransformations.Milestone0.Ob.Fragment

open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.IModel
open SpecialTransformations.Milestone0.Ob.VFAC
open scoped NNReal

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- **everything in `Axioms.ACVF` except `kField` and `kAlgClosed`**, at the general model
`C v` for any valuation on an algebraically closed field -/
theorem model_ACVF_minus_kField [IsAlgClosed K] (v : Valuation K Γ₀) :
    (C v) ⊨ (Axioms.sortAxioms ∪ Axioms.vfField ∪ Axioms.vfAlgClosed ∪ Axioms.rvGroup ∪
      Axioms.preorderRV ∪ Axioms.rvAxioms) := by
  rw [Theory.model_iff]; intro s hs
  simp only [Set.mem_union] at hs
  rcases hs with ((((hs | hs) | hs) | hs) | hs) | hs
  · exact model_of_mem v (model_sortAxioms_all v) hs
  · exact model_of_mem v (model_vfField v) hs
  · exact model_of_mem v (model_vfAlgClosed v) hs
  · exact model_of_mem v (model_rvGroup v) hs
  · exact model_of_mem v (model_preorderRV v) hs
  · exact model_of_mem v (model_rvAxioms_all v) hs

/-- the same at `K = ℂ_[p]`, `v = (PadicComplex.valued p).v` -/
theorem model_ACVF_minus_kField_padic (p : ℕ) [Fact (Nat.Prime p)] :
    (C ((PadicComplex.valued p).v)) ⊨
      (Axioms.sortAxioms ∪ Axioms.vfField ∪ Axioms.vfAlgClosed ∪ Axioms.rvGroup ∪
        Axioms.preorderRV ∪ Axioms.rvAxioms) :=
  model_ACVF_minus_kField ((PadicComplex.valued p).v)

end SpecialTransformations.Milestone0.Ob.Fragment

#print axioms SpecialTransformations.Milestone0.Ob.Fragment.model_ACVF_minus_kField
#print axioms SpecialTransformations.Milestone0.Ob.Fragment.model_ACVF_minus_kField_padic

/-! ## `Γ(S)` is nontrivial at `ℂ_[p]`

The milestone's requirement on the substructure `S` is that `Γ(S)` be nontrivial.  `Γ` is not a
sort of `L_RV` (it is the quotient `RV/Kˣ`), so the statement is made in the standard
`L_RV`-definable form: `S` contains an `RV`-element `t` which is neither `≤ 1` nor `≥ 1`, i.e.
`¬ (1 ≤ t ∧ t ≤ 1)` — the negation of "`t ∈ Kˣ`" read through the preorder (axiom
`leClassOne`).  Taking `S = ⊤` makes the substructure part trivial; the content is that `rv(p)`
has value `1/p ≠ 1`. -/

open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.IModel
open SpecialTransformations.Milestone0.IModel.SpecialTransformations.Milestone0
open scoped NNReal

namespace SpecialTransformations.Milestone0.Ob.Gamma

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- the reading of "`t` has value `≠ 1`" in `L_RV`: `¬ (1 ≤ t ∧ t ≤ 1)` -/
theorem not_class_one_iff (v : Valuation K Γ₀) (x : K) (hx : v x < 1) :
    ¬ (iLe (iRVOne (M := C v)) (mkRV v (some (RVM.rv v x))) ∧
        iLe (mkRV v (some (RVM.rv v x))) (iRVOne (M := C v))) := by
  rintro ⟨-, h2⟩
  obtain ⟨a2, b2, ha2, hb2, hl2⟩ := h2
  simp only [iRVOne, funMap_def, fMap, cRVOne, mkRV, Matrix.cons_val_fin_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Sum.inr.injEq] at ha2 hb2
  rw [← ha2, ← hb2] at hl2
  simp only [RVM.le0, RVM.rvLe, RVM.vrv_rv] at hl2
  rw [Valuation.map_one] at hl2
  exact absurd hl2 (not_le.mpr hx)

/-- **`Γ(S)` is nontrivial**, in the non-vacuous reading: `S` contains an element of
`RV^× = RV ∖ {0, ∞}` — so `t ≠ 0` and `t ≠ ∞` are part of the statement, and `∞ = rv 0`
(which lies in every substructure) cannot witness it — whose value is `≠ 1`, i.e. which is
outside the class of `1` (`¬ (1 ≤ t ∧ t ≤ 1)`). -/
theorem exists_gamma_nontrivial (v : Valuation K Γ₀) (x : K) (hx0 : x ≠ 0) (hx : v x < 1) :
    ∃ (S : LRV.Substructure (C v)),
      ∃ t, (S : Set (C v)) t ∧ iRV t ∧ t ≠ iRVZero (M := C v) ∧ t ≠ iRVInfty (M := C v) ∧
        ¬ (iLe (iRVOne (M := C v)) t ∧ iLe t (iRVOne (M := C v))) := by
  refine ⟨⊤, mkRV v (some (RVM.rv v x)), trivial, ⟨some (RVM.rv v x), rfl⟩, ?_, ?_,
    not_class_one_iff v x hx⟩
  · simp [iRVZero, funMap_def, fMap, cKZero, mkRV]
  · intro h
    simp only [iRVInfty, funMap_def, fMap, cInfty, mkRV, Sum.inr.injEq, Option.some.injEq] at h
    rw [RVM.rv_of_ne (v := v) hx0] at h
    exact absurd h (by simp)


end SpecialTransformations.Milestone0.Ob.Gamma

/-! ### the `p`-adic instantiation -/

namespace SpecialTransformations.Milestone0.Ob.GammaPadic

open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.IModel
open SpecialTransformations.Milestone0.Ob.Gamma
open SpecialTransformations.Milestone0.Ob.GammaPadic
open scoped NNReal

/-- **the value of `p` at `ℂ_[p]` is `1/p`** -/
theorem padic_val_self (p : ℕ) [Fact (Nat.Prime p)] :
    (PadicComplex.valued p).v (p : PadicComplex p) = 1 / (p : ℝ≥0) :=
  PadicComplex.valuation_p p

/-- **Milestone 1b, `Γ(S)` half, verified**: at `K = ℂ_[p]`, `v = (PadicComplex.valued p).v`
there is a substructure `S` (namely `⊤`) with nontrivial `Γ(S)`: an element `t` of
`S ∩ RV^×` (so `t ≠ 0` and `t ≠ ∞`) whose value is `≠ 1`.  A trivial valuation cannot satisfy
this (every element of `RV^×` then has value `1`). -/
theorem exists_gamma_nontrivial_padic (p : ℕ) [hp : Fact (Nat.Prime p)] :
    ∃ (S : LRV.Substructure (C ((PadicComplex.valued p).v))),
      ∃ t, (S : Set (C ((PadicComplex.valued p).v))) t ∧ iRV t ∧
        t ≠ iRVZero (M := C ((PadicComplex.valued p).v)) ∧
        t ≠ iRVInfty (M := C ((PadicComplex.valued p).v)) ∧
        ¬ (iLe (iRVOne (M := C ((PadicComplex.valued p).v))) t ∧
            iLe t (iRVOne (M := C ((PadicComplex.valued p).v)))) := by
  have hp2 : (2 : ℝ≥0) ≤ (p : ℝ≥0) := by
    have := hp.out.two_le
    exact_mod_cast this
  have h2 : (0 : ℝ≥0) < 2 := by norm_num
  have hlt : (PadicComplex.valued p).v (p : PadicComplex p) < 1 := by
    rw [padic_val_self p]
    calc (1 : ℝ≥0) / (p : ℝ≥0) ≤ 1 / 2 := one_div_le_one_div_of_le h2 hp2
      _ < 1 := by norm_num
  have hx0 : (p : PadicComplex p) ≠ 0 := by
    have hp0 : (p : ℕ) ≠ 0 := hp.out.ne_zero
    exact_mod_cast hp0
  exact exists_gamma_nontrivial _ (p : PadicComplex p) hx0 hlt

end SpecialTransformations.Milestone0.Ob.GammaPadic

#print axioms SpecialTransformations.Milestone0.Ob.Gamma.not_class_one_iff
#print axioms SpecialTransformations.Milestone0.Ob.Gamma.exists_gamma_nontrivial
#print axioms SpecialTransformations.Milestone0.Ob.GammaPadic.exists_gamma_nontrivial_padic

/-! ## The repaired milestone statement

`ACVF_S(0,0)` (Encoding Part 5) is `ACVF(0,0)` plus the atomic diagram of `S`.  By f3 that
theory is unsatisfiable at `ℂ_[p]` for every `S`, because `ACVF(0,0)` contains
`residueCharZero p` while the residue field of `ℂ_[p]` has characteristic `p`.  The repair is
to keep Definition 2.2 (`ACVF`) and drop only the residue-characteristic-zero sentences — the
paper's `ACVF(0,0)` is replaced by `ACVF` with residue characteristic `p`.  Below: the
diagram half (automatic), the assembly of `ACVF` from the two residue-field blocks, and the
two forms of the corrected existence statement. -/

open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.IModel
open SpecialTransformations.Milestone0.Ob.VFAC
open SpecialTransformations.Milestone0.Ob.Gamma
open SpecialTransformations.Milestone0.Ob.GammaPadic
open scoped NNReal

namespace SpecialTransformations.Milestone0.Ob.Milestone

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- the fragment of `ACVF` verified in this file: everything except `kField`, `kAlgClosed` -/
def FRAG : LRV.Theory :=
  Axioms.sortAxioms ∪ Axioms.vfField ∪ Axioms.vfAlgClosed ∪ Axioms.rvGroup ∪
    Axioms.preorderRV ∪ Axioms.rvAxioms

/-- **`FRAG` is exactly `ACVF` minus `kField` and `kAlgClosed`**, as a set of sentences -/
theorem ACVF_eq_FRAG_union :
    Axioms.ACVF = FRAG ∪ Axioms.kField ∪ Axioms.kAlgClosed := by
  ext s
  simp only [FRAG, Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

/-- **`ACVF` from the two residue-field blocks**: everything else is already verified -/
theorem model_ACVF_of_residue_blocks [IsAlgClosed K] (v : Valuation K Γ₀)
    (hk : (C v) ⊨ Axioms.kField) (hka : (C v) ⊨ Axioms.kAlgClosed) :
    (C v) ⊨ Axioms.ACVF := by
  rw [Theory.model_iff]
  intro s hs
  rw [Axioms.ACVF, Set.mem_union] at hs
  rcases hs with hs | hs
  · exact model_of_mem v (model_sortAxioms_all v) hs
  · rw [Axioms.ACVFpaper, Set.mem_union] at hs
    rcases hs with hs | hs
    · rw [Set.mem_union, Set.mem_union, Set.mem_union, Set.mem_union, Set.mem_union] at hs
      rcases hs with ((((hs | hs) | hs) | hs) | hs) | hs
      · exact model_of_mem v (model_vfField v) hs
      · exact model_of_mem v (model_vfAlgClosed v) hs
      · exact model_of_mem v (model_rvGroup v) hs
      · exact model_of_mem v hk hs
      · exact model_of_mem v hka hs
      · exact model_of_mem v (model_preorderRV v) hs
    · exact model_of_mem v (model_rvAxioms_all v) hs

/-- the atomic diagram of a substructure is realized by the ambient structure -/
theorem realize_atomicDiagram {M : Type*} [LRV.Structure M] (S : LRV.Substructure M) :
    M ⊨ SubstructureTheory.atomicDiagram S := by
  refine ⟨fun φ hφ => ?_⟩
  rcases hφ with ⟨-, h⟩ | ⟨ψ, -, rfl, h⟩
  · exact h
  · simpa using h

/-- a model of `ACVF` expanded by constants for `S` satisfies `ACVF` plus the diagram of `S`:
this is the repaired `ACVF_S` with `ACVF(0,0)` replaced by Definition 2.2 -/
theorem model_ACVF_diagram {M : Type*} [LRV.Structure M] (h : M ⊨ Axioms.ACVF)
    (S : LRV.Substructure M) :
    M ⊨ ((LRV.lhomWithConstants (S : Set M)).onTheory Axioms.ACVF ∪
      SubstructureTheory.atomicDiagram S) :=
  Theory.model_union_iff.mpr
    ⟨(LHom.onTheory_model (LRV.lhomWithConstants (S : Set M)) (T := Axioms.ACVF)).mpr h,
      realize_atomicDiagram S⟩

/-- **unconditional corrected milestone statement at `ℂ_[p]`**: there are a carrier and a
substructure `S` with `Γ(S)` nontrivial which satisfy Definition 2.2 together with the atomic
diagram of `S` (i.e. `ACVF_S` with `ACVF(0,0)` replaced by `ACVF`; `ACVF(0,0)` itself is
refuted at `ℂ_[p]` by `Ob.Padic.not_model_ACVF_S_padic`). -/
theorem milestone_unconditional (p : ℕ) [hp : Fact (Nat.Prime p)] :
    ∃ (S : LRV.Substructure (C ((PadicComplex.valued p).v))),
      (C ((PadicComplex.valued p).v)) ⊨
        ((LRV.lhomWithConstants (S : Set (C ((PadicComplex.valued p).v)))).onTheory FRAG ∪
          SubstructureTheory.atomicDiagram S) ∧
      ∃ t, (S : Set (C ((PadicComplex.valued p).v))) t ∧ iRV t ∧
        t ≠ iRVZero (M := C ((PadicComplex.valued p).v)) ∧
        t ≠ iRVInfty (M := C ((PadicComplex.valued p).v)) ∧
        ¬ (iLe (iRVOne (M := C ((PadicComplex.valued p).v))) t ∧
            iLe t (iRVOne (M := C ((PadicComplex.valued p).v)))) := by
  obtain ⟨S, t, hmem, hRV, hne0, hnei, hnontriv⟩ := exists_gamma_nontrivial_padic p
  refine ⟨S, ?_, t, hmem, hRV, hne0, hnei, hnontriv⟩
  refine Theory.model_union_iff.mpr ⟨?_, ?_⟩
  · exact (LHom.onTheory_model (LRV.lhomWithConstants (S : Set (C ((PadicComplex.valued p).v)))) (T := FRAG)).mpr
      (Ob.Fragment.model_ACVF_minus_kField_padic p)
  · refine ⟨fun φ hφ => ?_⟩
    rcases hφ with ⟨-, h⟩ | ⟨ψ, -, rfl, h⟩
    · exact h
    · simpa using h

/-- **the corrected milestone from the two residue-field blocks**: as soon as `kField` and
`kAlgClosed` hold at the `p`-adic model, `ACVF` (Definition 2.2) together with the atomic
diagram of a substructure with nontrivial `Γ(S)` exists at `ℂ_[p]` -/
theorem milestone_of_residue_blocks (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hk : (C ((PadicComplex.valued p).v)) ⊨ Axioms.kField)
    (hka : (C ((PadicComplex.valued p).v)) ⊨ Axioms.kAlgClosed) :
    ∃ (S : LRV.Substructure (C ((PadicComplex.valued p).v))),
      (C ((PadicComplex.valued p).v)) ⊨
        ((LRV.lhomWithConstants (S : Set (C ((PadicComplex.valued p).v)))).onTheory Axioms.ACVF ∪
          SubstructureTheory.atomicDiagram S) ∧
      ∃ t, (S : Set (C ((PadicComplex.valued p).v))) t ∧ iRV t ∧
        t ≠ iRVZero (M := C ((PadicComplex.valued p).v)) ∧
        t ≠ iRVInfty (M := C ((PadicComplex.valued p).v)) ∧
        ¬ (iLe (iRVOne (M := C ((PadicComplex.valued p).v))) t ∧
            iLe t (iRVOne (M := C ((PadicComplex.valued p).v)))) := by
  obtain ⟨S, t, hmem, hRV, hne0, hnei, hnontriv⟩ := exists_gamma_nontrivial_padic p
  exact ⟨S, model_ACVF_diagram
    (model_ACVF_of_residue_blocks _ hk hka) S, t, hmem, hRV, hne0, hnei, hnontriv⟩


/-- **the milestone's exact shape**, with the corrected theory: there is a carrier with an
`L_RV`-structure and a substructure `S` such that the carrier satisfies the fragment `FRAG`
(of `ACVF`) together with the atomic diagram of `S`, and `Γ(S)` is nontrivial.  The only
deviation from the task's statement is that `ACVF(0,0)` is replaced by `ACVF` — forced by
`Ob.Padic.not_model_ACVF_S_padic`, which shows the stated version is unsatisfiable at
`ℂ_[p]` for every `S`. -/
theorem exists_model_with_nontrivial_gamma (p : ℕ) [hp : Fact (Nat.Prime p)] :
    ∃ (M : Type) (_ : LRV.Structure M) (S : LRV.Substructure M),
      M ⊨ ((LRV.lhomWithConstants (S : Set M)).onTheory FRAG ∪
        SubstructureTheory.atomicDiagram S) ∧
      ∃ t, (S : Set M) t ∧ iRV t ∧ t ≠ iRVZero (M := M) ∧ t ≠ iRVInfty (M := M) ∧
        ¬ (iLe (iRVOne (M := M)) t ∧ iLe t (iRVOne (M := M))) := by
  obtain ⟨S, hS, t, hmem, hRV, hne0, hnei, hnt⟩ := milestone_unconditional p
  exact ⟨C ((PadicComplex.valued p).v), inferInstance, S, hS, t, hmem, hRV, hne0, hnei, hnt⟩

end SpecialTransformations.Milestone0.Ob.Milestone

#print axioms SpecialTransformations.Milestone0.Ob.Milestone.model_ACVF_of_residue_blocks
#print axioms SpecialTransformations.Milestone0.Ob.Milestone.milestone_unconditional
#print axioms SpecialTransformations.Milestone0.Ob.Milestone.milestone_of_residue_blocks

#print axioms SpecialTransformations.Milestone0.Ob.Milestone.exists_model_with_nontrivial_gamma

#print axioms SpecialTransformations.Milestone0.Ob.Milestone.ACVF_eq_FRAG_union

