module

/-
Milestone 0 for: Yimu Yin, "Special transformations in algebraically closed valued fields",
Annals of Pure and Applied Logic (2010), arXiv:1006.2467.

The paper's language `L_RV` (Definition 2.1), the theory `ACVF` (Definition 2.2), the
theory `ACVF_S(0,0)`, and the statements of quantifier elimination (Theorem 2.3) and
C-minimality (Theorem 2.8), encoded in Mathlib's one-sorted first-order model theory by
putting the sorts of `L_RV` on a single tagged carrier with unary sort predicates.

This file is self-contained: its only import is `Mathlib`.  Check it with

    lean VFAlgClosed.lean

It is `Milestone0/Encoding.lean` (repository commit d608de6) with the two `sorry`ed target
theorems of its Part 6 deleted, plus the material of Parts 8 and 11 added by swarm member
m6: **`vfAlgClosed` at the intended structure on `K ⊕ RV₀ v`** for an algebraically closed
field `K` and any valuation `v : Valuation K Γ₀`.  There is no `sorry` and no new axiom in
this file; the axiom footprint of every headline theorem is printed at the end.
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
  /-- the constant `0` of the `RV` sort (an element of `K`) -/
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
/-- The paper's `∞` is `rv(0) = 0`, the absorbing element of the `RV` sort -/
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

/-- the interpretation of the paper's `∞`, i.e. of `0` of the `RV` sort -/
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
namespace SpecialTransformations
namespace Milestone0

/-- the interpretation of `-` of the `RV` sort (not provided in Part 6) -/
def iKNeg {M : Type*} [LRV.Structure M] (x : M) : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) Fn.kNeg ![x]

/-- the interpretation of `0` of the `VF` sort (not provided in Part 6) -/
def iVFZero {M : Type*} [LRV.Structure M] : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfZero fun i => i.elim0

/-- the interpretation of `1` of the `VF` sort (not provided in Part 6) -/
def iVFOne {M : Type*} [LRV.Structure M] : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfOne fun i => i.elim0

/-! ## Part 8. Unfolding the semantics of the encoded axioms

The encoded axioms are `LRV.Sentence`s built from `allSorted` (guarded universal
quantifiers), `exSorted` (guarded existential quantifiers) and the term constructors of
`LRV`.  This part reduces `M ⊨ φ` for such a sentence to a statement about the values of
the symbols on the carrier, for an arbitrary `LRV.Structure M`.  Part 9 uses it to analyse
`Axioms.ACVF`.
-/

namespace Sem

open FirstOrder FirstOrder.Language

variable {M : Type*} [LRV.Structure M]

/-- the assignment that sends the variables `Fin k` to the values `xs` -/
abbrev rho {k : ℕ} (xs : Fin k → M) : Empty ⊕ Fin k → M := Sum.elim default xs

/-- the `![x]` and `fun _ => x` forms of a unary relation agree -/
theorem relMap_one_fun (r : LRV.Relations 1) (x : M) :
    Structure.RelMap r ![x] ↔ Structure.RelMap r (fun _ => x) := by
  have key : ![x] = (fun _ => x) := by
    funext i
    fin_cases i
    rfl
  rw [key]

theorem relMap_two_fun (r : LRV.Relations 2) (x y : M) :
    Structure.RelMap r ![x, y] ↔ Structure.RelMap r (fun i => ![x, y] i) := Iff.rfl

@[simp] theorem ev_tv {k : ℕ} (xs : Fin k → M) (i : Fin k) :
    Term.realize (rho xs) (LRV.tv i.val i.isLt) = xs i := by
  simp [LRV.tv, rho]

/-- evaluation of an arity-`0` function symbol -/
theorem ev_fun0 {k : ℕ} (xs : Fin k → M) (f : Fn 0) :
    Term.realize (rho xs) (Term.func f (fun i => i.elim0) : LRV.Term (Empty ⊕ Fin k))
      = Structure.funMap (L := LRV) f (fun i : Fin 0 => i.elim0) := by
  have key : Term.realize (rho xs)
        (Term.func f (fun i => i.elim0) : LRV.Term (Empty ⊕ Fin k))
      = Structure.funMap (L := LRV) f
        (fun i : Fin 0 => Term.realize (rho xs) (Fin.elim0 i)) := rfl
  rw [key]
  congr 1
  funext i
  exact i.elim0

@[simp] theorem ev_rvZero {k : ℕ} (xs : Fin k → M) :
    Term.realize (rho xs) (LRV.tRVZero (n := k)) = iRVZero := by
  rw [LRV.tRVZero, ev_fun0]
  rfl

@[simp] theorem ev_rvOne {k : ℕ} (xs : Fin k → M) :
    Term.realize (rho xs) (LRV.tRVOne (n := k)) = iRVOne := by
  rw [LRV.tRVOne, ev_fun0]
  rfl

@[simp] theorem ev_rvInfty {k : ℕ} (xs : Fin k → M) :
    Term.realize (rho xs) (LRV.tRVInfty (n := k)) = iRVInfty := by
  rw [LRV.tRVInfty, LRV.tRVZero, ev_fun0]
  rfl

@[simp] theorem ev_vfZero {k : ℕ} (xs : Fin k → M) :
    Term.realize (rho xs) (LRV.tVFZero (n := k)) = iVFZero := by
  rw [LRV.tVFZero, ev_fun0]
  rfl

@[simp] theorem ev_vfOne {k : ℕ} (xs : Fin k → M) :
    Term.realize (rho xs) (LRV.tVFOne (n := k)) = iVFOne := by
  rw [LRV.tVFOne, ev_fun0]
  rfl

/-- the value of a binary term constructor -/
theorem ev_bin {k : ℕ} (xs : Fin k → M) (f : Fn 2) (t u : LRV.Tm k) :
    Term.realize (rho xs) (Term.func f ![t, u] : LRV.Term (Empty ⊕ Fin k))
      = Structure.funMap (L := LRV) f
        ![Term.realize (rho xs) t, Term.realize (rho xs) u] := by
  have key : Term.realize (rho xs) (Term.func f ![t, u] : LRV.Term (Empty ⊕ Fin k))
      = Structure.funMap (L := LRV) f
        (fun i : Fin 2 => Term.realize (rho xs) (![t, u] i)) := rfl
  rw [key]
  have h2 : (fun i : Fin 2 => Term.realize (rho xs) (![t, u] i))
      = ![Term.realize (rho xs) t, Term.realize (rho xs) u] := by
    funext i
    fin_cases i <;> rfl
  rw [h2]

/-- the value of a unary term constructor -/
theorem ev_un {k : ℕ} (xs : Fin k → M) (f : Fn 1) (t : LRV.Tm k) :
    Term.realize (rho xs) (Term.func f ![t] : LRV.Term (Empty ⊕ Fin k))
      = Structure.funMap (L := LRV) f ![Term.realize (rho xs) t] := by
  have key : Term.realize (rho xs) (Term.func f ![t] : LRV.Term (Empty ⊕ Fin k))
      = Structure.funMap (L := LRV) f
        (fun i : Fin 1 => Term.realize (rho xs) (![t] i)) := rfl
  rw [key]
  have h1 : (fun i : Fin 1 => Term.realize (rho xs) (![t] i))
      = ![Term.realize (rho xs) t] := by
    funext i
    fin_cases i
    rfl
  rw [h1]

@[simp] theorem ev_vfAdd {k : ℕ} (xs : Fin k → M) (t u : LRV.Tm k) :
    Term.realize (rho xs) (LRV.tVFAdd t u)
      = iVFAdd (Term.realize (rho xs) t) (Term.realize (rho xs) u) :=
  ev_bin xs Fn.vfAdd t u

@[simp] theorem ev_vfNeg {k : ℕ} (xs : Fin k → M) (t : LRV.Tm k) :
    Term.realize (rho xs) (LRV.tVFNeg t) = iVFNeg (Term.realize (rho xs) t) :=
  ev_un xs Fn.vfNeg t

@[simp] theorem ev_vfMul {k : ℕ} (xs : Fin k → M) (t u : LRV.Tm k) :
    Term.realize (rho xs) (LRV.tVFMul t u)
      = iVFMul (Term.realize (rho xs) t) (Term.realize (rho xs) u) :=
  ev_bin xs Fn.vfMul t u

@[simp] theorem ev_rvMul {k : ℕ} (xs : Fin k → M) (t u : LRV.Tm k) :
    Term.realize (rho xs) (LRV.tRVMul t u)
      = iRVMul (Term.realize (rho xs) t) (Term.realize (rho xs) u) :=
  ev_bin xs Fn.rvMul t u

@[simp] theorem ev_kAdd {k : ℕ} (xs : Fin k → M) (t u : LRV.Tm k) :
    Term.realize (rho xs) (LRV.tKAdd t u)
      = iKAdd (Term.realize (rho xs) t) (Term.realize (rho xs) u) :=
  ev_bin xs Fn.kAdd t u

@[simp] theorem ev_kNeg {k : ℕ} (xs : Fin k → M) (t : LRV.Tm k) :
    Term.realize (rho xs) (LRV.tKNeg t) = iKNeg (Term.realize (rho xs) t) :=
  ev_un xs Fn.kNeg t

@[simp] theorem ev_rvMap {k : ℕ} (xs : Fin k → M) (t : LRV.Tm k) :
    Term.realize (rho xs) (LRV.tRv t) = iRv (Term.realize (rho xs) t) :=
  ev_un xs Fn.rvMap t

@[simp] theorem real_memVF {k : ℕ} (xs : Fin k → M) (t : LRV.Tm k) :
    (LRV.pVF t).Realize (default : Empty → M) xs ↔ iVF (Term.realize (rho xs) t) := by
  have key : (LRV.pVF t).Realize (default : Empty → M) xs
      = iVF (Term.realize (rho xs) t) := by
    show Structure.RelMap (L := LRV) Rel.memVF (fun i : Fin 1 => Term.realize (rho xs) (![t] i))
      = Structure.RelMap (L := LRV) Rel.memVF ![Term.realize (rho xs) t]
    have h1 : (fun i : Fin 1 => Term.realize (rho xs) (![t] i))
        = ![Term.realize (rho xs) t] := by
      funext i
      fin_cases i
      rfl
    rw [h1]
  rw [key]

@[simp] theorem real_memRV {k : ℕ} (xs : Fin k → M) (t : LRV.Tm k) :
    (LRV.pRVsort t).Realize (default : Empty → M) xs ↔ iRV (Term.realize (rho xs) t) := by
  have key : (LRV.pRVsort t).Realize (default : Empty → M) xs
      = iRV (Term.realize (rho xs) t) := by
    show Structure.RelMap (L := LRV) Rel.memRV (fun i : Fin 1 => Term.realize (rho xs) (![t] i))
      = Structure.RelMap (L := LRV) Rel.memRV ![Term.realize (rho xs) t]
    have h1 : (fun i : Fin 1 => Term.realize (rho xs) (![t] i))
        = ![Term.realize (rho xs) t] := by
      funext i
      fin_cases i
      rfl
    rw [h1]
  rw [key]

@[simp] theorem real_units {k : ℕ} (xs : Fin k → M) (t : LRV.Tm k) :
    (LRV.pUnits t).Realize (default : Empty → M) xs ↔ iUnits (Term.realize (rho xs) t) := by
  have key : (LRV.pUnits t).Realize (default : Empty → M) xs
      = iUnits (Term.realize (rho xs) t) := by
    show Structure.RelMap (L := LRV) Rel.memUnits (fun i : Fin 1 => Term.realize (rho xs) (![t] i))
      = Structure.RelMap (L := LRV) Rel.memUnits ![Term.realize (rho xs) t]
    have h1 : (fun i : Fin 1 => Term.realize (rho xs) (![t] i))
        = ![Term.realize (rho xs) t] := by
      funext i
      fin_cases i
      rfl
    rw [h1]
  rw [key]

@[simp] theorem real_le {k : ℕ} (xs : Fin k → M) (t u : LRV.Tm k) :
    (LRV.pLe t u).Realize (default : Empty → M) xs ↔
      iLe (Term.realize (rho xs) t) (Term.realize (rho xs) u) := by
  have key : (LRV.pLe t u).Realize (default : Empty → M) xs
      = iLe (Term.realize (rho xs) t) (Term.realize (rho xs) u) := by
    show Structure.RelMap (L := LRV) Rel.rvLe (fun i : Fin 2 => Term.realize (rho xs) (![t, u] i))
      = Structure.RelMap (L := LRV) Rel.rvLe ![Term.realize (rho xs) t, Term.realize (rho xs) u]
    have h2 : (fun i : Fin 2 => Term.realize (rho xs) (![t, u] i))
        = ![Term.realize (rho xs) t, Term.realize (rho xs) u] := by
      funext i
      fin_cases i <;> rfl
    rw [h2]
  rw [key]

@[simp] theorem real_eq {k : ℕ} (xs : Fin k → M) (t u : LRV.Tm k) :
    (LRV.pEq t u).Realize (default : Empty → M) xs ↔
      Term.realize (rho xs) t = Term.realize (rho xs) u := by
  rw [LRV.pEq, FirstOrder.Language.BoundedFormula.realize_bdEqual]

@[simp] theorem real_sortPred_vf {k : ℕ} (xs : Fin k → M) (t : LRV.Tm k) :
    (LRV.sortPred .vf t).Realize (default : Empty → M) xs ↔ iVF (Term.realize (rho xs) t) :=
  real_memVF xs t

@[simp] theorem real_sortPred_rv {k : ℕ} (xs : Fin k → M) (t : LRV.Tm k) :
    (LRV.sortPred .rv t).Realize (default : Empty → M) xs ↔ iRV (Term.realize (rho xs) t) :=
  real_memRV xs t

theorem realize_sortedHyps_aux {k : ℕ} (ss : Fin k → SortTag) (l : List (Fin k))
    (xs : Fin k → M) :
    (l.foldr (fun i acc => LRV.sortPred (ss i) (LRV.tv i.val i.isLt) ⊓ acc) ⊤).Realize
        (default : Empty → M) xs ↔
      ∀ i ∈ l, (LRV.sortPred (ss i) (LRV.tv i.val i.isLt)).Realize (default : Empty → M) xs := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem realize_sortedHyps {k : ℕ} (ss : Fin k → SortTag) (xs : Fin k → M) :
    (LRV.sortedHyps ss).Realize (default : Empty → M) xs ↔
      ∀ i : Fin k, (LRV.sortPred (ss i) (LRV.tv i.val i.isLt)).Realize (default : Empty → M) xs := by
  rw [LRV.sortedHyps, realize_sortedHyps_aux]
  exact ⟨fun h i => h i (List.mem_finRange i), fun h i _ => h i⟩

theorem alls_iff {k : ℕ} (ψ : LRV.Bf k) :
    M ⊨ (FirstOrder.Language.BoundedFormula.alls ψ : LRV.Sentence) ↔
      ∀ xs : Fin k → M, ψ.Realize (default : Empty → M) xs :=
  FirstOrder.Language.BoundedFormula.realize_alls

/-- **`M ⊨ allSorted ss φ` unfolded**: for every tuple from the sorts `ss`, `φ` holds. -/
theorem model_allSorted_iff {k : ℕ} (ss : Fin k → SortTag) (φ : LRV.Bf k) :
    M ⊨ LRV.allSorted ss φ ↔
      ∀ xs : Fin k → M,
        (∀ i : Fin k, (LRV.sortPred (ss i) (LRV.tv i.val i.isLt)).Realize
          (default : Empty → M) xs) →
        φ.Realize (default : Empty → M) xs := by
  have h1 : M ⊨ LRV.allSorted ss φ ↔
      ∀ xs : Fin k → M, (LRV.sortedHyps ss ⟹ φ).Realize (default : Empty → M) xs :=
    FirstOrder.Language.BoundedFormula.realize_alls
  refine h1.trans (forall_congr' fun xs => ?_)
  exact (FirstOrder.Language.BoundedFormula.realize_imp).trans
    (imp_congr (realize_sortedHyps ss xs) Iff.rfl)

@[simp] theorem real_exSorted_rv {k : ℕ} (xs : Fin k → M) (φ : LRV.Bf (k + 1)) :
    (LRV.exSorted .rv φ).Realize (default : Empty → M) xs ↔
      ∃ a : M, iRV a ∧ φ.Realize (default : Empty → M) (Fin.snoc xs a) := by
  have h := FirstOrder.Language.BoundedFormula.realize_ex
    (θ := LRV.sortPred .rv (LRV.tv k (Nat.lt_succ_self k)) ⊓ φ)
    (v := (default : Empty → M)) (xs := xs)
  refine h.trans (exists_congr fun a => ?_)
  have h2 : (LRV.sortPred .rv (LRV.tv k (Nat.lt_succ_self k))).Realize
      (default : Empty → M) (Fin.snoc xs a) ↔ iRV a := by
    rw [real_sortPred_rv]
    have htv : Term.realize (rho (Fin.snoc xs a)) (LRV.tv k (Nat.lt_succ_self k)) = a := by
      simp only [LRV.tv, rho, Term.realize_var, Sum.elim_inr]
      exact Fin.snoc_last (α := fun _ => M) a xs
    rw [htv]
  have h3 : ((LRV.sortPred .rv (LRV.tv k (Nat.lt_succ_self k)) ⊓ φ).Realize
      (default : Empty → M) (Fin.snoc xs a)) ↔
      (iRV a ∧ φ.Realize (default : Empty → M) (Fin.snoc xs a)) := by
    rw [FirstOrder.Language.BoundedFormula.realize_inf, h2]
  exact h3


end Sem

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

/-- The paper's `×` on the whole `RV` sort (axiom 2: `t × 0 = 0`, `∞` absorbing).  The author's
ruling identifies `∞ = rv 0` with the `RV`-sort constant `0`, so the two absorbing cases of the
three-layer reading collapse into one and this *is* `rvMul`. -/
abbrev rv0Mul : RV v → RV v → RV v := fun t s => rvMul t s

/-- The paper's `≤` on the whole `RV` sort: `0 = ∞` is the top element and the order is the one
induced by `vrv` (`le_iff`).  The residue-field zero of the three-layer reading is the same
element as `∞`, so there is no separate bottom and this *is* `rvLe`. -/
abbrev le0 : RV v → RV v → Prop := fun t s => rvLe v t s

/-- `K^×` as a subset of the `RV` sort: the class of `1`, i.e. the residue field's units
(axiom 4).  `0 = ∞` is `none`, so `K = K^× ∪ {0}` is `Kx0 ∪ {none}`. -/
def Kx0 : Set (RV v) := {t | ∃ q : RVUnit v, t = some q ∧ vrv v (some q) = 1}

@[simp] theorem rv0Mul_infty (t : RV v) : rv0Mul v t none = none := rvMul_infty t

theorem rv0Mul_some_rv (x y : K) : rv0Mul v (rv v x) (rv v y) = rv v (x * y) :=
  (rv_mul x y).symm

/-- `b : RV` is not `∞ = 0`. -/
theorem rv_shape {b : RV v} (hb : b ≠ none) : ∃ c : RVUnit v, b = some c := by
  match b, hb with
  | none, h => exact absurd rfl h
  | some c, _ => exact ⟨c, rfl⟩

/-- The group law of `RV^×` at the level of `RVUnit`. -/
theorem rvUnit_mul_comm (a b : RVUnit v) : a * b = b * a := mul_comm a b

theorem rvUnit_mul_assoc (a b c : RVUnit v) : a * b * c = a * (b * c) := mul_assoc a b c

theorem rvUnit_mul_one (a : RVUnit v) : a * 1 = a := mul_one a

theorem rvUnit_inv (a : RVUnit v) : ∃ c : RVUnit v, a * c = 1 := ⟨a⁻¹, mul_inv_cancel a⟩

theorem rv0Mul_some_some (a b : RVUnit v) : rv0Mul v (some a) (some b) = some (a * b) := rfl

theorem le0_refl (t : RV v) : le0 v t t := le_rfl

theorem le0_total (t s : RV v) : le0 v t s ∨ le0 v s t := le_total (vrv v s) (vrv v t)

theorem le0_trans {t s r : RV v} (h1 : le0 v t s) (h2 : le0 v s r) : le0 v t r :=
  le_trans h2 h1

/-- `∞ = rv 0 = 0` is the top element. -/
theorem le0_infty (t : RV v) : le0 v t none := le_infty v t
end Extra
end RVM
end SpecialTransformations

open Polynomial

namespace ACVFResidue

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-- The residue field of the valuation ring of `v`.  This is the paper's `K`
(the field `K^× ∪ {0}` that sits inside the `RV`-sort). -/
abbrev ResidueField : Type _ := IsLocalRing.ResidueField v.valuationSubring

noncomputable instance : Field (ResidueField v) := inferInstanceAs (Field (IsLocalRing.ResidueField v.valuationSubring))

/-- A root in the fraction field of a monic-izable polynomial over the valuation ring is
integral over the valuation ring.  (Used to show that a root of a lift of a polynomial over
the residue field lies in the valuation ring.) -/
theorem isIntegral_of_isUnit_leadingCoeff {F : (v.valuationSubring)[X]}
    (hu : IsUnit F.leadingCoeff) {x : K}
    (hx : F.eval₂ (algebraMap v.valuationSubring K) x = 0) :
    IsIntegral v.valuationSubring x := by
  obtain ⟨u, hu'⟩ := hu
  refine ⟨C ((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) * F,
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one ?_, ?_⟩
  · show ((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) * F.leadingCoeff = 1
    rw [← hu', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  · rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, hx, mul_zero]

/-- **A monic polynomial of positive degree over the residue field has a root.**

The lift of a monic `p` to the valuation ring `𝒪` is made monic-izable (its leading
coefficient is a unit of `𝒪`), so a root `x ∈ K` of its image in `K[X]` is integral over
`𝒪`; since `𝒪` is integrally closed in `K` (Mathlib:
`ValuationSubring.instIsIntegrallyClosed`), `x ∈ 𝒪`; then `rv x` is a root of `p`. -/
theorem exists_root_of_monic [IsAlgClosed K] (p : (ResidueField v)[X]) (hp : p.Monic)
    (hdeg : 1 ≤ p.natDegree) : ∃ y : ResidueField v, p.IsRoot y := by
  classical
  obtain ⟨G, hG⟩ := Polynomial.map_surjective (IsLocalRing.residue v.valuationSubring)
    (IsLocalRing.residue_surjective) p
  -- truncate the lift to degree at most `natDegree p`
  obtain ⟨n, hn⟩ : ∃ n, n = p.natDegree := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : (v.valuationSubring)[X], F = G %ₘ X ^ (n + 1) := ⟨_, rfl⟩
  have hXm : (X ^ (n + 1) : (v.valuationSubring)[X]).Monic := monic_X_pow _
  have hXne : (X ^ (n + 1) : (v.valuationSubring)[X]) ≠ 1 := by
    intro h
    have h1 : (X ^ (n + 1) : (v.valuationSubring)[X]).natDegree = n + 1 := natDegree_X_pow _
    rw [h] at h1
    simp at h1
  have hpn : p.degree < (X ^ (n + 1) : (ResidueField v)[X]).degree := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero, ← hn, Polynomial.degree_X_pow]
    exact_mod_cast Nat.lt_succ_self n
  have hmapX : (X ^ (n + 1) : (v.valuationSubring)[X]).map
      (IsLocalRing.residue v.valuationSubring) = (X ^ (n + 1) : (ResidueField v)[X]) := by
    simp
  have hFmap : F.map (IsLocalRing.residue v.valuationSubring) = p := by
    rw [hF, Polynomial.map_modByMonic _ hXm, hG, hmapX]
    exact (Polynomial.modByMonic_eq_self_iff (monic_X_pow (n + 1))).mpr hpn
  have hFle : F.natDegree ≤ n := by
    have h := Polynomial.natDegree_modByMonic_lt G hXm hXne
    rw [natDegree_X_pow] at h
    rw [hF]; omega
  have hFcoeff : IsLocalRing.residue v.valuationSubring (F.coeff n) = 1 := by
    have h : (F.map (IsLocalRing.residue v.valuationSubring)).coeff n = p.coeff n := by rw [hFmap]
    rw [Polynomial.coeff_map] at h
    rw [h, hn, hp.coeff_natDegree]
  have hFnat : F.natDegree = n := by
    refine le_antisymm hFle (by_contra fun h => ?_)
    rw [not_le] at h
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt h, map_zero] at hFcoeff
    exact zero_ne_one hFcoeff
  have hlc : F.leadingCoeff = F.coeff n := by rw [Polynomial.leadingCoeff, hFnat]
  have hunit : IsUnit F.leadingCoeff := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    have hzero : IsLocalRing.residue v.valuationSubring F.leadingCoeff = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [hlc, hFcoeff] at hzero
    exact one_ne_zero hzero
  have hF0 : F ≠ 0 := fun h => by
    rw [h, Polynomial.leadingCoeff_zero] at hunit
    exact not_isUnit_zero hunit
  -- a root of the image of `F` in `K[X]`
  have hKnat : (F.map (algebraMap v.valuationSubring K)).natDegree = n := by
    rw [Polynomial.natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective (v.valuationSubring) K), hFnat]
  have hn0 : n ≠ 0 := by omega
  have hKne : F.map (algebraMap v.valuationSubring K) ≠ 0 := by
    intro h
    rw [h] at hKnat
    simp at hKnat
    omega
  have hKdeg : (F.map (algebraMap v.valuationSubring K)).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hKne, hKnat]
    exact_mod_cast hn0
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (F.map (algebraMap v.valuationSubring K)) hKdeg
  have hxev : F.eval₂ (algebraMap v.valuationSubring K) x = 0 := by
    rw [← hx, Polynomial.eval_map]
  obtain ⟨y, hy⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := v.valuationSubring) (A := K)).mp
    (isIntegral_of_isUnit_leadingCoeff v hunit hxev)
  refine ⟨IsLocalRing.residue v.valuationSubring y, ?_⟩
  rw [Polynomial.IsRoot.def, ← hFmap, Polynomial.eval_map]
  have hFeval : F.eval y = 0 := by
    have h := hxev
    rw [← hy] at h
    rw [Polynomial.eval₂_at_apply] at h
    exact (FaithfulSMul.algebraMap_injective (v.valuationSubring) K) (by rw [h, map_zero])
  rw [Polynomial.eval₂_at_apply, hFeval, map_zero]

/-- **Axiom 3 of Definition 2.2**: the residue field of an algebraically closed valued
field is algebraically closed. -/
theorem isAlgClosed_residueField [IsAlgClosed K] : IsAlgClosed (ResidueField v) :=
  IsAlgClosed.of_exists_root _ fun p hp hpirr =>
    exists_root_of_monic v p hp hpirr.natDegree_pos

/-- A natural number is zero in the residue field exactly when it is zero, provided the
valuation is `≥ 1` on the positive integers (i.e. provided the residue field has
characteristic `0`). -/
theorem natCast_eq_zero_iff (h : ∀ n : ℕ, n ≠ 0 → (1 : Γ₀) ≤ v (n : K)) (n : ℕ) :
    (n : ResidueField v) = 0 ↔ n = 0 := by
  constructor
  · intro hzero
    by_contra hn
    have hlt : v (n : K) < 1 := by
      have hres : IsLocalRing.residue v.valuationSubring (n : v.valuationSubring) = 0 := by
        rw [map_natCast]
        exact hzero
      have hmem := (IsLocalRing.residue_eq_zero_iff _).mp hres
      rw [Valuation.mem_maximalIdeal_iff] at hmem
      simpa using hmem
    exact absurd (h n hn) (not_le.mpr hlt)
  · rintro rfl
    simp

/-- **Residue characteristic zero.**  The residue field of `v` has characteristic zero iff
every positive integer has valuation `1`, i.e. iff every positive integer is a unit of the
valuation ring.  (This is an extra hypothesis on `v`: it fails for the `p`-adic valuation on
`ℚ` and holds for the trivial valuation, where the residue field *is* `K`.) -/
theorem charZero_residueField_iff :
    CharZero (ResidueField v) ↔ ∀ n : ℕ, n ≠ 0 → (1 : Γ₀) ≤ v (n : K) := by
  constructor
  · intro hc n hn
    by_contra h
    have hlt : v (n : K) < 1 := lt_of_not_ge h
    have hmem : (n : v.valuationSubring) ∈ IsLocalRing.maximalIdeal v.valuationSubring := by
      rw [Valuation.mem_maximalIdeal_iff]
      simpa using hlt
    have hres : IsLocalRing.residue v.valuationSubring (n : v.valuationSubring) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [map_natCast] at hres
    exact hn (hc.cast_injective (by simpa using hres))
  · intro h
    refine ⟨fun a b hab => ?_⟩
    rcases le_total a b with hle | hle
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
      have hk : (k : ResidueField v) = 0 := by
        have h2 : (a : ResidueField v) + (k : ResidueField v) = (a : ResidueField v) + 0 := by
          rw [← Nat.cast_add, ← hab]
          simp
        exact add_left_cancel h2
      have hk0 : k = 0 := (natCast_eq_zero_iff v h k).mp hk
      omega
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
      have hk : (k : ResidueField v) = 0 := by
        have h2 : (b : ResidueField v) + (k : ResidueField v) = (b : ResidueField v) + 0 := by
          rw [← Nat.cast_add, hab]
          simp
        exact add_left_cancel h2
      have hk0 : k = 0 := (natCast_eq_zero_iff v h k).mp hk
      omega

section Bridge

/-- `RV^× = Kˣ / (1 + 𝔪)`, exactly as in `Milestone0/RVModel.lean` (repeated here because a
deliverable of this swarm must be a single file with `import Mathlib` as its only import). -/
abbrev RVUnit : Type _ := Kˣ ⧸ v.valuationSubring.principalUnitGroup

/-- The valuation, as a monoid homomorphism on the units of `K`. -/
noncomputable def vUnits : Kˣ →* Γ₀ˣ where
  toFun u := Units.mk0 (v (u : K)) (by rw [Valuation.ne_zero_iff]; exact Units.ne_zero u)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [Valuation.map_mul]

/-- `vrv` restricted to the group part of the `RV`-sort: the quotient map
`RV^× = Kˣ/(1+𝔪) → Γ`. -/
noncomputable def vrvUnit : RVUnit v →* Γ₀ˣ :=
  QuotientGroup.lift _ (vUnits v) (by
    intro x hx
    rw [MonoidHom.mem_ker, Units.ext_iff]
    exact (Valuation.mem_unitGroup_iff K v x).1 (v.valuationSubring.principal_units_le_units hx))

/-- The paper's `K^×` as a subgroup of `RV^×`: the equivalence class of `1`, i.e. `ker vrv`.
(Axiom 4 of Definition 2.2: `K^× = {x ∈ RV : vrv x = 1}`.) -/
noncomputable def kUnitsSubgroup : Subgroup (RVUnit v) := MonoidHom.ker (vrvUnit v)

abbrev KUnits : Type _ := kUnitsSubgroup v

/-- The units of the valuation ring, mapped to `K^× ⊂ RV^×`. -/
noncomputable def unitGroupToKUnits : v.valuationSubring.unitGroup →* KUnits v where
  toFun u := ⟨QuotientGroup.mk' v.valuationSubring.principalUnitGroup (u : Kˣ), by
    change vrvUnit v (QuotientGroup.mk' v.valuationSubring.principalUnitGroup (u : Kˣ)) = 1
    refine Units.ext ?_
    show v ((u : Kˣ) : K) = 1
    exact (Valuation.mem_unitGroup_iff K v (u : Kˣ)).1 u.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

theorem unitGroupToKUnits_ker :
    (unitGroupToKUnits v).ker =
      v.valuationSubring.principalUnitGroup.comap v.valuationSubring.unitGroup.subtype := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_comap]
  constructor
  · intro h
    have h1 : (QuotientGroup.mk' v.valuationSubring.principalUnitGroup (u : Kˣ)) = 1 :=
      congrArg Subtype.val h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  · intro h
    have h1 : (QuotientGroup.mk' v.valuationSubring.principalUnitGroup (u : Kˣ)) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h
    exact Subtype.ext h1

theorem unitGroupToKUnits_surjective : Function.Surjective (unitGroupToKUnits v) := by
  rintro ⟨q, hq⟩
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective v.valuationSubring.principalUnitGroup q
  have hu : u ∈ v.valuationSubring.unitGroup := by
    rw [Valuation.mem_unitGroup_iff]
    have h := congrArg (fun x : Γ₀ˣ => (x : Γ₀)) hq
    simpa [vrvUnit, vUnits] using h
  exact ⟨⟨u, hu⟩, Subtype.ext rfl⟩

/-- **`K^×` is the residue field's unit group**: the units of the valuation ring modulo the
principal units agree with `ker vrv`. -/
noncomputable def unitsQuotEquivKUnits :
    (v.valuationSubring.unitGroup ⧸
        v.valuationSubring.principalUnitGroup.comap v.valuationSubring.unitGroup.subtype) ≃*
      KUnits v :=
  (QuotientGroup.quotientMulEquivOfEq (unitGroupToKUnits_ker v).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (unitGroupToKUnits v)
      (unitGroupToKUnits_surjective v))

/-- **The units of the internal residue field `K^× ⊂ RV` are the residue field's units**,
i.e. `RV^× ∩ ker vrv ≅ k^×` (`(𝒪 ∖ 𝔪)/(1+𝔪) ≅ k^×` of the paper). -/
noncomputable def kUnitsEquivResidueUnits : KUnits v ≃* (ResidueField v)ˣ :=
  (unitsQuotEquivKUnits v).symm.trans
    v.valuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits

/-- The internal residue field `k = K^× ∪ {0}` of the `RV`-sort as a type: `0` adjoined to
`K^× = ker vrv`.  This is the paper's `K` of Definition 2.1(2d). -/
noncomputable def kToResidue : Option (KUnits v) → ResidueField v
  | none => 0
  | some u => ((kUnitsEquivResidueUnits v u : (ResidueField v)ˣ) : ResidueField v)

theorem kToResidue_bijective : Function.Bijective (kToResidue v) := by
  constructor
  · rintro (_ | ⟨u, hu⟩) (_ | ⟨u', hu'⟩) h
    · rfl
    · exact absurd h.symm (Units.ne_zero (kUnitsEquivResidueUnits v ⟨u', hu'⟩))
    · exact absurd h (Units.ne_zero (kUnitsEquivResidueUnits v ⟨u, hu⟩))
    · have h' : kUnitsEquivResidueUnits v ⟨u, hu⟩ = kUnitsEquivResidueUnits v ⟨u', hu'⟩ :=
        Units.val_injective h
      have h'' : (⟨u, hu⟩ : KUnits v) = ⟨u', hu'⟩ := (kUnitsEquivResidueUnits v).injective h'
      rw [h'']
  · intro x
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨none, rfl⟩
    · obtain ⟨u, hu'⟩ := (kUnitsEquivResidueUnits v).surjective (Units.mk0 x hx)
      refine ⟨some u, ?_⟩
      show ((kUnitsEquivResidueUnits v u : (ResidueField v)ˣ) : ResidueField v) = x
      rw [hu']
      exact Units.val_mk0 hx

/-- `k = K^× ∪ {0}` is the residue field. -/
noncomputable def kEquiv : Option (KUnits v) ≃ ResidueField v :=
  Equiv.ofBijective _ (kToResidue_bijective v)

/-- **The field structure of the residue field, transported to the `RV`-sort's `K`.** -/
noncomputable abbrev kField : Field (Option (KUnits v)) :=
  (kEquiv v).field

section KFieldInstance

attribute [local instance] kField

/-- **Axiom 3 on the `RV`-sort's `K`**: `k = K^× ∪ {0}` is algebraically closed when `K` is. -/
theorem isAlgClosed_k [IsAlgClosed K] : IsAlgClosed (Option (KUnits v)) := by
  haveI : IsAlgClosed (ResidueField v) := isAlgClosed_residueField v
  exact IsAlgClosed.of_ringEquiv (k' := Option (KUnits v)) (e := (kEquiv v).ringEquiv.symm)

end KFieldInstance

end Bridge

end ACVFResidue

/-! ## probe -/
namespace Probe
open SpecialTransformations.Milestone0
variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
example (q : SpecialTransformations.RVM.RVUnit v) (h : SpecialTransformations.RVM.vrvUnit v q = 1) :
    ACVFResidue.KUnits v := ⟨q, h⟩
example : (ACVFResidue.RVUnit v) = (SpecialTransformations.RVM.RVUnit v) := rfl
attribute [local instance] ACVFResidue.kField
example (a b : Option (ACVFResidue.KUnits v)) : a + b = a + b := rfl
end Probe
namespace SpecialTransformations
namespace Milestone0
namespace IModel

open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

attribute [local instance] ACVFResidue.kField

/-! ### the residue field `K = K^× ∪ {0}` inside the `RV` sort, transported from
`Valuation.valuationSubring.ResidueField` along `K^× ≃ k^×` -/

/-- the paper's `K^× ∪ {0}` inside `RV₀`, as a predicate -/
def IK (t : RVM.RV v) : Prop :=
  t = none ∨ ∃ q : RVM.RVUnit v, t = some q ∧ RVM.vrv v (some q) = 1

/-- the `RV^×`-valuation of `RVM` and the residue-field bridge of `ACVFResidue` agree -/
theorem vrv_some_eq_vrvUnit (q : RVM.RVUnit v) :
    RVM.vrv v (some q) = (ACVFResidue.vrvUnit v q : Γ₀) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (v.valuationSubring.principalUnitGroup) q
  rw [RVM.vrv_mk]
  rfl

theorem vrv_some_one_iff (q : RVM.RVUnit v) :
    RVM.vrv v (some q) = 1 ↔ ACVFResidue.vrvUnit v q = 1 := by
  rw [vrv_some_eq_vrvUnit v q]
  exact ⟨fun h => Units.ext h, fun h => by rw [h]; rfl⟩

/-- the residue-field element carried by an `RV₀` element (junk `↦ 0`) -/
noncomputable def kOf (t : RVM.RV v) : Option (ACVFResidue.KUnits v) :=
  match t with
  | none => none
  | some q =>
    if h : RVM.vrv v (some q) = 1 then some ⟨q, (vrv_some_one_iff v q).mp h⟩ else none

/-- the `RV₀` element carrying a residue-field element -/
def ofK (s : Option (ACVFResidue.KUnits v)) : RVM.RV v :=
  match s with
  | none => none
  | some u => some (u : RVM.RVUnit v)

@[simp] theorem kOf_none : kOf v (none : RVM.RV v) = none := rfl
@[simp] theorem kOf_some_none : kOf v (none) = none := rfl
theorem kOf_some_some (q : RVM.RVUnit v) (h : RVM.vrv v (some q) = 1) :
    kOf v (some q) = some ⟨q, (vrv_some_one_iff v q).mp h⟩ := by
  simp only [kOf, dif_pos h]

@[simp] theorem ofK_none : ofK v (none : Option (ACVFResidue.KUnits v)) = none := rfl
@[simp] theorem ofK_some (u : ACVFResidue.KUnits v) :
    ofK v (some u) = some (some (u : RVM.RVUnit v)) := rfl

theorem ik_ofK (s : Option (ACVFResidue.KUnits v)) : IK v (ofK v s) := by
  cases s with
  | none => exact Or.inl rfl
  | some u => exact Or.inr ⟨(u : RVM.RVUnit v), rfl, (vrv_some_one_iff v _).mpr u.2⟩

theorem kOf_ofK (s : Option (ACVFResidue.KUnits v)) : kOf v (ofK v s) = s := by
  cases s with
  | none => rfl
  | some u =>
    show (if h : RVM.vrv v (some (u : RVM.RVUnit v)) = 1 then
        some ⟨(u : RVM.RVUnit v), (vrv_some_one_iff v _).mp h⟩ else none) = some u
    rw [dif_pos ((vrv_some_one_iff v _).mpr u.2)]

theorem ofK_kOf {t : RVM.RV v} (h : IK v t) : ofK v (kOf v t) = t := by
  rcases h with rfl | ⟨q, rfl, hq⟩
  · rfl
  · show ofK v (if h : RVM.vrv v (some q) = 1 then some ⟨q, _⟩ else none) = some q
    rw [dif_pos hq]
    rfl

theorem IK_iff (t : RVM.RV v) : IK v t ↔ ofK v (kOf v t) = t :=
  ⟨ofK_kOf v, fun h => h ▸ ik_ofK v (kOf v t)⟩

/-- `0` of the transferred field structure is `none` (the residue zero) -/
@[simp] theorem kZero_eq : (0 : Option (ACVFResidue.KUnits v)) = none := by
  have h := map_zero (ACVFResidue.kEquiv v).ringEquiv
  simp only [Equiv.ringEquiv_apply] at h
  exact (ACVFResidue.kEquiv v).injective (by rw [h]; rfl)

/-- `1` of the transferred field structure is `some 1` (the class of `1`) -/
@[simp] theorem kOne_eq : (1 : Option (ACVFResidue.KUnits v)) = some 1 := by
  have h := map_one (ACVFResidue.kEquiv v).ringEquiv
  simp only [Equiv.ringEquiv_apply] at h
  have h2 : ACVFResidue.kEquiv v (some (1 : ACVFResidue.KUnits v)) = 1 := by
    show ((ACVFResidue.kUnitsEquivResidueUnits v 1 :
      (ACVFResidue.ResidueField v)ˣ) : ACVFResidue.ResidueField v) = 1
    simp
  exact (ACVFResidue.kEquiv v).injective (by rw [h, h2])

theorem kSome_mul (a b : ACVFResidue.KUnits v) :
    ((some a) * (some b) : Option (ACVFResidue.KUnits v)) = some (a * b) := by
  apply (ACVFResidue.kEquiv v).injective
  have h := map_mul (ACVFResidue.kEquiv v).ringEquiv (some a) (some b)
  simp only [Equiv.ringEquiv_apply] at h
  have h2 : ACVFResidue.kEquiv v (some (a * b)) =
      ACVFResidue.kEquiv v (some a) * ACVFResidue.kEquiv v (some b) := by
    show ((ACVFResidue.kUnitsEquivResidueUnits v (a * b) :
      (ACVFResidue.ResidueField v)ˣ) : ACVFResidue.ResidueField v) = _
    rw [map_mul]; rfl
  rw [h, h2]

/-- the residue field's `+`, total on `RV₀` with junk `0` -/
noncomputable def kAdd (t s : RVM.RV v) : RVM.RV v := ofK v (kOf v t + kOf v s)
/-- the residue field's unary `-` -/
noncomputable def kNeg (t : RVM.RV v) : RVM.RV v := ofK v (-(kOf v t))

/-- The carrier of the intended `L_RV`-structure of the valued field `(K, v)`:
`M = VF ⊕ RV₀` with `VF = K` and `RV₀ = Option (Option (Kˣ ⧸ (1+𝔪)))`. -/
abbrev C : Type _ := K ⊕ RVM.RV v

/-- the `VF`-tag -/
abbrev mkVF (x : K) : C v := Sum.inl x
/-- the `RV`-tag -/
abbrev mkRV (t : RVM.RV v) : C v := Sum.inr t

/-- the paper's `0` (the residue field's zero) -/
abbrev cKZero : C v := Sum.inr none
/-- the paper's `∞ = rv 0` -/
abbrev cInfty : C v := Sum.inr (none)
/-- an element of `RV^×`, i.e. the class of a unit -/
abbrev cUnit (q : RVM.RVUnit v) : C v := Sum.inr (some q)
/-- the paper's `1` in the `RV` sort -/
noncomputable abbrev cRVOne : C v := Sum.inr (RVM.rvOne v)

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
  | _, .rvMul, xs => match xs 0, xs 1 with
      | Sum.inr t, Sum.inr s => mkRV v (RVM.rv0Mul v t s)
      | _, _ => cInfty v
  | _, .kAdd, xs => match xs 0, xs 1 with
      | Sum.inr t, Sum.inr s => mkRV v (kAdd v t s)
      | _, _ => cKZero v
  | _, .kNeg, xs => match xs 0 with
      | Sum.inr t => mkRV v (kNeg v t)
      | _ => cKZero v
  | _, .rvMap, xs => match xs 0 with
      | Sum.inl a => mkRV v (RVM.rv v a)
      | _ => cInfty v

/-- The interpretation of the four relation symbols. -/
noncomputable def rMap : {n : ℕ} → Rel n → (Fin n → C v) → Prop
  | _, .memVF, xs => ∃ x : K, xs 0 = mkVF v x
  | _, .memRV, xs => ∃ t : RVM.RV v, xs 0 = mkRV v t
  | _, .memUnits, xs => ∃ q : RVM.RVUnit v, xs 0 = cUnit v q ∧ RVM.vrv v (some q) = 1
  | _, .rvLe, xs => ∃ t s : RVM.RV v, xs 0 = mkRV v t ∧ xs 1 = mkRV v s ∧ RVM.le0 v t s

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

attribute [local instance] ACVFResidue.kField

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
      ∃ t : RVM.RV v, xs i = mkRV v t := by
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
        (ss i = .rv → ∃ t : RVM.RV v, xs i = mkRV v t)) := by
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
        (ss i = .rv → ∃ t : RVM.RV v, xs i = mkRV v t))) →
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
    SpecialTransformations.Milestone0.LRV.pK, SpecialTransformations.Milestone0.LRV.pRV0,
    SpecialTransformations.Milestone0.LRV.pGtOne,
    SpecialTransformations.Milestone0.LRV.pInK,
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

@[simp] theorem mkRV_inj {t s : RVM.RV v} : mkRV v t = mkRV v s ↔ t = s :=
  ⟨fun h => Sum.inr.injEq .. ▸ h, fun h => by rw [h]⟩

theorem ik_of_hyp {x : C v} {t : RVM.RV v} (ht : x = mkRV v t)
    (hp : (∃ q : RVM.RVUnit v, x = cUnit v q ∧ RVM.vrv v (some q) = 1) ∨ x = Sum.inr none) :
    IK v t := by
  rcases hp with ⟨q, hq, hv⟩ | hz
  · refine Or.inr ⟨q, ?_, hv⟩
    rw [ht] at hq
    exact (mkRV_inj v).mp hq
  · refine Or.inl ?_
    rw [ht] at hz
    exact (mkRV_inj v).mp hz

theorem hyp_of_ik {x : C v} {t : RVM.RV v} (ht : x = mkRV v t) (hik : IK v t) :
    (∃ q : RVM.RVUnit v, x = cUnit v q ∧ RVM.vrv v (some q) = 1) ∨ x = Sum.inr none := by
  rcases hik with rfl | ⟨q, rfl, hv⟩
  · exact Or.inr ht
  · exact Or.inl ⟨q, ht, hv⟩


theorem mkVF_ne_mkRV (x : K) (t : RVM.RV v) : mkVF v x ≠ mkRV v t := by
  simp [mkVF, mkRV]

theorem realize_pUnits {n : ℕ} (i : Fin n) (xs : Fin n → C v) :
    (LRV.pUnits (LRV.tv i.val i.isLt)).Realize (dflt v) xs ↔
      ∃ q : RVM.RVUnit v, xs i = cUnit v q ∧ RVM.vrv v (some q) = 1 := by
  simp only [LRV.pUnits, LRV.tv, FirstOrder.Language.Relations.boundedFormula₁,
    FirstOrder.Language.BoundedFormula.realize_rel,
    FirstOrder.Language.Term.realize_var, Function.comp_apply, Sum.elim_inr,
    Matrix.cons_val_fin_one, RelMap_def, rMap]

/-- `t ∈ K = K^× ∪ {0}` at a variable, in terms of the carrier -/
theorem realize_pInK {n : ℕ} (i : Fin n) (xs : Fin n → C v) :
    (LRV.pInK (LRV.tv i.val i.isLt)).Realize (dflt v) xs ↔
      ∃ t : RVM.RV v, xs i = mkRV v t ∧ IK v t := by
  prep
  constructor
  · rintro (⟨q, hq, hv⟩ | hz)
    · exact ⟨some q, hq, Or.inr ⟨q, rfl, hv⟩⟩
    · exact ⟨none, hz, Or.inl rfl⟩
  · rintro ⟨t, ht, h⟩
    rcases h with rfl | ⟨q, rfl, hv⟩
    · exact Or.inr ht
    · exact Or.inl ⟨q, ht, hv⟩

theorem realize_kHyps {k : ℕ} (xs : Fin k → C v) :
    (LRV.kHyps).Realize (dflt v) xs ↔
      ∀ i : Fin k, ∃ t : RVM.RV v, xs i = mkRV v t ∧ IK v t := by
  rw [LRV.kHyps, realize_foldr_inf]
  exact ⟨fun h i => (realize_pInK v i xs).mp (h i (List.mem_finRange i)),
    fun h i _ => (realize_pInK v i xs).mpr (h i)⟩

/-- **the guarded `K`-universal sentence, unfolded at the intended model** -/
theorem model_allSortedK {k : ℕ} (ss : Fin k → SortTag) (φ : LRV.BoundedFormula Empty k) :
    ((C v) ⊨ LRV.allSortedK ss φ) ↔
      ∀ xs : Fin k → C v,
        (∀ i : Fin k, ((ss i = .vf → ∃ x : K, xs i = mkVF v x) ∧
          (ss i = .rv → ∃ t : RVM.RV v, xs i = mkRV v t))) →
        (∀ i : Fin k, ∃ t : RVM.RV v, xs i = mkRV v t ∧ IK v t) →
        φ.Realize (dflt v) xs := by
  rw [LRV.allSortedK, model_alls v]
  refine forall_congr' (fun xs => ?_)
  rw [FirstOrder.Language.BoundedFormula.realize_imp,
    FirstOrder.Language.BoundedFormula.realize_inf, realize_sortedHyps v ss xs,
    realize_kHyps v xs]
  exact ⟨fun h h1 h2 => h ⟨h1, h2⟩, fun h h1 => h h1.1 h1.2⟩

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
  exact ⟨RVM.rv v a, rfl⟩

theorem model_sdRVZero : (C v) ⊨ Axioms.sdRVZero := by
  simp only [Axioms.sdRVZero]; prep
  exact ⟨none, rfl⟩

theorem model_sdRVOne : (C v) ⊨ Axioms.sdRVOne := by
  simp only [Axioms.sdRVOne]; prep
  exact ⟨RVM.rvOne v, rfl⟩

theorem model_sdRVInfty : (C v) ⊨ Axioms.sdRVInfty := by
  simp only [Axioms.sdRVInfty]; prep
  exact ⟨none, rfl⟩

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
    obtain ⟨a, ha⟩ := (h 0).1 rfl
    obtain ⟨b, hb⟩ := (h 1).1 rfl
    obtain ⟨c, hc⟩ := (h 2).1 rfl
    rw [ha, hb, hc]; exact congrArg (mkVF v) (add_assoc a b c)
  obtain rfl | h3 := h2
  · rw [model_allSorted v]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl
    obtain ⟨b, hb⟩ := (h 1).1 rfl
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
    obtain ⟨a, ha⟩ := (h 0).1 rfl
    obtain ⟨b, hb⟩ := (h 1).1 rfl
    obtain ⟨c, hc⟩ := (h 2).1 rfl
    rw [ha, hb, hc]; exact congrArg (mkVF v) (mul_assoc a b c)
  obtain rfl | h7 := h6
  · rw [model_allSorted v]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl
    obtain ⟨b, hb⟩ := (h 1).1 rfl
    rw [ha, hb]; exact congrArg (mkVF v) (mul_comm a b)
  obtain rfl | h8 := h7
  · rw [model_allSorted v]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl
    rw [ha]; exact congrArg (mkVF v) (mul_one a)
  obtain rfl | h9 := h8
  · rw [model_allSorted v]; intro xs h; prep
    obtain ⟨a, ha⟩ := (h 0).1 rfl
    obtain ⟨b, hb⟩ := (h 1).1 rfl
    obtain ⟨c, hc⟩ := (h 2).1 rfl
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
    simpa [mkVF, fMap] using hh
  rw [RVM.rv_eq_none_iff] at h1
  rw [h1]

theorem model_rvMulHom : (C v) ⊨ Axioms.rvMulHom := by
  simp only [Axioms.rvMulHom]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  obtain ⟨b, hb⟩ := (h 1).1 rfl
  rw [ha, hb]
  show Sum.inr (RVM.rv v (a * b)) = Sum.inr (RVM.rv0Mul v (RVM.rv v a) (RVM.rv v b))
  rw [RVM.rv0Mul_some_rv]

theorem model_rvSurj : (C v) ⊨ Axioms.rvSurj := by
  simp only [Axioms.rvSurj]; rw [model_allSorted v]; intro xs h; prep
  intro hx
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  have ht0 : t ≠ none := by
    intro h0
    exact hx (by rw [ht, h0])
  obtain ⟨x, -, hxq⟩ := RVM.rv_surjective (v := v) (t := t) ht0
  refine ⟨mkVF v x, ⟨x, rfl⟩, ?_⟩
  show Sum.inr (RVM.rv v x) = xs 0
  rw [hxq, ht]

theorem le0_rv_add (a b : K) :
    RVM.le0 v (RVM.rv v a) (RVM.rv v (a + b)) ∨
      RVM.le0 v (RVM.rv v b) (RVM.rv v (a + b)) := by
  simp only [show ∀ x y : K, RVM.le0 v (RVM.rv v x) (RVM.rv v y) =
      (RVM.vrv v (RVM.rv v y) ≤ RVM.vrv v (RVM.rv v x)) from fun x y => rfl, RVM.vrv_rv]
  exact Valuation.map_add' v a b

theorem model_rvUltrametric : (C v) ⊨ Axioms.rvUltrametric := by
  simp only [Axioms.rvUltrametric]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  obtain ⟨b, hb⟩ := (h 1).1 rfl
  rw [ha, hb]
  rcases le0_rv_add v a b with h | h
  · exact Or.inl ⟨RVM.rv v a, RVM.rv v (a + b), rfl, rfl, h⟩
  · exact Or.inr ⟨RVM.rv v b, RVM.rv v (a + b), rfl, rfl, h⟩


/-! ### the multiplicative monoid of the `RV` sort (Definition 2.2 item 2), partial -/

/-- multiplication of the residue field inside `RV₀`, in terms of `kOf`/`ofK` -/
theorem ofK_kOf_mul (t s : RVM.RV v) (ht : IK v t) (hs : IK v s) :
    ofK v (kOf v t * kOf v s) = RVM.rv0Mul v t s := by
  rcases ht with rfl | ⟨q, rfl, hq⟩
  · rcases hs with rfl | ⟨r, rfl, hr⟩
    · rw [kOf_none, ← kZero_eq, mul_zero, kZero_eq]
      rfl
    · rw [kOf_none, kOf_some_some v r hr, ← kZero_eq, zero_mul, kZero_eq]
      rfl
  · rcases hs with rfl | ⟨r, rfl, hr⟩
    · rw [kOf_some_some v q hq, kOf_none, ← kZero_eq, mul_zero, kZero_eq]
      rfl
    · rw [kOf_some_some v q hq, kOf_some_some v r hr, kSome_mul]
      rfl

theorem rv0Mul_ik {t s : RVM.RV v} (ht : IK v t) (hs : IK v s) : IK v (RVM.rv0Mul v t s) := by
  rw [← ofK_kOf_mul v t s ht hs]
  exact ik_ofK v _

theorem rv0Mul_zero {t : RVM.RV v} (h : t ≠ none) : RVM.rv0Mul v t none = none := by
  rcases t with _ | q
  · rfl
  · rfl

theorem rv0Mul_comm (t s : RVM.RV v) : RVM.rv0Mul v t s = RVM.rv0Mul v s t :=
  RVM.rvMul_comm t s

theorem rv0Mul_assoc (t s r : RVM.RV v) :
    RVM.rv0Mul v (RVM.rv0Mul v t s) r = RVM.rv0Mul v t (RVM.rv0Mul v s r) :=
  RVM.rvMul_assoc t s r

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
  have hik := ik_of_hyp v (rfl : _ = mkRV v t) hpK
  rcases hik with rfl | ⟨q, rfl, hq⟩
  · rfl
  · rfl

/-- **`sdUnits` holds at the intended structure**: the predicate `K^×` is borne by
`RV`-sort elements (its actual content is `leClassOne`, i.e. `K^× = ker vrv`). -/
theorem models_sdUnits : (C v) ⊨ Axioms.sdUnits := by
  simp only [Axioms.sdUnits, LRV.allOne]
  rw [model_alls v]
  intro xs
  prep
  rintro ⟨q, hq, -⟩
  exact ⟨some q, hq⟩

/-! ### the preorder on `RV` (Definition 2.2 item 4) -/

theorem le0_mkRV_iff {t s : RVM.RV v} :
    (∃ a b : RVM.RV v, mkRV v t = mkRV v a ∧ mkRV v s = mkRV v b ∧ RVM.le0 v a b) ↔
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
  exact ⟨t, none, rfl, rfl, RVM.le0_infty v t⟩

theorem model_leInftyEq : (C v) ⊨ Axioms.leInftyEq := by
  simp only [Axioms.leInftyEq]; rw [model_allSorted v]; intro xs h; prep
  intro _ hle
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht] at hle ⊢
  obtain ⟨a, b, ha, hb, hab⟩ := hle
  simp only [mkRV, Sum.inr.injEq] at ha hb
  subst ha
  rw [hb]
  rcases b with _ | q
  · rfl
  · exfalso
    have hne : RVM.vrv v (some q) ≠ 0 := by simp [RVM.vrv_some]
    have h0 : RVM.vrv v (some q) = 0 := le_antisymm hab zero_le
    exact hne h0

/-! ### the residue-arithmetic sort-closure sentences -/

/-- `pInK` at a variable, read off from `IK` -/
theorem pInK_of_eq {n : ℕ} (i : Fin n) (xs : Fin n → C v) {t : RVM.RV v}
    (ht : xs i = mkRV v t) (hik : IK v t) :
    (LRV.pInK (LRV.tv i.val i.isLt)).Realize (dflt v) xs :=
  (realize_pInK v i xs).mpr ⟨t, ht, hik⟩

theorem model_sdKAdd : (C v) ⊨ Axioms.sdKAdd := by
  simp only [Axioms.sdKAdd]; rw [model_allSorted v]; intro xs h; prep
  intro h1 h2
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  rw [ht, hs]
  exact hyp_of_ik v rfl (ik_ofK v _)

theorem model_sdKNeg : (C v) ⊨ Axioms.sdKNeg := by
  simp only [Axioms.sdKNeg]; rw [model_allSorted v]; intro xs h; prep
  intro h1
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht]
  exact hyp_of_ik v rfl (ik_ofK v _)

theorem model_sdKMul : (C v) ⊨ Axioms.sdKMul := by
  simp only [Axioms.sdKMul]; rw [model_allSorted v]; intro xs h; prep
  intro h1 h2
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  rw [ht, hs]
  exact hyp_of_ik v rfl (rv0Mul_ik v (ik_of_hyp v ht h1) (ik_of_hyp v hs h2))

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

end SpecialTransformations.Milestone0.IModel


namespace SpecialTransformations
namespace Milestone0
namespace IModel

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0

attribute [local instance] ACVFResidue.kField

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

theorem realize_tRVOne {N : ℕ} (w : Empty → C v) (xs : Fin N → C v) :
    Term.realize (Sum.elim w xs) (LRV.tRVOne (n := N)) = iRVOne (M := C v) := by
  show Structure.funMap (L := LRV) Fn.rvOne (fun i : Fin 0 => i.elim0) = iRVOne (M := C v)
  rfl

theorem realize_tVFOne' {N : ℕ} (w : Empty → C v) (xs : Fin N → C v) :
    Term.realize (Sum.elim w xs) (LRV.tVFOne (n := N)) = mkVF v 1 := by
  show Structure.funMap (L := LRV) Fn.vfOne (fun i : Fin 0 => i.elim0) = mkVF v 1
  rfl

theorem realize_numeral {N : ℕ} (w : Empty → C v) (xs : Fin N → C v) (k : ℕ) :
    Term.realize (Sum.elim w xs) (LRV.tVFNumeral (n := N) k) = mkVF v (k : K) := by
  induction k with
  | zero =>
    have h0 : LRV.tVFNumeral (n := N) 0 = LRV.tVFZero (n := N) := rfl
    rw [h0]
    show Structure.funMap (L := LRV) Fn.vfZero (fun i : Fin 0 => i.elim0) = mkVF v ((0 : ℕ) : K)
    rw [show ((0 : ℕ) : K) = 0 from Nat.cast_zero]
    rfl
  | succ k ih =>
    have hstep : LRV.tVFNumeral (n := N) (k + 1) =
        LRV.tVFAdd (LRV.tVFNumeral (n := N) k) (LRV.tVFOne (n := N)) := rfl
    rw [hstep]
    show Structure.funMap (L := LRV) Fn.vfAdd
      (fun i : Fin 2 => Term.realize (Sum.elim w xs) (![LRV.tVFNumeral (n := N) k,
        LRV.tVFOne (n := N)] i)) = mkVF v ((k + 1 : ℕ) : K)
    have hfun : (fun i : Fin 2 => Term.realize (Sum.elim w xs)
        (![LRV.tVFNumeral (n := N) k, LRV.tVFOne (n := N)] i)) = ![mkVF v (k : K), mkVF v 1] := by
      funext i
      fin_cases i
      · simpa using ih
      · simpa using realize_tVFOne' v w xs
    rw [hfun]
    show mkVF v ((k : K) + 1) = mkVF v ((k + 1 : ℕ) : K)
    rw [Nat.cast_add, Nat.cast_one]

/-- realization of `pGtOne (rv (k·1))`: the paper's `1 < vv(k·1)`, i.e. `v k < 1` -/
theorem real_pGtOne_numeral {N : ℕ} (w : Empty → C v) (xs : Fin N → C v) (k : ℕ) :
    (LRV.pGtOne (LRV.tRv (LRV.tVFNumeral (n := N) k))).Realize w xs ↔ v (k : K) < 1 := by
  have h1 : (LRV.pLe (LRV.tRVOne (n := N)) (LRV.tRv (LRV.tVFNumeral (n := N) k))).Realize w xs ↔
      v (k : K) ≤ 1 := by
    prep
    rw [realize_numeral]
    simp only [mkVF]
    constructor
    · rintro ⟨t, s, ht, hs, hts⟩
      rw [Sum.inr.injEq] at ht hs
      rw [← ht, ← hs] at hts
      simpa [RVM.le0, RVM.rvLe, RVM.vrv_rv, RVM.rvOne, Valuation.map_one] using hts
    · intro h
      exact ⟨RVM.rvOne v, RVM.rv v (k : K), rfl, rfl, by
        simpa [RVM.le0, RVM.rvLe, RVM.vrv_rv, RVM.rvOne, Valuation.map_one] using h⟩
  have h2 : (LRV.pLe (LRV.tRv (LRV.tVFNumeral (n := N) k)) (LRV.tRVOne (n := N))).Realize w xs ↔
      (1 : Γ₀) ≤ v (k : K) := by
    prep
    rw [realize_numeral]
    simp only [mkVF]
    constructor
    · rintro ⟨t, s, ht, hs, hts⟩
      rw [Sum.inr.injEq] at ht hs
      rw [← ht, ← hs] at hts
      simpa [RVM.le0, RVM.rvLe, RVM.vrv_rv, RVM.rvOne, Valuation.map_one] using hts
    · intro h
      exact ⟨RVM.rv v (k : K), RVM.rvOne v, rfl, rfl, by
        simpa [RVM.le0, RVM.rvLe, RVM.vrv_rv, RVM.rvOne, Valuation.map_one] using h⟩
  rw [LRV.pGtOne, FirstOrder.Language.BoundedFormula.realize_inf,
    FirstOrder.Language.BoundedFormula.realize_not, h1, h2]
  exact ⟨fun h => lt_of_not_ge h.2, fun h => ⟨le_of_lt h, not_le.mpr h⟩⟩

/-- **the residue-characteristic-zero sentence, evaluated**: it holds at the intended
model exactly when `p · 1` is a unit of the valuation ring -/
theorem exists_le0_iff (a b : K) :
    (∃ t s : RVM.RV v, (Sum.inr (RVM.rv v a) : C v) = Sum.inr t ∧
      (Sum.inr (RVM.rv v b) : C v) = Sum.inr s ∧ RVM.le0 v t s) ↔ v b ≤ v a := by
  constructor
  · rintro ⟨t, s, ht, hs, hts⟩
    rw [Sum.inr.injEq] at ht hs
    rw [← ht, ← hs] at hts
    simpa [RVM.le0, RVM.rvLe, RVM.vrv_rv] using hts
  · intro h
    exact ⟨_, _, rfl, rfl, by simpa [RVM.le0, RVM.rvLe, RVM.vrv_rv] using h⟩

/-- **the residue-characteristic-zero sentence, evaluated**: it holds at the intended
model exactly when `p · 1` is a unit of the valuation ring -/
theorem model_residueCharZero_iff (k : ℕ) :
    (C v) ⊨ Axioms.residueCharZero k ↔ (1 : Γ₀) ≤ v (k : K) := by
  rw [Axioms.residueCharZero]
  prep
  rw [realize_numeral]
  simp only [mkVF]
  rw [exists_le0_iff v 1 k, exists_le0_iff v k 1, Valuation.map_one]
  constructor
  · intro h
    by_contra hB
    exact h ⟨le_of_lt (lt_of_not_ge hB), hB⟩
  · rintro hB ⟨-, h⟩
    exact h hB

end SpecialTransformations.Milestone0.IModel

/-! ## The `p`-adic complex numbers do not model `ACVF(0,0)`

`ℂ_[p]` is algebraically closed of characteristic `0` and carries the nontrivial valuation
`v = (PadicComplex.valued p).v` with `v p = 1/p < 1`, so `p · 1` is *not* a unit of the
valuation ring: the residue field of `ℂ_[p]` has characteristic `p`, not `0`.  Hence
`Axioms.ACVF00` — which demands `residueCharZero p`, i.e. `1 ≤ v p` — fails at `ℂ_[p]`. -/

namespace SpecialTransformations
namespace Milestone0
namespace IModel

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0

open scoped NNReal

variable {p : ℕ} [hp : Fact p.Prime]

theorem padic_valuation_lt_one : (PadicComplex.valued p).v (p : PadicComplex p) < 1 := by
  rw [PadicComplex.valuation_p]
  have hp2 : (2 : ℝ≥0) ≤ (p : ℝ≥0) := by
    have h2 : 2 ≤ p := hp.out.two_le
    exact_mod_cast h2
  have hp0 : (0 : ℝ≥0) < (p : ℝ≥0) := lt_of_lt_of_le (by norm_num) hp2
  rw [div_lt_one hp0]
  have h1 : (1 : ℕ) < p := hp.out.one_lt
  exact_mod_cast h1

/-- **`residueCharZero p` is false at `ℂ_[p]`** -/
theorem padicComplex_not_residueCharZero :
    ¬ ((C (PadicComplex.valued p).v) ⊨ Axioms.residueCharZero p) := by
  rw [model_residueCharZero_iff, not_le]
  exact padic_valuation_lt_one (p := p)

/-- **`ℂ_[p]` is not a model of `ACVF(0,0)`**: its residue field has characteristic `p` -/
theorem padicComplex_not_model_ACVF00 :
    ¬ ((C (PadicComplex.valued p).v) ⊨ Axioms.ACVF00) := by
  intro h
  have hmem : Axioms.residueCharZero p ∈ Axioms.ACVF00 := by
    rw [Axioms.ACVF00]
    exact Or.inr ⟨p, hp.out, rfl⟩
  exact padicComplex_not_residueCharZero (p := p) ((Theory.model_iff ..).mp h _ hmem)

end SpecialTransformations.Milestone0.IModel

namespace SpecialTransformations
namespace Milestone0
namespace VFPort

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.IModel

attribute [local instance] ACVFResidue.kField

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

theorem iVF_iff {x : C v} : iVF x ↔ ∃ a : K, x = Sum.inl a := Iff.rfl

theorem exists_of_iVF {x : C v} (h : iVF x) : ∃ a : K, x = Sum.inl a := h

theorem iVF_inl (a : K) : iVF (Sum.inl a : C v) := ⟨a, rfl⟩

theorem iVFZero_eq : iVFZero (M := C v) = Sum.inl (0 : K) := rfl

theorem realize_tVFZero {n : ℕ} (xs : Fin n → C v) :
    Term.realize (Sem.rho xs) (LRV.tVFZero (n := n)) = Sum.inl (0 : K) := by
  rw [Sem.ev_vfZero, iVFZero_eq]

/-! ### 11.2 The monic polynomial behind `hornerPoly` -/

open Polynomial

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- the monic polynomial `x^{n+1} + a_n x^n + ⋯ + a_0` in the same Horner shape as
`LRV.hornerPoly` (the value at `0` is immaterial; `acfScheme` is used with `k ≥ 1`) -/
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

/-! ### 11.3 The term `hornerPoly` at the intended structure -/

/-- `exSorted .vf` unfolded: a witness in the `VF` sort -/
theorem real_exSorted_vf {M : Type*} [LRV.Structure M] {k : ℕ} (xs : Fin k → M)
    (φ : LRV.Bf (k + 1)) :
    (LRV.exSorted .vf φ).Realize (default : Empty → M) xs ↔
      ∃ a : M, iVF a ∧ φ.Realize (default : Empty → M) (Fin.snoc xs a) := by
  have h := FirstOrder.Language.BoundedFormula.realize_ex
    (θ := LRV.sortPred .vf (LRV.tv k (Nat.lt_succ_self k)) ⊓ φ)
    (v := (default : Empty → M)) (xs := xs)
  refine h.trans (exists_congr fun a => ?_)
  have htv : Term.realize (Sem.rho (Fin.snoc xs a)) (LRV.tv k (Nat.lt_succ_self k)) = a := by
    simp only [LRV.tv, Sem.rho, Term.realize_var, Sum.elim_inr]
    exact Fin.snoc_last (α := fun _ => M) a xs
  have h2 : (LRV.sortPred .vf (LRV.tv k (Nat.lt_succ_self k))).Realize
      (default : Empty → M) (Fin.snoc xs a) ↔ iVF a := by
    rw [Sem.real_sortPred_vf, htv]
  rw [FirstOrder.Language.BoundedFormula.realize_inf, h2]

variable (v : Valuation K Γ₀)

/-- the value of the variable `j` -/
theorem ev_tv_of {N : ℕ} (xs : Fin N → C v) (a : ℕ → K)
    (ha : ∀ i : Fin N, xs i = Sum.inl (a i.val)) (j : Fin N) :
    Term.realize (Sem.rho xs) (LRV.tv j.val j.isLt) = Sum.inl (a j.val) := by
  rw [Sem.ev_tv]
  exact ha j

/-- the value of the Horner fold -/
theorem ev_fold {n N : ℕ} (hn : n ≤ N) (xs : Fin N → C v) (xT : LRV.Tm N) (xc : K)
    (hx : Term.realize (Sem.rho xs) xT = Sum.inl xc) (a : ℕ → K)
    (ha : ∀ i : Fin N, xs i = Sum.inl (a i.val)) (l : List (Fin n))
    (accT : LRV.Tm N) (acc : K) (hacc : Term.realize (Sem.rho xs) accT = Sum.inl acc) :
    Term.realize (Sem.rho xs)
      (l.foldl (fun acc i => LRV.tVFAdd (LRV.tVFMul acc xT) (LRV.tv i.val (by omega))) accT)
      = Sum.inl (l.foldl (fun v i => v * xc + a i.val) acc) := by
  induction l generalizing accT acc with
  | nil => simpa using hacc
  | cons i l ih =>
    rw [List.foldl_cons, List.foldl_cons]
    refine ih _ _ ?_
    rw [Sem.ev_vfAdd, Sem.ev_vfMul, hacc, hx, ev_tv_of v xs a ha ⟨i.val, by omega⟩]
    rfl

/-- **the load-bearing term-evaluation lemma**: at the intended structure the term
`hornerPoly tVFAdd tVFMul` (with `k = n+1` coefficients) evaluates to the Horner value of
the coefficients -/
theorem realize_hornerPoly {n : ℕ} (xs : Fin (n + 1 + 1) → C v) (a : ℕ → K)
    (ha : ∀ i : Fin (n + 1 + 1), xs i = Sum.inl (a i.val)) :
    Term.realize (Sem.rho xs) (LRV.hornerPoly LRV.tVFAdd LRV.tVFMul (k := n + 1))
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
  · rw [Sem.ev_vfAdd, ev_tv_of v xs a ha ⟨n + 1, by omega⟩,
      ev_tv_of v xs a ha ⟨n, by omega⟩]
    rfl

/-! ### 11.4 `vfAlgClosed` at the intended structure -/

theorem acfScheme_vf (v : Valuation K Γ₀) [IsAlgClosed K] {k : ℕ} (hk : 1 ≤ k) :
    (C v) ⊨ Axioms.acfScheme .vf LRV.tVFZero LRV.tVFAdd LRV.tVFMul k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [Axioms.acfScheme, Sem.model_allSorted_iff]
  intro xs hxs
  have hxs' : ∀ i : Fin (n + 1), iVF (xs i) := by
    intro i
    simpa [LRV.tv] using hxs i
  -- the coefficients of the polynomial, read off the `VF` summand
  let a : ℕ → K := fun i =>
    if h : i < n + 1 then Classical.choose (exists_of_iVF (v := v) (hxs' ⟨i, h⟩)) else 0
  have ha : ∀ i : Fin (n + 1), xs i = Sum.inl (a i.val) := by
    intro i
    have h1 : a i.val = Classical.choose (exists_of_iVF (v := v) (hxs' ⟨i.val, i.isLt⟩)) := dif_pos i.isLt
    rw [h1]
    exact Classical.choose_spec (exists_of_iVF (v := v) (hxs' ⟨i.val, i.isLt⟩))
  -- a root of the corresponding monic polynomial
  have hmonic : (hornerPolyK a (n + 1)).Monic := hornerPolyK_monic a
  have hdeg : (hornerPolyK a (n + 1)).degree ≠ 0 := by
    refine ne_of_gt ?_
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hornerPolyK_natDegree]
    omega
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (hornerPolyK a (n + 1)) hdeg
  rw [real_exSorted_vf]
  refine ⟨Sum.inl x, iVF_inl v x, ?_⟩
  rw [Sem.real_eq, realize_tVFZero]
  -- the tuple with the root adjoined
  set a' : ℕ → K := Function.update a (n + 1) x with ha'_def
  have ha'_last : a' (n + 1) = x := by
    simp only [ha'_def]
    exact Function.update_self (n + 1) x a
  have ha'_prev : ∀ i, i < n + 1 → a' i = a i := by
    intro i hi
    simp only [ha'_def]
    exact Function.update_of_ne (show i ≠ n + 1 by omega) x a
  have hs : ∀ i : Fin (n + 1 + 1),
      (@Fin.snoc (n + 1) (fun _ => C v) xs (Sum.inl x)) i
        = (Sum.inl (a' i.val) : C v) := by
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
  rw [show (Fin.snoc xs (Sum.inl x) : Fin (n + 1 + 1) → C v)
      = @Fin.snoc (n + 1) (fun _ => C v) xs (Sum.inl x) from rfl]
  rw [realize_hornerPoly v (xs := @Fin.snoc (n + 1) (fun _ => C v) xs (Sum.inl x))
    (a := a') hs]
  -- the polynomial only sees the first `n+1` coefficients
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

/-- the value form of `vfAlgClosed`: every Horner polynomial of degree `n+1` with
coefficients in `K` has a root in `K` -/
theorem exists_root_horner (n : ℕ) (a : ℕ → K) [IsAlgClosed K] :
    ∃ x : K, (List.finRange n).reverse.foldl (fun v i => v * x + a i.val) (x + a n) = 0 := by
  have hmonic : (hornerPolyK a (n + 1)).Monic := hornerPolyK_monic a
  have hdeg : (hornerPolyK a (n + 1)).degree ≠ 0 := by
    refine ne_of_gt ?_
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hornerPolyK_natDegree]
    omega
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (hornerPolyK a (n + 1)) hdeg
  exact ⟨x, by rw [← hornerPolyK_eval]; exact hx⟩

/-- **`vfAlgClosed` holds at the intended structure on `K ⊕ RV₀ v`**, for `K` an
algebraically closed field and any valuation `v` on it: the `VF` summand is a field and is
algebraically closed. -/
theorem model_vfAlgClosed (v : Valuation K Γ₀) [IsAlgClosed K] :
    (C v) ⊨ Axioms.vfAlgClosed where
  realize_of_mem φ hφ := by
    obtain ⟨k, hk, rfl⟩ := hφ
    exact acfScheme_vf v hk

end VFPort
end Milestone0
end SpecialTransformations

namespace SpecialTransformations
namespace Milestone0
namespace IModel

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0

attribute [local instance] ACVFResidue.kField

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-! ### the remaining `RV`-group and preorder sentences -/

theorem model_rvMulInfty : (C v) ⊨ Axioms.rvMulInfty := by
  simp only [Axioms.rvMulInfty]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht]
  exact congrArg (fun x => mkRV v x) (RVM.rv0Mul_infty v t)

theorem model_leTrans : (C v) ⊨ Axioms.leTrans := by
  simp only [Axioms.leTrans]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).2 rfl
  obtain ⟨b, hb⟩ := (h 1).2 rfl
  obtain ⟨c, hc⟩ := (h 2).2 rfl
  rw [ha, hb, hc]
  rintro _ _ _ h1 h2
  obtain ⟨a', b', h1', h2', hab⟩ := h1
  obtain ⟨b'', c', h3', h4', hbc⟩ := h2
  rw [mkRV_inj] at h1' h2' h3' h4'
  subst h1'; subst h2'; subst h3'; subst h4'
  exact ⟨_, _, rfl, rfl, RVM.le0_trans v hab hbc⟩

theorem le0_some_some_iff (a b : RVM.RV v) : RVM.le0 v a b ↔ a ≤ b := Iff.rfl

theorem vrv_rvOne : RVM.vrv v (RVM.rvOne v) = 1 := by
  rw [RVM.rvOne_eq, RVM.vrv_some]
  simp

theorem le_class_of_one_iff_of_le {b : RVM.RV v} (h1 : RVM.rvOne v ≤ b) (h2 : b ≤ RVM.rvOne v) :
    ∃ q : RVM.RVUnit v, b = some q ∧ RVM.vrv v (some q) = 1 := by
  have hone : RVM.vrv v b = 1 := (RVM.le_class_of_one_iff (v := v) (t := b)).mp ⟨h1, h2⟩
  rcases b with _ | q
  · rw [RVM.vrv_none] at hone
    exact absurd hone (zero_ne_one' Γ₀)
  · exact ⟨q, rfl, hone⟩

theorem model_leClassOne : (C v) ⊨ Axioms.leClassOne := by
  simp only [Axioms.leClassOne]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  intro ht0
  rw [ht] at ht0 ⊢
  rcases t with _ | b
  · exact absurd rfl ht0
  constructor
  · rintro ⟨q, hq, hv⟩
    have hq' : b = q := by simpa using hq
    rw [hq'] at ⊢
    refine ⟨⟨RVM.rvOne v, some q, rfl, rfl, ?_⟩,
      ⟨some q, RVM.rvOne v, rfl, rfl, ?_⟩⟩
    · exact (RVM.le_class_of_one_iff (v := v) (t := some q)).mpr hv |>.1
    · exact (RVM.le_class_of_one_iff (v := v) (t := some q)).mpr hv |>.2
  · rintro ⟨⟨a1, b1, h1, h1', hle1⟩, ⟨a2, b2, h2, h2', hle2⟩⟩
    rw [mkRV_inj] at h1 h1' h2 h2'
    subst h1; subst h1'; subst h2; subst h2'
    obtain ⟨q, hq, hv⟩ := le_class_of_one_iff_of_le (v := v) hle1 hle2
    exact ⟨q, by rw [hq], hv⟩

/-! ### compatibility of `≤` with `×` -/

theorem le0_mul_compat {a b u : RVM.RV v} (ha : a ≠ none) (hb : b ≠ none)
    {q : RVM.RVUnit v} (hu : u = some q) (hq : RVM.vrv v (some q) = 1)
    (h : RVM.le0 v a b) : RVM.le0 v (RVM.rv0Mul v a u) (RVM.rv0Mul v b u) := by
  obtain ⟨a', rfl⟩ := RVM.rv_shape (v := v) ha
  obtain ⟨b', rfl⟩ := RVM.rv_shape (v := v) hb
  subst hu
  have hqmul : ∀ z : RVM.RV v, RVM.vrv v (RVM.rv0Mul v z (some q)) = RVM.vrv v z := by
    intro z
    rw [RVM.vrv_mul, hq, mul_one]
  have h' : RVM.vrv v (RVM.rv0Mul v (some b') (some q)) ≤
      RVM.vrv v (RVM.rv0Mul v (some a') (some q)) := by
    rw [hqmul (some b'), hqmul (some a')]
    exact h
  exact h'

theorem model_leMulCompat : (C v) ⊨ Axioms.leMulCompat := by
  simp only [Axioms.leMulCompat]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).2 rfl
  obtain ⟨b, hb⟩ := (h 1).2 rfl
  obtain ⟨u, hu⟩ := (h 2).2 rfl
  rw [ha, hb, hu]
  rintro h0 h1 h2 ⟨q, hq, hv⟩ hab
  have hq' : u = some q := by simpa using hq
  subst hq'
  have hab' : RVM.le0 v a b := by
    obtain ⟨a1, b1, h1, h2, h3⟩ := hab
    rw [mkRV_inj] at h1 h2
    subst h1; subst h2
    exact h3
  exact ⟨RVM.rv0Mul v a (some q), RVM.rv0Mul v b (some q), rfl, rfl,
    le0_mul_compat v (by simpa using h0) (by simpa using h1) rfl hv hab'⟩

theorem cUnit_one_eq : cUnit v (1 : RVM.RVUnit v) = iRVOne (M := C v) := by
  show Sum.inr (some (1 : RVM.RVUnit v)) = Sum.inr (RVM.rvOne v)
  rw [RVM.rvOne_eq]

theorem model_rvMulInv : (C v) ⊨ Axioms.rvMulInv := by
  simp only [Axioms.rvMulInv]; rw [model_allSorted v]; intro xs h; prep
  rintro ⟨q, hq, hv⟩
  have hq1 : RVM.vrv v (some q) = 1 := hv
  refine ⟨cUnit v q⁻¹, ⟨some q⁻¹, rfl⟩, ⟨q⁻¹, rfl, ?_⟩, ?_⟩
  · have hm : RVM.vrv v (some (q * q⁻¹)) = RVM.vrv v (some q) * RVM.vrv v (some q⁻¹) := by
      rw [RVM.vrv_some, RVM.vrv_some, RVM.vrv_some, map_mul, Units.val_mul]
    rw [mul_inv_cancel, RVM.vrv_some, map_one, Units.val_one, hq1, one_mul] at hm
    exact hm.symm
  · have e1 : (Fin.snoc xs (cUnit v q⁻¹) : Fin 2 → C v) 1 = cUnit v q⁻¹ := by
      rw [show (1 : Fin 2) = Fin.last 1 from rfl]
      exact Fin.snoc_last (α := fun _ => C v) (cUnit v q⁻¹) xs
    have e0 : (Fin.snoc xs (cUnit v q⁻¹) : Fin 2 → C v) 0 = cUnit v q :=
      hq
    rw [e1, e0]
    show mkRV v (RVM.rv0Mul v (some q⁻¹) (some q)) = iRVOne (M := C v)
    rw [RVM.rv0Mul_some_some, inv_mul_cancel]
    exact (cUnit_one_eq v)

/-! ### assembly: which components of `ACVF` hold at `K ⊕ RV₀`

The two components that are **not** proved in this file are `Axioms.kField` and
`Axioms.kAlgClosed` (the residue field `K = K^× ∪ {0}` inside the `RV` sort — its `+`/`-`
are implemented here through `kOf`/`ofK` and `ACVFResidue.kField`, but the ten field
sentences and the ACF scheme for `K` are not carried out), and the divisibility scheme
`rvDivisible k` of `Axioms.rvGroup`.  Everything else is proved. -/

theorem model_rvGroup_list (s : LRV.Sentence) (hs : s ∈ Axioms.ofList
    [Axioms.rvOneMem, Axioms.rvMulMem, Axioms.rvMulAssoc, Axioms.rvMulComm,
      Axioms.rvMulOne, Axioms.rvMulInv, Axioms.rvMulZeroK, Axioms.rvMulInfty]) :
    (C v) ⊨ s := by
  simp only [Axioms.ofList, List.mem_cons, List.mem_nil_iff, or_false] at hs
  obtain rfl | h2 := hs
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
  · exact model_rvMulInv v
  obtain rfl | h8 := h7
  · exact model_rvMulZeroK v
  obtain rfl := by simpa using h8
  exact model_rvMulInfty v

theorem model_rvAxioms_mem (s : LRV.Sentence) (hs : s ∈ Axioms.rvAxioms) : (C v) ⊨ s := by
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

theorem model_preorderRV_all (s : LRV.Sentence) (hs : s ∈ Axioms.preorderRV) : (C v) ⊨ s := by
  simp only [Axioms.preorderRV, Axioms.ofList, List.mem_cons, List.mem_nil_iff, or_false] at hs
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

/-- `Axioms.rvGroup` minus the divisibility scheme -/
theorem model_rvGroup_ofList (s : LRV.Sentence)
    (hs : s ∈ Axioms.ofList [Axioms.rvOneMem, Axioms.rvMulMem, Axioms.rvMulAssoc,
      Axioms.rvMulComm, Axioms.rvMulOne, Axioms.rvMulInv, Axioms.rvMulZeroK,
      Axioms.rvMulInfty]) : (C v) ⊨ s := model_rvGroup_list v s hs

/-- **The assembly**: `ACVF` holds at `K ⊕ RV₀` as soon as the residue-field axioms
`kField`, `kAlgClosed` and the divisibility scheme hold.  Everything else is proved here. -/
theorem model_ACVF_of_components [IsAlgClosed K]
    (hkf : (C v) ⊨ Axioms.kField) (hka : (C v) ⊨ Axioms.kAlgClosed)
    (hdiv : ∀ k : ℕ, 1 ≤ k → (C v) ⊨ Axioms.rvDivisible k) :
    (C v) ⊨ Axioms.ACVF := by
  rw [Theory.model_iff] at *
  intro s hs
  rw [Axioms.ACVF, Set.mem_union] at hs
  rcases hs with hs | hs
  · exact (Theory.model_iff ..).mp (model_sortAxioms_all v) s hs
  rw [Axioms.ACVFpaper] at hs
  simp only [Set.mem_union] at hs
  rcases hs with (((((hs | hs) | hs) | hs) | hs) | hs) | hs
  · exact (Theory.model_iff ..).mp (model_vfField v) s hs
  · exact (Theory.model_iff ..).mp (VFPort.model_vfAlgClosed v) s hs
  · rw [Axioms.rvGroup, Set.mem_union] at hs
    rcases hs with hs | hs
    · exact model_rvGroup_list v s hs
    · obtain ⟨k, hk, rfl⟩ := hs
      exact hdiv k hk
  · exact hkf s hs
  · exact hka s hs
  · exact model_preorderRV_all v s hs
  · exact model_rvAxioms_mem v s hs

/-! ### `Γ(S)` is nontrivial at `K ⊕ RV₀ v` for every nontrivial valuation

The paper's standing hypothesis is that the value group `Γ(S)` of the substructure `S` is
nontrivial.  Nontriviality of `Γ` is not a sort of `L_RV`; we read it off the preorder and the
predicate `K^×`: `Γ(S)` is nontrivial at `t` of the `RV` sort of `S` when
`¬ (1 ≤ t ∧ t ≤ 1)`, i.e. `vrv t ≠ 1`.  (`K^×` is the class of `1` by axiom `leClassOne`, so
`1 ≤ t ∧ t ≤ 1` is the statement `t ∈ K^×`.) -/

theorem gamma_nontrivial_iff (a : K) :
    (iLe (iRVOne (M := C v)) (iRv (mkVF v a)) ∧ iLe (iRv (mkVF v a)) (iRVOne (M := C v))) ↔
      v a = 1 := by
  have h1 : iLe (iRVOne (M := C v)) (iRv (mkVF v a)) ↔
      RVM.le0 v (RVM.rvOne v) (RVM.rv v a) :=
    (le0_mkRV_iff (v := v) (t := RVM.rvOne v) (s := RVM.rv v a))
  have h2 : iLe (iRv (mkVF v a)) (iRVOne (M := C v)) ↔
      RVM.le0 v (RVM.rv v a) (RVM.rvOne v) :=
    (le0_mkRV_iff (v := v) (t := RVM.rv v a) (s := RVM.rvOne v))
  rw [h1, h2]
  constructor
  · rintro ⟨h1', h2'⟩
    have := (RVM.le_class_of_one_iff (v := v) (t := RVM.rv v a)).mp ⟨h1', h2'⟩
    rw [RVM.vrv_rv] at this
    simpa using this
  · intro h
    have hrv : RVM.vrv v (RVM.rv v a) = 1 := by rw [RVM.vrv_rv]; exact h
    exact (RVM.le_class_of_one_iff (v := v) (t := RVM.rv v a)).mpr hrv

/-- **`Γ(S)` is nontrivial**: for `x` with `v x ≠ 1`, the substructure generated by `x` has an
`RV`-element `rv x` that is not in the class of `1`, so the value group of `S` is nontrivial. -/
theorem exists_substructure_gamma_nontrivial (x : K) (hx : v x ≠ 1) :
    ∃ (S : LRV.Substructure (C v)) (t : C v), (S : Set (C v)) t ∧ iRV t ∧
      ¬ (iLe (iRVOne (M := C v)) t ∧ iLe t (iRVOne (M := C v))) := by
  refine ⟨FirstOrder.Language.Substructure.closure LRV {mkVF v x}, iRv (mkVF v x), ?_,
    ⟨RVM.rv v x, rfl⟩, ?_⟩
  · exact (FirstOrder.Language.Substructure.closure LRV {mkVF v x}).fun_mem Fn.rvMap
      ![mkVF v x] (fun i => by
        fin_cases i
        exact FirstOrder.Language.Substructure.subset_closure (L := LRV) rfl)
  · intro h
    exact hx ((gamma_nontrivial_iff v x).mp h)

end SpecialTransformations.Milestone0.IModel

/-! ## Axiom footprints of the main results -/

#print axioms SpecialTransformations.Milestone0.IModel.exists_substructure_gamma_nontrivial
#print axioms SpecialTransformations.Milestone0.IModel.model_ACVF_of_components
#print axioms SpecialTransformations.Milestone0.IModel.model_residueCharZero_iff
#print axioms SpecialTransformations.Milestone0.IModel.padicComplex_not_model_ACVF00
#print axioms SpecialTransformations.Milestone0.IModel.model_leClassOne
#print axioms SpecialTransformations.Milestone0.IModel.model_rvMulInv
#print axioms SpecialTransformations.Milestone0.IModel.model_rvAxioms_mem
#print axioms SpecialTransformations.Milestone0.VFPort.model_vfAlgClosed
#print axioms SpecialTransformations.Milestone0.IModel.model_sortAxioms_all
