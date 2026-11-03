/-
Milestone 0 for: Yimu Yin, "Special transformations in algebraically closed valued fields",
Annals of Pure and Applied Logic (2010), arXiv:1006.2467.

The paper's language `L_RV` (Definition 2.1), the theory `ACVF` (Definition 2.2), the
theory `ACVF_S(0,0)`, and the statements of quantifier elimination (Theorem 2.3) and
C-minimality (Theorem 2.8), encoded in Mathlib's one-sorted first-order model theory by
putting the sorts of `L_RV` on a single tagged carrier with unary sort predicates.

This file is self-contained: its only import is `Mathlib`.  Check it with

    lean Obstruction.lean

It consists of Parts 0-3 of `Milestone0/Encoding.lean` (verbatim, except that `def LRV`
is written `abbrev LRV`, which is the same term `⟨Fn, Rel⟩` and only lets the elaborator
unfold `LRV.Functions` while rewriting), followed by new material: an obstruction showing
that the encoded `ACVF` forces the two constants `0` and `∞` of the `RV` sort to be equal;
and the repaired (`pK`-guarded) invertibility axiom.  No `sorry`.

**Conversion (author's ruling: the paper's `0` and `∞` are ONE element, `rv(0) = 0`).**  The
ruling adopts exactly what this file's Part 4 derives, so `Fn.rvInfty` is deleted,
`iRVInfty := iRVZero`, `sdRVInfty`/`rvMulInfty`/`leTop`/`leInftyEq` are stated at `tRVZero`,
and `rvSurj` is the paper's unguarded surjectivity `t ≠ rv(0) → ∃ x, rv x = t`.  The theorems
below keep their statements: `ACVF_forces_zero_eq_infty` is now *definitionally* true (the
derivation still goes through unchanged), and `intended_carrier_does_not_model_ACVF(00)`,
whose hypotheses put `0` and `∞` on two distinct carrier elements, are now **vacuous** (their
hypotheses contradict `iRVInfty = iRVZero`); the three-layer `Valued.RV0` they mention is kept
as a legacy alias only.
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

/-- the universal closure of a formula in a single variable -/
def allOne (φ : Bf 1) : LRV.Sentence := BoundedFormula.alls φ

/-- Horner form `x^k + a_{k-1} x^{k-1} + ⋯ + a_0` of the monic polynomial of degree `k`
whose coefficients are the variables `0, …, k-1` and whose variable is the variable `k`. -/
def hornerPoly {k : ℕ} (add mul : {n : ℕ} → Tm n → Tm n → Tm n) : Tm (k + 1) :=
  let x : Tm (k + 1) := tv k (Nat.lt_succ_self k)
  (List.finRange k).reverse.foldl
    (fun acc i => add (mul acc x) (tv i.val (Nat.lt_succ_of_lt i.isLt))) x

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
/-- `Kˣ` is `RV ∖ {0, ∞}`, i.e. the `RV` sort minus its two constants `0` and `∞` -/
def sdUnits : LRV.Sentence :=
  allSorted ![.rv] (pUnits &0 ⇔ (pK &0 ⊓ ∼(pEq &0 tRVZero)))
/-- `K = Kˣ ∪ {0}` is closed under `+` -/
def sdKAdd : LRV.Sentence := allSorted ![.rv, .rv] (pK &0 ⟹ (pK &1 ⟹ pK (tKAdd &0 &1)))
/-- `K` is closed under unary `-` -/
def sdKNeg : LRV.Sentence := allSorted ![.rv] (pK &0 ⟹ pK (tKNeg &0))

/-- The closure part of the sort discipline: each sort is closed under its own symbols,
and the two sorts are related through the symbols that cross them. -/
def sortClosure : LRV.Theory :=
  ofList [sdVFZero, sdVFOne, sdVFAdd, sdVFNeg, sdVFMul, sdRv,
    sdRVZero, sdRVInfty, sdRVOne, sdRVMul, sdUnits, sdKAdd, sdKNeg]

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

/-- Definition 2.2 item 3: `(K, 0, 1, +, -, ×)` is an algebraically closed field. -/
def kField : LRV.Theory :=
  ofList (fieldAxioms .rv tRVZero tRVOne tKAdd tRVMul tKNeg)
/-- algebraic closedness of `K = Kˣ ∪ {0}` -/
def kAlgClosed : LRV.Theory := {s | ∃ k, 1 ≤ k ∧ s = acfScheme .rv tRVZero tKAdd tRVMul k}

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
/-- `t × ∞ = ∞` for `t ∈ RV₀`, i.e. for every `t` of the `RV` sort; since `∞ = rv(0) = 0`
this is `t × 0 = 0` -/
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
some `x ∈ VF`.  (With `RV^× = RV ∖ {0}` this is `RV = rv(VF) ∪ {0}`.) -/
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


/-!
## Part 4 (member m5): the theory-level obstruction `ACVF ⊢ tRVZero = tRVInfty`

The only change to `Milestone0/Encoding.lean` above is `def LRV` → `abbrev LRV`
(same term `⟨Fn, Rel⟩`, definitionally equal): it lets the elaborator unfold
`LRV.Functions` when rewriting, and changes no statement.
-/

namespace Model

open FirstOrder FirstOrder.Language

variable {M : Type*} [LRV.Structure M]

/-- `x` lies in the `VF` sort -/
def iVF (x : M) : Prop := Structure.RelMap (L := LRV) Rel.memVF ![x]
/-- `x` lies in the `RV` sort -/
def iRV (x : M) : Prop := Structure.RelMap (L := LRV) Rel.memRV ![x]
/-- `x ∈ Kˣ` -/
def iUnits (x : M) : Prop := Structure.RelMap (L := LRV) Rel.memUnits ![x]
/-- `x ≤ y` -/
def iLe (x y : M) : Prop := Structure.RelMap (L := LRV) Rel.rvLe ![x, y]
def iVFAdd (x y : M) : M := Structure.funMap (L := LRV) Fn.vfAdd ![x, y]
def iVFNeg (x : M) : M := Structure.funMap (L := LRV) Fn.vfNeg ![x]
def iVFMul (x y : M) : M := Structure.funMap (L := LRV) Fn.vfMul ![x, y]
def iKAdd (x y : M) : M := Structure.funMap (L := LRV) Fn.kAdd ![x, y]
def iKNeg (x : M) : M := Structure.funMap (L := LRV) Fn.kNeg ![x]
def iRVMul (x y : M) : M := Structure.funMap (L := LRV) Fn.rvMul ![x, y]
def iRv (x : M) : M := Structure.funMap (L := LRV) Fn.rvMap ![x]
def iRVZero : M := Structure.funMap (L := LRV) Fn.rvZero fun i => i.elim0
/-- The interpretation of the paper's `∞`, which is the interpretation of `0` of the `RV` sort -/
def iRVInfty : M := iRVZero (M := M)
def iRVOne : M := Structure.funMap (L := LRV) Fn.rvOne fun i => i.elim0

noncomputable section

/-- the empty assignment -/
abbrev v0 : Empty → M := default

variable {n : ℕ}

/-! ### Term realisation -/

theorem realize_tRVInfty (xs : Fin n → M) :
    Term.realize (Sum.elim v0 xs) (LRV.tRVInfty : LRV.Tm n) = iRVInfty := by
  simp only [LRV.tRVInfty, LRV.tRVZero, Term.realize_func, iRVZero]
  congr 1
  funext i
  exact Fin.elim0 i

theorem realize_tRVZero (xs : Fin n → M) :
    Term.realize (Sum.elim v0 xs) (LRV.tRVZero : LRV.Tm n) = iRVZero := by
  simp only [LRV.tRVZero, Term.realize_func, iRVZero]
  congr 1
  funext i
  exact Fin.elim0 i

theorem realize_tRVOne (xs : Fin n → M) :
    Term.realize (Sum.elim v0 xs) (LRV.tRVOne : LRV.Tm n) = iRVOne := by
  simp only [LRV.tRVOne, Term.realize_func, iRVOne]
  congr 1
  funext i
  exact Fin.elim0 i

theorem realize_tv (i : ℕ) (h : i < n) (xs : Fin n → M) :
    Term.realize (Sum.elim v0 xs) (LRV.tv i h) = xs ⟨i, h⟩ := rfl

theorem realize_tRVMul (t u : LRV.Tm n) (xs : Fin n → M) :
    Term.realize (Sum.elim v0 xs) (LRV.tRVMul t u) =
      iRVMul (Term.realize (Sum.elim v0 xs) t) (Term.realize (Sum.elim v0 xs) u) := by
  have key : (fun i : Fin 2 => Term.realize (Sum.elim v0 xs) (![t, u] i))
      = ![Term.realize (Sum.elim v0 xs) t, Term.realize (Sum.elim v0 xs) u] := by
    funext i; fin_cases i <;> rfl
  rw [LRV.tRVMul, Term.realize_func, iRVMul, key]

theorem realize_var (i : Fin n) (xs : Fin n → M) :
    Term.realize (Sum.elim v0 xs) (Term.var (Sum.inr i) : LRV.Tm n) = xs i := rfl

theorem snoc_vec (x y : M) :
    Fin.snoc (α := fun _ => M) (fun _ : Fin 1 => x) y = ![x, y] := by
  funext i; fin_cases i <;> rfl

/-! ### Formula realisation -/

theorem realize_pRVsort (t : LRV.Tm n) (xs : Fin n → M) :
    (LRV.pRVsort t).Realize v0 xs ↔ iRV (Term.realize (Sum.elim v0 xs) t) := by
  have key : (fun i : Fin 1 => Term.realize (Sum.elim v0 xs) (![t] i))
      = ![Term.realize (Sum.elim v0 xs) t] := by
    funext i; fin_cases i; rfl
  simp only [LRV.pRVsort, Relations.boundedFormula₁, BoundedFormula.realize_rel, iRV, key]

theorem realize_pUnits (t : LRV.Tm n) (xs : Fin n → M) :
    (LRV.pUnits t).Realize v0 xs ↔ iUnits (Term.realize (Sum.elim v0 xs) t) := by
  have key : (fun i : Fin 1 => Term.realize (Sum.elim v0 xs) (![t] i))
      = ![Term.realize (Sum.elim v0 xs) t] := by
    funext i; fin_cases i; rfl
  simp only [LRV.pUnits, Relations.boundedFormula₁, BoundedFormula.realize_rel, iUnits, key]

theorem realize_pEq (t u : LRV.Tm n) (xs : Fin n → M) :
    (LRV.pEq t u).Realize v0 xs ↔
      Term.realize (Sum.elim v0 xs) t = Term.realize (Sum.elim v0 xs) u :=
  BoundedFormula.realize_bdEqual t u

theorem realize_pK (t : LRV.Tm n) (xs : Fin n → M) :
    (LRV.pK t).Realize v0 xs ↔ ¬ (Term.realize (Sum.elim v0 xs) t = iRVInfty) := by
  simp only [LRV.pK, LRV.pEq, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    realize_tRVInfty]

theorem realize_pEq_zero (t : LRV.Tm n) (xs : Fin n → M) :
    (LRV.pEq t LRV.tRVZero).Realize v0 xs ↔ Term.realize (Sum.elim v0 xs) t = iRVZero := by
  simp only [LRV.pEq, BoundedFormula.realize_bdEqual, realize_tRVZero]

theorem realize_pEq_one (t : LRV.Tm n) (xs : Fin n → M) :
    (LRV.pEq t LRV.tRVOne).Realize v0 xs ↔ Term.realize (Sum.elim v0 xs) t = iRVOne := by
  simp only [LRV.pEq, BoundedFormula.realize_bdEqual, realize_tRVOne]

/-! ### Reading the guarded sentences `allSorted ss φ` -/

/-- `M ⊨ allSorted ss φ` says: `φ` holds at every tuple whose components lie in
the prescribed sorts. -/
theorem models_allSorted {k : ℕ} (ss : Fin k → SortTag) (φ : LRV.Bf k)
    (h : M ⊨ LRV.allSorted ss φ) :
    ∀ (xs : Fin k → M), (LRV.sortedHyps ss).Realize v0 xs → φ.Realize v0 xs := by
  intro xs hx
  have h1 : (BoundedFormula.alls (LRV.sortedHyps ss ⟹ φ)).Realize v0 := h
  rw [BoundedFormula.realize_alls] at h1
  have h2 : (LRV.sortedHyps ss ⟹ φ).Realize v0 xs := h1 xs
  rw [BoundedFormula.realize_imp] at h2
  exact h2 hx

theorem finRange_one : (List.finRange 1) = ([0] : List (Fin 1)) := by decide

theorem finRange_two : (List.finRange 2) = ([0, 1] : List (Fin 2)) := by decide

theorem vec1_zero : (![SortTag.rv] : Fin 1 → SortTag) 0 = SortTag.rv := rfl

theorem vec2_zero : (![SortTag.rv, SortTag.rv] : Fin 2 → SortTag) 0 = SortTag.rv := rfl
theorem vec2_one : (![SortTag.rv, SortTag.rv] : Fin 2 → SortTag) 1 = SortTag.rv := rfl

theorem realize_sortedHyps_one_rv (x : M) :
    (LRV.sortedHyps ![SortTag.rv]).Realize v0 (fun _ : Fin 1 => x) ↔ iRV x := by
  rw [LRV.sortedHyps, finRange_one]
  simp only [List.foldr_cons, List.foldr_nil, vec1_zero, LRV.sortPred,
    BoundedFormula.realize_inf, BoundedFormula.realize_top, realize_pRVsort, realize_tv,
    and_true]

theorem realize_sortedHyps_two_rv (xs : Fin 2 → M) :
    (LRV.sortedHyps ![SortTag.rv, SortTag.rv]).Realize v0 xs ↔ iRV (xs 0) ∧ iRV (xs 1) := by
  rw [LRV.sortedHyps, finRange_two]
  simp only [List.foldr_cons, List.foldr_nil, LRV.sortPred, BoundedFormula.realize_inf,
    BoundedFormula.realize_top, realize_pRVsort, realize_tv, and_true, vec2_zero, vec2_one]

/-- reading an `allSorted` sentence in one `RV`-sorted variable -/
theorem models_rv1 {φ : LRV.Bf 1} (h : M ⊨ LRV.allSorted ![SortTag.rv] φ)
    (x : M) (hx : iRV x) : φ.Realize v0 (fun _ : Fin 1 => x) :=
  models_allSorted _ _ h (fun _ => x) ((realize_sortedHyps_one_rv x).mpr hx)

/-- reading an `allSorted` sentence in two `RV`-sorted variables -/
theorem models_rv2 {φ : LRV.Bf 2}
    (h : M ⊨ LRV.allSorted ![SortTag.rv, SortTag.rv] φ)
    (x y : M) (hx : iRV x) (hy : iRV y) : φ.Realize v0 ![x, y] := by
  refine models_allSorted _ _ h ![x, y] ?_
  simpa using (realize_sortedHyps_two_rv ![x, y]).mpr (by simpa using ⟨hx, hy⟩)



/-! ## 5. Membership of the sentences used in the derivation -/

theorem sdRVInfty_mem : Axioms.sdRVInfty ∈ Axioms.sortClosure := by
  simp only [Axioms.sortClosure, Axioms.ofList, Set.mem_ofPred_eq]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))

theorem sdRVOne_mem : Axioms.sdRVOne ∈ Axioms.sortClosure := by
  simp only [Axioms.sortClosure, Axioms.ofList, Set.mem_ofPred_eq]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))

theorem sdUnits_mem : Axioms.sdUnits ∈ Axioms.sortClosure := by
  simp only [Axioms.sortClosure, Axioms.ofList, Set.mem_ofPred_eq]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))

theorem rvOneMem_mem : Axioms.rvOneMem ∈ Axioms.rvGroup := by
  simp only [Axioms.rvGroup, Axioms.ofList, Set.mem_ofPred_eq, Set.mem_union]
  exact Or.inl (List.mem_cons_self)

theorem rvMulComm_mem : Axioms.rvMulComm ∈ Axioms.rvGroup := by
  simp only [Axioms.rvGroup, Axioms.ofList, Set.mem_ofPred_eq, Set.mem_union]
  exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))

theorem rvMulInfty_mem : Axioms.rvMulInfty ∈ Axioms.rvGroup := by
  simp only [Axioms.rvGroup, Axioms.ofList, Set.mem_ofPred_eq, Set.mem_union]
  exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))

/-- the `RV`-sorted invertibility axiom of `fieldAxioms` -/
abbrev kFieldInv : LRV.Sentence :=
  LRV.allSorted ![SortTag.rv]
    (LRV.pEq &0 LRV.tRVZero ⊔ (LRV.exSorted SortTag.rv (LRV.pEq (LRV.tRVMul &0 &1) LRV.tRVOne)))

theorem kField_inv_mem : kFieldInv ∈ Axioms.kField := by
  simp only [Axioms.kField, Axioms.ofList, Set.mem_ofPred_eq, Axioms.fieldAxioms]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))

/-! ## 6. Those sentences are axioms of `ACVF` -/

theorem ACVF_of_sortClosure {φ : LRV.Sentence} (h : φ ∈ Axioms.sortClosure) :
    φ ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.sortAxioms, Axioms.ACVFpaper, Set.mem_union]
  tauto

theorem ACVF_of_rvGroup {φ : LRV.Sentence} (h : φ ∈ Axioms.rvGroup) :
    φ ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.sortAxioms, Axioms.ACVFpaper, Set.mem_union]
  tauto

theorem ACVF_of_kField {φ : LRV.Sentence} (h : φ ∈ Axioms.kField) :
    φ ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.sortAxioms, Axioms.ACVFpaper, Set.mem_union]
  tauto

end

end Model

namespace Model

open FirstOrder FirstOrder.Language

variable {M : Type*} [LRV.Structure M]

/-! ## 7. What the axioms say at a concrete element -/

theorem models_sdRVInfty (hM : M ⊨ Axioms.ACVF) : iRV (M := M) iRVInfty := by
  have h : M ⊨ Axioms.sdRVInfty := hM.realize_of_mem (Axioms.sdRVInfty) (ACVF_of_sortClosure sdRVInfty_mem)
  simpa only [FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
    Axioms.sdRVInfty, realize_pRVsort, realize_tRVZero, iRVInfty] using h

theorem models_sdRVOne (hM : M ⊨ Axioms.ACVF) : iRV (M := M) iRVOne := by
  have h : M ⊨ Axioms.sdRVOne := hM.realize_of_mem (Axioms.sdRVOne) (ACVF_of_sortClosure sdRVOne_mem)
  simpa only [FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
    Axioms.sdRVOne, realize_pRVsort, realize_tRVOne] using h

theorem models_rvOneMem (hM : M ⊨ Axioms.ACVF) : iUnits (M := M) iRVOne := by
  have h : M ⊨ Axioms.rvOneMem := hM.realize_of_mem (Axioms.rvOneMem) (ACVF_of_rvGroup rvOneMem_mem)
  simpa only [FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
    Axioms.rvOneMem, realize_pUnits, realize_tRVOne] using h

theorem models_sdUnits (hM : M ⊨ Axioms.ACVF) (x : M) (hx : iRV x) :
    iUnits x ↔ (¬ x = iRVInfty ∧ ¬ x = iRVZero) := by
  have h : M ⊨ Axioms.sdUnits := hM.realize_of_mem (Axioms.sdUnits) (ACVF_of_sortClosure sdUnits_mem)
  have h2 := models_rv1 h x hx
  simpa only [FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
    Axioms.sdUnits, BoundedFormula.realize_iff, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, realize_pUnits, realize_pK, realize_pEq_zero, realize_var,
    Term.realize_var, Sum.elim_inr, Function.comp_apply] using h2

theorem models_rvMulInfty (hM : M ⊨ Axioms.ACVF) (y : M) (hy : iRV y) :
    iRVMul y iRVInfty = iRVInfty := by
  have h : M ⊨ Axioms.rvMulInfty := hM.realize_of_mem (Axioms.rvMulInfty) (ACVF_of_rvGroup rvMulInfty_mem)
  have h2 := models_rv1 h y hy
  simpa only [FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
    Axioms.rvMulInfty, realize_pEq, realize_tRVMul, realize_tRVZero, iRVInfty, realize_var,
    Term.realize_var, Sum.elim_inr, Function.comp_apply] using h2

theorem models_rvMulComm (hM : M ⊨ Axioms.ACVF) (x y : M) (hx : iRV x) (hy : iRV y) :
    iRVMul x y = iRVMul y x := by
  have h : M ⊨ Axioms.rvMulComm := hM.realize_of_mem (Axioms.rvMulComm) (ACVF_of_rvGroup rvMulComm_mem)
  have h2 := models_rv2 h x y hx hy
  simpa only [FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
    Axioms.rvMulComm, realize_pEq, realize_tRVMul, realize_var, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using h2

/-- the `RV`-sorted invertibility axiom, read in the model -/
theorem models_kField_inv (hM : M ⊨ Axioms.ACVF) (x : M) (hx : iRV x) :
    x = iRVZero ∨ ∃ y : M, iRV y ∧ iRVMul x y = iRVOne := by
  have h : M ⊨ kFieldInv := hM.realize_of_mem (kFieldInv) (ACVF_of_kField kField_inv_mem)
  have h2 := models_rv1 h x hx
  have h2' : (LRV.pEq &0 LRV.tRVZero).Realize v0 (fun _ : Fin 1 => x) ∨
      (LRV.exSorted SortTag.rv (LRV.pEq (LRV.tRVMul &0 &1) LRV.tRVOne)).Realize v0
        (fun _ : Fin 1 => x) := by
    rwa [BoundedFormula.realize_sup] at h2
  rcases h2' with h2' | h2'
  · left
    rw [realize_pEq_zero] at h2'
    simpa only [realize_var, Term.realize_var, Sum.elim_inr, Function.comp_apply] using h2'
  · right
    rw [LRV.exSorted, BoundedFormula.realize_ex] at h2'
    obtain ⟨y, hy⟩ := h2'
    rw [snoc_vec] at hy
    simp only [BoundedFormula.realize_inf, LRV.sortPred, LRV.tv, realize_pRVsort, realize_pEq,
      realize_tRVMul, realize_tRVOne, realize_var, Term.realize_var, Sum.elim_inr,
      Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hy
    exact ⟨y, hy.1, hy.2⟩

/-! ## 8. The obstruction -/

/-- **In every model of `ACVF`, the residue zero and `∞` coincide.** -/
theorem ACVF_forces_zero_eq_infty (hM : M ⊨ Axioms.ACVF) :
    (iRVZero : M) = (iRVInfty : M) := by
  have hInf : iRV (M := M) iRVInfty := models_sdRVInfty (M := M) hM
  have hOneRV : iRV (M := M) iRVOne := models_sdRVOne (M := M) hM
  have hOne : iUnits (M := M) iRVOne := models_rvOneMem (M := M) hM
  have hne : ¬ ((iRVOne : M) = iRVInfty) := ((models_sdUnits (M := M) hM iRVOne hOneRV).mp hOne).1
  rcases models_kField_inv (M := M) hM iRVInfty hInf with h | ⟨y, hy, hmul⟩
  · exact h.symm
  · exfalso
    have h1 : iRVMul iRVInfty y = iRVInfty := by
      rw [models_rvMulComm (M := M) hM iRVInfty y hInf hy, models_rvMulInfty (M := M) hM y hy]
    exact hne (by rw [← hmul, h1])

/-- `ACVF(0,0)` has the same defect, since `ACVF ⊆ ACVF(0,0)`. -/
theorem ACVF00_forces_zero_eq_infty (hM : M ⊨ Axioms.ACVF00) :
    (iRVZero : M) = (iRVInfty : M) := by
  refine ACVF_forces_zero_eq_infty (M := M) (Theory.Model.mk (fun φ hφ => hM.realize_of_mem φ ?_))
  simp only [Axioms.ACVF00, Set.mem_union]
  tauto


open FirstOrder FirstOrder.Language

variable (M : Type*) [LRV.Structure M]

/-! ## 8bis. Exactly which sentences clash with the intended model -/

/-- **The obstruction, isolated.**  These seven facts about an `L_RV`-structure are all that
the derivation uses.  Every structure satisfying them has `0 = ∞`, so *any* axiom set
containing them (in particular `ACVF`) has no model in which `0` and `∞` are distinct. -/
theorem obstacle_core (M : Type*) [LRV.Structure M]
    (hInf : iRV (M := M) iRVInfty)
    (hOneRV : iRV (M := M) iRVOne)
    (hOne : iUnits (M := M) iRVOne)
    (hUnits : ∀ x : M, iRV x → (iUnits x ↔ (¬ x = iRVInfty ∧ ¬ x = iRVZero)))
    (hMulInfty : ∀ y : M, iRV y → iRVMul y iRVInfty = iRVInfty)
    (hComm : ∀ x y : M, iRV x → iRV y → iRVMul x y = iRVMul y x)
    (hInv : ∀ x : M, iRV x → x = iRVZero ∨ ∃ y : M, iRV y ∧ iRVMul x y = iRVOne) :
    (iRVZero : M) = iRVInfty := by
  have hne : ¬ ((iRVOne : M) = iRVInfty) := (hUnits iRVOne hOneRV).mp hOne |>.1
  rcases hInv iRVInfty hInf with h | ⟨y, hy, hmul⟩
  · exact h.symm
  · exfalso
    have h1 : iRVMul iRVInfty y = iRVInfty := by
      rw [hComm iRVInfty y hInf hy, hMulInfty y hy]
    exact hne (by rw [← hmul, h1])

/-! ## 9. The intended carrier is not a model -/

/-- the guarded sentence `kFieldInv` says nothing at `∞`, because `∞ ≠ ∞` is false -/
theorem pK_infty_false {n : ℕ} (xs : Fin n → M) :
    ¬ (LRV.pK (LRV.tRVInfty : LRV.Tm n)).Realize v0 xs := by
  rw [realize_pK, realize_tRVInfty]
  intro h
  exact h rfl

/-- the repaired invertibility axiom of the `K`-sort: `x` and its inverse range over
`K = RV ∖ {∞}` (`pK`), not over the whole `RV` sort -/
def kFieldInvFixed : LRV.Sentence :=
  LRV.allSorted ![SortTag.rv]
    (LRV.pK &0 ⟹ (LRV.pEq &0 LRV.tRVZero ⊔
      LRV.exSorted SortTag.rv (LRV.pK &1 ⊓ LRV.pEq (LRV.tRVMul &0 &1) LRV.tRVOne)))

end Model

namespace Model

open FirstOrder FirstOrder.Language

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀)

/-- the intended carrier: `K ⊕ RV₀ v`, outer `none` the residue zero `0`,
`some none` the point `∞` at the top of the preorder -/
abbrev Carrier : Type _ := K ⊕ Valued.RV0 v

/-- **VACUOUS under the author's convention \(0 = ∞ = rv 0\).**  Any `L_RV`-structure on the
old three-layer carrier `K ⊕ RV₀ v` that puts the constant `0` of the `RV`-sort on
`Sum.inr none` and the constant `∞` on `Sum.inr (some none)` fails `ACVF` — but in the
converted encoding `iRVInfty` *is* `iRVZero`, so the two hypotheses of this theorem are
contradictory and the statement holds trivially.  Kept (with its statement unchanged) as the
record of the pre-ruling situation. -/
theorem intended_carrier_does_not_model_ACVF (inst : LRV.Structure (K ⊕ Valued.RV0 v))
    (hz : @iRVZero (K ⊕ Valued.RV0 v) inst = Sum.inr (none : Option (Valued.RV v)))
    (hi : @iRVInfty (K ⊕ Valued.RV0 v) inst = Sum.inr (some (none : Valued.RV v))) :
    ¬ (K ⊕ Valued.RV0 v) ⊨ Axioms.ACVF := by
  intro hM
  have h := ACVF_forces_zero_eq_infty (M := K ⊕ Valued.RV0 v) hM
  rw [hz, hi] at h
  exact absurd h (by simp)

/-- the same for `ACVF(0,0)`; vacuous for the same reason as
`intended_carrier_does_not_model_ACVF` -/
theorem intended_carrier_does_not_model_ACVF00 (inst : LRV.Structure (K ⊕ Valued.RV0 v))
    (hz : @iRVZero (K ⊕ Valued.RV0 v) inst = Sum.inr (none : Option (Valued.RV v)))
    (hi : @iRVInfty (K ⊕ Valued.RV0 v) inst = Sum.inr (some (none : Valued.RV v))) :
    ¬ (K ⊕ Valued.RV0 v) ⊨ Axioms.ACVF00 := by
  intro hM
  have hACVF : (K ⊕ Valued.RV0 v) ⊨ Axioms.ACVF :=
    Theory.Model.mk (fun ψ hψ => hM.realize_of_mem ψ (by
      simp only [Axioms.ACVF00, Set.mem_union]; tauto))
  exact intended_carrier_does_not_model_ACVF v inst hz hi hACVF

end Model

namespace Model

open FirstOrder FirstOrder.Language

/-- `⋀ i < k, x_i ≠ ∞`, i.e. the tuple of coefficients lies in `K = RV ∖ {∞}` -/
def kHyps (k : ℕ) : LRV.Bf k :=
  (List.finRange k).foldr (fun i acc => LRV.pK (LRV.tv i.val i.isLt) ⊓ acc) ⊤

/-- **The repaired `K`-sort field axioms**: every quantifier is restricted to `K = RV ∖ {∞}`
(`pK`), so nothing is asserted about `∞`.  Compare `Axioms.fieldAxioms .rv`, whose guards
are the whole `RV` sort. -/
def fieldAxiomsK : List LRV.Sentence :=
  [ /- associativity of `+` -/
    LRV.allSorted ![SortTag.rv, SortTag.rv, SortTag.rv]
      (LRV.pK &0 ⟹ LRV.pK &1 ⟹ LRV.pK &2 ⟹
        LRV.pEq (LRV.tKAdd (LRV.tKAdd &0 &1) &2) (LRV.tKAdd &0 (LRV.tKAdd &1 &2))),
    /- commutativity of `+` -/
    LRV.allSorted ![SortTag.rv, SortTag.rv]
      (LRV.pK &0 ⟹ LRV.pK &1 ⟹ LRV.pEq (LRV.tKAdd &0 &1) (LRV.tKAdd &1 &0)),
    /- `0` is neutral for `+` -/
    LRV.allSorted ![SortTag.rv] (LRV.pK &0 ⟹ LRV.pEq (LRV.tKAdd &0 LRV.tRVZero) &0),
    /- additive inverses -/
    LRV.allSorted ![SortTag.rv]
      (LRV.pK &0 ⟹ LRV.pEq (LRV.tKAdd &0 (LRV.tKNeg &0)) LRV.tRVZero),
    /- associativity of `×` -/
    LRV.allSorted ![SortTag.rv, SortTag.rv, SortTag.rv]
      (LRV.pK &0 ⟹ LRV.pK &1 ⟹ LRV.pK &2 ⟹
        LRV.pEq (LRV.tRVMul (LRV.tRVMul &0 &1) &2) (LRV.tRVMul &0 (LRV.tRVMul &1 &2))),
    /- commutativity of `×` -/
    LRV.allSorted ![SortTag.rv, SortTag.rv]
      (LRV.pK &0 ⟹ LRV.pK &1 ⟹ LRV.pEq (LRV.tRVMul &0 &1) (LRV.tRVMul &1 &0)),
    /- `1` is neutral for `×` -/
    LRV.allSorted ![SortTag.rv] (LRV.pK &0 ⟹ LRV.pEq (LRV.tRVMul &0 LRV.tRVOne) &0),
    /- distributivity -/
    LRV.allSorted ![SortTag.rv, SortTag.rv, SortTag.rv]
      (LRV.pK &0 ⟹ LRV.pK &1 ⟹ LRV.pK &2 ⟹
        LRV.pEq (LRV.tRVMul &0 (LRV.tKAdd &1 &2))
          (LRV.tKAdd (LRV.tRVMul &0 &1) (LRV.tRVMul &0 &2))),
    /- `0 ≠ 1` -/
    ∼(LRV.pEq LRV.tRVZero LRV.tRVOne),
    /- invertibility, restricted to `K` -/
    kFieldInvFixed ]

/-- the repaired `K`-sort algebraic-closedness scheme: coefficients and root in `K` -/
def kAlgClosedFixed (k : ℕ) : LRV.Sentence :=
  LRV.allSorted (fun _ : Fin k => SortTag.rv)
    (kHyps k ⟹ LRV.exSorted SortTag.rv
      (LRV.pK (LRV.tv k (Nat.lt_succ_self k)) ⊓
        LRV.pEq (LRV.hornerPoly LRV.tKAdd LRV.tRVMul) LRV.tRVZero))

/-- the repaired invertibility axiom is one of the repaired field axioms -/
theorem kFieldInvFixed_mem : kFieldInvFixed ∈ fieldAxiomsK := by
  simp only [fieldAxiomsK, List.mem_cons, List.not_mem_nil, or_false]
  tauto

end Model

/-! ## 10. Axiom audit -/

#print axioms SpecialTransformations.Milestone0.Model.ACVF_forces_zero_eq_infty
#print axioms SpecialTransformations.Milestone0.Model.ACVF00_forces_zero_eq_infty
#print axioms SpecialTransformations.Milestone0.Model.intended_carrier_does_not_model_ACVF
#print axioms SpecialTransformations.Milestone0.Model.obstacle_core
#print axioms SpecialTransformations.Milestone0.Model.intended_carrier_does_not_model_ACVF00
#print axioms SpecialTransformations.Milestone0.Model.kFieldInvFixed_mem
#print axioms SpecialTransformations.Milestone0.Model.kField_inv_mem
#print axioms SpecialTransformations.Milestone0.Model.models_sdUnits
#print axioms SpecialTransformations.Milestone0.Model.models_kField_inv
#print axioms SpecialTransformations.Milestone0.Model.pK_infty_false
#print axioms SpecialTransformations.Milestone0.Model.realize_sortedHyps_two_rv
