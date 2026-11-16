module

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

/-- **The language `L_RV` of Definition 2.1**, in the tagged one-sorted encoding.
Declared as an abbreviation so that `LRV.Relations`/`LRV.Functions` are transparent to
unification; this is the same language, definitionally. -/
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
namespace SpecialTransformations
namespace RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

section Basics

variable (v : Valuation K Γ₀)

/-- `RV× = Kˣ / (1 + M)`, the multiplicative RV sort. -/
abbrev RVUnit : Type _ := Kˣ ⧸ v.valuationSubring.principalUnitGroup

/-- The RV sort with the point at infinity: `RV = RV× ∪ {∞}`.  `none` is `∞`. -/
abbrev RV : Type _ := Option (RVUnit v)

/-- The old three-layer carrier `RV0 = RV ∪ {0}` (outer `none` the added residue zero).
It is kept only as a legacy alias: the paper's `0` and `∞` are *one* element (`rv 0`), so the
intended structure below is built on the two-layer `RV v` and nothing here uses `RV0`. -/
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
/-- Legacy (unused by the intended structure, cf. `RV0`): an admissible reading of the
paper's multiplication on the old three-layer `RV_0 = RV ∪ {0}`: the group law
on `RV^×`, `∞` absorbing, `0` absorbing on `K`.  (The axioms do not determine `t × 0` for
`t ∈ RV^× ∖ K^×`, so this is one faithful choice.) -/
def rv0Mul : RV0 v → RV0 v → RV0 v
  | some none, _ => some none
  | _, some none => some none
  | none, _ => none
  | some (some _), none => none
  | some (some a), some (some b) => some (some (a * b))

/-- Legacy (unused by the intended structure): the old order on the three-layer `RV_0`, where
the residue-field zero was the bottom and `∞` the top.  With `0 = ∞ = rv 0` one element, the
order of the intended structure is `RVM.rvLe` on `RV`, whose top is `none` (`le_infty`). -/
def le0 : RV0 v → RV0 v → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => rvLe v a b

/-- Legacy (unused by the intended structure): `K^×` as a subset of the old three-layer
`RV_0`, the class of `1` (axiom 4).  In the two-layer carrier this is
`{t : RV v | ∃ q, t = some q ∧ vrv v (some q) = 1}`. -/
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
`M = VF ⊕ RV` with `VF = K` and `RV = Option (Kˣ ⧸ (1+𝔪))`.

The `RV` part has exactly **two** layers, the paper's two cases: `none` is `rv 0`, and `some q`
is the group element `rv(x)` of the unit `x`.  `rv 0` is the residue field's zero `0`, the
absorbing element of `RV`, *and* the paper's top element `∞`: one element, not three. -/
abbrev C : Type _ := K ⊕ RVM.RV v

/-- the `VF`-tag -/
def mkVF (x : K) : C v := Sum.inl x
/-- the `RV`-tag -/
def mkRV (t : RVM.RV v) : C v := Sum.inr t

/-- the paper's `0`: the residue field's zero, `rv 0`, and the absorbing top `∞` -/
def cKZero : C v := Sum.inr none
/-- the paper's `∞ = rv 0`, the *same* carrier element as `0` -/
def cInfty : C v := Sum.inr none
/-- an element of `RV^×`, i.e. the class of a unit -/
def cUnit (q : RVM.RVUnit v) : C v := Sum.inr (some q)
/-- the paper's `1` in the `RV` sort -/
noncomputable def cRVOne : C v := Sum.inr (RVM.rvOne v)

/-- Junk totalisation of the residue field's `+` on `RV`: `0` as soon as one argument is `0`,
and the *nonzero* junk value `1` otherwise.  (The junk value used to be `0`, which is correct
only while `0` and `∞` are two distinct symbols: with `0 = ∞` the guard `pK` is `≠ 0`, and a
junk value `0` would falsify the sort-closure sentence `sdKAdd`.) -/
noncomputable def kAdd (t s : RVM.RV v) : RVM.RV v :=
  if t = none ∨ s = none then none else some 1

/-- Junk totalisation of the residue field's `-`, with the nonzero junk value `1` off `0`
(see `kAdd`). -/
noncomputable def kNeg (t : RVM.RV v) : RVM.RV v := if t = none then none else some 1

/-- The interpretation of the eleven function symbols.  The junk value for the partial
symbols is `∞` (`Milestone0/Partiality.lean`) off the intended sort — and `∞ = 0 = rv 0`, so
the junk value of the `VF` symbols is the `RV`-sort's absorbing element; `kAdd`, `kNeg` (the
residue field's `+`/`-`) keep their junk value `1` on `K = RV ∖ {0}` (see `kAdd`).  The field
axioms for `K` itself (`kField`, `kAlgClosed`) are proved only in the trivially valued case,
where `K` *is* the residue field. -/
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
      | Sum.inr t, Sum.inr s => mkRV v (RVM.rvMul t s)
      | _, _ => cInfty v
  | _, .kAdd, xs => match xs 0, xs 1 with
      | Sum.inr t, Sum.inr s => mkRV v (kAdd v t s)
      | _, _ => cInfty v
  | _, .kNeg, xs => match xs 0 with
      | Sum.inr t => mkRV v (kNeg v t)
      | _ => cInfty v
  | _, .rvMap, xs => match xs 0 with
      | Sum.inl a => mkRV v (RVM.rv v a)
      | _ => cInfty v

/-- The interpretation of the four relation symbols. -/
noncomputable def rMap : {n : ℕ} → Rel n → (Fin n → C v) → Prop
  | _, .memVF, xs => ∃ x : K, xs 0 = mkVF v x
  | _, .memRV, xs => ∃ t : RVM.RV v, xs 0 = mkRV v t
  | _, .memUnits, xs => ∃ q : RVM.RVUnit v, xs 0 = cUnit v q ∧ RVM.vrv v (some q) = 1
  | _, .rvLe, xs => ∃ t s : RVM.RV v, xs 0 = mkRV v t ∧ xs 1 = mkRV v s ∧ RVM.rvLe v t s

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
  exact ⟨RVM.rvMul s t, rfl⟩

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
  have h1 : RVM.rv v a = none := by simpa [mkVF, fMap] using hh
  rw [RVM.rv_eq_none_iff] at h1
  rw [h1]
  rfl

theorem model_rvMulHom : (C v) ⊨ Axioms.rvMulHom := by
  simp only [Axioms.rvMulHom]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  obtain ⟨b, hb⟩ := (h 1).1 rfl
  rw [ha, hb]
  show Sum.inr (RVM.rv v (a * b)) = Sum.inr (RVM.rvMul (RVM.rv v a) (RVM.rv v b))
  rw [RVM.rv_mul]

theorem model_rvSurj : (C v) ⊨ Axioms.rvSurj := by
  simp only [Axioms.rvSurj]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  intro hne
  have ht0 : t ≠ none := by rintro rfl; exact hne ht
  obtain ⟨x, -, hxq⟩ := RVM.rv_surjective (v := v) (t := t) ht0
  refine ⟨mkVF v x, ⟨x, rfl⟩, ?_⟩
  show Sum.inr (RVM.rv v x) = xs 0
  rw [hxq, ht]
  rfl

theorem rvLe_rv_add (a b : K) :
    RVM.rvLe v (RVM.rv v a) (RVM.rv v (a + b)) ∨
      RVM.rvLe v (RVM.rv v b) (RVM.rv v (a + b)) := by
  simp only [show ∀ x y : K, RVM.rvLe v (RVM.rv v x) (RVM.rv v y) =
      (RVM.vrv v (RVM.rv v y) ≤ RVM.vrv v (RVM.rv v x)) from fun x y => rfl, RVM.vrv_rv]
  exact Valuation.map_add' v a b

theorem model_rvUltrametric : (C v) ⊨ Axioms.rvUltrametric := by
  simp only [Axioms.rvUltrametric]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  obtain ⟨b, hb⟩ := (h 1).1 rfl
  rw [ha, hb]
  rcases rvLe_rv_add v a b with h | h
  · exact Or.inl ⟨RVM.rv v a, RVM.rv v (a + b), rfl, rfl, h⟩
  · exact Or.inr ⟨RVM.rv v b, RVM.rv v (a + b), rfl, rfl, h⟩


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
  · simp only [cUnit]
    rw [RVM.rvMul_some_some]
  · rw [← RVM.rvMul_some_some, RVM.vrv_mul, hv1, hv2, mul_one]

theorem model_rvMulComm : (C v) ⊨ Axioms.rvMulComm := by
  simp only [Axioms.rvMulComm]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  rw [ht, hs]
  exact congrArg (fun x => mkRV v x) (RVM.rvMul_comm t s)

theorem model_rvMulAssoc : (C v) ⊨ Axioms.rvMulAssoc := by
  simp only [Axioms.rvMulAssoc]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  obtain ⟨r, hr⟩ := (h 2).2 rfl
  rw [ht, hs, hr]
  exact congrArg (fun x => mkRV v x) (RVM.rvMul_assoc t s r)

theorem model_rvMulOne : (C v) ⊨ Axioms.rvMulOne := by
  simp only [Axioms.rvMulOne]; rw [model_allSorted v]; intro xs h; prep
  rintro ⟨q, hq, -⟩
  rw [hq]
  show Sum.inr (RVM.rvMul (RVM.rvOne v) (some q)) = Sum.inr (some q)
  rw [RVM.rvOne_eq, RVM.rvMul_some_some]
  exact congrArg (fun x => Sum.inr (some x)) (one_mul q)

theorem model_rvMulZeroK : (C v) ⊨ Axioms.rvMulZeroK := by
  simp only [Axioms.rvMulZeroK]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  intro hpK
  rw [ht] at hpK ⊢
  rcases t with _ | q
  · simp only [mkRV, cKZero]; simp [RVM.rvMul]
  · simp only [mkRV, cKZero]; simp [RVM.rvMul]

/-- **`sdUnits` holds at the intended structure**: the predicate `K^×` is borne by
`RV`-sort elements (its actual content is `leClassOne`, i.e. `K^× = ker vrv`). -/
theorem models_sdUnits : (C v) ⊨ Axioms.sdUnits := by
  simp only [Axioms.sdUnits, LRV.allOne]
  rw [model_alls v]
  intro xs
  prep
  rintro ⟨q, hq, -⟩
  exact ⟨q, hq⟩

/-! ### the preorder on `RV` (Definition 2.2 item 4) -/

theorem rvLe_mkRV_iff {t s : RVM.RV v} :
    (∃ a b : RVM.RV v, mkRV v t = mkRV v a ∧ mkRV v s = mkRV v b ∧ RVM.rvLe v a b) ↔
      RVM.rvLe v t s := by
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
  exact ⟨t, t, rfl, rfl, le_rfl⟩

theorem model_leTotal : (C v) ⊨ Axioms.leTotal := by
  simp only [Axioms.leTotal]; rw [model_allSorted v]; intro xs h; prep
  intro _ _
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  rw [ht, hs]
  rcases le_total (RVM.vrv v s) (RVM.vrv v t) with h' | h'
  · exact Or.inl ⟨t, s, rfl, rfl, h'⟩
  · exact Or.inr ⟨s, t, rfl, rfl, h'⟩

theorem model_leTop : (C v) ⊨ Axioms.leTop := by
  simp only [Axioms.leTop]; rw [model_allSorted v]; intro xs h; prep
  intro _
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht]
  exact ⟨t, none, rfl, rfl, show RVM.rvLe v t none from RVM.le_infty v t⟩

theorem model_leInftyEq : (C v) ⊨ Axioms.leInftyEq := by
  simp only [Axioms.leInftyEq]; rw [model_allSorted v]; intro xs h; prep
  intro _ hle
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht] at hle ⊢
  obtain ⟨a, b, ha, hb, hab⟩ := hle
  simp only [mkRV, Sum.inr.injEq] at ha hb
  subst ha
  subst hb
  have h0 : RVM.vrv v t = 0 := le_antisymm hab zero_le
  rcases t with _ | q
  · rfl
  · exact absurd h0 (by simp [RVM.vrv_some])

/-! ### the residue-arithmetic sort-closure sentences -/

theorem model_sdKAdd : (C v) ⊨ Axioms.sdKAdd := by
  simp only [Axioms.sdKAdd]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  simp only [mkRV] at ht hs
  intro h1 h2
  have ht0 : t ≠ none := fun hc => h1 (by rw [ht, hc])
  have hs0 : s ≠ none := fun hc => h2 (by rw [hs, hc])
  simp only [ht, hs, fMap, kAdd, cKZero, mkRV, ht0, hs0, or_false, if_false]
  simp

theorem model_sdKNeg : (C v) ⊨ Axioms.sdKNeg := by
  simp only [Axioms.sdKNeg]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  simp only [mkRV] at ht
  intro h1
  have ht0 : t ≠ none := fun hc => h1 (by rw [ht, hc])
  simp only [ht, fMap, kNeg, cKZero, mkRV, ht0, if_false]
  simp

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
  obtain rfl := by simpa using h15
  exact model_sdKNeg v

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

/-! ## axiom footprint -/

#print axioms SpecialTransformations.Milestone0.IModel.model_sortAxioms_all
#print axioms SpecialTransformations.Milestone0.IModel.model_vfField
#print axioms SpecialTransformations.Milestone0.IModel.model_rvAxioms_all
#print axioms SpecialTransformations.Milestone0.IModel.model_preorderRV_easy
#print axioms SpecialTransformations.Milestone0.IModel.model_rvMulAssoc
