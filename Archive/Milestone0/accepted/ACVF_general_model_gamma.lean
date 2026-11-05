/-
Copied verbatim from `.ultramath/smw06c8tw/m2/kFieldModel.lean` (member m2, swarm smw06c8tw,
direction d3) at 05:15 UTC, for independent verification by m6; the section marked
"added by m6" at the end is mine.  The copied part proves

    theorem model_ACVF [IsAlgClosed K] : (C v) ⊨ Axioms.ACVF
    theorem model_kField, theorem model_kAlgClosed, theorem model_rvGroup
    theorem model_ACVF00 [IsAlgClosed K] [CharZero K]
        (h : ∀ n : ℕ, n ≠ 0 → (1 : Γ₀) ≤ v (n : K)) : (C v) ⊨ Axioms.ACVF00

i.e. Definition 2.2 at the intended structure `C v = K ⊕ RV₀ v` for an arbitrary valuation of
an algebraically closed field.  m6 verified: `lean general_model.lean` exits 0, no `sorry`,
and every `#print axioms` is `[propext, Classical.choice, Quot.sound]`.
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

/-- `t ∈ K = K^× ∪ {0}`, the residue field inside the `RV` sort. -/
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
/-- `K` is closed under `×` -/
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

end Milestone0
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
noncomputable def kField : Field (Option (KUnits v)) :=
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

#print axioms ACVFResidue.isAlgClosed_residueField
#print axioms ACVFResidue.exists_root_of_monic
#print axioms ACVFResidue.isIntegral_of_isUnit_leadingCoeff
#print axioms ACVFResidue.isAlgClosed_k
#print axioms ACVFResidue.charZero_residueField_iff

namespace SpecialTransformations
namespace RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

section Basics

variable (v : Valuation K Γ₀)

/-- `RV× = Kˣ / (1 + M)`, the multiplicative RV sort. -/
abbrev RVUnit : Type _ := Kˣ ⧸ v.valuationSubring.principalUnitGroup

/-- The `RV` sort: `RV = RV^× ∪ {rv 0}`.  `none` is `rv 0` — the absorbing element of `RV`,
the zero of the residue field, and the paper's `∞`: by the ruling these are one element, so
the carrier has no layer between `rv 0` and the group elements. -/
abbrev RV : Type _ := Option (RVUnit v)

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
/-- `K^×` as a subset of the `RV` sort: the class of `1`, i.e. the residue field's units
(axiom 4).  The residue-field zero is `none`, which is also `rv 0` and the absorbing `∞`. -/
def Kx : Set (RV v) := {t | ∃ q : RVUnit v, t = some q ∧ vrv v (some q) = 1}

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

end Extra
end RVM
end SpecialTransformations

namespace SpecialTransformations
namespace Milestone0
namespace IModel

open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-- The carrier of the intended `L_RV`-structure of the valued field `(K, v)`:
`M = VF ⊕ RV` with `VF = K` and `RV = Option (Kˣ ⧸ (1+𝔪)) = RV^× ∪ {rv 0}`. -/
abbrev C : Type _ := K ⊕ RVM.RV v

/-- the `VF`-tag -/
def mkVF (x : K) : C v := Sum.inl x
/-- the `RV`-tag -/
def mkRV (t : RVM.RV v) : C v := Sum.inr t

/-- The paper's `0` in the `RV` sort: the residue field's zero, which is `rv 0` and the
absorbing element `∞`.  One element, the `none` of `RV`. -/
def cKZero : C v := Sum.inr none
/-- The paper's `∞`: the same element as `0` of the `RV` sort, since `rv 0 = ∞`. -/
def cInfty : C v := Sum.inr none
/-- an element of `RV^×`, i.e. the class of a unit -/
def cUnit (q : RVM.RVUnit v) : C v := Sum.inr (some q)
/-- the paper's `1` in the `RV` sort -/
noncomputable def cRVOne : C v := Sum.inr (RVM.rvOne v)

/-- The units of the internal residue field `k = K^× ∪ {0}` of the `RV`-sort, embedded
in `RV`: `none ↦ 0` and `some u ↦ u`.  This is a bijection onto `K = {0} ∪ K^×`
(`Axioms.pInK`); `0` is `none`, which is also `rv 0` and the absorbing `∞`. -/
def iota (v : Valuation K Γ₀) : Option (ACVFResidue.KUnits v) → RVM.RV v
  | none => none
  | some u => some (u : RVM.RVUnit v)

/-- The inverse of `iota` on its range; off the range it is `0`. -/
noncomputable def jota (v : Valuation K Γ₀) : RVM.RV v → Option (ACVFResidue.KUnits v)
  | none => none
  | some q => by
      classical
      exact if h : ∃ u : ACVFResidue.KUnits v, (u : RVM.RVUnit v) = q then some h.choose else none

/-- The residue-field `+` of the `RV` sort, read through `iota`/`jota`. -/
noncomputable def kAddFun (v : Valuation K Γ₀) (a b : RVM.RV v) : RVM.RV v :=
  letI := ACVFResidue.kField v
  iota v (jota v a + jota v b)

/-- The residue-field unary `-` of the `RV` sort, read through `iota`/`jota`. -/
noncomputable def kNegFun (v : Valuation K Γ₀) (a : RVM.RV v) : RVM.RV v :=
  letI := ACVFResidue.kField v
  iota v (- jota v a)

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
      | Sum.inr t, Sum.inr s => mkRV v (RVM.rvMul t s)
      | _, _ => cInfty v
  | _, .kAdd, xs => match xs 0, xs 1 with
      | Sum.inr a, Sum.inr b => mkRV v (kAddFun v a b)
      | _, _ => cInfty v
  | _, .kNeg, xs => match xs 0 with
      | Sum.inr a => mkRV v (kNegFun v a)
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
      exact ⟨fun _ => (realize_sortPred_vf v i xs).mp (hss ▸ hi), fun hh => by simp at hh⟩
    | rv =>
      exact ⟨fun hh => by simp at hh, fun _ => (realize_sortPred_rv v i xs).mp (hss ▸ hi)⟩
  · intro h φ _
    rcases h φ with ⟨hvf, hrv⟩
    cases hss : ss φ with
    | vf => exact (realize_sortPred_vf v φ xs).mpr (hvf hss)
    | rv => exact (realize_sortPred_rv v φ xs).mpr (hrv hss)

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

/-! ## Part 3. The internal residue field `k = K^× ∪ {0}` of the `RV` sort

The paper's residue field sits inside the `RV` sort as `K = K^× ∪ {0}`, where `K^×` is
the class of `1` (axiom 4).  We build it as `Option (KUnits v)` — `0` adjoined to
`K^× = ker vrv ≅ k^×` (the bridge `kEquiv` of the residue-field file) — and read it in the
carrier through the injection `iota`.  The residue-field operations `+`, `-` on the
`RV` sort are then *defined* to be the transported ones (`kAddFun`, `kNegFun`), which is
what makes `kField` hold; `×` is the `RV`-multiplication `rvMul` of the rvGroup block,
which already agrees with the field's `×` on `K`. -/

attribute [local instance] ACVFResidue.kField

/-! ### 3.1 The two spellings of `K^×`: `ker vrv` and the residue field's units -/

theorem vrvUnit_mk' (u : Kˣ) :
    ACVFResidue.vrvUnit v (QuotientGroup.mk' v.valuationSubring.principalUnitGroup u)
      = ACVFResidue.vUnits v u := by
  rw [ACVFResidue.vrvUnit, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']

theorem vUnits_eq_one {u : v.valuationSubring.unitGroup} : ACVFResidue.vUnits v u = 1 :=
  Units.ext ((Valuation.mem_unitGroup_iff K v (u : Kˣ)).1 u.2)

theorem mem_kUnits_iff (q : RVM.RVUnit v) :
    q ∈ ACVFResidue.kUnitsSubgroup v ↔ RVM.vrv v (some q) = 1 := by
  rw [RVM.vrv_kernel]
  constructor
  · intro hq
    obtain ⟨u, hu⟩ := ACVFResidue.unitGroupToKUnits_surjective v ⟨q, hq⟩
    exact ⟨u, congrArg some (congrArg Subtype.val hu)⟩
  · rintro ⟨u, hu⟩
    have hu' : (QuotientGroup.mk' v.valuationSubring.principalUnitGroup (u : Kˣ) :
        RVM.RVUnit v) = q := Option.some.inj hu
    show ACVFResidue.vrvUnit v q = 1
    rw [← hu', vrvUnit_mk']
    exact vUnits_eq_one v

/-! ### 3.2 The zero and the one of the transported field, concretely -/

theorem zero_eq_none : (0 : Option (ACVFResidue.KUnits v)) = none := by
  have h : (0 : Option (ACVFResidue.KUnits v)) = (ACVFResidue.kEquiv v).symm 0 := rfl
  rw [h, Equiv.symm_apply_eq]
  rfl

theorem kEquiv_some_one :
    ACVFResidue.kEquiv v (some (1 : ACVFResidue.KUnits v)) = 1 := by
  show ((ACVFResidue.kUnitsEquivResidueUnits v (1 : ACVFResidue.KUnits v) :
      (ACVFResidue.ResidueField v)ˣ) : ACVFResidue.ResidueField v) = 1
  rw [show ACVFResidue.kUnitsEquivResidueUnits v (1 : ACVFResidue.KUnits v) = 1 from map_one _]
  rfl

theorem one_eq_some : (1 : Option (ACVFResidue.KUnits v)) = some 1 := by
  have h : (1 : Option (ACVFResidue.KUnits v)) = (ACVFResidue.kEquiv v).symm 1 := rfl
  rw [h, Equiv.symm_apply_eq]
  exact (kEquiv_some_one v).symm

theorem mul_some_some (a b : ACVFResidue.KUnits v) :
    (some a : Option (ACVFResidue.KUnits v)) * some b = some (a * b) := by
  have h : ((some a : Option (ACVFResidue.KUnits v)) * some b)
      = (ACVFResidue.kEquiv v).symm ((ACVFResidue.kEquiv v (some a)) *
          (ACVFResidue.kEquiv v (some b))) := rfl
  rw [h, Equiv.symm_apply_eq]
  show (ACVFResidue.kEquiv v (some a)) * (ACVFResidue.kEquiv v (some b))
      = (ACVFResidue.kEquiv v) (some (a * b))
  rw [show (ACVFResidue.kEquiv v (some a))
        = ((ACVFResidue.kUnitsEquivResidueUnits v a :
            (ACVFResidue.ResidueField v)ˣ) : ACVFResidue.ResidueField v) from rfl,
      show (ACVFResidue.kEquiv v (some b))
        = ((ACVFResidue.kUnitsEquivResidueUnits v b :
            (ACVFResidue.ResidueField v)ˣ) : ACVFResidue.ResidueField v) from rfl,
      show (ACVFResidue.kEquiv v (some (a * b)))
        = ((ACVFResidue.kUnitsEquivResidueUnits v (a * b) :
            (ACVFResidue.ResidueField v)ˣ) : ACVFResidue.ResidueField v) from rfl,
      ← Units.val_mul, ← map_mul]

theorem mul_none_left (b : Option (ACVFResidue.KUnits v)) :
    (none : Option (ACVFResidue.KUnits v)) * b = none := by
  rw [show (none : Option (ACVFResidue.KUnits v)) = 0 from (zero_eq_none v).symm, zero_mul,
    zero_eq_none v]

theorem mul_none_right (a : Option (ACVFResidue.KUnits v)) :
    a * (none : Option (ACVFResidue.KUnits v)) = none := by
  rw [show (none : Option (ACVFResidue.KUnits v)) = 0 from (zero_eq_none v).symm, mul_zero,
    zero_eq_none v]

/-! ### 3.3 `iota` and its inverse -/

theorem jota_iota (a : Option (ACVFResidue.KUnits v)) : jota v (iota v a) = a := by
  cases a with
  | none => rfl
  | some u =>
    simp only [iota, jota]
    by_cases h : ∃ w : ACVFResidue.KUnits v, (w : RVM.RVUnit v) = (u : RVM.RVUnit v)
    · rw [dif_pos h]
      exact congrArg some (Subtype.ext (Classical.choose_spec h))
    · exact absurd ⟨u, rfl⟩ h

theorem iota_injective : Function.Injective (iota v) := by
  intro a b h
  have h2 := congrArg (jota v) h
  rwa [jota_iota, jota_iota] at h2

theorem iota_zero : iota v (0 : Option (ACVFResidue.KUnits v)) = none := by
  rw [zero_eq_none]
  rfl

theorem iota_one : iota v (1 : Option (ACVFResidue.KUnits v))
    = some (1 : RVM.RVUnit v) := by
  rw [one_eq_some]
  rfl

/-- `iota 0` is the residue-field zero `0` of the `RV` sort -/
theorem mkRV_iota_zero : (Sum.inr (iota v 0) : C v) = cKZero v := by
  rw [iota_zero]
  rfl

/-- `iota 1` is the `1` of the `RV` sort -/
theorem mkRV_iota_one : (Sum.inr (iota v 1) : C v) = cRVOne v := by
  rw [iota_one]
  show Sum.inr (some (1 : RVM.RVUnit v)) = Sum.inr (RVM.rvOne v)
  rw [RVM.rvOne_eq]

/-! ### 3.4 The residue-field operations read in the carrier -/

theorem kAdd_iota (a b : Option (ACVFResidue.KUnits v)) :
    kAddFun v (iota v a) (iota v b) = iota v (a + b) := by
  simp only [kAddFun, jota_iota]

theorem kNeg_iota (a : Option (ACVFResidue.KUnits v)) :
    kNegFun v (iota v a) = iota v (-a) := by
  simp only [kNegFun, jota_iota]

theorem kMul_iota (a b : Option (ACVFResidue.KUnits v)) :
    RVM.rvMul (iota v a) (iota v b) = iota v (a * b) := by
  cases a with
  | none =>
    cases b with
    | none => rw [mul_none_left]; rfl
    | some b => rw [mul_none_left]; rfl
  | some a =>
    cases b with
    | none => rw [mul_none_right]; rfl
    | some b => rw [mul_some_some]; rfl

/-! ### 3.5 Reading the guards `K^×` and `K = K^× ∪ {0}` -/

theorem realize_pUnits_var {n : ℕ} (xs : Fin n → C v) (i : Fin n) :
    (LRV.pUnits (LRV.tv i.val i.isLt)).Realize (dflt v) xs ↔
      ∃ q : RVM.RVUnit v, xs i = cUnit v q ∧ RVM.vrv v (some q) = 1 := by
  prep

theorem realize_eq_var_zero {n : ℕ} (xs : Fin n → C v) (i : Fin n) :
    (LRV.pEq (LRV.tv i.val i.isLt) LRV.tRVZero).Realize (dflt v) xs ↔ xs i = cKZero v := by
  prep

theorem realize_pInK_var {n : ℕ} (xs : Fin n → C v) (i : Fin n) :
    (LRV.pInK (LRV.tv i.val i.isLt)).Realize (dflt v) xs ↔
      ∃ a : Option (ACVFResidue.KUnits v), xs i = Sum.inr (iota v a) := by
  rw [LRV.pInK, BoundedFormula.realize_sup, realize_pUnits_var v xs i, realize_eq_var_zero v xs i]
  constructor
  · rintro (⟨q, hq, hv⟩ | h)
    · exact ⟨some ⟨q, (mem_kUnits_iff v q).mpr hv⟩, by rw [hq]; rfl⟩
    · exact ⟨none, by rw [h]; rfl⟩
  · rintro ⟨a, ha⟩
    rw [ha]
    cases a with
    | none => exact Or.inr rfl
    | some u => exact Or.inl ⟨(u : RVM.RVUnit v), rfl, (mem_kUnits_iff v _).mp u.2⟩

theorem realize_kHyps {k : ℕ} (xs : Fin k → C v) :
    (LRV.kHyps (k := k)).Realize (dflt v) xs ↔
      ∀ i : Fin k, ∃ a : Option (ACVFResidue.KUnits v), xs i = Sum.inr (iota v a) := by
  rw [LRV.kHyps, realize_foldr_inf v]
  constructor
  · intro h i
    exact (realize_pInK_var v xs i).mp (h i (List.mem_finRange i))
  · intro h i hi
    exact (realize_pInK_var v xs i).mpr (h i)

/-- **the `K`-guarded universal sentence, unfolded at the intended model**: universal
over `RV`-sorted tuples all of whose entries lie in `K = K^× ∪ {0}` -/
theorem model_allSortedK {k : ℕ} (ss : Fin k → SortTag) (φ : LRV.BoundedFormula Empty k) :
    ((C v) ⊨ LRV.allSortedK ss φ) ↔
      ∀ xs : Fin k → C v,
        (∀ i : Fin k, ((ss i = .vf → ∃ x : K, xs i = mkVF v x) ∧
          (ss i = .rv → ∃ t : RVM.RV v, xs i = mkRV v t))) →
        (∀ i : Fin k, ∃ a : Option (ACVFResidue.KUnits v), xs i = Sum.inr (iota v a)) →
        φ.Realize (dflt v) xs := by
  rw [LRV.allSortedK, model_alls v]
  refine forall_congr' (fun xs => ?_)
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_inf, realize_kHyps v xs]
  exact ⟨fun h hg hk => h ⟨(realize_sortedHyps v ss xs).mpr hg, hk⟩,
    fun h h1 => h ((realize_sortedHyps v ss xs).mp h1.1) h1.2⟩

/-- `exSortedK .rv` unfolded at the intended model: a witness in `K = K^× ∪ {0}` -/
theorem realize_exSortedK {k : ℕ} (xs : Fin k → C v) (φ : LRV.Bf (k + 1)) :
    (LRV.exSortedK .rv φ).Realize (dflt v) xs ↔
      ∃ y : C v, ((∃ t : RVM.RV v, y = mkRV v t) ∧
        (∃ a : Option (ACVFResidue.KUnits v), y = Sum.inr (iota v a))) ∧
        φ.Realize (dflt v) (Fin.snoc xs y) := by
  have h := BoundedFormula.realize_ex
    (θ := LRV.sortPred .rv (LRV.tv k (Nat.lt_succ_self k)) ⊓
      LRV.pInK (LRV.tv k (Nat.lt_succ_self k)) ⊓ φ)
    (v := dflt v) (xs := xs)
  refine h.trans (exists_congr fun y => ?_)
  rw [BoundedFormula.realize_inf, BoundedFormula.realize_inf]
  have hlast : (Fin.snoc xs y : Fin (k + 1) → C v) ⟨k, Nat.lt_succ_self k⟩ = y := by
    have h : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k := rfl
    rw [h, Fin.snoc_last]
  have h1 : (LRV.sortPred .rv (LRV.tv k (Nat.lt_succ_self k))).Realize (dflt v) (Fin.snoc xs y)
      ↔ ∃ t : RVM.RV v, y = mkRV v t := by
    rw [realize_sortPred_rv v (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) (Fin.snoc xs y), hlast]
  have h2 : (LRV.pInK (LRV.tv k (Nat.lt_succ_self k))).Realize (dflt v) (Fin.snoc xs y)
      ↔ ∃ a : Option (ACVFResidue.KUnits v), y = Sum.inr (iota v a) := by
    rw [realize_pInK_var v (Fin.snoc xs y) (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)), hlast]
  rw [h1, h2]

/-! ### 3.6 The ten sentences of `kField` -/

theorem model_ofList {l : List LRV.Sentence} (h : ∀ s ∈ l, (C v) ⊨ s) :
    (C v) ⊨ Axioms.ofList l := by
  rw [Theory.model_iff]
  intro s hs
  exact h s hs

theorem model_kAddAssoc : (C v) ⊨ LRV.allSortedK ![.rv, .rv, .rv]
    (LRV.pEq (LRV.tKAdd (LRV.tKAdd &0 &1) &2) (LRV.tKAdd &0 (LRV.tKAdd &1 &2))) := by
  rw [model_allSortedK v]
  intro xs h hk
  obtain ⟨a, ha⟩ := hk 0
  obtain ⟨b, hb⟩ := hk 1
  obtain ⟨c, hc⟩ := hk 2
  prep
  rw [ha, hb, hc]
  simp only [fMap, mkRV]
  rw [kAdd_iota, kAdd_iota, kAdd_iota, kAdd_iota, add_assoc]

theorem model_kAddComm : (C v) ⊨ LRV.allSortedK ![.rv, .rv]
    (LRV.pEq (LRV.tKAdd &0 &1) (LRV.tKAdd &1 &0)) := by
  rw [model_allSortedK v]
  intro xs h hk
  obtain ⟨a, ha⟩ := hk 0
  obtain ⟨b, hb⟩ := hk 1
  prep
  rw [ha, hb]
  simp only [fMap, mkRV]
  rw [kAdd_iota, kAdd_iota, add_comm]

theorem model_kAddZero : (C v) ⊨ LRV.allSortedK ![.rv]
    (LRV.pEq (LRV.tKAdd &0 LRV.tRVZero) &0) := by
  rw [model_allSortedK v]
  intro xs h hk
  obtain ⟨a, ha⟩ := hk 0
  prep
  rw [ha, ← iota_zero v]
  simp only [fMap, mkRV]
  rw [kAdd_iota, add_zero]

theorem model_kAddNeg : (C v) ⊨ LRV.allSortedK ![.rv]
    (LRV.pEq (LRV.tKAdd &0 (LRV.tKNeg &0)) LRV.tRVZero) := by
  rw [model_allSortedK v]
  intro xs h hk
  obtain ⟨a, ha⟩ := hk 0
  prep
  rw [ha, ← iota_zero v]
  simp only [fMap, mkRV]
  rw [kNeg_iota, kAdd_iota, add_neg_cancel]

theorem model_kMulAssoc : (C v) ⊨ LRV.allSortedK ![.rv, .rv, .rv]
    (LRV.pEq (LRV.tRVMul (LRV.tRVMul &0 &1) &2) (LRV.tRVMul &0 (LRV.tRVMul &1 &2))) := by
  rw [model_allSortedK v]
  intro xs h hk
  obtain ⟨a, ha⟩ := hk 0
  obtain ⟨b, hb⟩ := hk 1
  obtain ⟨c, hc⟩ := hk 2
  prep
  rw [ha, hb, hc]
  simp only [fMap, mkRV]
  rw [kMul_iota, kMul_iota, kMul_iota, kMul_iota, mul_assoc]

theorem model_kMulComm : (C v) ⊨ LRV.allSortedK ![.rv, .rv]
    (LRV.pEq (LRV.tRVMul &0 &1) (LRV.tRVMul &1 &0)) := by
  rw [model_allSortedK v]
  intro xs h hk
  obtain ⟨a, ha⟩ := hk 0
  obtain ⟨b, hb⟩ := hk 1
  prep
  rw [ha, hb]
  simp only [fMap, mkRV]
  rw [kMul_iota, kMul_iota, mul_comm]

theorem model_kMulOne : (C v) ⊨ LRV.allSortedK ![.rv]
    (LRV.pEq (LRV.tRVMul &0 LRV.tRVOne) &0) := by
  rw [model_allSortedK v]
  intro xs h hk
  obtain ⟨a, ha⟩ := hk 0
  prep
  rw [ha, RVM.rvOne_eq, ← iota_one v]
  simp only [fMap, mkRV]
  rw [kMul_iota, mul_one]

theorem model_kDistrib : (C v) ⊨ LRV.allSortedK ![.rv, .rv, .rv]
    (LRV.pEq (LRV.tRVMul &0 (LRV.tKAdd &1 &2))
      (LRV.tKAdd (LRV.tRVMul &0 &1) (LRV.tRVMul &0 &2))) := by
  rw [model_allSortedK v]
  intro xs h hk
  obtain ⟨a, ha⟩ := hk 0
  obtain ⟨b, hb⟩ := hk 1
  obtain ⟨c, hc⟩ := hk 2
  prep
  rw [ha, hb, hc]
  simp only [fMap, mkRV]
  simp only [kMul_iota, kAdd_iota]
  rw [mul_add]

theorem model_kZeroNeOne : (C v) ⊨ ∼(LRV.pEq LRV.tRVZero LRV.tRVOne) := by
  prep
  simp [RVM.rvOne_eq]

theorem model_kMulInv : (C v) ⊨ LRV.allSortedK ![.rv]
    (LRV.pEq &0 LRV.tRVZero ⊔
      LRV.exSortedK .rv (LRV.pEq (LRV.tRVMul &0 &1) LRV.tRVOne)) := by
  rw [model_allSortedK v]
  intro xs h hk
  obtain ⟨a, ha⟩ := hk 0
  prep
  rw [ha, ← iota_zero v]
  rw [realize_exSortedK v xs]
  by_cases h0 : a = 0
  · exact Or.inl (by rw [h0])
  · right
    have hinv : a⁻¹ ≠ 0 := inv_ne_zero h0
    obtain ⟨u, hu⟩ : ∃ u : ACVFResidue.KUnits v, a⁻¹ = some u := by
      cases hh : a⁻¹ with
      | none => exact absurd (hh.trans (zero_eq_none v).symm) hinv
      | some u => exact ⟨u, rfl⟩
    refine ⟨Sum.inr (iota v a⁻¹),
      ⟨⟨⟨iota v a⁻¹, rfl⟩, ⟨some u, by rw [hu]⟩⟩, ?_⟩⟩
    have hT : (Fin.snoc xs (Sum.inr (iota v a⁻¹)) : Fin 2 → C v)
        = ![xs 0, Sum.inr (iota v a⁻¹)] := by
      funext i
      fin_cases i
      · rfl
      · show (Fin.snoc xs (Sum.inr (iota v a⁻¹)) : Fin 2 → C v) 1 = Sum.inr (iota v a⁻¹)
        have h : (1 : Fin 2) = Fin.last 1 := rfl
        rw [h, Fin.snoc_last]
    rw [hT]
    prep
    rw [ha]
    simp only [fMap, mkRV]
    rw [kMul_iota, mul_inv_cancel₀ h0, RVM.rvOne_eq, iota_one]

/-- **Definition 2.2 item 3 at the intended structure**: `(K, 0, 1, +, -, ×)` is a
field, where `K = K^× ∪ {0}` is the residue field inside the `RV` sort. -/
theorem model_kField : (C v) ⊨ Axioms.kField := by
  refine model_ofList v ?_
  intro s hs
  simp only [Axioms.kField, Axioms.ofList, List.mem_cons, List.mem_nil_iff, or_false] at hs
  obtain rfl | hs := hs
  · exact model_kAddAssoc v
  obtain rfl | hs := hs
  · exact model_kAddComm v
  obtain rfl | hs := hs
  · exact model_kAddZero v
  obtain rfl | hs := hs
  · exact model_kAddNeg v
  obtain rfl | hs := hs
  · exact model_kMulAssoc v
  obtain rfl | hs := hs
  · exact model_kMulComm v
  obtain rfl | hs := hs
  · exact model_kMulOne v
  obtain rfl | hs := hs
  · exact model_kDistrib v
  obtain rfl | hs := hs
  · exact model_kZeroNeOne v
  obtain rfl := hs
  exact model_kMulInv v
end SpecialTransformations.Milestone0.IModel

/-! ### 3.7 Monic polynomials in Horner shape, over an arbitrary field

Every monic polynomial `x^{n+1} + a_n x^n + ⋯ + a_0` has a root in an algebraically closed
field; this is the semantic content of `kAlgClosed` after reading the term `hornerPoly`
through `iota`.  The block is stated for an arbitrary field `F` so that it applies to the
internal residue field `k = K^× ∪ {0}` of the `RV` sort. -/

namespace SpecialTransformations.Milestone0.Horner

open Polynomial

variable {F : Type*} [Field F]

noncomputable def poly (a : ℕ → F) : ℕ → F[X]
  | 0 => 0
  | (n + 1) =>
    (List.finRange n).reverse.foldl (fun acc i => acc * X + Polynomial.C (a i.val))
      (X + Polynomial.C (a n))

theorem degree_C_lt_X (c : F) : (Polynomial.C c).degree < (X : F[X]).degree := by
  rw [Polynomial.degree_X]
  calc (Polynomial.C c).degree ≤ 0 := Polynomial.degree_C_le
    _ < 1 := by rw [← WithBot.coe_zero, ← WithBot.coe_one, WithBot.coe_lt_coe]; omega

theorem monic_X_add_C (c : F) : (X + Polynomial.C c : F[X]).Monic :=
  Polynomial.monic_X.add_of_left (degree_C_lt_X c)

theorem natDegree_X_add_C (c : F) : (X + Polynomial.C c : F[X]).natDegree = 1 := by
  rw [Polynomial.natDegree_add_eq_left_of_degree_lt (degree_C_lt_X c),
    Polynomial.natDegree_X]

theorem monic_mul_X_add_C (a : ℕ → F) {y : F[X]} (hy : y.Monic) (c : ℕ) :
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

theorem natDegree_mul_X_add_C (a : ℕ → F) {y : F[X]} (hy : y.Monic) (c : ℕ) :
    (y * X + Polynomial.C (a c)).natDegree = y.natDegree + 1 := by
  have hy0 : y ≠ 0 := hy.ne_zero
  have h1 : (y * X).natDegree = y.natDegree + 1 := by
    rw [Polynomial.natDegree_mul hy0 Polynomial.X_ne_zero, Polynomial.natDegree_X]
  rw [← h1]
  refine Polynomial.natDegree_add_eq_left_of_degree_lt ?_
  rw [Polynomial.degree_eq_natDegree (mul_ne_zero hy0 Polynomial.X_ne_zero), h1]
  calc (Polynomial.C (a c)).degree ≤ 0 := Polynomial.degree_C_le
    _ < ((y.natDegree + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.succ_pos y.natDegree

theorem fold_monic {n : ℕ} (a : ℕ → F) (y : F[X]) (hy : y.Monic) (l : List (Fin n)) :
    (l.foldl (fun acc i => acc * X + Polynomial.C (a i.val)) y).Monic := by
  induction l generalizing y with
  | nil => simpa using hy
  | cons i l ih =>
    rw [List.foldl_cons]
    exact ih _ (monic_mul_X_add_C a hy i.val)

theorem fold_natDegree {n : ℕ} (a : ℕ → F) (y : F[X]) (hy : y.Monic) (l : List (Fin n)) :
    (l.foldl (fun acc i => acc * X + Polynomial.C (a i.val)) y).natDegree
      = y.natDegree + l.length := by
  induction l generalizing y with
  | nil => simp
  | cons i l ih =>
    rw [List.foldl_cons, ih _ (monic_mul_X_add_C a hy i.val),
      natDegree_mul_X_add_C a hy i.val]
    simp only [List.length_cons]
    omega

theorem fold_congr {m : ℕ} (f g : F[X] → Fin m → F[X]) (h : ∀ acc i, f acc i = g acc i)
    (l : List (Fin m)) (y : F[X]) : l.foldl f y = l.foldl g y := by
  induction l generalizing y with
  | nil => rfl
  | cons i l ih => rw [List.foldl_cons, List.foldl_cons, h, ih]

theorem fold_eval {n : ℕ} (a : ℕ → F) (y : F[X]) (x : F) (l : List (Fin n)) :
    Polynomial.eval x (l.foldl (fun acc i => acc * X + Polynomial.C (a i.val)) y)
      = l.foldl (fun v i => v * x + a i.val) (Polynomial.eval x y) := by
  induction l generalizing y with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    simp

theorem poly_monic {n : ℕ} (a : ℕ → F) : (poly a (n + 1)).Monic := by
  rw [poly]
  exact fold_monic a _ (monic_X_add_C (a n)) _

theorem poly_natDegree {n : ℕ} (a : ℕ → F) :
    (poly a (n + 1)).natDegree = n + 1 := by
  rw [poly, fold_natDegree a _ (monic_X_add_C (a n)) _, natDegree_X_add_C]
  simp only [List.length_reverse, List.length_finRange]
  omega

theorem poly_eval {n : ℕ} (a : ℕ → F) (x : F) :
    Polynomial.eval x (poly a (n + 1))
      = (List.finRange n).reverse.foldl (fun v i => v * x + a i.val) (x + a n) := by
  rw [poly, fold_eval]
  have h : Polynomial.eval x (X + Polynomial.C (a n) : F[X]) = x + a n := by
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [h]

theorem list_foldl_congr {α β : Type*} (l : List β) (f g : α → β → α)
    (h : ∀ a b, f a b = g a b) (init : α) : l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons b l ih => rw [List.foldl_cons, List.foldl_cons, h, ih]

/-- **algebraic closedness in Horner form**: every monic polynomial of degree `n+1` with
coefficients `a 0, …, a n` has a root -/
theorem exists_root_horner (n : ℕ) (a : ℕ → F) [IsAlgClosed F] :
    ∃ x : F, (List.finRange n).reverse.foldl (fun v i => v * x + a i.val) (x + a n) = 0 := by
  have hdeg : (poly a (n + 1)).degree ≠ 0 := by
    refine ne_of_gt ?_
    rw [← Polynomial.natDegree_pos_iff_degree_pos, poly_natDegree]
    omega
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (poly a (n + 1)) hdeg
  exact ⟨x, by rw [← poly_eval a x]; exact hx⟩

end SpecialTransformations.Milestone0.Horner

namespace SpecialTransformations.Milestone0.IModel
open SpecialTransformations.Milestone0
open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
attribute [local instance] ACVFResidue.kField

/-! ### 3.8 The term `hornerPoly` read in the internal residue field -/

theorem ev_tv_of {N : ℕ} (xs : Fin N → C v) (a : ℕ → Option (ACVFResidue.KUnits v))
    (ha : ∀ i : Fin N, xs i = Sum.inr (iota v (a i.val))) (j : Fin N) :
    Term.realize (Sum.elim (dflt v) xs) (LRV.tv j.val j.isLt) = Sum.inr (iota v (a j.val)) := by
  simp only [LRV.tv, Term.realize_var, Sum.elim_inr, Fin.eta]
  exact ha j

theorem ev_fold {n N : ℕ} (hn : n + 1 < N) (xs : Fin N → C v) (xT : LRV.Tm N)
    (xc : Option (ACVFResidue.KUnits v))
    (hx : Term.realize (Sum.elim (dflt v) xs) xT = Sum.inr (iota v xc))
    (a : ℕ → Option (ACVFResidue.KUnits v))
    (ha : ∀ i : Fin N, xs i = Sum.inr (iota v (a i.val)))
    (l : List (Fin n)) (accT : LRV.Tm N) (acc : Option (ACVFResidue.KUnits v))
    (hacc : Term.realize (Sum.elim (dflt v) xs) accT = Sum.inr (iota v acc)) :
    Term.realize (Sum.elim (dflt v) xs)
      (l.foldl (fun acc i => LRV.tKAdd (LRV.tRVMul acc xT) (LRV.tv i.val (by omega))) accT)
      = Sum.inr (iota v (l.foldl (fun v i => v * xc + a i.val) acc)) := by
  induction l generalizing accT acc with
  | nil => simpa using hacc
  | cons i l ih =>
    rw [List.foldl_cons, List.foldl_cons]
    refine ih _ _ ?_
    have h1 : Term.realize (Sum.elim (dflt v) xs) (LRV.tRVMul accT xT)
        = Sum.inr (iota v (acc * xc)) := by
      simp only [LRV.tRVMul, Term.realize_func, funMap_def, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
        Function.comp_apply, hacc, hx, fMap, mkRV]
      rw [kMul_iota]
    have h2 : Term.realize (Sum.elim (dflt v) xs)
        (LRV.tKAdd (LRV.tRVMul accT xT) (LRV.tv i.val (by omega)))
        = Sum.inr (iota v (acc * xc + a i.val)) := by
      simp only [LRV.tKAdd, Term.realize_func, funMap_def, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
        Function.comp_apply, h1, ev_tv_of v xs a ha ⟨i.val, by omega⟩, fMap, mkRV]
      rw [kAdd_iota]
    exact h2

/-- **the load-bearing term-evaluation lemma for the residue field**: at the intended
structure the term `hornerPoly tKAdd tRVMul` (with `k = n+1` coefficients) evaluates to the
`iota` of the Horner value of the coefficients -/
theorem realize_hornerPoly {n : ℕ} (xs : Fin (n + 1 + 1) → C v)
    (a : ℕ → Option (ACVFResidue.KUnits v))
    (ha : ∀ i : Fin (n + 1 + 1), xs i = Sum.inr (iota v (a i.val))) :
    Term.realize (Sum.elim (dflt v) xs)
        (LRV.hornerPoly LRV.tKAdd LRV.tRVMul (k := n + 1))
      = Sum.inr (iota v ((List.finRange n).reverse.foldl
          (fun v i => v * a (n + 1) + a i.val) (a (n + 1) + a n))) := by
  have hpoly : LRV.hornerPoly LRV.tKAdd LRV.tRVMul (k := n + 1)
      = (List.finRange n).reverse.foldl
          (fun acc i => LRV.tKAdd (LRV.tRVMul acc (LRV.tv (n + 1) (by omega)))
            (LRV.tv i.val (by omega)))
          (LRV.tKAdd (LRV.tv (n + 1) (by omega)) (LRV.tv n (by omega))) := rfl
  rw [hpoly]
  refine ev_fold v (n := n) (N := n + 1 + 1) (by omega) xs _ (a (n + 1)) ?_ a ha
    (List.finRange n).reverse _ (a (n + 1) + a n) ?_
  · exact ev_tv_of v xs a ha ⟨n + 1, by omega⟩
  · simp only [LRV.tKAdd, Term.realize_func, funMap_def, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
      Function.comp_apply, ev_tv_of v xs a ha ⟨n + 1, by omega⟩,
      ev_tv_of v xs a ha ⟨n, by omega⟩, fMap, mkRV]
    rw [kAdd_iota]

theorem snoc_coeff {n : ℕ} (xs : Fin (n + 1) → C v) (y : C v) (j : Fin (n + 1)) :
    (Fin.snoc xs y : Fin (n + 1 + 1) → C v) ⟨j.val, by omega⟩ = xs j := by
  show (Fin.snoc xs y : Fin (n + 1 + 1) → C v) (Fin.castSucc j) = xs j
  exact Fin.snoc_castSucc (α := fun _ => C v) y xs j

theorem snoc_root {n : ℕ} (xs : Fin (n + 1) → C v) (y : C v) :
    (Fin.snoc xs y : Fin (n + 1 + 1) → C v) ⟨n + 1, by omega⟩ = y := by
  show (Fin.snoc xs y : Fin (n + 1 + 1) → C v) (Fin.last (n + 1)) = y
  exact Fin.snoc_last (α := fun _ => C v) y xs

/-- the same for the tuple `Fin.snoc xs y` produced by the existential quantifier of
`acfSchemeK` -/
theorem realize_hornerPoly_snoc {n : ℕ} (xs : Fin (n + 1) → C v) (y : C v)
    (a : ℕ → Option (ACVFResidue.KUnits v))
    (ha : ∀ i : Fin (n + 1), xs i = Sum.inr (iota v (a i.val)))
    (xc : Option (ACVFResidue.KUnits v)) (hy : y = Sum.inr (iota v xc)) :
    Term.realize (Sum.elim (dflt v) (Fin.snoc xs y : Fin (n + 1 + 1) → C v))
        (LRV.hornerPoly LRV.tKAdd LRV.tRVMul (k := n + 1))
      = Sum.inr (iota v ((List.finRange n).reverse.foldl
          (fun v i => v * xc + a i.val) (xc + a n))) := by
  have ha' : ∀ i : Fin (n + 1 + 1), (Fin.snoc xs y : Fin (n + 1 + 1) → C v) i
      = Sum.inr (iota v ((Function.update a (n + 1) xc) i.val)) := by
    intro i
    rcases Nat.lt_or_ge i.val (n + 1) with hlt | hge
    · rw [snoc_coeff v xs y ⟨i.val, hlt⟩, ha ⟨i.val, hlt⟩,
        Function.update_of_ne (by omega : i.val ≠ n + 1)]
    · have hlast : i = ⟨n + 1, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      rw [hlast, snoc_root v xs y, hy, Function.update_self]
  rw [realize_hornerPoly v (Fin.snoc xs y) (fun j => (Function.update a (n + 1) xc) j) ha']
  have hu1 : (Function.update a (n + 1) xc) (n + 1) = xc := Function.update_self ..
  have hu2 : (Function.update a (n + 1) xc) n = a n :=
    Function.update_of_ne (by omega) ..
  have hfun : ∀ (acc : Option (ACVFResidue.KUnits v)) (i : Fin n),
      acc * (Function.update a (n + 1) xc) (n + 1) + (Function.update a (n + 1) xc) i.val
        = acc * xc + a i.val := by
    intro acc i
    rw [hu1, Function.update_of_ne (by omega : i.val ≠ n + 1)]
  rw [Horner.list_foldl_congr (List.finRange n).reverse _ _ hfun, hu1, hu2]

theorem realize_pEq_iff {m : ℕ} (t u : LRV.Tm m) (ρ : Empty → C v) (xs : Fin m → C v) :
    (LRV.pEq t u).Realize ρ xs ↔
      Term.realize (Sum.elim ρ xs) t = Term.realize (Sum.elim ρ xs) u := by
  simp only [LRV.pEq, BoundedFormula.realize_bdEqual]

theorem realize_tRVZero {m : ℕ} (ρ : Empty → C v) (xs : Fin m → C v) :
    Term.realize (Sum.elim ρ xs) (LRV.tRVZero (n := m)) = cKZero v := by
  simp only [LRV.tRVZero, Term.realize_func, funMap_def, fMap]

theorem exists_root_horner_k [IsAlgClosed K] (n : ℕ)
    (a : ℕ → Option (ACVFResidue.KUnits v)) :
    ∃ x : Option (ACVFResidue.KUnits v),
      (List.finRange n).reverse.foldl (fun v i => v * x + a i.val) (x + a n) = 0 := by
  haveI : IsAlgClosed (Option (ACVFResidue.KUnits v)) := ACVFResidue.isAlgClosed_k v
  exact Horner.exists_root_horner n a

/-- **Definition 2.2 item 3, algebraic closedness at the intended structure**: every monic
polynomial with coefficients in `K = K^× ∪ {0}` has a root in `K`. -/
theorem model_kAlgClosed [IsAlgClosed K] : (C v) ⊨ Axioms.kAlgClosed := by
  rw [Theory.model_iff]
  rintro s ⟨k, hk1, rfl⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [Axioms.acfSchemeK, model_allSortedK v]
  intro xs h hk
  rw [realize_exSortedK v xs]
  choose b hb using hk
  let a : ℕ → Option (ACVFResidue.KUnits v) :=
    fun j => if h : j < n + 1 then b ⟨j, h⟩ else 0
  have ha : ∀ i : Fin (n + 1), xs i = Sum.inr (iota v (a i.val)) := by
    intro i
    have hai : a i.val = b i := by
      simp only [a]
      rw [dif_pos i.isLt]
    rw [hb i, hai]
  obtain ⟨x, hx⟩ := exists_root_horner_k v n a
  refine ⟨Sum.inr (iota v x), ⟨⟨⟨iota v x, rfl⟩, ⟨x, rfl⟩⟩, ?_⟩⟩
  rw [realize_pEq_iff]
  rw [realize_hornerPoly_snoc v xs (Sum.inr (iota v x)) a ha x rfl]
  rw [hx, realize_tRVZero]
  exact mkRV_iota_zero v

end SpecialTransformations.Milestone0.IModel
namespace SpecialTransformations.Milestone0.IModel
open SpecialTransformations.Milestone0
open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
attribute [local instance] ACVFResidue.kField


theorem realize_pInK_var' {n : ℕ} (xs : Fin n → C v) (i : Fin n) :
    (LRV.pInK (((FirstOrder.Language.Term.var) ∘ Sum.inr) i)).Realize (dflt v) xs ↔
      ∃ a : Option (ACVFResidue.KUnits v), xs i = Sum.inr (iota v a) := by
  simpa only [Function.comp_apply, LRV.tv] using realize_pInK_var v xs i

theorem realize_pUnits_term {m : ℕ} (xs : Fin m → C v) (t : LRV.Tm m) :
    (LRV.pUnits t).Realize (dflt v) xs ↔
      ∃ q : RVM.RVUnit v, Term.realize (Sum.elim (dflt v) xs) t = cUnit v q ∧
        RVM.vrv v (some q) = 1 := by
  prep

/-- `K = K^× ∪ {0}` holds of every term whose value is an `iota` of a residue-field
element -/
theorem pInK_of_iota {m : ℕ} (xs : Fin m → C v) (t : LRV.Tm m)
    (a : Option (ACVFResidue.KUnits v))
    (h : Term.realize (Sum.elim (dflt v) xs) t = Sum.inr (iota v a)) :
    (LRV.pInK t).Realize (dflt v) xs := by
  rw [LRV.pInK, BoundedFormula.realize_sup, realize_pUnits_term v xs t]
  cases a with
  | none =>
    right
    rw [realize_pEq_iff, h, realize_tRVZero]
    rfl
  | some u =>
    left
    exact ⟨(u : RVM.RVUnit v), by rw [h]; rfl, (mem_kUnits_iff v _).mp u.2⟩

/-! ### 3.9 The sort discipline for the residue-field operations

These three sentences of `sortAxioms` are the ones that depend on the choice of the junk
values of `kAdd`, `kNeg`; with the transported operations they follow from the fact that
`K = K^× ∪ {0}` is closed under the residue-field operations. -/

theorem model_sdKAdd : (C v) ⊨ Axioms.sdKAdd := by
  rw [Axioms.sdKAdd, model_allSorted v]
  intro xs h
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp]
  intro h0 h1
  rw [realize_pInK_var' v xs 0] at h0
  rw [realize_pInK_var' v xs 1] at h1
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  refine pInK_of_iota v xs _ (a + b) ?_
  simp only [LRV.tKAdd, Term.realize_func, funMap_def, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    Function.comp_apply, Term.realize_var, Sum.elim_inr, Fin.eta, ha, hb, fMap, mkRV]
  rw [kAdd_iota]

theorem model_sdKNeg : (C v) ⊨ Axioms.sdKNeg := by
  rw [Axioms.sdKNeg, model_allSorted v]
  intro xs h
  rw [BoundedFormula.realize_imp]
  intro h0
  rw [realize_pInK_var' v xs 0] at h0
  obtain ⟨a, ha⟩ := h0
  refine pInK_of_iota v xs _ (-a) ?_
  simp only [LRV.tKNeg, Term.realize_func, funMap_def, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    Function.comp_apply, Term.realize_var, Sum.elim_inr, Fin.eta, ha, fMap, mkRV]
  rw [kNeg_iota]

theorem model_sdKMul : (C v) ⊨ Axioms.sdKMul := by
  rw [Axioms.sdKMul, model_allSorted v]
  intro xs h
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp]
  intro h0 h1
  rw [realize_pInK_var' v xs 0] at h0
  rw [realize_pInK_var' v xs 1] at h1
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  refine pInK_of_iota v xs _ (a * b) ?_
  simp only [LRV.tRVMul, Term.realize_func, funMap_def, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    Function.comp_apply, Term.realize_var, Sum.elim_inr, Fin.eta, ha, hb, fMap, mkRV]
  rw [kMul_iota]

end SpecialTransformations.Milestone0.IModel

namespace SpecialTransformations.Milestone0.IModel
open SpecialTransformations.Milestone0
open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
attribute [local instance] ACVFResidue.kField

/-! ### 3.10 The multiplicative sentences of `rvGroup`

All but the divisibility scheme `rvDivisible`: these are the sentences of Definition 2.2(2)
that mention only `rvOne`, `rvMul`, `K^×` and the absorbing `0`/`∞`. -/

theorem realize_pInK_var_apply {n : ℕ} (xs : Fin n → C v) (i : Fin n) :
    (LRV.pInK (FirstOrder.Language.Term.var (Sum.inr i))).Realize (dflt v) xs ↔
      ∃ a : Option (ACVFResidue.KUnits v), xs i = Sum.inr (iota v a) := by
  simpa only [LRV.tv] using realize_pInK_var v xs i

theorem realize_pUnits_var' {n : ℕ} (xs : Fin n → C v) (i : Fin n) :
    (LRV.pUnits (((FirstOrder.Language.Term.var) ∘ Sum.inr) i)).Realize (dflt v) xs ↔
      ∃ q : RVM.RVUnit v, xs i = cUnit v q ∧ RVM.vrv v (some q) = 1 := by
  simpa only [Function.comp_apply, LRV.tv] using realize_pUnits_var v xs i

/-- `exSorted .rv` unfolded at the intended model -/
theorem realize_exSorted_rv {k : ℕ} (xs : Fin k → C v) (φ : LRV.Bf (k + 1)) :
    (LRV.exSorted .rv φ).Realize (dflt v) xs ↔
      ∃ y : C v, (∃ t : RVM.RV v, y = mkRV v t) ∧
        φ.Realize (dflt v) (Fin.snoc xs y) := by
  have h := BoundedFormula.realize_ex
    (θ := LRV.sortPred .rv (LRV.tv k (Nat.lt_succ_self k)) ⊓ φ)
    (v := dflt v) (xs := xs)
  refine h.trans (exists_congr fun y => ?_)
  rw [BoundedFormula.realize_inf]
  have hlast : (Fin.snoc xs y : Fin (k + 1) → C v) ⟨k, Nat.lt_succ_self k⟩ = y := by
    have h : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k := rfl
    rw [h, Fin.snoc_last]
  have h1 : (LRV.sortPred .rv (LRV.tv k (Nat.lt_succ_self k))).Realize (dflt v) (Fin.snoc xs y)
      ↔ ∃ t : RVM.RV v, y = mkRV v t := by
    rw [realize_sortPred_rv v (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) (Fin.snoc xs y), hlast]
  rw [h1]

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
  · simp only [cUnit, RVM.rvMul_some_some]
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
  simp only [cUnit, RVM.rvOne_eq, RVM.rvMul_some_some, mul_one, mkRV, Sum.inr.injEq,
    Option.some.injEq]
  exact one_mul q

/-- `t × 0 = 0` holds for **every** `t` of the `RV` sort at the intended structure, so the
`pInK` guard of the frozen encoding is irrelevant here. -/
theorem model_rvMulZeroK : (C v) ⊨ Axioms.rvMulZeroK := by
  simp only [Axioms.rvMulZeroK]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht]
  intro hk
  have hk2 : (LRV.pInK (((FirstOrder.Language.Term.var) ∘ Sum.inr) 0)).Realize
      (dflt v) xs := hk
  rw [realize_pInK_var' v xs 0] at hk2
  obtain ⟨a, ha⟩ := hk2
  have ht' : t = iota v a := by
    rw [ht] at ha
    simp only [mkRV] at ha
    exact Sum.inr.inj ha
  rw [ht']
  cases a with
  | none => rfl
  | some u => rfl

theorem model_rvMulInv : (C v) ⊨ Axioms.rvMulInv := by
  simp only [Axioms.rvMulInv]; rw [model_allSorted v]; intro xs h
  rw [BoundedFormula.realize_imp]
  intro hx
  rw [realize_pUnits_var' v xs 0] at hx
  obtain ⟨q, hq, hv⟩ := hx
  rw [realize_exSorted_rv v xs]
  have hq' : RVM.vrv v (some q⁻¹) = 1 := by
    have h := RVM.vrv_mul v (some q) (some q⁻¹)
    rw [RVM.rvMul_some_some, mul_inv_cancel, hv] at h
    simpa using h.symm
  refine ⟨cUnit v q⁻¹, ⟨⟨some q⁻¹, rfl⟩, ?_⟩⟩
  have hT : (Fin.snoc xs (cUnit v q⁻¹) : Fin 2 → C v) = ![xs 0, cUnit v q⁻¹] := by
    funext i
    fin_cases i
    · rfl
    · show (Fin.snoc xs (cUnit v q⁻¹) : Fin 2 → C v) 1 = cUnit v q⁻¹
      have h : (1 : Fin 2) = Fin.last 1 := rfl
      rw [h, Fin.snoc_last]
  rw [hT]
  prep
  refine ⟨⟨q⁻¹, rfl, hq'⟩, ?_⟩
  rw [hq]
  simp only [cUnit, RVM.rvMul_some_some, RVM.rvOne_eq]
  rw [inv_mul_cancel]

end SpecialTransformations.Milestone0.IModel

namespace SpecialTransformations.Milestone0.IModel
open SpecialTransformations.Milestone0
open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
attribute [local instance] ACVFResidue.kField

/-- the term `tRVPow t n` evaluates to the `n`-th power of the value of `t` -/
theorem realize_tRVPow_of {m : ℕ} (xs : Fin m → C v) (t : LRV.Tm m) (q : RVM.RVUnit v)
    (h : Term.realize (Sum.elim (dflt v) xs) t = cUnit v q) (n : ℕ) :
    Term.realize (Sum.elim (dflt v) xs) (LRV.tRVPow t n) = cUnit v (q ^ n) := by
  induction n with
  | zero =>
    show Term.realize (Sum.elim (dflt v) xs) LRV.tRVOne = cUnit v (q ^ 0)
    rw [pow_zero]
    prep
    simp [cRVOne, cUnit, RVM.rvOne_eq]
  | succ n ih =>
    show Term.realize (Sum.elim (dflt v) xs) (LRV.tRVMul (LRV.tRVPow t n) t)
      = cUnit v (q ^ (n + 1))
    simp only [LRV.tRVMul, Term.realize_func, funMap_def, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
      Function.comp_apply, ih, h, fMap, mkRV, cUnit, RVM.rvMul_some_some]
    rw [pow_succ]

theorem kUnits_divisible [IsAlgClosed K] (u : ACVFResidue.KUnits v) (n : ℕ) (hn : n ≠ 0) :
    ∃ s : ACVFResidue.KUnits v, (s : RVM.RVUnit v) ^ n = (u : RVM.RVUnit v) := by
  obtain ⟨s, hs⟩ := RVM.rvUnit_divisible v n hn (u : RVM.RVUnit v)
  have hmem : s ∈ ACVFResidue.kUnitsSubgroup v := by
    rw [mem_kUnits_iff]
    have hpow : (RVM.vrv v (some s)) ^ n = 1 := by
      have h1 : ∀ m : ℕ, RVM.vrv v (some (s ^ m)) = (RVM.vrv v (some s)) ^ m := by
        intro m
        induction m with
        | zero => simp
        | succ j ih =>
          rw [pow_succ, pow_succ, ← ih, ← RVM.rvMul_some_some, RVM.vrv_mul]
      rw [← h1, hs, (mem_kUnits_iff v u).mp u.2]
    exact (pow_eq_one_iff_of_nonneg (zero_le) hn).mp hpow
  exact ⟨⟨s, hmem⟩, hs⟩

theorem model_rvDivisible [IsAlgClosed K] (k : ℕ) (hk : 1 ≤ k) :
    (C v) ⊨ Axioms.rvDivisible k := by
  simp only [Axioms.rvDivisible]; rw [model_allSorted v]; intro xs h
  rw [BoundedFormula.realize_imp]
  intro hx
  rw [realize_pUnits_var' v xs 0] at hx
  obtain ⟨q, hq, hv⟩ := hx
  rw [realize_exSorted_rv v xs]
  obtain ⟨s, hs⟩ := kUnits_divisible v ⟨q, (mem_kUnits_iff v q).mpr hv⟩ k (by omega)
  refine ⟨cUnit v (s : RVM.RVUnit v), ⟨⟨some (s : RVM.RVUnit v), rfl⟩, ?_⟩⟩
  have hT : (Fin.snoc xs (cUnit v (s : RVM.RVUnit v)) : Fin 2 → C v)
      = ![xs 0, cUnit v (s : RVM.RVUnit v)] := by
    funext i
    fin_cases i
    · rfl
    · show (Fin.snoc xs (cUnit v (s : RVM.RVUnit v)) : Fin 2 → C v) 1
        = cUnit v (s : RVM.RVUnit v)
      have hh : (1 : Fin 2) = Fin.last 1 := rfl
      rw [hh, Fin.snoc_last]
  rw [hT]
  prep
  refine ⟨⟨(s : RVM.RVUnit v), rfl, (mem_kUnits_iff v _).mp s.2⟩, ?_⟩
  have hval : Term.realize (Sum.elim (dflt v) ![xs 0, cUnit v (s : RVM.RVUnit v)])
      (FirstOrder.Language.Term.var (L := LRV) (Sum.inr (1 : Fin 2))) = cUnit v (s : RVM.RVUnit v) := by
    simp only [Term.realize_var, Sum.elim_inr]
    simp
  rw [realize_tRVPow_of v _ _ (s : RVM.RVUnit v) hval k, hq, hs]

end SpecialTransformations.Milestone0.IModel

namespace SpecialTransformations.Milestone0.IModel
open SpecialTransformations.Milestone0
open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
attribute [local instance] ACVFResidue.kField

theorem model_rvMulInfty : (C v) ⊨ Axioms.rvMulInfty := by
  simp only [Axioms.rvMulInfty]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht]
  simp only [mkRV, RVM.rvMul_infty]

/-- **Definition 2.2 item 2 at the intended structure**: `(RV^×, 1, ×)` is a divisible
abelian group, `×` is augmented by the absorbing `0` and `∞`. -/
theorem model_rvGroup [IsAlgClosed K] : (C v) ⊨ Axioms.rvGroup := by
  rw [Theory.model_iff]
  intro s hs
  rcases hs with hs | ⟨k, hk1, rfl⟩
  · simp only [Axioms.ofList, Set.mem_setOf_eq, List.mem_cons, List.mem_nil_iff,
      or_false] at hs
    obtain rfl | hs := hs
    · exact model_rvOneMem v
    obtain rfl | hs := hs
    · exact model_rvMulMem v
    obtain rfl | hs := hs
    · exact model_rvMulAssoc v
    obtain rfl | hs := hs
    · exact model_rvMulComm v
    obtain rfl | hs := hs
    · exact model_rvMulOne v
    obtain rfl | hs := hs
    · exact model_rvMulInv v
    obtain rfl | hs := hs
    · exact model_rvMulZeroK v
    obtain rfl := hs
    exact model_rvMulInfty v
  · exact model_rvDivisible v k hk1

#print axioms SpecialTransformations.Milestone0.IModel.model_kField
#print axioms SpecialTransformations.Milestone0.IModel.model_kAlgClosed
#print axioms SpecialTransformations.Milestone0.IModel.model_rvGroup
#print axioms SpecialTransformations.Milestone0.IModel.model_sdKAdd
#print axioms SpecialTransformations.Milestone0.IModel.model_sdKNeg
#print axioms SpecialTransformations.Milestone0.IModel.model_sdKMul

end SpecialTransformations.Milestone0.IModel

namespace SpecialTransformations.Milestone0.IModel
open SpecialTransformations.Milestone0
open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
attribute [local instance] ACVFResidue.kField

/-! ### 3.12 The sort discipline, the `VF` field axioms, the `rv` axioms and the
preorder: the remaining sentences that do not involve `kAdd`/`kNeg`, ported to the
corrected structure (they are insensitive to the choice of the residue-field operations) -/


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

theorem models_sdUnits : (C v) ⊨ Axioms.sdUnits := by
  simp only [Axioms.sdUnits, LRV.allOne]
  rw [model_alls v]
  intro xs
  prep
  rintro ⟨q, hq, -⟩
  exact ⟨some q, hq⟩

/-! ### the preorder on `RV` (Definition 2.2 item 4) -/

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
  intro hne
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  have ht' : t ≠ none := by
    intro htn
    apply hne
    rw [ht, htn]
    rfl
  obtain ⟨x, -, hx⟩ := RVM.rv_surjective (v := v) (t := t) ht'
  refine ⟨mkVF v x, ⟨x, rfl⟩, ?_⟩
  show Sum.inr (RVM.rv v x) = xs 0
  rw [hx, ht]
  rfl

theorem le_rv_add (a b : K) :
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
  rcases le_rv_add v a b with h | h
  · exact Or.inl ⟨RVM.rv v a, RVM.rv v (a + b), rfl, rfl, h⟩
  · exact Or.inr ⟨RVM.rv v b, RVM.rv v (a + b), rfl, rfl, h⟩


/-! ### the multiplicative monoid of the `RV` sort (Definition 2.2 item 2), partial -/


theorem le_mkRV_iff {t s : RVM.RV v} :
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
  exact ⟨t, t, rfl, rfl, le_refl t⟩

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
  exact ⟨t, none, rfl, rfl, RVM.le_infty v t⟩

theorem model_leInftyEq : (C v) ⊨ Axioms.leInftyEq := by
  simp only [Axioms.leInftyEq]; rw [model_allSorted v]; intro xs h; prep
  intro _ hle
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht] at hle ⊢
  obtain ⟨a, b, ha, hb, hab⟩ := hle
  simp only [mkRV, Sum.inr.injEq] at ha hb
  subst ha
  rw [hb]
  have hb0 : RVM.vrv v b = 0 := le_antisymm hab zero_le
  rcases b with _ | q
  · rfl
  · exfalso
    have hne : RVM.vrv v (some q) ≠ 0 := by simp [RVM.vrv_some]
    exact hne hb0


end SpecialTransformations.Milestone0.IModel

namespace SpecialTransformations.Milestone0.IModel
open SpecialTransformations.Milestone0
open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
attribute [local instance] ACVFResidue.kField

/-! ### 3.13 `vfAlgClosed`: algebraic closedness of the `VF` sort -/

theorem realize_exSorted_vf {k : ℕ} (xs : Fin k → C v) (φ : LRV.Bf (k + 1)) :
    (LRV.exSorted .vf φ).Realize (dflt v) xs ↔
      ∃ y : C v, (∃ x : K, y = mkVF v x) ∧
        φ.Realize (dflt v) (Fin.snoc xs y) := by
  have h := BoundedFormula.realize_ex
    (θ := LRV.sortPred .vf (LRV.tv k (Nat.lt_succ_self k)) ⊓ φ)
    (v := dflt v) (xs := xs)
  refine h.trans (exists_congr fun y => ?_)
  rw [BoundedFormula.realize_inf]
  have hlast : (Fin.snoc xs y : Fin (k + 1) → C v) ⟨k, Nat.lt_succ_self k⟩ = y := by
    have h' : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k := rfl
    rw [h', Fin.snoc_last]
  have h1 : (LRV.sortPred .vf (LRV.tv k (Nat.lt_succ_self k))).Realize (dflt v) (Fin.snoc xs y)
      ↔ ∃ x : K, y = mkVF v x := by
    rw [realize_sortPred_vf v (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) (Fin.snoc xs y), hlast]
  rw [h1]

theorem realize_tVFZero {m : ℕ} (ρ : Empty → C v) (xs : Fin m → C v) :
    Term.realize (Sum.elim ρ xs) (LRV.tVFZero (n := m)) = mkVF v 0 := by
  simp only [LRV.tVFZero, Term.realize_func, funMap_def, fMap]

theorem ev_tv_of_vf {N : ℕ} (xs : Fin N → C v) (a : ℕ → K)
    (ha : ∀ i : Fin N, xs i = Sum.inl (a i.val)) (j : Fin N) :
    Term.realize (Sum.elim (dflt v) xs) (LRV.tv j.val j.isLt) = Sum.inl (a j.val) := by
  simp only [LRV.tv, Term.realize_var, Sum.elim_inr, Fin.eta]
  exact ha j

theorem ev_fold_vf {n N : ℕ} (hn : n + 1 < N) (xs : Fin N → C v) (xT : LRV.Tm N) (xc : K)
    (hx : Term.realize (Sum.elim (dflt v) xs) xT = Sum.inl xc)
    (a : ℕ → K) (ha : ∀ i : Fin N, xs i = Sum.inl (a i.val))
    (l : List (Fin n)) (accT : LRV.Tm N) (acc : K)
    (hacc : Term.realize (Sum.elim (dflt v) xs) accT = Sum.inl acc) :
    Term.realize (Sum.elim (dflt v) xs)
      (l.foldl (fun acc i => LRV.tVFAdd (LRV.tVFMul acc xT) (LRV.tv i.val (by omega))) accT)
      = Sum.inl (l.foldl (fun v i => v * xc + a i.val) acc) := by
  induction l generalizing accT acc with
  | nil => simpa using hacc
  | cons i l ih =>
    rw [List.foldl_cons, List.foldl_cons]
    refine ih _ _ ?_
    have h1 : Term.realize (Sum.elim (dflt v) xs) (LRV.tVFMul accT xT) = Sum.inl (acc * xc) := by
      simp only [LRV.tVFMul, Term.realize_func, funMap_def, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
        Function.comp_apply, hacc, hx, fMap, mkVF]
    have h2 : Term.realize (Sum.elim (dflt v) xs)
        (LRV.tVFAdd (LRV.tVFMul accT xT) (LRV.tv i.val (by omega)))
        = Sum.inl (acc * xc + a i.val) := by
      simp only [LRV.tVFAdd, Term.realize_func, funMap_def, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
        Function.comp_apply, h1, ev_tv_of_vf v xs a ha ⟨i.val, by omega⟩, fMap, mkVF]
    exact h2

theorem realize_hornerPoly_vf {n : ℕ} (xs : Fin (n + 1 + 1) → C v) (a : ℕ → K)
    (ha : ∀ i : Fin (n + 1 + 1), xs i = Sum.inl (a i.val)) :
    Term.realize (Sum.elim (dflt v) xs)
        (LRV.hornerPoly LRV.tVFAdd LRV.tVFMul (k := n + 1))
      = Sum.inl ((List.finRange n).reverse.foldl
          (fun v i => v * a (n + 1) + a i.val) (a (n + 1) + a n)) := by
  have hpoly : LRV.hornerPoly LRV.tVFAdd LRV.tVFMul (k := n + 1)
      = (List.finRange n).reverse.foldl
          (fun acc i => LRV.tVFAdd (LRV.tVFMul acc (LRV.tv (n + 1) (by omega)))
            (LRV.tv i.val (by omega)))
          (LRV.tVFAdd (LRV.tv (n + 1) (by omega)) (LRV.tv n (by omega))) := rfl
  rw [hpoly]
  refine ev_fold_vf v (n := n) (N := n + 1 + 1) (by omega) xs _ (a (n + 1)) ?_ a ha
    (List.finRange n).reverse _ (a (n + 1) + a n) ?_
  · exact ev_tv_of_vf v xs a ha ⟨n + 1, by omega⟩
  · simp only [LRV.tVFAdd, Term.realize_func, funMap_def, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
      Function.comp_apply, ev_tv_of_vf v xs a ha ⟨n + 1, by omega⟩,
      ev_tv_of_vf v xs a ha ⟨n, by omega⟩, fMap, mkVF]

theorem snoc_coeff_vf {n : ℕ} (xs : Fin (n + 1) → C v) (y : C v) (j : Fin (n + 1)) :
    (Fin.snoc xs y : Fin (n + 1 + 1) → C v) ⟨j.val, by omega⟩ = xs j := by
  show (Fin.snoc xs y : Fin (n + 1 + 1) → C v) (Fin.castSucc j) = xs j
  exact Fin.snoc_castSucc (α := fun _ => C v) y xs j

theorem snoc_root_vf {n : ℕ} (xs : Fin (n + 1) → C v) (y : C v) :
    (Fin.snoc xs y : Fin (n + 1 + 1) → C v) ⟨n + 1, by omega⟩ = y := by
  show (Fin.snoc xs y : Fin (n + 1 + 1) → C v) (Fin.last (n + 1)) = y
  exact Fin.snoc_last (α := fun _ => C v) y xs

theorem realize_hornerPoly_snoc_vf {n : ℕ} (xs : Fin (n + 1) → C v) (y : C v)
    (a : ℕ → K) (ha : ∀ i : Fin (n + 1), xs i = Sum.inl (a i.val))
    (xc : K) (hy : y = Sum.inl xc) :
    Term.realize (Sum.elim (dflt v) (Fin.snoc xs y : Fin (n + 1 + 1) → C v))
        (LRV.hornerPoly LRV.tVFAdd LRV.tVFMul (k := n + 1))
      = Sum.inl ((List.finRange n).reverse.foldl
          (fun v i => v * xc + a i.val) (xc + a n)) := by
  have ha' : ∀ i : Fin (n + 1 + 1), (Fin.snoc xs y : Fin (n + 1 + 1) → C v) i
      = Sum.inl ((Function.update a (n + 1) xc) i.val) := by
    intro i
    rcases Nat.lt_or_ge i.val (n + 1) with hlt | hge
    · rw [snoc_coeff_vf v xs y ⟨i.val, hlt⟩, ha ⟨i.val, hlt⟩,
        Function.update_of_ne (by omega : i.val ≠ n + 1)]
    · have hlast : i = ⟨n + 1, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      rw [hlast, snoc_root_vf v xs y, hy, Function.update_self]
  rw [realize_hornerPoly_vf v (Fin.snoc xs y) (fun j => (Function.update a (n + 1) xc) j) ha']
  have hu1 : (Function.update a (n + 1) xc) (n + 1) = xc := Function.update_self ..
  have hu2 : (Function.update a (n + 1) xc) n = a n :=
    Function.update_of_ne (by omega) ..
  have hfun : ∀ (acc : K) (i : Fin n),
      acc * (Function.update a (n + 1) xc) (n + 1) + (Function.update a (n + 1) xc) i.val
        = acc * xc + a i.val := by
    intro acc i
    rw [hu1, Function.update_of_ne (by omega : i.val ≠ n + 1)]
  rw [Horner.list_foldl_congr (List.finRange n).reverse _ _ hfun, hu1, hu2]

/-- **Definition 2.2 item 1, algebraic closedness of the `VF` sort** -/
theorem model_vfAlgClosed [IsAlgClosed K] : (C v) ⊨ Axioms.vfAlgClosed := by
  rw [Theory.model_iff]
  rintro s ⟨k, hk1, rfl⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [Axioms.acfScheme, model_allSorted v]
  intro xs h
  rw [realize_exSorted_vf v xs]
  have hex : ∀ i : Fin (n + 1), ∃ x : K, xs i = mkVF v x := fun i => (h i).1 rfl
  choose b hb using hex
  let a : ℕ → K := fun j => if h : j < n + 1 then b ⟨j, h⟩ else 0
  have ha : ∀ i : Fin (n + 1), xs i = Sum.inl (a i.val) := by
    intro i
    have hai : a i.val = b i := by
      simp only [a]
      rw [dif_pos i.isLt]
    rw [hb i, hai]
    rfl
  obtain ⟨x, hx⟩ := Horner.exists_root_horner (F := K) n a
  refine ⟨mkVF v x, ⟨x, rfl⟩, ?_⟩
  rw [realize_pEq_iff]
  rw [realize_hornerPoly_snoc_vf v xs (mkVF v x) a ha x rfl]
  rw [hx, realize_tVFZero]
  rfl

end SpecialTransformations.Milestone0.IModel

namespace SpecialTransformations.Milestone0.IModel
open SpecialTransformations.Milestone0
open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
attribute [local instance] ACVFResidue.kField

/-! ### 3.14 The remaining three sentences of the preorder -/

theorem model_leTrans : (C v) ⊨ Axioms.leTrans := by
  simp only [Axioms.leTrans]; rw [model_allSorted v]; intro xs h; prep
  intro _ _ _ hxy hyz
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  obtain ⟨r, hr⟩ := (h 2).2 rfl
  simp only [ht, hs, hr] at hxy hyz ⊢
  obtain ⟨a1, b1, ha1, hb1, hab1⟩ := hxy
  obtain ⟨a2, b2, ha2, hb2, hab2⟩ := hyz
  simp only [mkRV, Sum.inr.injEq] at ha1 hb1 ha2 hb2
  subst ha1; subst hb1; subst ha2; subst hb2
  exact ⟨t, r, rfl, rfl, le_trans hab2 hab1⟩

theorem model_leClassOne : (C v) ⊨ Axioms.leClassOne := by
  simp only [Axioms.leClassOne]; rw [model_allSorted v]; intro xs h; prep
  intro hne
  constructor
  · rintro ⟨q, hq, hv⟩
    rw [hq]
    have hone : RVM.vrv v (some (1 : RVM.RVUnit v)) = 1 := by simp [RVM.vrv_some]
    constructor
    · refine ⟨RVM.rvOne v, some q, rfl, rfl, ?_⟩
      show RVM.vrv v (some q) ≤ RVM.vrv v (RVM.rvOne v)
      rw [show RVM.vrv v (RVM.rvOne v) = 1 from by simp [RVM.rvOne_eq, RVM.vrv_some], hv]
    · refine ⟨some q, RVM.rvOne v, rfl, rfl, ?_⟩
      show RVM.vrv v (RVM.rvOne v) ≤ RVM.vrv v (some q)
      rw [show RVM.vrv v (RVM.rvOne v) = 1 from by simp [RVM.rvOne_eq, RVM.vrv_some], hv]
  · rintro ⟨⟨a1, b1, ha1, hb1, hab1⟩, ⟨a2, b2, ha2, hb2, hab2⟩⟩
    simp only [mkRV, cRVOne, Sum.inr.injEq, RVM.rvOne_eq] at ha1 hb1 ha2 hb2
    have hts : a2 = b1 := by
      have hh : (Sum.inr b1 : C v) = Sum.inr a2 := by rw [← hb1, ha2]
      exact (Sum.inr.inj hh).symm
    subst ha1
    subst hb2
    have hone : RVM.vrv v (some (1 : RVM.RVUnit v)) = 1 := by simp [RVM.vrv_some]
    have hv1 : RVM.vrv v b1 = 1 := by
      refine le_antisymm ?_ ?_
      · simpa [RVM.rvLe, hone] using hab1
      · have hh := hab2
        rw [hts] at hh
        simpa [RVM.rvLe, hone] using hh
    rcases b1 with _ | q
    · simp [RVM.vrv_none] at hv1
    · exact ⟨q, by rw [hb1]; rfl, hv1⟩

/-- multiplying both sides of `≤` by a unit on the right -/
theorem le_mul_unit (x y : RVM.RV v) (q : RVM.RVUnit v) (hv : RVM.vrv v (some q) = 1)
    (h : RVM.rvLe v x y) :
    RVM.rvLe v (RVM.rvMul x (some q)) (RVM.rvMul y (some q)) := by
  have hqmul : ∀ z : RVM.RV v, RVM.vrv v (RVM.rvMul z (some q)) = RVM.vrv v z := by
    intro z
    rw [RVM.vrv_mul, hv, mul_one]
  show RVM.vrv v (RVM.rvMul y (some q)) ≤ RVM.vrv v (RVM.rvMul x (some q))
  rw [hqmul y, hqmul x]
  exact h

theorem model_leMulCompat : (C v) ⊨ Axioms.leMulCompat := by
  simp only [Axioms.leMulCompat]; rw [model_allSorted v]; intro xs h; prep
  intro _ _ _ hunit hle
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  obtain ⟨r, hr⟩ := (h 2).2 rfl
  simp only [ht, hs, hr] at hunit hle ⊢
  obtain ⟨q, hq, hv⟩ := hunit
  rw [hq]
  obtain ⟨a, b, ha, hb, hab⟩ := hle
  have hta : t = a := by simpa [mkRV] using ha
  have hsb : s = b := by simpa [mkRV] using hb
  rw [hta, hsb]
  exact ⟨RVM.rvMul a (some q), RVM.rvMul b (some q), rfl, rfl,
    le_mul_unit v a b q hv hab⟩

end SpecialTransformations.Milestone0.IModel

namespace SpecialTransformations.Milestone0.IModel
open SpecialTransformations.Milestone0
open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
attribute [local instance] ACVFResidue.kField

/-! ### 3.15 Assembly: `Axioms.ACVF` at the intended structure -/

theorem model_union {T₁ T₂ : LRV.Theory} (h1 : (C v) ⊨ T₁) (h2 : (C v) ⊨ T₂) :
    (C v) ⊨ (T₁ ∪ T₂) := by
  rw [Theory.model_iff] at *
  intro s hs
  rcases hs with hs | hs
  · exact h1 s hs
  · exact h2 s hs

theorem model_rvAxioms : (C v) ⊨ Axioms.rvAxioms := by
  rw [Theory.model_iff]
  intro s hs
  simp only [Axioms.rvAxioms, Axioms.ofList, Set.mem_ofPred_eq, List.mem_cons,
    List.mem_nil_iff, or_false] at hs
  obtain rfl | hs := hs
  · exact model_rvZeroEq v
  obtain rfl | hs := hs
  · exact model_rvEqInfty v
  obtain rfl | hs := hs
  · exact model_rvMulHom v
  obtain rfl | hs := hs
  · exact model_rvSurj v
  obtain rfl := hs
  exact model_rvUltrametric v

theorem model_preorderRV : (C v) ⊨ Axioms.preorderRV := by
  rw [Theory.model_iff]
  intro s hs
  simp only [Axioms.preorderRV, Axioms.ofList, Set.mem_ofPred_eq, List.mem_cons,
    List.mem_nil_iff, or_false] at hs
  obtain rfl | hs := hs
  · exact model_leRefl v
  obtain rfl | hs := hs
  · exact model_leTrans v
  obtain rfl | hs := hs
  · exact model_leTotal v
  obtain rfl | hs := hs
  · exact model_leTop v
  obtain rfl | hs := hs
  · exact model_leInftyEq v
  obtain rfl | hs := hs
  · exact model_leClassOne v
  obtain rfl := hs
  exact model_leMulCompat v

theorem model_sortClosure : (C v) ⊨ Axioms.sortClosure := by
  rw [Theory.model_iff]
  intro s hs
  simp only [Axioms.sortClosure, Axioms.ofList, Set.mem_ofPred_eq, List.mem_cons,
    List.mem_nil_iff, or_false] at hs
  obtain rfl | hs := hs
  · exact model_sdVFZero v
  obtain rfl | hs := hs
  · exact model_sdVFOne v
  obtain rfl | hs := hs
  · exact model_sdVFAdd v
  obtain rfl | hs := hs
  · exact model_sdVFNeg v
  obtain rfl | hs := hs
  · exact model_sdVFMul v
  obtain rfl | hs := hs
  · exact model_sdRv v
  obtain rfl | hs := hs
  · exact model_sdRVZero v
  obtain rfl | hs := hs
  · exact model_sdRVInfty v
  obtain rfl | hs := hs
  · exact model_sdRVOne v
  obtain rfl | hs := hs
  · exact model_sdRVMul v
  obtain rfl | hs := hs
  · exact models_sdUnits v
  obtain rfl | hs := hs
  · exact model_sdKAdd v
  obtain rfl | hs := hs
  · exact model_sdKNeg v
  obtain rfl := hs
  exact model_sdKMul v

theorem model_sortAxioms : (C v) ⊨ Axioms.sortAxioms := by
  refine model_union v (model_sortClosure v) ?_
  rw [Theory.model_iff]
  intro s hs
  simp only [Axioms.ofList, Set.mem_ofPred_eq, List.mem_cons, List.mem_nil_iff,
    or_false] at hs
  obtain rfl | hs := hs
  · exact model_sdCover v
  obtain rfl := hs
  exact model_sdDisjoint v

/-- **the paper's own content of `ACVF`, Definition 2.2 items 1–6, at the intended model** -/
theorem model_ACVFpaper [IsAlgClosed K] : (C v) ⊨ Axioms.ACVFpaper := by
  have h1 : (C v) ⊨ (Axioms.vfField ∪ Axioms.vfAlgClosed) :=
    model_union v (model_vfField v) (model_vfAlgClosed v)
  have h2 : (C v) ⊨ (Axioms.vfField ∪ Axioms.vfAlgClosed ∪ Axioms.rvGroup) :=
    model_union v h1 (model_rvGroup v)
  have h3 : (C v) ⊨ (Axioms.vfField ∪ Axioms.vfAlgClosed ∪ Axioms.rvGroup ∪ Axioms.kField) :=
    model_union v h2 (model_kField v)
  have h4 : (C v) ⊨
      (Axioms.vfField ∪ Axioms.vfAlgClosed ∪ Axioms.rvGroup ∪ Axioms.kField ∪
        Axioms.kAlgClosed) :=
    model_union v h3 (model_kAlgClosed v)
  have h5 : (C v) ⊨
      (Axioms.vfField ∪ Axioms.vfAlgClosed ∪ Axioms.rvGroup ∪ Axioms.kField ∪
        Axioms.kAlgClosed ∪ Axioms.preorderRV) :=
    model_union v h4 (model_preorderRV v)
  exact model_union v h5 (model_rvAxioms v)

/-- **`Axioms.ACVF` holds at the intended structure**: for every algebraically closed field
`K` of characteristic `0` and every valuation `v` with value group `Γ₀`, the tagged
structure `K ⊕ RV₀ v` is a model of Definition 2.2. -/
theorem model_ACVF [IsAlgClosed K] : (C v) ⊨ Axioms.ACVF :=
  model_union v (model_sortAxioms v) (model_ACVFpaper v)

#print axioms SpecialTransformations.Milestone0.IModel.model_ACVF
#print axioms SpecialTransformations.Milestone0.IModel.model_rvGroup
#print axioms SpecialTransformations.Milestone0.IModel.model_kField
#print axioms SpecialTransformations.Milestone0.IModel.model_kAlgClosed

end SpecialTransformations.Milestone0.IModel

namespace SpecialTransformations.Milestone0.IModel
open SpecialTransformations.Milestone0
open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
attribute [local instance] ACVFResidue.kField

/-! ### 3.16 `ACVF(0,0)`: pure characteristic zero

`ACVF00` adds characteristic `0` of the valued field and of its residue field.  The first
is a hypothesis on `K` (`CharZero K`); the second is a hypothesis on `v` (`1 ≤ v n` for all
`n ≠ 0`), which for instance FAILS for the `p`-adic valuation at `n = p`. -/

theorem realize_tVFOne {m : ℕ} (ρ : Empty → C v) (xs : Fin m → C v) :
    Term.realize (Sum.elim ρ xs) (LRV.tVFOne (n := m)) = mkVF v 1 := by
  simp only [LRV.tVFOne, Term.realize_func, funMap_def, fMap]

theorem realize_tVFNumeral {m : ℕ} (ρ : Empty → C v) (xs : Fin m → C v) (n : ℕ) :
    Term.realize (Sum.elim ρ xs) (LRV.tVFNumeral (n := m) n) = mkVF v (n : K) := by
  induction n with
  | zero =>
    show Term.realize (Sum.elim ρ xs) (LRV.tVFZero (n := m)) = mkVF v ((0 : ℕ) : K)
    rw [realize_tVFZero]
    norm_cast
  | succ n ih =>
    show Term.realize (Sum.elim ρ xs) (LRV.tVFAdd (LRV.tVFNumeral (n := m) n) LRV.tVFOne)
      = mkVF v ((n + 1 : ℕ) : K)
    simp only [LRV.tVFAdd, Term.realize_func, funMap_def, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
      Function.comp_apply, ih, realize_tVFOne v ρ xs, fMap, mkVF]
    push_cast
    rfl

theorem model_charZeroVF [CharZero K] (k : ℕ) : (C v) ⊨ Axioms.charZeroVF k := by
  simp only [Axioms.charZeroVF]
  prep
  intro h
  have h2 : Term.realize (Sum.elim (default : Empty → C v) ![])
      (LRV.tVFNumeral (n := 0) (k + 1)) = mkVF v ((k + 1 : ℕ) : K) :=
    realize_tVFNumeral _ _ _ _
  simp only [realize_tVFNumeral] at h
  simp only [mkVF, Sum.inl.injEq] at h
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k) h

theorem model_residueCharZero (p : ℕ) (hp : p.Prime) (h : (1 : Γ₀) ≤ v (p : K)) :
    (C v) ⊨ Axioms.residueCharZero p := by
  simp only [Axioms.residueCharZero, LRV.pGtOne]
  prep
  intro hconj
  refine hconj.2 ?_
  have hpv : Term.realize (Sum.elim (default : Empty → C v) ![])
      (LRV.tVFNumeral (n := 0) p) = mkVF v (p : K) :=
    realize_tVFNumeral _ _ _ _
  simp only [realize_tVFNumeral]
  refine ⟨RVM.rv v (p : K), RVM.rvOne v, rfl, ?_, ?_⟩
  · show cRVOne v = Sum.inr (RVM.rvOne v)
    rfl
  · show RVM.vrv v (RVM.rvOne v) ≤ RVM.vrv v (RVM.rv v (p : K))
    simpa [RVM.vrv_rv, Valuation.map_one] using h

/-- **`ACVF(0,0)` at the intended structure**: `ACVF` together with characteristic `0` of
the valued field and of the residue field. -/
theorem model_ACVF00 [IsAlgClosed K] [CharZero K]
    (h : ∀ n : ℕ, n ≠ 0 → (1 : Γ₀) ≤ v (n : K)) : (C v) ⊨ Axioms.ACVF00 := by
  rw [Axioms.ACVF00]
  have h1 : (C v) ⊨ (Axioms.ACVF ∪ {s | ∃ k, s = Axioms.charZeroVF k}) := by
    refine model_union v (model_ACVF v) ?_
    rw [Theory.model_iff]
    rintro s ⟨k, rfl⟩
    exact model_charZeroVF v k
  refine model_union v h1 ?_
  rw [Theory.model_iff]
  rintro s ⟨p, hp, rfl⟩
  exact model_residueCharZero v p hp (h p hp.pos.ne')

#print axioms SpecialTransformations.Milestone0.IModel.model_ACVF00
#print axioms SpecialTransformations.Milestone0.IModel.model_charZeroVF
#print axioms SpecialTransformations.Milestone0.IModel.model_residueCharZero

end SpecialTransformations.Milestone0.IModel

namespace SpecialTransformations
namespace Milestone0

/-! ## Part 5 of the encoding, also omitted by the snapshot: `ACVF_S(0,0)` -/

namespace SubstructureTheory

open Axioms

variable {M : Type*} [LRV.Structure M]

/-- atomic formulas: equalities of terms and applications of relation symbols -/
def IsAtomic {L : FirstOrder.Language} {α : Type*} : L.BoundedFormula α 0 → Prop
  | .equal _ _ => True
  | .rel _ _ => True
  | _ => False

/-- the atomic diagram of a substructure `S` -/
def atomicDiagram (S : LRV.Substructure M) : LRV[[(S : Set M)]].Theory :=
  {φ | IsAtomic φ ∧ (M ⊨ φ)} ∪
    {φ | ∃ ψ, IsAtomic ψ ∧ φ = BoundedFormula.not ψ ∧ ¬ (M ⊨ ψ)}

/-- **`ACVF_S(0,0)`**: `ACVF(0,0)` together with the atomic diagram of `S` -/
def ACVF_S (S : LRV.Substructure M) : LRV[[(S : Set M)]].Theory :=
  (LRV.lhomWithConstants (S : Set M)).onTheory ACVF00 ∪ atomicDiagram S

end SubstructureTheory

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

namespace SpecialTransformations
namespace Milestone0
namespace IModel

attribute [local instance] ACVFResidue.kField

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-! ## added by m6: Γ is nontrivial at ℂ_[p], so `ACVF` has a model there with nontrivial value
group.  (The companion file `refute.lean` shows that `ACVF_S(0,0)`, which additionally needs
`ACVF(0,0)`, has NO model at ℂ_[p].) -/

theorem vrv_rvOne : RVM.vrv v (RVM.rvOne v) = 1 := by
  rw [RVM.rvOne_eq, RVM.vrv_some]
  simp

/-- the `rv`-class of an element of `K` -/
noncomputable def rvOf (a : K) : C v := mkRV v (RVM.rv v a)

theorem iLe_one_rvOf_iff (a : K) :
    iLe (M := C v) iRVOne (rvOf v a) ↔ v a ≤ 1 := by
  simp only [iLe, iRVOne, rvOf, RelMap_def, rMap, funMap_def, fMap, cRVOne,
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨t, s, h1, h2, h3⟩
    simp only [mkRV, Sum.inr.injEq] at h1 h2
    rw [← h1, ← h2] at h3
    simpa [RVM.rvLe, RVM.rvLe, RVM.vrv_rv, vrv_rvOne] using h3
  · intro h
    refine ⟨RVM.rvOne v, RVM.rv v a, rfl, rfl, ?_⟩
    simpa [RVM.rvLe, RVM.rvLe, RVM.vrv_rv, vrv_rvOne] using h

theorem iLe_rvOf_one_iff (a : K) :
    iLe (M := C v) (rvOf v a) iRVOne ↔ 1 ≤ v a := by
  simp only [iLe, iRVOne, rvOf, RelMap_def, rMap, funMap_def, fMap, cRVOne,
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨t, s, h1, h2, h3⟩
    simp only [mkRV, Sum.inr.injEq] at h1 h2
    rw [← h1, ← h2] at h3
    simpa [RVM.rvLe, RVM.rvLe, RVM.vrv_rv, vrv_rvOne] using h3
  · intro h
    refine ⟨RVM.rv v a, RVM.rvOne v, rfl, rfl, ?_⟩
    simpa [RVM.rvLe, RVM.rvLe, RVM.vrv_rv, vrv_rvOne] using h

/-- `rv a ≠ rv 0` for `a ≠ 0`.  The hypothesis is needed: `0` and `∞` are one element, so
`rvOf v 0 = iRVZero`. -/
theorem rvOf_ne_zero (a : K) (ha : a ≠ 0) : rvOf v a ≠ iRVZero (M := C v) := by
  intro h
  have h' : RVM.rv v a = (none : RVM.RV v) := by
    simpa [rvOf, mkRV, iRVZero, funMap_def, fMap, cKZero] using h
  exact ha (RVM.rv_eq_none_iff.mp h')

/-- The same statement with `∞` for `0`: the two symbols name one element. -/
theorem rvOf_ne_infty (a : K) (ha : a ≠ 0) : rvOf v a ≠ iRVInfty (M := C v) := by
  simpa [iRVInfty] using rvOf_ne_zero v a ha

/-- nontrivial `Γ` from an element of value `≠ 1` (faithful reading: `0` and `∞` excluded) -/
theorem gamma_nontrivial_of_val (a : K) (ha : a ≠ 0) (hv : v a ≠ 1) :
    ∃ t : C v, iRV (M := C v) t ∧ t ≠ iRVZero (M := C v) ∧
      t ≠ iRVInfty (M := C v) ∧
        ¬ (iLe (M := C v) iRVOne t ∧ iLe (M := C v) t iRVOne) := by
  refine ⟨rvOf v a, ⟨RVM.rv v a, rfl⟩, rvOf_ne_zero v a ha, rvOf_ne_infty v a ha, ?_⟩
  rintro ⟨h1, h2⟩
  exact hv (le_antisymm ((iLe_one_rvOf_iff v a).mp h1) ((iLe_rvOf_one_iff v a).mp h2))


open scoped NNReal

/-- `v p = 1/p < 1`: the residue of the prime `p` vanishes in `ℂ_[p]` -/
theorem valuation_p_lt_one (p : ℕ) [Fact p.Prime] :
    (PadicComplex.valued p).v (p : ℂ_[p]) < 1 := by
  rw [PadicComplex.valuation_p]
  have hp : (2 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  calc 1 / (p : ℝ≥0) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp
    _ < 1 := by norm_num


/-- **Milestone 1b, the part `ℂ_[p]` can supply**: a model of the full `Axioms.ACVF` whose value
group is nontrivial (`t = rv p` is not `≤`-equivalent to `1`). -/
theorem exists_model_ACVF_nontrivial_gamma_padic (p : ℕ) [Fact p.Prime] :
    ∃ (M : Type) (_ : LRV.Structure M), M ⊨ Axioms.ACVF ∧
      ∃ t : M, iRV (M := M) t ∧ t ≠ iRVZero (M := M) ∧ t ≠ iRVInfty (M := M) ∧
        ¬ (iLe (M := M) iRVOne t ∧ iLe (M := M) t iRVOne) :=
  ⟨C ((PadicComplex.valued p).v), inferInstance, model_ACVF ((PadicComplex.valued p).v),
    gamma_nontrivial_of_val ((PadicComplex.valued p).v) (p : ℂ_[p])
      (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
      (ne_of_lt (valuation_p_lt_one p))⟩

/-- **The milestone, in its final form.**  There is a model of `ACVF` together with a
substructure `S` whose value group is nontrivial, in the non-vacuous reading: `S` contains an
element of `RV^×` outside the class of `1`.  The model is the general one over `ℂ_[p]`, where
the witness is `rv p` and `Γ` is nontrivial because `v p = 1/p ≠ 1`.

The `(0,0)` refinement is not available here — `ℂ_[p]` has residue characteristic `p` — so
this is `ACVF`, the theory over which Theorems 2.3 and 2.8 are stated, and not `ACVF_S(0,0)`. -/
theorem milestone_model_with_nontrivial_gamma (p : ℕ) [Fact p.Prime] :
    ∃ (M : Type) (_ : LRV.Structure M) (S : LRV.Substructure M),
      M ⊨ Axioms.ACVF ∧
        ∃ t, (S : Set M) t ∧ iRV (M := M) t ∧ t ≠ iRVZero (M := M) ∧
          t ≠ iRVInfty (M := M) ∧ ¬ (iLe (M := M) iRVOne t ∧ iLe (M := M) t iRVOne) := by
  obtain ⟨M, inst, hM, t, ht, ht0, hti, hcls⟩ :=
    exists_model_ACVF_nontrivial_gamma_padic p
  exact ⟨M, inst, ⊤, hM, t, Set.mem_univ t, ht, ht0, hti, hcls⟩

end IModel
end Milestone0
end SpecialTransformations

#print axioms SpecialTransformations.Milestone0.IModel.milestone_model_with_nontrivial_gamma
