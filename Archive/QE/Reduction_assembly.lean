/-
Formalization of the reduction in Yin, *Special transformations in algebraically closed valued
fields* (arXiv:1006.2467), Section 3 = companion paper arXiv:1006.1393, Section 3: quantifier
elimination for `ACVF` in `L_RV` (Theorem 3.10) from Weispfenning's QE theorem for the
two-sorted `L_v`.

Contents.

* Part 0-3 and the `HasQE`/interpretation definitions in Part A are copied **verbatim** from
  `Milestone0/Encoding.lean` (commit d608de6, sha256
  `78607b94c28343fc3aa5c260cb1f296063f579d5f38b5f14b260618827980be6`), so that every statement
  below is a statement about the *frozen* encoding `LRV`, `Axioms.ACVF`, `HasQE`.  The copy is
  forced by the rule that every file of this run has `import Mathlib` as its only import.
* Part B is the general back-and-forth machinery (`BackAndForth.lean`): unions of chains of
  partial isomorphisms, the exhaustion theorem `exists_exhaust` ("iterating these procedures we
  may exhaust all elements"), and `exists_total_embedding`.
* Part C is the assembly: the paper's Lemmas 3.3-3.8 and Remark 3.1 are stated as explicit Lean
  `Prop`s, and Proposition 3.9 (`lrv:mono:lift`) and Theorem 3.10 (`qe:acvf`) are *proved* from
  them.

Converted to the project's ruling that the paper's `0` and `∞` are ONE element (the element
`rv(0)`, which is the residue field's zero and the absorbing element of `RV`).  As in
`QE/Reduction_Lv.lean`: the constructor `Fn.rvInfty` is deleted, `tRVInfty`/`iRVInfty` are
definitions of `tRVZero`/`iRVZero`, `Axioms.rvSurj` is the paper's surjectivity
(`∀ t ≠ rv(0), ∃ x, rv x = t`), the axioms that name the top through `tRVInfty` are unchanged
textually and are now the `rvZero`-versions, and the `RV0` alias is the two-layer `RV`.
The only theorem whose statement changed is `Axioms.rvSurj`.

The unrestricted `rvSurj` has content: with it, `RV = rv(VF^×) ∪ {0}` is a *theorem* about models
of `ACVF` (`RVeqRvVF_of_model`, proved here from the realization lemmas in the `Realize`
section), whereas the old `Kˣ`-guarded axiom could not exclude "junk" `RV`-elements.  The
hypothesis `AlgIngredients.rv` is therefore discharged: `theorem_2_3_of_three` is Theorem 3.10
with only the three remaining ingredients.

Nothing is assumed as an `axiom`; every unproved ingredient is a named hypothesis of the
theorem that uses it.  See the report for the list.
-/
import Mathlib

set_option linter.style.haveILetI false


open FirstOrder FirstOrder.Language

namespace SpecialTransformations
namespace Milestone0

/-! ## Part 0. The paper's `RV` sort (conventions of `SpecialTransformations/Basic.lean`) -/

/- The algebraic layer of the paper, as it exists in the repository: `RV^× = Kˣ/(1+M)`,
`RV = RV^× ∪ {rv 0}` and `rv : K → RV`.  The paper's `∞` is `rv 0`; the `RV` sort has one
absorbing element, which is also the residue field's zero. -/
namespace Valued

open Valuation

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀)

/-- `RV× = Kˣ / (1 + M)`, the multiplicative RV sort. -/
abbrev RVUnit : Type _ := Kˣ ⧸ v.valuationSubring.principalUnitGroup

/-- The `RV` sort: `RV = RV^× ∪ {rv 0}`.  `none` is `rv 0`, the absorbing element — the paper's
`∞`, which is also the residue field's zero `0`. -/
abbrev RV : Type _ := Option (RVUnit v)

/-- The paper's `RV₀ = RV ∪ {0}`.  Since `0 = ∞ = rv 0` is already the element `none` of `RV`,
`RV₀` is the same type; the alias is kept for the paper's notation. -/
abbrev RV0 : Type _ := RV v

/-- The quotient map `rv : K → RV`, with `rv 0 = 0` (the paper's `∞`). -/
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
/-- the paper's `RV-sort ∖ {∞}`.

**Caution.**  Since `∞ = rv(0) = 0`, this predicate is `RV ∖ {0}` — the multiplicative group
`RV^×` — and *not* the residue field `K`: `K = K^× ∪ {0}` is `pInK`, which does contain the
absorbing element.  The name is kept only because the paper's own notation `RV ∖ {∞}` appears
in its statements; `pK` is the same predicate as `pRV`. -/
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

The `RV` sort's carrier is the multiplicative group `RV^×` together with one absorbing element,
`rv 0 = 0 = ∞`, which is also the residue field's zero.  The paper's field is
`K = K^× ∪ {0}` — the units together with the absorbing element — and that is *not* the same as
`RV ∖ {0}`, which is the group `RV^×`: when `Γ` is nontrivial there are elements of value
`≠ 1` in `RV^×` at which the residue operations are junk.  Axioms about the field `K` are
therefore relativised to `pInK t = (t ∈ K^×) ⊔ (t = 0)`, not to `t ≠ ∞ = 0`. -/

/-- `⋀ i < k, x_i ∈ K`: the tuple lies in `K = K^× ∪ {0}` -/
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
`K = K^× ∪ {0}`, the units of `RV` together with the absorbing element `0 = ∞ = rv 0`.

Every quantifier is relativised to `K` (`allSortedK`, `exSortedK`), not merely to the `RV`
sort.  This is not cosmetic: `RV^×` also contains the elements of value `≠ 1`, where the
residue operations are junk, so asserting the field axioms at every element of `RV`
(equivalently at every `t ≠ ∞`, since `RV ∖ {0}` *is* the group) would force `Γ` trivial. -/
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
/-- `t × 0 = 0` for every `t` of the `RV` sort: the absorbing element.  (This is the paper's
`t × ∞ = ∞`; `∞ = rv 0 = 0`.) -/
def rvMulInfty : LRV.Sentence := allSorted ![.rv] (pEq (tRVMul &0 tRVInfty) tRVInfty)

/-- Definition 2.2 item 2: `(RV^×, 1, ×)` is a divisible abelian group, with `×`
augmented by `t × 0 = 0`, i.e. `0 = ∞ = rv 0` absorbing. -/
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

/-! ## Back-and-forth (general, copied from `BackAndForth.lean`) -/

universe u w w'

variable {L : Language.{u}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-! ## Unions of chains of partial isomorphisms -/

/-- The index type of a chain is directed. -/
theorem chain_isDirected (c : Set (M ≃ₚ[L] N)) (hch : IsChain (· ≤ ·) c) :
    IsDirectedOrder ↥c :=
  ⟨fun a b => by
    rcases eq_or_ne a b with rfl | hne
    · exact ⟨a, le_rfl, le_rfl⟩
    · rcases hch a.2 b.2 (fun hh => hne (Subtype.ext hh)) with h' | h'
      · exact ⟨b, h', le_rfl⟩
      · exact ⟨a, le_rfl, h'⟩⟩

/-- The union of a nonempty chain of partial isomorphisms `M ≃ₚ[L] N`: a chain in the order of
`PartialEquiv` is a directed system of substructures and the union of the maps is again a partial
isomorphism (`DirectLimit.partialEquivLimit`). -/
noncomputable def chainSup (c : Set (M ≃ₚ[L] N)) (hne : c.Nonempty)
    (hch : IsChain (· ≤ ·) c) : M ≃ₚ[L] N :=
  letI : Nonempty ↥c := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  letI : IsDirectedOrder ↥c := chain_isDirected c hch
  DirectLimit.partialEquivLimit (⟨Subtype.val, fun _ _ hh => hh⟩ : ↥c →o M ≃ₚ[L] N)

/-- Every member of a chain is below its union. -/
theorem le_chainSup {c : Set (M ≃ₚ[L] N)} (hne : c.Nonempty) (hch : IsChain (· ≤ ·) c)
    {z : M ≃ₚ[L] N} (hz : z ∈ c) : z ≤ chainSup c hne hch := by
  letI : Nonempty ↥c := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  letI : IsDirectedOrder ↥c := chain_isDirected c hch
  exact DirectLimit.le_partialEquivLimit (⟨Subtype.val, fun _ _ hh => hh⟩ : ↥c →o M ≃ₚ[L] N)
    ⟨z, hz⟩

/-! ## Exhausting a set of elements -/

/-- **The paper's transfinite bookkeeping**, abstractly.  Let `P` be a property of partial
isomorphisms `M ≃ₚ[L] N` (e.g. "the domain satisfies the standing assumptions of Lemmas 3.4-3.8")
that is preserved by unions of chains, and suppose every `P`-partial isomorphism can be enlarged,
preserving `P`, so that its domain contains any one prescribed element of a set `Q ⊆ M` (the
one-element steps of Lemmas 3.4-3.8).  Then every `P`-partial isomorphism extends to a
`P`-partial isomorphism whose domain contains all of `Q` ("iterating these procedures we may
exhaust all elements"). -/
theorem exists_exhaust (P : (M ≃ₚ[L] N) → Prop) (Q : M → Prop)
    (hsup : ∀ (c : Set (M ≃ₚ[L] N)) (hne : c.Nonempty) (hch : IsChain (· ≤ ·) c),
      (∀ z ∈ c, P z) → P (chainSup c hne hch))
    (hstep : ∀ (G : M ≃ₚ[L] N), P G → ∀ m : M, Q m →
      ∃ G' : M ≃ₚ[L] N, G ≤ G' ∧ P G' ∧ m ∈ G'.dom)
    (G₀ : M ≃ₚ[L] N) (hP₀ : P G₀) :
    ∃ G : M ≃ₚ[L] N, G₀ ≤ G ∧ P G ∧ ∀ m : M, Q m → m ∈ G.dom := by
  let s : Set (M ≃ₚ[L] N) := {G | P G ∧ G₀ ≤ G}
  have hs : G₀ ∈ s := ⟨hP₀, le_rfl⟩
  have hzorn : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub := by
    intro c hcs hch
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨G₀, hs, by simp⟩
    · have hPc : ∀ z ∈ c, P z := fun z hz => (hcs hz).1
      refine ⟨chainSup c hne hch, ⟨hsup c hne hch hPc, ?_⟩, fun z hz => le_chainSup hne hch hz⟩
      exact (hcs hne.choose_spec).2.trans (le_chainSup hne hch hne.choose_spec)
  obtain ⟨G, hG⟩ := zorn_le₀ s hzorn
  · refine ⟨G, hG.1.2, hG.1.1, fun m hm => ?_⟩
    by_contra hmem
    obtain ⟨G', hGG', hPG', hmG'⟩ := hstep G hG.1.1 m hm
    have hG's : G' ∈ s := ⟨hPG', hG.1.2.trans hGG'⟩
    have hle : G' ≤ G := hG.2 hG's hGG'
    exact hmem (PartialEquiv.dom_le_dom hle hmG')

/-! ## The one-element extension property, and full extension -/

/-- The one-element extension property in partial-isomorphism form. -/
def OneStep : Prop := ∀ (f : M ≃ₚ[L] N) (m : M), ∃ g : M ≃ₚ[L] N, f ≤ g ∧ m ∈ g.dom

/-- Every partial isomorphism extends to one whose domain is all of `M`. -/
theorem exists_dom_top (h : OneStep (L := L) (M := M) (N := N)) (f : M ≃ₚ[L] N) :
    ∃ g : M ≃ₚ[L] N, f ≤ g ∧ g.dom = ⊤ := by
  obtain ⟨G, hfG, -, hall⟩ :=
    exists_exhaust (L := L) (M := M) (N := N) (fun _ => True) (fun _ => True)
      (fun _ _ _ _ => trivial) (fun G _ m _ => by obtain ⟨g, h1, h2⟩ := h G m; exact ⟨g, h1, trivial, h2⟩) f trivial
  refine ⟨G, hfG, ?_⟩
  ext x
  exact ⟨fun _ => Substructure.mem_top x, fun _ => hall x trivial⟩

/-- The paper's one-element extension property, in the form used in Lemmas 3.4-3.8: an embedding
of a substructure of `M` into `N` extends to a larger substructure containing a prescribed
element. -/
def OneStepEmb : Prop :=
  ∀ (S : L.Substructure M) (f : S ↪[L] N) (m : M),
    ∃ (T : L.Substructure M) (g : T ↪[L] N) (hST : S ≤ T),
      m ∈ T ∧ ∀ x : S, g ⟨(x : M), hST x.2⟩ = f x

/-- The partial isomorphism associated with an embedding of a substructure. -/
noncomputable def embPE {S : L.Substructure M} (f : S ↪[L] N) : M ≃ₚ[L] N :=
  ⟨S, f.toHom.range, f.equivRange⟩

/-- An embedding of a larger substructure which agrees with `f` on `S` gives a larger partial
isomorphism. -/
theorem embPE_le_of_extends {S T : L.Substructure M} (f : S ↪[L] N) (g : T ↪[L] N)
    (hST : S ≤ T) (hagree : ∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) :
    embPE f ≤ embPE g := by
  rw [PartialEquiv.le_iff]
  refine ⟨hST, ?_, ?_⟩
  · rintro y ⟨x, rfl⟩
    exact ⟨⟨(x : M), hST x.2⟩, hagree x⟩
  · intro x
    apply Subtype.ext
    show (f.equivRange x : N) = (g ⟨(x : M), hST x.2⟩ : N)
    rw [hagree x]
    exact Embedding.equivRange_apply f x

/-- If a partial isomorphism sits above the partial isomorphism of `f`, then it agrees with `f`
on the domain of `f`. -/
theorem agree_of_le {S : L.Substructure M} (f : S ↪[L] N) {G : M ≃ₚ[L] N}
    (hle : embPE f ≤ G) (x : S) (hx : (x : M) ∈ G.dom) :
    ((G.toEquiv ⟨(x : M), hx⟩ : G.cod) : N) = f x := by
  have key := congrArg (fun y : G.cod => (y : N))
    (PartialEquiv.toEquiv_inclusion_apply hle x)
  have harg : (⟨(x : M), hx⟩ : G.dom)
      = Substructure.inclusion (PartialEquiv.dom_le_dom hle) x := Subtype.ext rfl
  rw [harg, key]
  exact Embedding.equivRange_apply f x

/-- The embedding form implies the partial-isomorphism form. -/
theorem oneStep_of_oneStepEmb (h : OneStepEmb (L := L) (M := M) (N := N)) :
    OneStep (L := L) (M := M) (N := N) := by
  intro f m
  obtain ⟨T, g, hST, hmT, hagree⟩ := h f.dom (PartialEquiv.toEmbedding f) m
  refine ⟨⟨T, g.toHom.range, g.equivRange⟩, ?_, ?_⟩
  swap
  · exact hmT
  rw [PartialEquiv.le_iff]
  refine ⟨hST, ?_, ?_⟩
  · rintro y hy
    refine ⟨⟨((f.toEquiv.symm ⟨y, hy⟩ : f.dom) : M), hST (f.toEquiv.symm ⟨y, hy⟩).2⟩, ?_⟩
    show g ⟨((f.toEquiv.symm ⟨y, hy⟩ : f.dom) : M), hST (f.toEquiv.symm ⟨y, hy⟩).2⟩ = y
    rw [hagree]
    simp
  · intro x
    apply Subtype.ext
    show ((f.toEquiv x : f.cod) : N) = (g ⟨(x : M), hST x.2⟩ : N)
    rw [hagree]
    rfl

/-- **Shoenfield's total-extension step**: if every embedding of a substructure of `M` into `N`
can be extended one element at a time, then every embedding of a substructure of `M` into `N`
extends to an embedding defined on all of `M`.  (Proposition 3.9's last step; the one-element
property is what Lemmas 3.2-3.8 and Remark 3.1 supply.) -/
theorem exists_total_embedding (h : OneStepEmb (L := L) (M := M) (N := N))
    (S : L.Substructure M) (f : S ↪[L] N) :
    ∃ g : M ↪[L] N, ∀ x : S, g (x : M) = f x := by
  obtain ⟨G, hle, htop⟩ := exists_dom_top (oneStep_of_oneStepEmb h) (embPE f)
  refine ⟨PartialEquiv.toEmbeddingOfEqTop htop, ?_⟩
  intro x
  rw [PartialEquiv.toEmbeddingOfEqTop_apply]
  exact agree_of_le f hle x (htop.symm ▸ Substructure.mem_top (x : M))

/-! ## Realising an atomic type extends a monomorphism by one element -/

namespace Realize

open FirstOrder FirstOrder.Language

variable {L : Language.{u}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
variable {S : L.Substructure M} {f : S ↪[L] N} {m : M} {b : N}

/-- the parameters of the type, evaluated in `M` -/
def mv (S : L.Substructure M) (m : M) : S ⊕ Unit → M :=
  Sum.elim (fun s => (s : M)) (fun _ => m)

/-- the parameters of the type, evaluated in `N` -/
def wv (f : S ↪[L] N) (b : N) : S ⊕ Unit → N :=
  Sum.elim (fun s => f s) (fun _ => b)

/-- **`b` realises the atomic type of `m` over `S`** (pushed forward by `f`): equalities of
terms with parameters in `S` and the point `m` transfer, and so do relation atoms. -/
def RealizesAtomic (S : L.Substructure M) (f : S ↪[L] N) (m : M) (b : N) : Prop :=
  (∀ (u v : L.Term (S ⊕ Unit)),
      u.realize (mv S m) = v.realize (mv S m) ↔ u.realize (wv f b) = v.realize (wv f b)) ∧
    (∀ (n : ℕ) (r : L.Relations n) (ts : Fin n → L.Term (S ⊕ Unit)),
      Structure.RelMap r (fun i => (ts i).realize (mv S m)) ↔
        Structure.RelMap r (fun i => (ts i).realize (wv f b)))

/-- the generators `↑S ∪ {m}` mapped into `S ⊕ Unit` -/
noncomputable def kappa (S : L.Substructure M) (m : M) (hm : m ∉ S) :
    ↥((S : Set M) ∪ {m}) → S ⊕ Unit := by
  classical
  exact fun y => if h : (y : M) ∈ S then Sum.inl ⟨y.1, h⟩ else Sum.inr ()

theorem mv_kappa (hm : m ∉ S) (y : ↥((S : Set M) ∪ {m})) :
    mv S m (kappa S m hm y) = (y : M) := by
  classical
  unfold kappa mv
  split_ifs with h
  · rfl
  · have hy : (y : M) = m := by
      rcases (show (y : M) = m ∨ (y : M) ∈ S from by simpa using y.2) with h3 | h3
      · simpa using h3
      · exact absurd h3 h
    simp [hy]

/-- the value in `N` of the generators `↑S ∪ {m}` -/
noncomputable def toN (S : L.Substructure M) (f : S ↪[L] N) (b : N) (m : M) (hm : m ∉ S) :
    ↥((S : Set M) ∪ {m}) → N :=
  fun y => wv f b (kappa S m hm y)

theorem realize_mv (hm : m ∉ S) (u : L.Term ↥((S : Set M) ∪ {m})) :
    (u.relabel (kappa S m hm)).realize (mv S m) = u.realize (Subtype.val) := by
  rw [Term.realize_relabel]
  congr 1
  funext y
  exact mv_kappa hm y

theorem realize_wv (hm : m ∉ S) (u : L.Term ↥((S : Set M) ∪ {m})) :
    (u.relabel (kappa S m hm)).realize (wv f b) = u.realize (toN S f b m hm) := by
  rw [Term.realize_relabel]
  rfl

/-- Terms with the same value in `M` have the same value in `N`. -/
theorem realize_eq (hb : RealizesAtomic S f m b) (hm : m ∉ S)
    (t₁ t₂ : L.Term ↥((S : Set M) ∪ {m}))
    (h : t₁.realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M) = t₂.realize Subtype.val) :
    t₁.realize (toN S f b m hm) = t₂.realize (toN S f b m hm) := by
  have h' : (t₁.relabel (kappa S m hm)).realize (mv S m) = (t₂.relabel (kappa S m hm)).realize (mv S m) := by
    rw [realize_mv hm, realize_mv hm]; exact h
  rw [← realize_wv hm, ← realize_wv hm]
  exact (hb.1 _ _).mp h'

/-- Terms with the same value in `N` have the same value in `M`. -/
theorem realize_eq' (hb : RealizesAtomic S f m b) (hm : m ∉ S)
    (t₁ t₂ : L.Term ↥((S : Set M) ∪ {m}))
    (h : t₁.realize (toN S f b m hm) = t₂.realize (toN S f b m hm)) :
    t₁.realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M) = t₂.realize Subtype.val := by
  rw [← realize_wv hm, ← realize_wv hm] at h
  rw [← realize_mv hm, ← realize_mv hm]
  exact (hb.1 _ _).mpr h

/-- the value in `N` of a point of `closure L (↑S ∪ {m})` -/
noncomputable def gfun (f : S ↪[L] N) (b : N) (hm : m ∉ S) (x : M)
    (hx : x ∈ Substructure.closure L ((S : Set M) ∪ {m})) : N :=
  (Classical.choose (Substructure.mem_closure_iff_exists_term.mp hx)).realize (toN S f b m hm)

theorem gfun_spec (hb : RealizesAtomic S f m b) (hm : m ∉ S)
    (t : L.Term ↥((S : Set M) ∪ {m})) :
    gfun f b hm (t.realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M))
        (Term.realize_mem t Subtype.val (fun a => Substructure.subset_closure a.2))
      = t.realize (toN S f b m hm) :=
  realize_eq hb hm _ t
    (Classical.choose_spec (Substructure.mem_closure_iff_exists_term.mp
      (Term.realize_mem t Subtype.val (fun a => Substructure.subset_closure a.2))))



/-- every element of the generated substructure is the value of a term -/
theorem exists_term_eq {x : M} (hx : x ∈ Substructure.closure L ((S : Set M) ∪ {m})) :
    ∃ t : L.Term ↥((S : Set M) ∪ {m}), t.realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M) = x :=
  Substructure.mem_closure_iff_exists_term.mp hx

theorem gfun_eq (hb : RealizesAtomic S f m b) (hm : m ∉ S)
    (t : L.Term ↥((S : Set M) ∪ {m})) (x : M)
    (hx : x ∈ Substructure.closure L ((S : Set M) ∪ {m}))
    (ht : t.realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M) = x) :
    gfun f b hm x hx = t.realize (toN S f b m hm) := by
  unfold gfun
  exact realize_eq hb hm _ t (by rw [Classical.choose_spec (exists_term_eq (S := S) (m := m) hx)]; exact ht.symm)

section OneStep

variable (hb : RealizesAtomic S f m b) (hm : m ∉ S)

/-- The embedding of `closure L (↑S ∪ {m})` in `N` determined by `f` and by the realisation
`b` of the atomic type of `m`. -/
noncomputable def gEmb : ↥(Substructure.closure L ((S : Set M) ∪ {m})) ↪[L] N where
  toFun x := gfun f b hm x.1 x.2
  inj' x y hxy := by
    apply Subtype.ext
    have hx := Classical.choose_spec (exists_term_eq (S := S) (m := m) x.2)
    have hy := Classical.choose_spec (exists_term_eq (S := S) (m := m) y.2)
    have h := realize_eq' hb hm _ _ hxy
    rw [← hx, ← hy]
    exact h
  map_fun' {n} F x := by
    let t : Fin n → L.Term ↥((S : Set M) ∪ {m}) := fun i =>
      Classical.choose (exists_term_eq (S := S) (m := m) (x i).2)
    have hx : ∀ i, (t i).realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M) = (x i).1 :=
      fun i => Classical.choose_spec (exists_term_eq (S := S) (m := m) (x i).2)
    have ht : (Term.func F t).realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M)
        = Structure.funMap F (fun i => (x i).1) := by
      simp only [Term.realize_func]
      congr 1
      funext i
      exact hx i
    show gfun f b hm (Structure.funMap F (fun i => (x i).1)) _ = Structure.funMap F (fun i => gfun f b hm (x i).1 (x i).2)
    rw [gfun_eq hb hm (Term.func F t) (Structure.funMap F (fun i => (x i).1)) _ ht]
    rw [Term.realize_func]
    exact congrArg (Structure.funMap F) (funext fun i => (gfun_eq hb hm (t i) (x i).1 _ (hx i)).symm)
  map_rel' {n} r x := by
    let t : Fin n → L.Term ↥((S : Set M) ∪ {m}) := fun i =>
      Classical.choose (exists_term_eq (S := S) (m := m) (x i).2)
    have hx : ∀ i, (t i).realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M) = (x i).1 :=
      fun i => Classical.choose_spec (exists_term_eq (S := S) (m := m) (x i).2)
    have h := hb.2 n r (fun i => (t i).relabel (kappa S m hm))
    simp only [realize_mv hm, realize_wv hm] at h
    rw [show (fun i => (t i).realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M))
        = (fun i => (x i).1) from funext hx] at h
    rw [show (fun i => (t i).realize (toN S f b m hm))
        = (fun i => gfun f b hm (x i).1 (x i).2) from
      funext fun i => (gfun_eq hb hm (t i) (x i).1 _ (hx i)).symm] at h
    show Structure.RelMap r ((fun y : ↥(Substructure.closure L ((S : Set M) ∪ {m})) =>
      gfun f b hm y.1 y.2) ∘ x) ↔ Structure.RelMap r x
    exact h.symm

/-- **A realisation of the atomic type of one element extends the embedding by that element.** -/
theorem exists_oneStep (hb : RealizesAtomic S f m b) (hm : m ∉ S) :
    ∃ (T : L.Substructure M) (g : T ↪[L] N) (hST : S ≤ T),
      m ∈ T ∧ ∀ x : S, g ⟨(x : M), hST x.2⟩ = f x := by
  refine ⟨Substructure.closure L ((S : Set M) ∪ {m}), gEmb hb hm, ?_, ?_, ?_⟩
  · intro x hx
    exact Substructure.subset_closure (Set.mem_union_left _ hx)
  · exact Substructure.subset_closure (Set.mem_union_right _ (Set.mem_singleton m))
  · intro x
    have hxT : (x : M) ∈ Substructure.closure L ((S : Set M) ∪ {m}) :=
      Substructure.subset_closure (Set.mem_union_left {m} x.2)
    have hk : kappa S m hm (⟨(x : M), Set.mem_union_left {m} x.2⟩ : ↥((S : Set M) ∪ {m}))
        = Sum.inl (⟨(x : M), x.2⟩ : S) := by
      simp only [kappa]
      exact (dif_pos x.2).trans (congrArg Sum.inl (Subtype.ext rfl))
    show gfun f b hm (x : M) hxT = f x
    rw [gfun_eq hb hm (Term.var (⟨(x : M), Set.mem_union_left {m} x.2⟩ : ↥((S : Set M) ∪ {m})))
      (x : M) hxT rfl]
    show toN S f b m hm ⟨(x : M), Set.mem_union_left {m} x.2⟩ = f x
    show wv f b (kappa S m hm ⟨(x : M), Set.mem_union_left {m} x.2⟩) = f x
    rw [hk]
    rfl

end OneStep


/-- Type realisation gives the one-element extension property. -/
theorem oneStepEmb_of_realizesAtomic
    (h : ∀ (S : L.Substructure M) (f : S ↪[L] N) (m : M), m ∉ S → ∃ b : N, RealizesAtomic S f m b) :
    OneStepEmb (L := L) (M := M) (N := N) := by
  intro S f m
  by_cases hm : m ∈ S
  · exact ⟨S, f, le_rfl, hm, fun x => rfl⟩
  · obtain ⟨b, hb⟩ := h S f m hm
    exact exists_oneStep hb hm

/-- **Shoenfield's extension step from type realisability**: if the atomic type of every element
of `M` over every substructure is realisable in `N`, then every monomorphism of a substructure of
`M` into `N` extends to a monomorphism defined on all of `M`. -/
theorem exists_total_embedding_of_realizesAtomic
    (h : ∀ (S : L.Substructure M) (f : S ↪[L] N) (m : M), m ∉ S → ∃ b : N, RealizesAtomic S f m b)
    (S : L.Substructure M) (f : S ↪[L] N) :
    ∃ g : M ↪[L] N, ∀ x : S, g (x : M) = f x :=
  exists_total_embedding (oneStepEmb_of_realizesAtomic h) S f

end Realize


/-! ## `HasQE` and the interpretations of the symbols (copied verbatim from Part 6 of the frozen file) -/

section IotaDefs

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


end IotaDefs

/-! ## Part C. The paper's Section 3.1, assembled

The paper fixes `M, N ⊨ ACVF` with `N` `‖M‖⁺`-saturated, a substructure `S ⊆ M` and a
monomorphism `f : S → N`, and proves Proposition 3.9 (`lrv:mono:lift`): `f` extends to a
monomorphism `M → N`.  The ingredients are Lemma 3.3 (enlarge to a substructure with `K(S) = K(M)`
and `Γ(S)` divisible), Lemmas 3.4-3.8 (add one element of `VF(M)` at a time, preserving those
two properties), and Remark 3.1 together with Weispfenning's QE theorem for `L_v` (extend a
monomorphism whose domain is `VF`-generated, the target being saturated).

Each ingredient is stated below as a named `Prop` with its hypotheses spelled out; everything
that follows is proved from them. -/

namespace Assembly

open Axioms

/-! ### The two standing assumptions of the paper -/

variable {M : Type*} [LRV.Structure M] [M ⊨ ACVF]

/-- the `n`-th power in the `RV` sort -/
def rvPow (x : M) : ℕ → M
  | 0 => iRVOne
  | (n + 1) => iRVMul (rvPow x n) x

/-- `K(S) = K(M)`: every unit of `M` already lies in the substructure `S`.  (`K = Kˣ ∪ {0}` is
the residue field inside the `RV` sort; `0` is in `S` because it is a constant.) -/
def KEqTop (S : LRV.Substructure M) : Prop := ∀ x : M, iUnits x → x ∈ S

/-- `Γ(S)` is divisible.  `Γ = RV / Kˣ`, so an element of `Γ(S)` is `[t]` with `t ∈ RV(S)`,
`t ≠ 0`, and divisibility says: for every `n ≥ 1` there are `u ∈ RV(S)`, `u ≠ 0`, and
`c ∈ Kˣ(S)` with `uⁿ = t · c`. -/
def GammaDivisible (S : LRV.Substructure M) : Prop :=
  ∀ t : M, t ∈ S → iRV t → t ≠ iRVZero → ∀ n : ℕ, 1 ≤ n →
    ∃ u c : M, u ∈ S ∧ iRV u ∧ u ≠ iRVZero ∧ c ∈ S ∧ iUnits c ∧ rvPow u n = iRVMul t c

/-- the paper's standing assumptions after Lemma 3.3 -/
def Standing (S : LRV.Substructure M) : Prop := KEqTop S ∧ GammaDivisible S

/-- `S` is `VF`-generated (the paper's `rv(VF(S)) = RV(S)`): every element of the `RV` sort in
`S` is `rv` of an element of the `VF` sort in `S`, except possibly the absorbing element
`0 = rv(0)`, which is handled by the second disjunct.  (In a model of `ACVF` even that element
has a witness, namely `0` of the `VF` sort — see `RVeqRvVF_of_model`.) -/
def IsVFGen (S : LRV.Substructure M) : Prop :=
  ∀ x : M, x ∈ S → iRV x → (∃ y : M, y ∈ S ∧ iVF y ∧ iRv y = x) ∨ x = iRVZero

/-- In a model of `ACVF` every element of the `RV` sort is `rv` of an element of the `VF` sort,
up to the residue zero: `RV = rv(VF^×) ∪ {0}`, where `0 = ∞ = rv(0)`.  This is the content of the
axiom `Axioms.rvSurj` (the paper's surjectivity of `rv : VF^× → RV^×`, which since the
identification of `0` with `∞` reads "every `RV`-element other than `rv(0)` is `rv(x)`"), so it
is a theorem about models of `ACVF`; `RVeqRvVF_of_model` below proves it.  It is kept as a
named `Prop` because the Section 3.1 argument (Proposition 3.9) uses it as an explicit
hypothesis: the paper derives it from the model-theoretic description of `RV`, the encoding
derives it from the axiom. -/
def RVeqRvVF (M : Type*) [LRV.Structure M] : Prop :=
  ∀ x : M, iRV x → (∃ y : M, iVF y ∧ iRv y = x) ∨ x = iRVZero

/-! ### Reading an encoded axiom off a model

`allSorted ss φ` abbreviates `∀ x̄ ∈ s̄, φ`.  To extract the content of an axiom from a model one
has to unfold `BoundedFormula.alls`, `sortedHyps` and the term constructors; the lemmas below do
that.  They are used once, for `Axioms.rvSurj`. -/

section Realize

open FirstOrder FirstOrder.Language

/-- the assignment that sends the variables `Fin k` to the values `xs` -/
abbrev rho {k : ℕ} (xs : Fin k → M) : Empty ⊕ Fin k → M := Sum.elim default xs

theorem ev_tv {k : ℕ} (xs : Fin k → M) (i : Fin k) :
    Term.realize (rho xs) (LRV.tv i.val i.isLt) = xs i := by
  simp [LRV.tv, rho]

/-- evaluation of an arity-`0` function symbol -/
theorem ev_fun0 {k : ℕ} (xs : Fin k → M) (f : Fn 0) :
    Term.realize (rho xs) (Term.func f (fun i => i.elim0) : LRV.Tm k)
      = Structure.funMap (L := LRV) f (fun i : Fin 0 => i.elim0) := by
  have key : Term.realize (rho xs) (Term.func f (fun i => i.elim0) : LRV.Tm k)
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

/-- the value of a unary term constructor -/
theorem ev_un {k : ℕ} (xs : Fin k → M) (f : Fn 1) (t : LRV.Tm k) :
    Term.realize (rho xs) (Term.func f ![t] : LRV.Tm k)
      = Structure.funMap (L := LRV) f ![Term.realize (rho xs) t] := by
  have key : Term.realize (rho xs) (Term.func f ![t] : LRV.Tm k)
      = Structure.funMap (L := LRV) f
        (fun i : Fin 1 => Term.realize (rho xs) (![t] i)) := rfl
  rw [key]
  have h1 : (fun i : Fin 1 => Term.realize (rho xs) (![t] i))
      = ![Term.realize (rho xs) t] := by
    funext i
    fin_cases i
    rfl
  rw [h1]

@[simp] theorem ev_rvMap {k : ℕ} (xs : Fin k → M) (t : LRV.Tm k) :
    Term.realize (rho xs) (LRV.tRv t) = iRv (Term.realize (rho xs) t) :=
  ev_un xs Fn.rvMap t

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

@[simp] theorem real_eq {k : ℕ} (xs : Fin k → M) (t u : LRV.Tm k) :
    (LRV.pEq t u).Realize (default : Empty → M) xs ↔
      Term.realize (rho xs) t = Term.realize (rho xs) u := by
  rw [LRV.pEq, FirstOrder.Language.BoundedFormula.realize_bdEqual]

theorem real_sortPred_rv {k : ℕ} (xs : Fin k → M) (t : LRV.Tm k) :
    (LRV.sortPred .rv t).Realize (default : Empty → M) xs ↔ iRV (Term.realize (rho xs) t) :=
  real_memRV xs t

theorem real_sortPred_vf {k : ℕ} (xs : Fin k → M) (t : LRV.Tm k) :
    (LRV.sortPred .vf t).Realize (default : Empty → M) xs ↔ iVF (Term.realize (rho xs) t) :=
  real_memVF xs t

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

@[simp] theorem real_exSorted_vf {k : ℕ} (xs : Fin k → M) (φ : LRV.Bf (k + 1)) :
    (LRV.exSorted .vf φ).Realize (default : Empty → M) xs ↔
      ∃ a : M, iVF a ∧ φ.Realize (default : Empty → M) (Fin.snoc xs a) := by
  have h := FirstOrder.Language.BoundedFormula.realize_ex
    (θ := LRV.sortPred .vf (LRV.tv k (Nat.lt_succ_self k)) ⊓ φ)
    (v := (default : Empty → M)) (xs := xs)
  refine h.trans (exists_congr fun a => ?_)
  have h2 : (LRV.sortPred .vf (LRV.tv k (Nat.lt_succ_self k))).Realize
      (default : Empty → M) (Fin.snoc xs a) ↔ iVF a := by
    rw [real_sortPred_vf]
    have htv : Term.realize (rho (Fin.snoc xs a)) (LRV.tv k (Nat.lt_succ_self k)) = a := by
      simp only [LRV.tv, rho, Term.realize_var, Sum.elim_inr]
      exact Fin.snoc_last (α := fun _ => M) a xs
    rw [htv]
  have h3 : ((LRV.sortPred .vf (LRV.tv k (Nat.lt_succ_self k)) ⊓ φ).Realize
      (default : Empty → M) (Fin.snoc xs a)) ↔
      (iVF a ∧ φ.Realize (default : Empty → M) (Fin.snoc xs a)) := by
    rw [FirstOrder.Language.BoundedFormula.realize_inf, h2]
  exact h3

/-- **`RV = rv(VF^×) ∪ {0}` in every model of `ACVF`**: read off the axiom `Axioms.rvSurj`, which
says that every `RV`-element other than `rv(0)` is `rv(x)`. -/
theorem RVeqRvVF_of_model : RVeqRvVF M := by
  intro x hxRV
  by_cases hx0 : x = iRVZero
  · exact Or.inr hx0
  · left
    have hmem : Axioms.rvSurj ∈ Axioms.ACVF := by
      simp [Axioms.ACVF, Axioms.ACVFpaper, Axioms.rvAxioms, Axioms.ofList]
    have hreal : M ⊨ Axioms.rvSurj := Theory.realize_sentence_of_mem (T := Axioms.ACVF) hmem
    have hbody := (model_allSorted_iff ![SortTag.rv] _).mp hreal ![x]
      (fun i => by
        have hi : ![SortTag.rv] i = SortTag.rv := by fin_cases i; rfl
        rw [hi, real_sortPred_rv, ev_tv]
        fin_cases i
        exact hxRV)
    rw [FirstOrder.Language.BoundedFormula.realize_imp,
      FirstOrder.Language.BoundedFormula.realize_not, real_eq, ev_rvZero] at hbody
    have hx0' : Term.realize (rho ![x]) ((&0 : LRV.Tm 1)) ≠ iRVZero := by
      have hx : Term.realize (rho ![x]) ((&0 : LRV.Tm 1)) = x := by simp [rho]
      rwa [hx]
    have hex := hbody hx0'
    rw [real_exSorted_vf] at hex
    obtain ⟨a, haVF, ha⟩ := hex
    refine ⟨a, haVF, ?_⟩
    rw [real_eq, ev_rvMap] at ha
    have h1 : Term.realize (rho (Fin.snoc ![x] a)) ((&1 : LRV.Tm 2)) = a := by
      simp only [rho, Term.realize_var, Sum.elim_inr]
      exact Fin.snoc_last (α := fun _ => M) a ![x]
    have h0 : Term.realize (rho (Fin.snoc ![x] a)) ((&0 : LRV.Tm 2)) = x := by
      simp [rho]
    rw [h1, h0] at ha
    exact ha

end Realize

end Assembly

/-- **Saturation**, recorded in the only form the argument uses: for every model `M` of `ACVF`,
every substructure `S ⊆ M`, every monomorphism `f : S → N` and every `m ∈ M`, the complete type
of `m` over `S` is realised in `N`.  This is a consequence of `N` being `‖M‖⁺`-saturated
(compactness: the type has `|S| + ℵ₀ ≤ ‖M‖` parameters).  Mathlib has no notion of saturation,
so it is left as an explicit hypothesis of the theorems that need it. -/
def Assembly.Saturated (N : Type w) [LRV.Structure N] : Prop :=
  ∀ (M : Type w) [LRV.Structure M] [M ⊨ Axioms.ACVF] (S : LRV.Substructure M)
    (f : S ↪[LRV] N) (m : M),
    ∃ b : N, ∀ (φ : LRV.Formula (S ⊕ Unit)),
      φ.Realize (Sum.elim (fun s => (s : M)) (fun _ => m)) →
      φ.Realize (Sum.elim (fun s => f s) (fun _ => b))

namespace Assembly

open Axioms

section

variable {M : Type*} [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF]

/-! ### The paper's ingredients, as explicit hypotheses -/

/-- **Lemma 3.3** (unnamed in the paper), together with the henselization step at the start of
the proof of Proposition 3.9: from any monomorphism of a substructure of `M` into `N` one can
pass (using saturation) to one whose domain satisfies `K(S) = K(M)` and `Γ(S)` divisible. -/
def PrepStep (hSat : Saturated N) : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ Standing T

/-- **Lemmas 3.4-3.8** (`lift:all:root`, `lift:divisible:hull`, `lift:transcendental`,
`e:transc`, `lift:value:full`), in the form in which the proof of Proposition 3.9 uses them: one
element of the `VF` sort can be added to the domain, keeping `K(S) = K(M)` and `Γ(S)` divisible
(Lemma 3.5 keeps the first too, by the proof of `lift:divisible:hull`).  The paper proves this
under the extra case hypotheses of the lemmas and then exhausts `K(M)`; here the case analysis
and the exhaustion are separated, `exists_vf_all` below supplying the exhaustion. -/
def OneStepVF (hSat : Saturated N) : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Standing S → ∀ m : M, iVF m →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Standing T

/-- **Remark 3.1** (`L:v:and:L:RV`) together with Weispfenning's QE theorem for `L_v`
(Theorem `weis:qe`, an explicit hypothesis of this development, never an axiom): a monomorphism
whose domain is `VF`-generated extends to all of `M` when the target is saturated.

**The `Saturated N` parameter is not optional.**  Without it the statement is false: `⊥` is
`VF`-generated (it contains the constants, and `rv 1` is `rv` of the constant `1`), so the
saturation-free form asserts `∃ g : M ↪[LRV] N` for *every* pair of models of `ACVF`, in particular
an injection from an uncountable model into a countable one.  The paper's step is exactly the
saturated one — `qe.tex:552`: *"If `L` is sufficiently saturated then, by Theorem 2.7, `f'` may be
extended to an `L_v`-monomorphism `f : K → L`"* — and `prop39` already has `hSat` in scope when it
uses this, so demanding it costs nothing. -/
def VFGenCase (hSat : Saturated N) : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), IsVFGen S →
    ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x

/-! ### `K(S) = K(M)` and divisibility of `Γ(S)` are preserved by unions of chains -/

theorem KEqTop_chainSup {c : Set (M ≃ₚ[LRV] N)} (hne : c.Nonempty)
    (hch : IsChain (· ≤ ·) c) (h : ∀ z ∈ c, KEqTop z.dom) :
    KEqTop (chainSup c hne hch).dom :=
  fun x hx => PartialEquiv.dom_le_dom (le_chainSup hne hch hne.choose_spec)
    (h _ hne.choose_spec x hx)

theorem GammaDivisible_chainSup {c : Set (M ≃ₚ[LRV] N)} (hne : c.Nonempty)
    (hch : IsChain (· ≤ ·) c) (h : ∀ z ∈ c, GammaDivisible z.dom) :
    GammaDivisible (chainSup c hne hch).dom := by
  letI : Nonempty ↥c := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  letI : IsDirectedOrder ↥c := chain_isDirected c hch
  intro t ht hrv h0 n hn
  have hsup : (chainSup c hne hch).dom
      = ⨆ z : ↥c, (z.1 : M ≃ₚ[LRV] N).dom :=
    DirectLimit.dom_partialEquivLimit _
  have hdir : Directed (· ≤ ·) (fun z : ↥c => (z.1 : M ≃ₚ[LRV] N).dom) :=
    Monotone.directed_le (fun _ _ hab => PartialEquiv.dom_le_dom hab)
  have ht' : t ∈ ⨆ z : ↥c, (z.1 : M ≃ₚ[LRV] N).dom := by rw [← hsup]; exact ht
  rw [Substructure.mem_iSup_of_directed hdir] at ht'
  obtain ⟨z, hz⟩ := ht'
  obtain ⟨u, cc, hu, hru, hu0, hc, hcu, heq⟩ := h z.1 z.2 t hz hrv h0 n hn
  have hzle : (z.1 : M ≃ₚ[LRV] N) ≤ chainSup c hne hch := le_chainSup hne hch z.2
  exact ⟨u, cc, PartialEquiv.dom_le_dom hzle hu, hru, hu0,
    PartialEquiv.dom_le_dom hzle hc, hcu, heq⟩

theorem Standing_chainSup {c : Set (M ≃ₚ[LRV] N)} (hne : c.Nonempty)
    (hch : IsChain (· ≤ ·) c) (h : ∀ z ∈ c, Standing z.dom) :
    Standing (chainSup c hne hch).dom :=
  ⟨KEqTop_chainSup hne hch fun z hz => (h z hz).1,
   GammaDivisible_chainSup hne hch fun z hz => (h z hz).2⟩

/-! ### The exhaustion step -/

/-- Lemmas 3.4-3.8 in partial-isomorphism form: they are about monomorphisms of substructures,
which is the same data as a partial isomorphism (its codomain is the range). -/
theorem oneStepVF_pe (hSat : Saturated N) (h : OneStepVF (M := M) (N := N) hSat) :
    ∀ (G : M ≃ₚ[LRV] N), Standing G.dom → ∀ m : M, iVF m →
      ∃ G' : M ≃ₚ[LRV] N, G ≤ G' ∧ Standing G'.dom ∧ m ∈ G'.dom := by
  intro G hStandG m hm
  obtain ⟨T, g, hGT, hagree, hmT, hStandT⟩ := h G.dom (PartialEquiv.toEmbedding G) hStandG m hm
  refine ⟨embPE g, ?_, hStandT, hmT⟩
  rw [PartialEquiv.le_iff]
  refine ⟨hGT, ?_, ?_⟩
  · rintro y hy
    refine ⟨⟨((G.toEquiv.symm ⟨y, hy⟩ : G.dom) : M), hGT (G.toEquiv.symm ⟨y, hy⟩).2⟩, ?_⟩
    show g ⟨((G.toEquiv.symm ⟨y, hy⟩ : G.dom) : M), hGT (G.toEquiv.symm ⟨y, hy⟩).2⟩ = y
    rw [hagree]
    simp
  · intro x
    apply Subtype.ext
    show ((G.toEquiv x : G.cod) : N) = (g ⟨(x : M), hGT x.2⟩ : N)
    rw [hagree]
    rfl

/-- **The paper's exhaustion** ("iterating these procedures we may exhaust all elements in
`K(M)`"): from Lemma 3.3 and Lemmas 3.4-3.8, every monomorphism of a substructure of `M` into
`N` extends to one whose domain contains every element of the `VF` sort of `M`. -/
theorem exists_vf_all (hSat : Saturated N) (hPrep : PrepStep (M := M) (N := N) hSat)
    (hOne : OneStepVF (M := M) (N := N) hSat) (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ (∀ y : M, iVF y → y ∈ T) := by
  obtain ⟨T₀, f₀, hST₀, hagree₀, hStand₀⟩ := hPrep S f
  obtain ⟨G, hG₀G, hStand, hall⟩ :=
    exists_exhaust (L := LRV) (M := M) (N := N) (fun G => Standing G.dom) (fun m => iVF m)
      (fun c hne hch hP => Standing_chainSup hne hch hP)
      (oneStepVF_pe hSat hOne) (embPE f₀) hStand₀
  refine ⟨G.dom, PartialEquiv.toEmbedding G, hST₀.trans (PartialEquiv.dom_le_dom hG₀G), ?_, hall⟩
  intro x
  have h1 : (PartialEquiv.toEmbedding G
        ⟨(x : M), PartialEquiv.dom_le_dom hG₀G (hST₀ x.2)⟩ : N)
      = ((G.toEquiv ⟨(x : M), PartialEquiv.dom_le_dom hG₀G (hST₀ x.2)⟩ : G.cod) : N) := rfl
  rw [h1, agree_of_le f₀ hG₀G ⟨(x : M), hST₀ x.2⟩ (PartialEquiv.dom_le_dom hG₀G (hST₀ x.2))]
  exact hagree₀ x

/-- A substructure containing all `VF` elements of `M` is `VF`-generated, in a model of `ACVF`. -/
theorem isVFGen_of_vf_all (hRv : RVeqRvVF M) {T : LRV.Substructure M}
    (hT : ∀ y : M, iVF y → y ∈ T) : IsVFGen T := by
  intro x hxS hxRV
  rcases hRv x hxRV with ⟨y, hyVF, hyx⟩ | hzero
  · exact Or.inl ⟨y, hT y hyVF, hyVF, hyx⟩
  · exact Or.inr hzero

/-- **Proposition 3.9** (`lrv:mono:lift`), proved from the paper's Lemmas 3.3-3.8 and
Remark 3.1. -/
theorem prop39 (hSat : Saturated N) (hRv : RVeqRvVF M)
    (hPrep : PrepStep (M := M) (N := N) hSat) (hOne : OneStepVF (M := M) (N := N) hSat)
    (hVFGen : VFGenCase (M := M) (N := N) hSat) (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x := by
  obtain ⟨T, g, hST, hagree, hall⟩ := exists_vf_all hSat hPrep hOne S f
  obtain ⟨g', hg'⟩ := hVFGen T g (isVFGen_of_vf_all hRv hall)
  exact ⟨g', fun x => by rw [hg' ⟨(x : M), hST x.2⟩, hagree x]⟩

end

/-! ### Theorem 3.10 -/

/-- **Shoenfield's test** in the frozen encoding, in the form used for Theorem 3.10: the
extension property of Proposition 3.9 implies quantifier elimination.  This is the hard
direction of Shoenfield's criterion; the easy direction (QE implies the extension property, the
step used in Remark 3.1) is the general back-and-forth machinery of Part B. -/
def ShoenfieldTest : Prop :=
  (∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF]
      (hSat : Saturated N) (S : LRV.Substructure M) (f : S ↪[LRV] N),
      ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x) →
    HasQE ACVF

/-- **The paper's Section 3.1 in one structure**: the four algebraic ingredients, uniformly in
the models.  (Weispfenning's QE theorem for `L_v` enters through `vfgen`, via Remark 3.1;
saturation enters each of them.) -/
structure AlgIngredients : Prop where
  /-- `RV = rv(VF^×) ∪ {0}`: this is the content of the axiom `Axioms.rvSurj` (the paper's
  surjectivity of `rv`), so it is a *theorem* (`RVeqRvVF_of_model`).  It is kept as a field so
  that `theorem_2_3_of_hypotheses` keeps the shape it had; `theorem_2_3_of_three` discharges
  it. -/
  rv : ∀ (M : Type) [LRV.Structure M], M ⊨ ACVF → RVeqRvVF M
  /-- Lemma 3.3 + henselization -/
  prep : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF]
    (hSat : Saturated N), PrepStep (M := M) (N := N) hSat
  /-- Lemmas 3.4-3.8 -/
  one : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF]
    (hSat : Saturated N), OneStepVF (M := M) (N := N) hSat
  /-- Remark 3.1 + Weispfenning's QE theorem for `L_v` -/
  vfgen : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF]
    (hSat : Saturated N), VFGenCase (M := M) (N := N) hSat

/-- **Theorem 3.10 of arXiv:1006.1393 = Theorem 2.3 of arXiv:1006.2467**, modulo the four
hypotheses listed in `AlgIngredients` and the hard direction of Shoenfield's test. -/
theorem theorem_2_3_of_hypotheses (hShoen : ShoenfieldTest) (hAlg : AlgIngredients) :
    HasQE ACVF := by
  apply hShoen
  intro M N _ _ hM hN hSat S f
  exact prop39 hSat (hAlg.rv M hM) (hAlg.prep M N hSat) (hAlg.one M N hSat) (hAlg.vfgen M N hSat) S f

/-- **Theorem 3.10 with the `RV = rv(VF^×) ∪ {0}` hypothesis discharged.**  Since the axiom
`Axioms.rvSurj` is the paper's surjectivity of `rv` (every `RV`-element other than `rv(0)` is
`rv(x)`), the first ingredient of `AlgIngredients` is a theorem (`RVeqRvVF_of_model`), and only
the three remaining ingredients are needed.  (Before the identification of `0` with `∞` the axiom
was guarded by `Kˣ` and this hypothesis could not be discharged.) -/
theorem theorem_2_3_of_three (hShoen : ShoenfieldTest)
    (hPrep : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF]
      (hSat : Saturated N), PrepStep (M := M) (N := N) hSat)
    (hOne : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF]
      (hSat : Saturated N), OneStepVF (M := M) (N := N) hSat)
    (hVFGen : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF]
      (hSat : Saturated N), VFGenCase (M := M) (N := N) hSat) :
    HasQE ACVF :=
  theorem_2_3_of_hypotheses hShoen
    { rv := fun M _ _ => RVeqRvVF_of_model (M := M)
      prep := hPrep
      one := hOne
      vfgen := hVFGen }

end Assembly


end Milestone0
end SpecialTransformations

#print axioms SpecialTransformations.Milestone0.Assembly.RVeqRvVF_of_model
#print axioms SpecialTransformations.Milestone0.Assembly.prop39
#print axioms SpecialTransformations.Milestone0.Assembly.theorem_2_3_of_hypotheses
#print axioms SpecialTransformations.Milestone0.Assembly.theorem_2_3_of_three
