/-
The reduction of Yin's Theorem 2.3 (quantifier elimination for `ACVF` in the Basarab-Kuhlmann
language `L_RV`) to Weispfenning's quantifier elimination theorem for the two-sorted language
`L_v` of valued fields.

Contents:
* Parts 0-3 and 6 (frozen): the tagged one-sorted encoding of `L_RV` — `LRV`, its axioms, the
  theory `ACVF`, the statement `HasQE` of quantifier elimination.  Copied verbatim from
  `Milestone0/Encoding.lean` (commit d608de6, sha256 78607b94…), with the two `sorry`ed targets
  (`theorem_2_3_quantifier_elimination`, `theorem_2_8_c_minimal`) and Parts 4, 5, 7 removed.
* Part 7 (`namespace LvTwo`): the two-sorted language `L_v` of valued fields, its theory `ACVF`
  (`LvTwo.Axioms.ACVF`), quantifier elimination in it (`LvTwo.HasQE`), and Weispfenning's theorem
  as the explicit `Prop` `LvTwo.Weispfenning`.
* Part 8 (`namespace Reduction`): the reduction itself, `Reduction.theorem_2_3_reduction`, with its
  hypotheses listed one by one, together with the proved language-level Remark 3.1
  (`Language.Embedding.ofIsExpansionOn`, `lvEmbeddingOfFull`), the definition of `VF`-generated
  substructures (`VFGenerated`), Shoenfield's hypothesis (`EmbProperty`, `EmbPropertyVFGen`) and
  Shoenfield's test (`ShoenfieldTest`).

Converted to the project's ruling that the paper's `0` and `∞` are ONE element (the element
`rv(0)`, which is the residue field's zero and the absorbing element of `RV`).  The five changes
of the ruling, as they apply to this file:
1. the constructor `Fn.rvInfty` is deleted (`Fn.rvZero` remains, and its docstring states that
   it is the residue field's zero, `rv(0)`, and the absorbing element);
2. `LRV.tRVInfty := LRV.tRVZero` and `LRV.iRVInfty := LRV.iRVZero` are definitions;
3. `Axioms.rvSurj` is the paper's surjectivity, `∀ t ≠ rv(0), ∃ x, rv x = t` (it used to be
   guarded by `Kˣ` and to cover only the class of `1`);
4. the axioms that name the top through `tRVInfty` (`sdRVInfty`, `rvMulInfty`, `leTop`,
   `leInftyEq`, `rvZeroEq`, `rvEqInfty`) are unchanged textually: `tRVInfty` is now `tRVZero`,
   so they are the `rvZero`-versions; no `zero_ne_infty` occurs in this file;
5. the file's algebra layer keeps the paper's `RV` of `SpecialTransformations/Basic.lean`; the
   `RV0` alias is now the two-layer `RV` (it had a redundant third layer; no code uses it).
No theorem statement changed except `Axioms.rvSurj` (item 3, plus the `RV0` alias); comments and
docstrings were brought in line with `Milestone0/Encoding.lean`.

Self-contained: its only import is `Mathlib`.  Check with `lean Reduction.lean` from the project
root.  No `sorry`, no `admit`, no new `axiom`.
-/
import Mathlib

namespace SpecialTransformations
namespace Milestone0

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

namespace LvTwo

/-! ## 1. The sorts and symbols of `L_v` -/

/-- The sorts of `L_v`, as tags on the single carrier. -/
inductive SortTag where
  /-- the valued-field sort -/
  | vf
  /-- the value-group sort `Γ ∪ {∞}` -/
  | gamma

/-- Function symbols of `L_v`, tagged by arity. -/
inductive Fn : ℕ → Type where
  /-- `0` of the field sort -/
  | vfZero : Fn 0
  /-- `1` of the field sort -/
  | vfOne : Fn 0
  /-- `+` of the field sort -/
  | vfAdd : Fn 2
  /-- `-` of the field sort -/
  | vfNeg : Fn 1
  /-- `×` of the field sort -/
  | vfMul : Fn 2
  /-- `0` of the value group -/
  | gZero : Fn 0
  /-- `1` of the value group -/
  | gOne : Fn 0
  /-- the top element `∞` of `Γ ∪ {∞}` -/
  | gTop : Fn 0
  /-- `+` of the value group -/
  | gAdd : Fn 2
  /-- `-` of the value group -/
  | gNeg : Fn 1
  /-- the valuation `vv : VF → Γ ∪ {∞}` -/
  | vv : Fn 1

/-- Relation symbols of `L_v`.  The first two are the sort predicates of the encoding; the
third is the order of the value group. -/
inductive Rel : ℕ → Type where
  /-- encoding: the `VF` sort -/
  | memVF : Rel 1
  /-- encoding: the `Γ` sort -/
  | memGamma : Rel 1
  /-- the order `≤` of the value group -/
  | gLe : Rel 2

/-- **The two-sorted language `L_v` of valued fields**, in the tagged one-sorted encoding. -/
abbrev Lv : Language := ⟨Fn, Rel⟩

namespace Lv

/-! ## 2. Terms and formulas of `L_v` -/

/-- Terms of `L_v` whose free variables are indexed by `Fin n`. -/
abbrev Tm (n : ℕ) : Type := Lv.Term (Empty ⊕ Fin n)

/-- Bounded formulas of `L_v` with `n` variables in scope and no free parameters. -/
abbrev Bf (n : ℕ) : Type := Lv.BoundedFormula Empty n

variable {n : ℕ}

/-! ### 2.1 Term constructors -/

/-- `0` of the field sort -/
def tVFZero : Tm n := Term.func Fn.vfZero fun i => i.elim0
/-- `1` of the field sort -/
def tVFOne : Tm n := Term.func Fn.vfOne fun i => i.elim0
/-- `+` of the field sort -/
def tVFAdd (t u : Tm n) : Tm n := Term.func Fn.vfAdd ![t, u]
/-- `-` of the field sort -/
def tVFNeg (t : Tm n) : Tm n := Term.func Fn.vfNeg ![t]
/-- `×` of the field sort -/
def tVFMul (t u : Tm n) : Tm n := Term.func Fn.vfMul ![t, u]
/-- `0` of the value group -/
def tGZero : Tm n := Term.func Fn.gZero fun i => i.elim0
/-- `1` of the value group -/
def tGOne : Tm n := Term.func Fn.gOne fun i => i.elim0
/-- the top element `∞` -/
def tGTop : Tm n := Term.func Fn.gTop fun i => i.elim0
/-- `+` of the value group -/
def tGAdd (t u : Tm n) : Tm n := Term.func Fn.gAdd ![t, u]
/-- `-` of the value group -/
def tGNeg (t : Tm n) : Tm n := Term.func Fn.gNeg ![t]
/-- the valuation -/
def tVv (t : Tm n) : Tm n := Term.func Fn.vv ![t]

/-- the bound variable of index `i < n` -/
def tv (i : ℕ) (h : i < n) : Tm n := Term.var (Sum.inr ⟨i, h⟩)

/-- the numeral `k · 1` of the field sort -/
def tVFNumeral : ℕ → Tm n
  | 0 => tVFZero
  | k + 1 => tVFAdd (tVFNumeral k) tVFOne

/-- `t ^ k`, in the field sort -/
def tVFPow (t : Tm n) : ℕ → Tm n
  | 0 => tVFOne
  | k + 1 => tVFMul (tVFPow t k) t

/-- `k · t` in the value group -/
def tGNSmul (t : Tm n) : ℕ → Tm n
  | 0 => tGZero
  | k + 1 => tGAdd (tGNSmul t k) t

/-! ### 2.2 Formula constructors -/

/-- `t` lies in the field sort -/
def pVF (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memVF t
/-- `t` lies in the value-group sort -/
def pGamma (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memGamma t
/-- the order of the value group -/
def pGLe (t u : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₂ Rel.gLe t u
/-- `t = u` -/
def pEq (t u : Tm n) : Bf n := t =' u
/-- `t ≠ ⊤`, i.e. `t` is an element of the value group proper -/
def pNeTop (t : Tm n) : Bf n := ∼(pEq t tGTop)

/-! ### 2.3 Guarded quantifiers -/

/-- the sort predicate of the sort `s` -/
def sortPred (s : SortTag) (t : Tm n) : Bf n :=
  match s with
  | .vf => pVF t
  | .gamma => pGamma t

/-- `⋀ i, x_i ∈ s_i` -/
def sortedHyps {k : ℕ} (ss : Fin k → SortTag) : Bf k :=
  (List.finRange k).foldr (fun i acc => sortPred (ss i) (tv i.val i.isLt) ⊓ acc) ⊤

/-- `∀ x̄, (⋀ i, x_i ∈ s_i) → φ` -/
def allSorted {k : ℕ} (ss : Fin k → SortTag) (φ : Bf k) : Lv.Sentence :=
  BoundedFormula.alls (sortedHyps ss ⟹ φ)

/-- `∃ x ∈ s, φ`, where `x` is the variable of index `k` -/
def exSorted {k : ℕ} (s : SortTag) (φ : Bf (k + 1)) : Bf k :=
  BoundedFormula.ex (sortPred s (tv k (Nat.lt_succ_self k)) ⊓ φ)

/-- `⋀ i, x_i ∈ Γ ∖ {⊤}`: the tuple lies in the value group proper (not at `∞`) -/
def gHyps {k : ℕ} : Bf k :=
  (List.finRange k).foldr (fun i acc => (pGamma (tv i.val i.isLt) ⊓ pNeTop (tv i.val i.isLt)) ⊓ acc)
    ⊤

/-- `∀ x̄ ∈ Γ ∖ {⊤}, φ` -/
def allG (k : ℕ) (φ : Bf k) : Lv.Sentence := BoundedFormula.alls (gHyps ⟹ φ)

/-- `∃ x ∈ Γ ∖ {⊤}, φ`, where `x` is the variable of index `k` -/
def exG {k : ℕ} (φ : Bf (k + 1)) : Bf k :=
  BoundedFormula.ex ((pGamma (tv k (Nat.lt_succ_self k)) ⊓ pNeTop (tv k (Nat.lt_succ_self k))) ⊓ φ)

/-- the universal closure of a formula in one variable -/
def allOne (φ : Bf 1) : Lv.Sentence := BoundedFormula.alls φ

/-- Horner form `x^k + a_{k-1} x^{k-1} + ⋯ + a_0` of the monic polynomial of degree `k`
whose coefficients are the variables `0, …, k-1` and whose variable is the variable `k`
(coefficients and variable in the field sort). -/
def hornerPoly {k : ℕ} : Tm (k + 1) :=
  match k with
  | 0 => tv 0 Nat.zero_lt_one
  | (m + 1) =>
    let x : Tm (m + 1 + 1) := tv (m + 1) (by omega)
    (List.finRange m).reverse.foldl
      (fun acc i => tVFAdd (tVFMul acc x) (tv i.val (by omega)))
      (tVFAdd x (tv m (by omega)))

end Lv

namespace Axioms

open Lv

/-- The sentences of a finite list, as a theory. -/
def ofList (l : List Lv.Sentence) : Lv.Theory := {s | s ∈ l}

/-! ## 3. The axioms of `ACVF` in `L_v` -/

/-! ### 3.1 The sort discipline of the encoding -/

/-- the carrier is covered by the two sorts -/
def sdCover : Lv.Sentence := allOne (pVF &0 ⊔ pGamma &0)
/-- the two sorts are disjoint -/
def sdDisjoint : Lv.Sentence := allOne (∼(pVF &0 ⊓ pGamma &0))
/-- `0` of the field sort lies in the field sort -/
def sdVFZero : Lv.Sentence := pVF tVFZero
/-- `1` of the field sort lies in the field sort -/
def sdVFOne : Lv.Sentence := pVF tVFOne
/-- the field sort is closed under `+` -/
def sdVFAdd : Lv.Sentence := allSorted ![.vf, .vf] (pVF (tVFAdd &0 &1))
/-- the field sort is closed under `-` -/
def sdVFNeg : Lv.Sentence := allSorted ![.vf] (pVF (tVFNeg &0))
/-- the field sort is closed under `×` -/
def sdVFMul : Lv.Sentence := allSorted ![.vf, .vf] (pVF (tVFMul &0 &1))
/-- `0` of the value group lies in the value-group sort -/
def sdGZero : Lv.Sentence := pGamma tGZero
/-- `1` and `⊤` of the value group lie in the value-group sort -/
def sdGTop : Lv.Sentence := pGamma tGTop
/-- the value-group sort is closed under `+` -/
def sdGAdd : Lv.Sentence := allSorted ![.gamma, .gamma] (pGamma (tGAdd &0 &1))
/-- the value-group sort is closed under `-` -/
def sdGNeg : Lv.Sentence := allSorted ![.gamma] (pGamma (tGNeg &0))
/-- the valuation maps the field sort into the value-group sort -/
def sdVv : Lv.Sentence := allSorted ![.vf] (pGamma (tVv &0))

/-- the sort discipline of the encoding -/
def sortAxioms : Lv.Theory :=
  ofList [sdCover, sdDisjoint, sdVFZero, sdVFOne, sdVFAdd, sdVFNeg, sdVFMul, sdGZero, sdGTop,
    sdGAdd, sdGNeg, sdVv]

/-! ### 3.2 The field sort is an algebraically closed field -/

/-- the field axioms for the field sort -/
def fieldAxioms : List Lv.Sentence :=
  [ /- associativity of `+` -/
    allSorted ![.vf, .vf, .vf] (pEq (tVFAdd (tVFAdd &0 &1) &2) (tVFAdd &0 (tVFAdd &1 &2))),
    /- commutativity of `+` -/
    allSorted ![.vf, .vf] (pEq (tVFAdd &0 &1) (tVFAdd &1 &0)),
    /- `0` is neutral for `+` -/
    allSorted ![.vf] (pEq (tVFAdd &0 tVFZero) &0),
    /- additive inverses -/
    allSorted ![.vf] (pEq (tVFAdd &0 (tVFNeg &0)) tVFZero),
    /- associativity of `×` -/
    allSorted ![.vf, .vf, .vf] (pEq (tVFMul (tVFMul &0 &1) &2) (tVFMul &0 (tVFMul &1 &2))),
    /- commutativity of `×` -/
    allSorted ![.vf, .vf] (pEq (tVFMul &0 &1) (tVFMul &1 &0)),
    /- `1` is neutral for `×` -/
    allSorted ![.vf] (pEq (tVFMul &0 tVFOne) &0),
    /- distributivity -/
    allSorted ![.vf, .vf, .vf]
      (pEq (tVFMul &0 (tVFAdd &1 &2)) (tVFAdd (tVFMul &0 &1) (tVFMul &0 &2))),
    /- `0 ≠ 1` -/
    ∼(pEq tVFZero tVFOne),
    /- every nonzero element is invertible: the language has no inverse symbol -/
    allSorted ![.vf] (pEq &0 tVFZero ⊔ exSorted .vf (pEq (tVFMul &0 &1) tVFOne)) ]

/-- the algebraic-closedness scheme for the field sort:
`∀ a₀ … a_{k-1} ∃ x, x^k + a_{k-1} x^{k-1} + ⋯ + a₀ = 0` -/
def acfScheme (k : ℕ) : Lv.Sentence :=
  allSorted (fun _ : Fin k => .vf) (exSorted .vf (pEq hornerPoly tVFZero))

/-- the field sort is an algebraically closed field -/
def vfACF : Lv.Theory :=
  ofList fieldAxioms ∪ {s | ∃ k, 1 ≤ k ∧ s = acfScheme k}

/-! ### 3.3 The value-group sort is a divisible ordered abelian group with a top element -/

/-- `⊤ = ∞` is absorbing for `+`: `⊤ + t = ⊤` -/
def gAddTop : Lv.Sentence := allSorted ![.gamma] (pEq (tGAdd tGTop &0) tGTop)
/-- `+` is associative on the value group -/
def gAddAssoc : Lv.Sentence :=
  allG 3 (pEq (tGAdd (tGAdd &0 &1) &2) (tGAdd &0 (tGAdd &1 &2)))
/-- `+` is commutative -/
def gAddComm : Lv.Sentence := allG 2 (pEq (tGAdd &0 &1) (tGAdd &1 &0))
/-- `0` is neutral for `+` -/
def gAddZero : Lv.Sentence := allG 1 (pEq (tGAdd &0 tGZero) &0)
/-- additive inverses in the value group -/
def gAddNeg : Lv.Sentence := allG 1 (pEq (tGAdd &0 (tGNeg &0)) tGZero)
/-- `≤` is reflexive on the value group -/
def gLeRefl : Lv.Sentence := allG 1 (pGLe &0 &0)
/-- `≤` is transitive -/
def gLeTrans : Lv.Sentence := allG 3 (pGLe &0 &1 ⟹ (pGLe &1 &2 ⟹ pGLe &0 &2))
/-- `≤` is total -/
def gLeTotal : Lv.Sentence := allG 2 (pGLe &0 &1 ⊔ pGLe &1 &0)
/-- `≤` is antisymmetric -/
def gLeAntisym : Lv.Sentence := allG 2 (pGLe &0 &1 ⟹ (pGLe &1 &0 ⟹ pEq &0 &1))
/-- `≤` is translation invariant -/
def gLeAdd : Lv.Sentence := allG 3 (pGLe &0 &1 ⟹ pGLe (tGAdd &0 &2) (tGAdd &1 &2))
/-- `⊤` is the top element -/
def gLeTop : Lv.Sentence := allG 1 (pGLe &0 tGTop)
/-- divisibility scheme of the value group: `∀ x ∃ y, k·y = x` -/
def gDivisible (k : ℕ) : Lv.Sentence := allG 1 (exG (pEq (tGNSmul (tv 1 (Nat.lt_succ_self 1)) k) (&0)))

/-- the value-group sort is a divisible ordered abelian group with top element `⊤` -/
def gammaAxioms : Lv.Theory :=
  ofList [gAddTop, gAddAssoc, gAddComm, gAddZero, gAddNeg, gLeRefl, gLeTrans, gLeTotal,
      gLeAntisym, gLeAdd, gLeTop] ∪
    {s | ∃ k, 1 ≤ k ∧ s = gDivisible k}

/-! ### 3.4 `vv` is a valuation -/

/-- `vv(0) = ⊤` -/
def vvZero : Lv.Sentence := pEq (tVv tVFZero) tGTop
/-- `vv(x) = ⊤` forces `x = 0` -/
def vvTop : Lv.Sentence := allSorted ![.vf] (pEq (tVv &0) tGTop ⟹ pEq &0 tVFZero)
/-- `vv(1) = 0` -/
def vvOne : Lv.Sentence := pEq (tVv tVFOne) tGZero
/-- `vv` is multiplicative: `vv(x·y) = vv(x) + vv(y)` -/
def vvMul : Lv.Sentence := allSorted ![.vf, .vf] (pEq (tVv (tVFMul &0 &1)) (tGAdd (tVv &0) (tVv &1)))
/-- `vv` is surjective onto the value group: every `γ ≠ ⊤` is `vv(x)` for some `x ∈ VF` -/
def vvSurj : Lv.Sentence := allG 1 (exSorted .vf (pEq (tVv (tv 1 (Nat.lt_succ_self 1))) (&0)))
/-- the ultrametric inequality `vv(x+y) ≥ min(vv x, vv y)` -/
def vvUltrametric : Lv.Sentence :=
  allSorted ![.vf, .vf] (pGLe (tVv &0) (tVv (tVFAdd &0 &1)) ⊔ pGLe (tVv &1) (tVv (tVFAdd &0 &1)))

/-- `vv` is a nontrivial-valuation, i.e. a surjective map onto `Γ ∪ {∞}`: `vv(0) = ⊤`,
`vv(x) = ⊤ → x = 0`, `vv(1) = 0`, multiplicativity, surjectivity onto `Γ ∖ {⊤}` and the ultrametric inequality.  This is the
paper's Definition 2.2 item 6 (with `vv = vrv ∘ rv`): the value group is the value group *of*
the valuation, so `vv` is onto `Γ ∖ {⊤}`. -/
def valAxioms : Lv.Theory := ofList [vvZero, vvTop, vvOne, vvMul, vvSurj, vvUltrametric]

/-! ### 3.5 `ACVF` and `ACVF(0,0)` in `L_v` -/

/-- **The theory of algebraically closed valued fields in the two-sorted language `L_v`**:
the field sort is an algebraically closed field, the value-group sort is a divisible ordered
abelian group with top element `⊤`, and `vv` is a valuation. -/
def ACVF : Lv.Theory := sortAxioms ∪ vfACF ∪ gammaAxioms ∪ valAxioms

/-- characteristic zero of the field sort -/
def charZero (k : ℕ) : Lv.Sentence := ∼(pEq (tVFNumeral (k + 1)) tVFZero)

/-- the residue field has characteristic zero: for each prime `p`, `vv(p·1) = 0` -/
def residueCharZero (p : ℕ) : Lv.Sentence := pEq (tVv (tVFNumeral p)) tGZero

/-- **`ACVF(0,0)` in `L_v`**: `ACVF` with both characteristics zero -/
def ACVF00 : Lv.Theory :=
  ACVF ∪ {s | ∃ k, s = charZero k} ∪ {s | ∃ p, p.Prime ∧ s = residueCharZero p}

end Axioms

/-! ## 4. Quantifier elimination in `L_v`, as an explicit hypothesis

Weispfenning's theorem is *not* proved here: it enters every statement below as an explicit
`Prop` hypothesis `Weispfenning`.  The deliverable of this part of the swarm is the *reduction*
of Yin's Theorem 2.3 to it. -/

open Axioms

/-- A theory `T` of `L_v` **admits quantifier elimination**: every `L_v`-formula is
`T`-equivalent to a quantifier-free `L_v`-formula. -/
def HasQE (T : Lv.Theory) : Prop :=
  ∀ (α : Type) (φ : Lv.Formula α), ∃ ψ : Lv.Formula α,
    FirstOrder.Language.BoundedFormula.IsQF ψ ∧ T ⊨ᵇ (φ ⇔ ψ)

/-- **Weispfenning's theorem** (Yin, arXiv:1006.1393, Theorem 2.1 / `weis:qe`): the theory of
algebraically closed valued fields formulated in `L_v` admits quantifier elimination.  Stated,
never assumed: it is a hypothesis of every reduction theorem below. -/
def Weispfenning : Prop := HasQE ACVF

/-- `HasQE` is monotone in the theory: quantifier elimination for a theory persists to any
stronger theory.  (Weispfenning's theorem is therefore available for `ACVF(0,0)` too.) -/
theorem HasQE.mono {T T' : Lv.Theory} (h : HasQE T) (hsub : T ⊆ T') : HasQE T' := by
  intro α φ
  obtain ⟨ψ, hqf, hψ⟩ := h α φ
  exact ⟨ψ, hqf, FirstOrder.Language.Theory.models_of_models_theory
    (fun θ hθ => FirstOrder.Language.Theory.models_sentence_of_mem (hsub hθ)) hψ⟩

/-- Weispfenning's theorem for `ACVF(0,0)`. -/
theorem weispfenning_ACVF00 (h : Weispfenning) : HasQE ACVF00 :=
  h.mono (by intro s hs; simp only [LvTwo.Axioms.ACVF00, LvTwo.Axioms.ACVF, Set.mem_union] at hs ⊢; tauto)

end LvTwo

/-! ## Part 8. The reduction of Theorem 2.3 to Weispfenning's theorem

This part formalizes the *reduction* that Yin's argument (arXiv:1006.1393, Section 3) performs,
in the frozen tagged encoding of `L_RV` (`LRV`, `Axioms.ACVF`, `HasQE` above).

* `Lfull = L_v ⊕ L_RV` is the joint language.  `Language.Embedding.ofIsExpansionOn` proves, in
  general, that an `L'`-embedding is an `L`-embedding whenever `L'` expands `L` on both
  structures; applied to the two summands of `Lfull` this is the language-level content of
  Remark 3.1 ("`L_RV` may be viewed as an expansion of `L_v`", hence an `L_RV`-monomorphism "may
  also be treated as an `L_v`-monomorphism").
* `VFGenerated` is the paper's notion of a `VF`-generated substructure, `EmbProperty` is
  Shoenfield's hypothesis for a theory and `EmbPropertyVFGen` its restriction to `VF`-generated
  substructures.
* `theorem_2_3_reduction` composes the five steps of the paper's proof.  Each step is an explicit
  `Prop` hypothesis; nothing is postulated as an axiom.
-/

namespace Reduction

open FirstOrder FirstOrder.Language

/-! ### 8.1 Reducts of embeddings -/

/-- **An `L'`-embedding is an `L`-embedding when `L'` expands `L` on both structures.**  Applied
to `ϕ = LHom.sumInl : L_v →ᴸ L_v ⊕ L_RV` this is the assertion, used in Remark 3.1 of the paper,
that an `L_RV`-monomorphism "may also be treated as an `L_v`-monomorphism". -/
def Language.Embedding.ofIsExpansionOn {L L' : FirstOrder.Language} {M N : Type}
    [L.Structure M] [L.Structure N] [L'.Structure M] [L'.Structure N]
    (ϕ : L →ᴸ L') [ϕ.IsExpansionOn M] [ϕ.IsExpansionOn N] (f : M ↪[L'] N) : M ↪[L] N where
  toEmbedding := f.toEmbedding
  map_fun' := by
    intro n F x
    show (f : M → N) (Structure.funMap F x) = Structure.funMap F ((f : M → N) ∘ x)
    simpa only [LHom.map_onFunction] using f.map_fun (ϕ.onFunction F) x
  map_rel' := by
    intro n R x
    show Structure.RelMap R ((f : M → N) ∘ x) ↔ Structure.RelMap R x
    simpa only [LHom.map_onRelation] using f.map_rel (ϕ.onRelation R) x

/-! ### 8.2 The joint language `L_v ⊕ L_RV` -/

/-- the joint language `L_v ⊕ L_RV` -/
abbrev Lfull : FirstOrder.Language := LvTwo.Lv.sum LRV

/-- the `L_v`-structure of an `L_v ⊕ L_RV`-structure (the reduct) -/
@[instance_reducible]
def lvStruct (M : Type) [Lfull.Structure M] : LvTwo.Lv.Structure M :=
  (LHom.sumInl : LvTwo.Lv →ᴸ Lfull).reduct M

/-- the `L_RV`-structure of an `L_v ⊕ L_RV`-structure (the reduct) -/
@[instance_reducible]
def lrvStruct (M : Type) [Lfull.Structure M] : LRV.Structure M :=
  (LHom.sumInr : LRV →ᴸ Lfull).reduct M

section Joint

variable {M N : Type} [Lfull.Structure M] [Lfull.Structure N]

attribute [local instance] lvStruct lrvStruct

/-- **Remark 3.1, language level**: a monomorphism of `L_v ⊕ L_RV`-structures is an
`L_v`-monomorphism.  (No `VF`-generatedness is needed for this direction, so this is stronger
than what the paper states.) -/
def lvEmbeddingOfFull (f : M ↪[Lfull] N) : M ↪[LvTwo.Lv] N :=
  Language.Embedding.ofIsExpansionOn (LHom.sumInl : LvTwo.Lv →ᴸ Lfull) f

/-- **Remark 3.1, language level**: a monomorphism of `L_v ⊕ L_RV`-structures is an
`L_RV`-monomorphism. -/
def lrvEmbeddingOfFull (f : M ↪[Lfull] N) : M ↪[LRV] N :=
  Language.Embedding.ofIsExpansionOn (LHom.sumInr : LRV →ᴸ Lfull) f

end Joint

/-! ### 8.3 `VF`-generated substructures -/

/-- The paper's **`VF`-generated** substructures (Section 2 of arXiv:1006.1393): `S` is generated
by its `VF`-sort elements.  This is the paper's own definition, in terms of the substructure
closure. -/
def VFGenerated {M : Type} [LRV.Structure M] (S : LRV.Substructure M) : Prop :=
  S = Substructure.closure (L := LRV) {x : M | x ∈ S ∧ iVF x}

/-- **`VF`-generatedness in the form the paper uses**: `RV(S) = rv(VF(S))`, i.e. every `RV`-sort
element of `S` is `rv` of a `VF`-sort element of `S`, up to the residue zero.  Remark 3.1 of the
paper identifies this with the closure definition (`VFGenerated`); the two agree in models of
`ACVF`, but that equivalence is not proved here.  This is the form used in the chain below and in
the assembly file of the swarm's direction (viii). -/
def IsVFGen {M : Type} [LRV.Structure M] (S : LRV.Substructure M) : Prop :=
  ∀ x : M, x ∈ S → iRV x → (∃ y : M, y ∈ S ∧ iVF y ∧ iRv y = x) ∨ x = iRVZero

/-! ### 8.4 Shoenfield's hypothesis and Shoenfield's test -/

/-- A notion of saturation for structures.  `IsSat L M` is intended to be "`M` is `|M|⁺`-saturated
as an `L`-structure"; saturation itself is *not* formalized here (that is direction (B) of the
swarm), it enters only as this parameter, so that the reduction below is parametric in it. -/
def SatNotion : Type 1 := ∀ (L : FirstOrder.Language) (M : Type), L.Structure M → Prop

/-- **Shoenfield's hypothesis for `(L, T)`**: every monomorphism from a substructure of a model of
`T` into a saturated model of `T` extends to a monomorphism of the whole model. -/
def EmbProperty (IsSat : SatNotion) (L : FirstOrder.Language) (T : L.Theory) : Prop :=
  ∀ (M N : Type) [L.Structure M] [L.Structure N], M ⊨ T → N ⊨ T →
    IsSat L N (inferInstance : L.Structure N) →
    ∀ (S : L.Substructure M) (f : L.Embedding S N),
      ∃ F : L.Embedding M N, ∀ x : S, F (x : M) = f x

/-- **Shoenfield's hypothesis with the `VF`-generated restriction**: the same, but only for
`VF`-generated substructures `S`.  This is the hypothesis available from Remark 3.1 together with
Weispfenning's theorem; Lemmas 3.2–3.8 remove the restriction. -/
def EmbPropertyVFGen (IsSat : SatNotion) (T : LRV.Theory) : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N], M ⊨ T → N ⊨ T →
    IsSat LRV N (inferInstance : LRV.Structure N) →
    ∀ (S : LRV.Substructure M), IsVFGen S → ∀ (f : LRV.Embedding S N),
      ∃ F : LRV.Embedding M N, ∀ x : S, F (x : M) = f x

/-- **Shoenfield's test** for the tagged `L_RV` encoding, as an explicit hypothesis:
the extension property `EmbProperty` implies quantifier elimination. -/
def ShoenfieldTest (IsSat : SatNotion) (T : LRV.Theory) : Prop :=
  EmbProperty IsSat LRV T → HasQE T

/-- `HasQEOn L T`: every `L`-formula is `T`-equivalent to a quantifier-free one.  This is the same
statement as the frozen `HasQE` (at `L = LRV`) and as `LvTwo.HasQE` (at `L = L_v`). -/
def HasQEOn (L : FirstOrder.Language) (T : L.Theory) : Prop :=
  ∀ (α : Type) (φ : L.Formula α), ∃ ψ : L.Formula α,
    FirstOrder.Language.BoundedFormula.IsQF ψ ∧ T ⊨ᵇ (φ ⇔ ψ)

/-- the frozen `HasQE` is `HasQEOn LRV` -/
theorem hasQEOn_LRV {T : LRV.Theory} : HasQEOn LRV T ↔ HasQE T := Iff.rfl

/-- `LvTwo.HasQE` is `HasQEOn L_v` -/
theorem hasQEOn_Lv {T : LvTwo.Lv.Theory} : HasQEOn LvTwo.Lv T ↔ LvTwo.HasQE T := Iff.rfl

/-- **Shoenfield's test**, in both directions and uniformly in the language: for the notion of
saturation `IsSat`, every monomorphism from a substructure of a model of `T` into a saturated model
of `T` extends, if and only if `T` has quantifier elimination.  (This is the form in which the
criterion is usually quoted; it is strictly stronger than the one-directional `ShoenfieldTest`.) -/
def ShoenfieldCriterion (IsSat : SatNotion) : Prop :=
  ∀ (L : FirstOrder.Language) (T : L.Theory), EmbProperty IsSat L T ↔ HasQEOn L T

/-! ### 8.5 The reduction

The five hypotheses are, in the order of the paper:

1. `hWeis` — Weispfenning's theorem (`weis:qe`): `ACVF` in `L_v` admits QE.
2. `hQEtoEmb` — quantifier elimination gives Shoenfield's extension property for `L_v`: an
   `L_v`-monomorphism from a substructure of a model into a saturated model extends.  This is the
   implication "QE ⟹ monomorphisms into saturated models extend", i.e. the easy half of
   Shoenfield's test, applied to the `L_v`-theory `ACVF`.
3. `hRemark31` — Remark 3.1: since `L_RV` is an expansion of `L_v` (Lemma `lvEmbeddingOfFull`),
   Weispfenning's extension theorem for `L_v` yields the extension property for `L_RV`-monomorphisms
   out of `VF`-generated substructures.
4. `hProp39` — Lemmas 3.2–3.8 (root lifting, the divisible hull, transcendental extensions: the
   removal of the `VF`-generated hypothesis) plus Lemma `lift:any:sec`, i.e. Proposition 3.9:
   every `L_RV`-monomorphism from a substructure of a model into a saturated model extends.
5. `hShoenfield` — Shoenfield's test (Theorem 3.10): the extension property for `L_RV` implies
   quantifier elimination in `L_RV`.

The `VF`-generated hypothesis appears only in steps 3 and 4, exactly as in the paper. -/
theorem theorem_2_3_reduction
    (IsSat : SatNotion)
    (hWeis : LvTwo.HasQE LvTwo.Axioms.ACVF)
    (hQEtoEmb : LvTwo.HasQE LvTwo.Axioms.ACVF → EmbProperty IsSat LvTwo.Lv LvTwo.Axioms.ACVF)
    (hRemark31 : EmbProperty IsSat LvTwo.Lv LvTwo.Axioms.ACVF → EmbPropertyVFGen IsSat Axioms.ACVF)
    (hProp39 : EmbPropertyVFGen IsSat Axioms.ACVF → EmbProperty IsSat LRV Axioms.ACVF)
    (hShoenfield : ShoenfieldTest IsSat Axioms.ACVF) :
    HasQE Axioms.ACVF :=
  hShoenfield (hProp39 (hRemark31 (hQEtoEmb hWeis)))

/-- The reduction, with Weispfenning's theorem spelled out as `LvTwo.Weispfenning`. -/
theorem theorem_2_3_reduction_of_weispfenning
    (IsSat : SatNotion)
    (hWeis : LvTwo.Weispfenning)
    (hQEtoEmb : LvTwo.HasQE LvTwo.Axioms.ACVF → EmbProperty IsSat LvTwo.Lv LvTwo.Axioms.ACVF)
    (hRemark31 : EmbProperty IsSat LvTwo.Lv LvTwo.Axioms.ACVF → EmbPropertyVFGen IsSat Axioms.ACVF)
    (hProp39 : EmbPropertyVFGen IsSat Axioms.ACVF → EmbProperty IsSat LRV Axioms.ACVF)
    (hShoenfield : ShoenfieldTest IsSat Axioms.ACVF) :
    HasQE Axioms.ACVF :=
  theorem_2_3_reduction IsSat hWeis hQEtoEmb hRemark31 hProp39 hShoenfield

/-- The reduction with steps 1 and 2 combined: `hWeisEmb` says that Weispfenning's QE yields the
`L_v`-extension property.  This is the form in which Remark 3.1 uses Weispfenning's theorem. -/
theorem theorem_2_3_reduction'
    (IsSat : SatNotion)
    (hWeisEmb : LvTwo.HasQE LvTwo.Axioms.ACVF → EmbProperty IsSat LvTwo.Lv LvTwo.Axioms.ACVF)
    (hRemark31 : EmbProperty IsSat LvTwo.Lv LvTwo.Axioms.ACVF → EmbPropertyVFGen IsSat Axioms.ACVF)
    (hProp39 : EmbPropertyVFGen IsSat Axioms.ACVF → EmbProperty IsSat LRV Axioms.ACVF)
    (hShoenfield : ShoenfieldTest IsSat Axioms.ACVF)
    (hWeis : LvTwo.HasQE LvTwo.Axioms.ACVF) :
    HasQE Axioms.ACVF :=
  theorem_2_3_reduction IsSat hWeis hWeisEmb hRemark31 hProp39 hShoenfield

/-- **The reduction of Theorem 2.3 to Weispfenning's theorem**, with Shoenfield's test taken as a
single hypothesis (`ShoenfieldCriterion`, both directions) and only two further hypotheses: the two
steps of the paper that use the lifting lemmas. -/
theorem theorem_2_3_reduction_of_criterion
    (IsSat : SatNotion)
    (hShoen : ShoenfieldCriterion IsSat)
    (hRemark31 : EmbProperty IsSat LvTwo.Lv LvTwo.Axioms.ACVF → EmbPropertyVFGen IsSat Axioms.ACVF)
    (hProp39 : EmbPropertyVFGen IsSat Axioms.ACVF → EmbProperty IsSat LRV Axioms.ACVF)
    (hWeis : LvTwo.HasQE LvTwo.Axioms.ACVF) :
    HasQE Axioms.ACVF := by
  have h1 : EmbProperty IsSat LvTwo.Lv LvTwo.Axioms.ACVF :=
    ((hShoen LvTwo.Lv LvTwo.Axioms.ACVF).2) hWeis
  have h2 : EmbProperty IsSat LRV Axioms.ACVF := hProp39 (hRemark31 h1)
  exact ((hShoen LRV Axioms.ACVF).1) h2

/-- The same, starting from Weispfenning's theorem stated as `LvTwo.Weispfenning`. -/
theorem theorem_2_3_reduction_of_weispfenning' 
    (IsSat : SatNotion)
    (hShoen : ShoenfieldCriterion IsSat)
    (hRemark31 : EmbProperty IsSat LvTwo.Lv LvTwo.Axioms.ACVF → EmbPropertyVFGen IsSat Axioms.ACVF)
    (hProp39 : EmbPropertyVFGen IsSat Axioms.ACVF → EmbProperty IsSat LRV Axioms.ACVF)
    (hWeis : LvTwo.Weispfenning) :
    HasQE Axioms.ACVF :=
  theorem_2_3_reduction_of_criterion IsSat hShoen hRemark31 hProp39 hWeis

/-! ### 8.6 `ACVF(0,0)` -/

/-- Quantifier elimination is monotone in the theory: it descends from `ACVF` to the stronger
theory `ACVF(0,0)` of pure characteristic `0` (the frozen file's `Axioms.ACVF00`). -/
theorem hasQE_ACVF00 (h : HasQE Axioms.ACVF) : HasQE Axioms.ACVF00 := by
  intro α φ
  obtain ⟨ψ, hqf, hψ⟩ := h α φ
  exact ⟨ψ, hqf, FirstOrder.Language.Theory.models_of_models_theory
    (fun θ hθ => FirstOrder.Language.Theory.models_sentence_of_mem
      (by simp only [Axioms.ACVF00, Set.mem_union] at hθ ⊢; tauto)) hψ⟩

/-- **Theorem 2.3 of arXiv:1006.2467** (= Theorem 3.10 of arXiv:1006.1393), in the name of the
frozen target `Milestone0/Encoding.lean`'s `theorem_2_3_quantifier_elimination`, with the five
hypotheses of the reduction listed. -/
theorem theorem_2_3_quantifier_elimination
    (IsSat : SatNotion)
    (hWeis : LvTwo.HasQE LvTwo.Axioms.ACVF)
    (hQEtoEmb : LvTwo.HasQE LvTwo.Axioms.ACVF → EmbProperty IsSat LvTwo.Lv LvTwo.Axioms.ACVF)
    (hRemark31 : EmbProperty IsSat LvTwo.Lv LvTwo.Axioms.ACVF → EmbPropertyVFGen IsSat Axioms.ACVF)
    (hProp39 : EmbPropertyVFGen IsSat Axioms.ACVF → EmbProperty IsSat LRV Axioms.ACVF)
    (hShoenfield : ShoenfieldTest IsSat Axioms.ACVF) :
    HasQE Axioms.ACVF :=
  theorem_2_3_reduction IsSat hWeis hQEtoEmb hRemark31 hProp39 hShoenfield

end Reduction

#print axioms LvTwo.HasQE.mono
#print axioms LvTwo.weispfenning_ACVF00
#print axioms SpecialTransformations.Milestone0.Reduction.Language.Embedding.ofIsExpansionOn
#print axioms SpecialTransformations.Milestone0.Reduction.hasQEOn_LRV
#print axioms SpecialTransformations.Milestone0.Reduction.hasQEOn_Lv
#print axioms SpecialTransformations.Milestone0.Reduction.hasQE_ACVF00
#print axioms SpecialTransformations.Milestone0.Reduction.theorem_2_3_quantifier_elimination
#print axioms SpecialTransformations.Milestone0.Reduction.lvEmbeddingOfFull
#print axioms SpecialTransformations.Milestone0.Reduction.lrvEmbeddingOfFull
#print axioms SpecialTransformations.Milestone0.Reduction.theorem_2_3_reduction
#print axioms SpecialTransformations.Milestone0.Reduction.theorem_2_3_reduction_of_weispfenning
#print axioms SpecialTransformations.Milestone0.Reduction.theorem_2_3_reduction_of_criterion
#print axioms SpecialTransformations.Milestone0.Reduction.theorem_2_3_reduction_of_weispfenning'

end Milestone0
end SpecialTransformations
