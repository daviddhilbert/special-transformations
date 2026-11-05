/-
Milestone 0 for: Yimu Yin, "Special transformations in algebraically closed valued fields",
Annals of Pure and Applied Logic (2010), arXiv:1006.2467.

The paper's language `L_RV` (Definition 2.1), the theory `ACVF` (Definition 2.2), the
theory `ACVF_S(0,0)`, and the statements of quantifier elimination (Theorem 2.3) and
C-minimality (Theorem 2.8), encoded in Mathlib's one-sorted first-order model theory by
putting the sorts of `L_RV` on a single tagged carrier with unary sort predicates.

This file is self-contained: its only import is `Mathlib`.  Check it with

    lean Milestone0.lean

Part 6 records the QE target, proved with explicit authorized standard-reference
hypotheses in `QE/LocalQE/Theorem23.lean`. The sole remaining `sorry` in this file
is the separate C-minimality target; the QE proof does not use it.
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
* an `RV`-sort with the group language `{1, ×, (·)⁻¹}`, two constants `0` and `∞`, a unary
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
  /-- Multiplicative inverse on `RV`, totalized by `0⁻¹ = 0`.  Naming this operation
  makes the author's convention that generated substructures contain inverses explicit. -/
  | rvInv : Fn 1
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
/-- Multiplicative inverse on the `RV` sort, with `0⁻¹ = 0`. -/
def tRVInv (t : Tm n) : Tm n := Term.func Fn.rvInv ![t]
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

/-! ### Part 2b. The well-sorted fragment

The encoding is one-sorted, so `Tm n` and `Bf n` also contain *ill-sorted* terms (`rv (rv x)`,
the `VF` operations at an `RV` element, `kAdd` at a `VF` element, ...), and no axiom of `ACVF`
constrains their values.  The paper's `L_RV` is two-sorted and has no such terms.  This part
singles out the image of the paper's two-sorted language inside the encoding:

* `TmSort sα sn t` is the sort of the term `t`, if it has one (`none` is junk);
* `WellSorted sα sn φ` says that `φ` is a formula of the paper's two-sorted `L_RV`, with the
  free parameters `a : α` of sort `sα a` and the bound variables of sort `sn`, each quantifier
  being guarded by a sort hypothesis for the variable it binds.

`Milestone0.HasQE` is stated over this fragment, so that it is a statement about the paper's
two-sorted `L_RV` rather than about the encoding's junk values. -/

/-! #### The sort signature of the symbols -/

/-- The result sort of a function symbol of `L_RV`. -/
def Fn.resSort : {l : ℕ} → Fn l → SortTag
  | _, .vfZero => .vf
  | _, .vfOne => .vf
  | _, .vfAdd => .vf
  | _, .vfNeg => .vf
  | _, .vfMul => .vf
  | _, .rvOne => .rv
  | _, .rvZero => .rv
  | _, .rvMul => .rv
  | _, .rvInv => .rv
  | _, .kAdd => .rv
  | _, .kNeg => .rv
  | _, .rvMap => .rv

/-- The sort of the `i`-th argument of a function symbol of `L_RV`. -/
def Fn.argSort : {l : ℕ} → (f : Fn l) → Fin l → SortTag
  | _, .vfZero => Fin.elim0
  | _, .vfOne => Fin.elim0
  | _, .vfAdd => fun _ => .vf
  | _, .vfNeg => fun _ => .vf
  | _, .vfMul => fun _ => .vf
  | _, .rvOne => Fin.elim0
  | _, .rvZero => Fin.elim0
  | _, .rvMul => fun _ => .rv
  | _, .rvInv => fun _ => .rv
  | _, .kAdd => fun _ => .rv
  | _, .kNeg => fun _ => .rv
  | _, .rvMap => fun _ => .vf

/-- The sort of the `i`-th argument of a relation symbol of `L_RV`.  The two encoding predicates
`memVF`, `memRV` are dealt with like the paper's own predicates: `memVF` needs its argument in
`VF`, and `memRV`, `memUnits`, `rvLe` need their arguments in `RV`. -/
def Rel.argSort : {l : ℕ} → (R : Rel l) → Fin l → SortTag
  | _, .memVF => fun _ => .vf
  | _, .memRV => fun _ => .rv
  | _, .memUnits => fun _ => .rv
  | _, .rvLe => fun _ => .rv

/-! #### The sort of a term -/

/-- **The sort of a term**, if it has one.  `none` is exactly the encoding's ill-sorted terms:
`rv` applied to an `RV`-term, a `VF` operation at an `RV`-term, `kAdd` at a `VF`-term, and any
term containing one of those.  Parameters `a : α` carry the declared sort `sα a`, the bound
variable of index `i` carries `sn i`. -/
def TmSort {α : Type} (sα : α → SortTag) {n : ℕ} (sn : Fin n → SortTag) :
    LRV.Term (α ⊕ Fin n) → Option SortTag
  | Term.var (Sum.inl a) => some (sα a)
  | Term.var (Sum.inr i) => some (sn i)
  | Term.func f ts =>
    if (∀ i, TmSort sα sn (ts i) = some (Fn.argSort f i)) then some (Fn.resSort f) else none

/-- `t ∈ VF` with parameters `α` (`pVF` for `Bf n = LRV.BoundedFormula Empty n`). -/
def pVFG {α : Type} {n : ℕ} (t : LRV.Term (α ⊕ Fin n)) : LRV.BoundedFormula α n :=
  FirstOrder.Language.Relations.boundedFormula₁ Rel.memVF t

/-- `t ∈ RV` with parameters `α`. -/
def pRVG {α : Type} {n : ℕ} (t : LRV.Term (α ⊕ Fin n)) : LRV.BoundedFormula α n :=
  FirstOrder.Language.Relations.boundedFormula₁ Rel.memRV t

/-- the paper's unary predicate `Kˣ` with parameters `α`. -/
def pUnitsG {α : Type} {n : ℕ} (t : LRV.Term (α ⊕ Fin n)) : LRV.BoundedFormula α n :=
  FirstOrder.Language.Relations.boundedFormula₁ Rel.memUnits t

/-- the paper's preorder `≤` with parameters `α`. -/
def pLeG {α : Type} {n : ℕ} (t u : LRV.Term (α ⊕ Fin n)) : LRV.BoundedFormula α n :=
  FirstOrder.Language.Relations.boundedFormula₂ Rel.rvLe t u

/-- `t = u` with parameters `α`. -/
def pEqG {α : Type} {n : ℕ} (t u : LRV.Term (α ⊕ Fin n)) : LRV.BoundedFormula α n :=
  t =' u

/-- the sort predicate of the sort `s` at a term, with parameters `α` -/
def sortPredG {α : Type} {n : ℕ} (s : SortTag) (t : LRV.Term (α ⊕ Fin n)) :
    LRV.BoundedFormula α n :=
  match s with
  | .vf => pVFG t
  | .rv => pRVG t

theorem sortPred_eq_sortPredG {n : ℕ} (s : SortTag) (t : Tm n) :
    sortPred s t = sortPredG (α := Empty) s t := rfl

theorem pVF_eq_pVFG {n : ℕ} (t : Tm n) : pVF t = pVFG (α := Empty) t := rfl

/-! #### Guards -/

/-- The guard atom `xᵢ ∈ s`, for an arbitrary parameter type `α`. -/
def guardAtom {α : Type} {n : ℕ} (s : SortTag) (i : Fin n) : LRV.BoundedFormula α n :=
  sortPredG s (Term.var (Sum.inr i))

/-- **`InAntecedent s i η`**: `η` is a formula in which the guard atom `xᵢ ∈ s` occurs as a
*top-level conjunct*.  `a ⊓ b` is `¬(a → ¬b)` in the encoding, so a formula that starts with `⊓`
is an implication whose antecedent is an implication; the two `and` constructors descend through
exactly that.  Nothing weaker is admitted: the atom under a further negation or as the consequent
of an implication does not count, which is the whole point (an atom there is *true* at junk
elements, not false).

The paper's own antecedents are right-nested `⊓` of sort atoms (`sortedHyps`), which is the shape
this family decomposes. -/
inductive InAntecedent {α : Type} {n : ℕ} (s : SortTag) (i : Fin n) :
    LRV.BoundedFormula α n → Prop
  /-- the guard atom itself -/
  | atom : InAntecedent s i (guardAtom s i)
  /-- a conjunct of the left half -/
  | and_left {a b : LRV.BoundedFormula α n} :
      InAntecedent s i a → InAntecedent s i (a ⊓ b)
  /-- a conjunct of the right half -/
  | and_right {a b : LRV.BoundedFormula α n} :
      InAntecedent s i b → InAntecedent s i (a ⊓ b)

/-- **`Occurs i s η`**: the atom "the variable of index `i` lies in the sort `s`" is one of the
top-level conjuncts of `η`.  Only conjunctions are decomposed (`a ⊓ b` is `¬(a → ¬b)` in the
encoding), so an occurrence found by `Occurs` makes `η` *false* whenever the `i`-th element of the
tuple is not in the sort `s`, whatever the rest of `η` says.  Conjunctions are decomposed in the
form the tree's `sortedHyps` and friends are written in, which is the point of the definition.

`Occurs` **is** `InAntecedent` — a definition, not a compiled match.  A compiled match cannot be
unfolded at a constructor-headed argument whose subterms are variables, which is why the two had to
be identified rather than bridged (see `Milestone0/DECISION.md`, the guard repair); the inductive
form is the one the proofs can use. -/
def Occurs {α : Type} {m : ℕ} (i : Fin m) (s : SortTag) (φ : LRV.BoundedFormula α m) : Prop :=
  InAntecedent s i φ

/-- **The junk-truth condition on the body of a quantifier** (the author's ruling; `DECISION.md`).
`GuardTrue s i χ` is the syntactic condition on `χ` that makes it true at elements outside the sort
`s`:

* `χ = η ⟹ ψ` with the guard among the top-level conjuncts of `η`: the antecedent is false off
  the sort, so `χ` is true there;
* `χ = ∀ y, χ'` with `χ'` junk-true at the *same* variable (cast by `Fin.castSucc`): if the `i`-th
  element is junk then `χ'` holds at every value of `y`, so `∀ y, χ'` does too.

The second clause is what makes the condition survive the iteration in `wellSorted_alls`, where the
body of an inner quantifier is another quantifier.  Since `WellSorted` has no model parameter the
condition has to be syntactic, and this is the strongest shape that (a) excludes
`(x ∈ s ⟹ ⊥) ⟹ ψ`, (b) admits `sortedHyps`-shaped antecedents, and (c) is preserved by the
fragment's own quantifier. -/
inductive GuardTrue {α : Type} (s : SortTag) :
    {n : ℕ} → (i : Fin n) → LRV.BoundedFormula α n → Prop
  /-- the guard is a top-level conjunct of the antecedent -/
  | imp {n : ℕ} {i : Fin n} {η ψ : LRV.BoundedFormula α n}
      (h : InAntecedent s i η) : GuardTrue s i (η ⟹ ψ)
  /-- a universal inherits junk-truth from its body -/
  | all {n : ℕ} {i : Fin n} {χ : LRV.BoundedFormula α (n + 1)}
      (h : GuardTrue s (Fin.castSucc i) χ) : GuardTrue s i (.all χ)

/-- The `GuardTrue` obligation at an implication whose antecedent has the guard as a conjunct. -/
theorem GuardTrue.of_inAntecedent {α : Type} {m : ℕ} {i : Fin m} {s : SortTag}
    {η ψ : LRV.BoundedFormula α m} (h : InAntecedent s i η) :
    GuardTrue s i (η ⟹ ψ) :=
  GuardTrue.imp h

/-- Case analysis on a top-level conjunct: either it is the guard atom itself, or the formula is a
conjunction with the atom in one of its halves.  This is the elimination form of `InAntecedent`
(the family is indexed, so a plain `cases` cannot abstract the formula). -/
theorem InAntecedent.shape {α : Type} {m : ℕ} {i : Fin m} {s : SortTag}
    {φ : LRV.BoundedFormula α m} (h : InAntecedent s i φ) :
    φ = guardAtom s i ∨ ∃ a b : LRV.BoundedFormula α m, φ = a ⊓ b := by
  induction h with
  | atom => exact Or.inl rfl
  | and_left _ _ => exact Or.inr ⟨_, _, rfl⟩
  | and_right _ _ => exact Or.inr ⟨_, _, rfl⟩

/-- **`GuardsLast s i χ`**: `χ` has the atom "the variable of index `i` lies in the sort `s`" as a
conjunct of an antecedent, at its own level or under further quantifiers.  This is the syntactic
condition a guarded quantifier `∀ x ∈ s, ...` satisfies: descending under `all` keeps the indices
of the earlier variables, so the index only needs to be cast by `Fin.castSucc`. -/
def GuardsLast {α : Type} (s : SortTag) :
    {m : ℕ} → (i : Fin m) → LRV.BoundedFormula α m → Prop
  | _, i, .imp η ψ => Occurs i s η ∨ GuardsLast s i η ∨ GuardsLast s i ψ
  | _, i, .all χ => GuardsLast s (Fin.castSucc i) χ
  | _, _, _ => False

/-! #### Well-sorted formulas -/

/-- **`WellSorted sα sn φ`**: `φ` is a formula of the paper's two-sorted `L_RV`, with the free
parameters `a : α` of sort `sα a` and the free variables of sort `sn`.

* atoms: `t = u` only between terms of one sort, `t ∈ VF` only at a `VF`-term, and `t ∈ RV`,
  `t ∈ Kˣ`, `t ≤ u` only at `RV`-terms (this is `Rel.argSort`);
* connectives are componentwise;
* a quantifier is admitted only in guarded form: `∀ x, η → ψ` with `x` of sort `s` and `η`
  containing the conjunct `x ∈ s`.  Ill-sorted terms therefore never occur, and the value of a
  well-sorted formula at a tuple of the declared sorts is a function of the paper's two-sorted
  structure alone;
* **and the body of a quantifier is junk-true**: because `BoundedFormula.all` quantifies over the
  whole one-sorted carrier, not just the tag `s`, the body must hold at elements outside `s` too.
  That is the `GuardTrue` field, the author's ruling recorded in `Milestone0/DECISION.md`: the
  sort predicate of the bound variable is a *top-level conjunct* of the body's antecedent, so the
  antecedent is false — hence the body true — off the sort.  `GuardsLast` alone does not imply
  it (`(x ∈ s ⟹ ⊥) ⟹ ψ` satisfies `GuardsLast` and is false at junk elements). -/
inductive WellSorted {α : Type} (sα : α → SortTag) :
    {n : ℕ} → (Fin n → SortTag) → LRV.BoundedFormula α n → Prop
  /-- `⊥` -/
  | falsum {n : ℕ} (sn : Fin n → SortTag) : WellSorted sα sn .falsum
  /-- `t = u` between terms of one sort -/
  | equal {n : ℕ} (sn : Fin n → SortTag) {t u : LRV.Term (α ⊕ Fin n)} {s : SortTag}
      (ht : TmSort sα sn t = some s) (hu : TmSort sα sn u = some s) :
      WellSorted sα sn (.equal t u)
  /-- a relation of `L_RV` applied to terms of its declared sorts -/
  | rel {n l : ℕ} (sn : Fin n → SortTag) (R : Rel l) (ts : Fin l → LRV.Term (α ⊕ Fin n))
      (h : ∀ i, TmSort sα sn (ts i) = some (Rel.argSort R i)) :
      WellSorted sα sn (.rel R ts)
  /-- implication -/
  | imp {n : ℕ} (sn : Fin n → SortTag) {a b : LRV.BoundedFormula α n} :
      WellSorted sα sn a → WellSorted sα sn b → WellSorted sα sn (.imp a b)
  /-- the guarded universal quantifier `∀ x ∈ s, ψ`, whose body is junk-true (`GuardTrue`) -/
  | all {n : ℕ} (sn : Fin n → SortTag) {s : SortTag} {χ : LRV.BoundedFormula α (n + 1)}
      (hχ : WellSorted sα (Fin.snoc sn s) χ) (hg : GuardsLast s (Fin.last n) χ)
      (hj : GuardTrue s (Fin.last n) χ) :
      WellSorted sα sn (.all χ)
/-! #### The sort of a term, symbol by symbol

The statements are given for `Term.func f ![…]`, i.e. with an arbitrary parameter type `α`; the
tree's constructors `tVFAdd`, `tRv`, … are definitionally these terms at `α = Empty`, so the
lemmas apply to them verbatim. -/

section TmSortLemmas

variable {α : Type} (sα : α → SortTag) {n : ℕ} (sn : Fin n → SortTag)

theorem tmSort_var_inl (a : α) : TmSort sα sn (Term.var (Sum.inl a)) = some (sα a) := rfl

theorem tmSort_var_inr (i : Fin n) : TmSort sα sn (Term.var (Sum.inr i)) = some (sn i) := rfl

/-- the sort of the bound variable `i` -/
theorem tmSort_tv (i : ℕ) (h : i < n) :
    TmSort sα sn (Term.var (Sum.inr (⟨i, h⟩ : Fin n))) = some (sn ⟨i, h⟩) := rfl

/-- the sort of an application of a function symbol -/
theorem tmSort_func_iff {l : ℕ} (f : Fn l) (ts : Fin l → LRV.Term (α ⊕ Fin n)) {s : SortTag} :
    TmSort sα sn (Term.func f ts) = some s ↔
      (∀ i, TmSort sα sn (ts i) = some (Fn.argSort f i)) ∧ Fn.resSort f = s := by
  simp only [TmSort]
  split_ifs with h
  · simp [h]
  · simp [h]

theorem tmSort_func {l : ℕ} (f : Fn l) (ts : Fin l → LRV.Term (α ⊕ Fin n))
    (h : ∀ i, TmSort sα sn (ts i) = some (Fn.argSort f i)) :
    TmSort sα sn (Term.func f ts) = some (Fn.resSort f) :=
  (tmSort_func_iff sα sn f ts).2 ⟨h, rfl⟩

theorem tmSort_vfZero :
    TmSort sα sn (Term.func Fn.vfZero (fun i => i.elim0) : LRV.Term (α ⊕ Fin n)) = some .vf :=
  tmSort_func sα sn Fn.vfZero (fun i => i.elim0) (fun i => i.elim0)

theorem tmSort_vfOne :
    TmSort sα sn (Term.func Fn.vfOne (fun i => i.elim0) : LRV.Term (α ⊕ Fin n)) = some .vf :=
  tmSort_func sα sn Fn.vfOne (fun i => i.elim0) (fun i => i.elim0)

theorem tmSort_rvOne :
    TmSort sα sn (Term.func Fn.rvOne (fun i => i.elim0) : LRV.Term (α ⊕ Fin n)) = some .rv :=
  tmSort_func sα sn Fn.rvOne (fun i => i.elim0) (fun i => i.elim0)

theorem tmSort_rvZero :
    TmSort sα sn (Term.func Fn.rvZero (fun i => i.elim0) : LRV.Term (α ⊕ Fin n)) = some .rv :=
  tmSort_func sα sn Fn.rvZero (fun i => i.elim0) (fun i => i.elim0)

theorem tmSort_bin_iff (f : Fn 2) {t u : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func f ![t, u]) = some (Fn.resSort f) ↔
      TmSort sα sn t = some (Fn.argSort f 0) ∧ TmSort sα sn u = some (Fn.argSort f 1) := by
  rw [tmSort_func_iff, Fin.forall_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

theorem tmSort_un_iff (f : Fn 1) {t : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func f ![t]) = some (Fn.resSort f) ↔
      TmSort sα sn t = some (Fn.argSort f 0) := by
  rw [tmSort_func_iff, Fin.forall_fin_one]
  simp only [Matrix.cons_val_zero]
  exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

theorem tmSort_vfAdd {t u : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func Fn.vfAdd ![t, u]) = some .vf ↔
      TmSort sα sn t = some .vf ∧ TmSort sα sn u = some .vf :=
  tmSort_bin_iff sα sn Fn.vfAdd

theorem tmSort_vfMul {t u : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func Fn.vfMul ![t, u]) = some .vf ↔
      TmSort sα sn t = some .vf ∧ TmSort sα sn u = some .vf :=
  tmSort_bin_iff sα sn Fn.vfMul

theorem tmSort_rvMul {t u : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func Fn.rvMul ![t, u]) = some .rv ↔
      TmSort sα sn t = some .rv ∧ TmSort sα sn u = some .rv :=
  tmSort_bin_iff sα sn Fn.rvMul

theorem tmSort_rvInv {t : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func Fn.rvInv ![t]) = some .rv ↔ TmSort sα sn t = some .rv :=
  tmSort_un_iff sα sn Fn.rvInv

theorem tmSort_kAdd {t u : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func Fn.kAdd ![t, u]) = some .rv ↔
      TmSort sα sn t = some .rv ∧ TmSort sα sn u = some .rv :=
  tmSort_bin_iff sα sn Fn.kAdd

theorem tmSort_vfNeg {t : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func Fn.vfNeg ![t]) = some .vf ↔ TmSort sα sn t = some .vf :=
  tmSort_un_iff sα sn Fn.vfNeg

theorem tmSort_kNeg {t : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func Fn.kNeg ![t]) = some .rv ↔ TmSort sα sn t = some .rv :=
  tmSort_un_iff sα sn Fn.kNeg

theorem tmSort_tRv {t : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func Fn.rvMap ![t]) = some .rv ↔ TmSort sα sn t = some .vf :=
  tmSort_un_iff sα sn Fn.rvMap

/-- **The sort of a term does not change when the context is extended by a new variable.**
This is what lets a formula be read under a quantifier that has just been added. -/
theorem tmSort_relabel_castSucc (s : SortTag) (t : LRV.Term (α ⊕ Fin n)) :
    TmSort sα (Fin.snoc sn s) (t.relabel (Sum.map id Fin.castSucc)) = TmSort sα sn t := by
  induction t with
  | var a =>
    rcases a with a | i
    · rfl
    · show TmSort sα (Fin.snoc sn s) (Term.var (Sum.inr (Fin.castSucc i))) = some (sn i)
      simp only [TmSort]
      rw [Fin.snoc_castSucc]
  | @func l f ts ih =>
    simp only [Term.relabel, TmSort]
    by_cases h : ∀ i, TmSort sα sn (ts i) = some (Fn.argSort f i)
    · have h' : ∀ i, TmSort sα (Fin.snoc sn s)
          ((ts i).relabel (Sum.map id Fin.castSucc)) = some (Fn.argSort f i) :=
        fun i => by rw [ih i]; exact h i
      rw [if_pos h', if_pos h]
    · have h' : ¬ ∀ i, TmSort sα (Fin.snoc sn s)
          ((ts i).relabel (Sum.map id Fin.castSucc)) = some (Fn.argSort f i) :=
        fun hc => h (fun i => by rw [← ih i]; exact hc i)
      rw [if_neg h', if_neg h]

end TmSortLemmas
/-! #### Well-sortedness of the atoms, and the guarded quantifiers -/

section FormulaLemmas

variable {α : Type} (sα : α → SortTag) {n : ℕ} (sn : Fin n → SortTag)

/-- the conjunction of two well-sorted formulas is well-sorted -/
theorem wellSorted_inf {a b : LRV.BoundedFormula α n} (ha : WellSorted sα sn a)
    (hb : WellSorted sα sn b) : WellSorted sα sn (a ⊓ b) :=
  WellSorted.imp sn (WellSorted.imp sn ha (WellSorted.imp sn hb (WellSorted.falsum sn)))
    (WellSorted.falsum sn)

theorem wellSorted_top : WellSorted sα sn (⊤ : LRV.BoundedFormula α n) :=
  WellSorted.imp sn (WellSorted.falsum sn) (WellSorted.falsum sn)

/-- `t = u` between terms of one sort -/
theorem wellSorted_pEqG {t u : LRV.Term (α ⊕ Fin n)} {s : SortTag}
    (ht : TmSort sα sn t = some s) (hu : TmSort sα sn u = some s) :
    WellSorted sα sn (pEqG t u) :=
  WellSorted.equal sn ht hu

/-- `t ∈ VF` at a `VF`-term -/
theorem rel_argSort_memVF : Rel.argSort (Rel.memVF) = fun _ => .vf := rfl

theorem rel_argSort_memRV : Rel.argSort (Rel.memRV) = fun _ => .rv := rfl

theorem rel_argSort_memUnits : Rel.argSort (Rel.memUnits) = fun _ => .rv := rfl

theorem rel_argSort_rvLe : Rel.argSort (Rel.rvLe) = fun _ => .rv := rfl

theorem wellSorted_pVFG {t : LRV.Term (α ⊕ Fin n)} (h : TmSort sα sn t = some .vf) :
    WellSorted sα sn (pVFG t) :=
  WellSorted.rel sn Rel.memVF ![t]
    (fun i => by rw [rel_argSort_memVF]; fin_cases i; simpa using h)

/-- `t ∈ RV` at an `RV`-term -/
theorem wellSorted_pRVG {t : LRV.Term (α ⊕ Fin n)} (h : TmSort sα sn t = some .rv) :
    WellSorted sα sn (pRVG t) :=
  WellSorted.rel sn Rel.memRV ![t]
    (fun i => by rw [rel_argSort_memRV]; fin_cases i; simpa using h)

/-- `t ∈ Kˣ` at an `RV`-term -/
theorem wellSorted_pUnitsG {t : LRV.Term (α ⊕ Fin n)} (h : TmSort sα sn t = some .rv) :
    WellSorted sα sn (pUnitsG t) :=
  WellSorted.rel sn Rel.memUnits ![t]
    (fun i => by rw [rel_argSort_memUnits]; fin_cases i; simpa using h)

/-- `t ≤ u` at `RV`-terms -/
theorem wellSorted_pLeG {t u : LRV.Term (α ⊕ Fin n)}
    (ht : TmSort sα sn t = some .rv) (hu : TmSort sα sn u = some .rv) :
    WellSorted sα sn (pLeG t u) :=
  WellSorted.rel sn Rel.rvLe ![t, u] (fun i => by
    rw [rel_argSort_rvLe]
    fin_cases i
    · simpa using ht
    · simpa using hu)

/-- the sort predicate of the sort of a term of that sort -/
theorem wellSorted_sortPredG {s : SortTag} {t : LRV.Term (α ⊕ Fin n)}
    (h : TmSort sα sn t = some s) : WellSorted sα sn (sortPredG s t) := by
  cases s with
  | vf => exact wellSorted_pVFG sα sn h
  | rv => exact wellSorted_pRVG sα sn h

/-! ##### Guards -/

theorem Occurs.of_conj_left {m : ℕ} (i : Fin m) {s : SortTag} {a b : LRV.BoundedFormula α m}
    (h : Occurs i s a) : Occurs i s (a ⊓ b) := InAntecedent.and_left h

theorem Occurs.of_conj_right {m : ℕ} (i : Fin m) {s : SortTag} {a b : LRV.BoundedFormula α m}
    (h : Occurs i s b) : Occurs i s (a ⊓ b) := InAntecedent.and_right h

/-- an occurrence in an antecedent guards the implication -/
theorem GuardsLast.of_occurs {m : ℕ} (i : Fin m) {s : SortTag} {η ψ : LRV.BoundedFormula α m}
    (h : Occurs i s η) : GuardsLast s i (η ⟹ ψ) := Or.inl h

/-- the atom `x_i ∈ s` occurs in `sortPred s (x_i)` -/
theorem occurs_self (α : Type) {m : ℕ} (i : Fin m) (s : SortTag) :
    @Occurs α m i s (sortPredG s (Term.var (Sum.inr i))) :=
  InAntecedent.atom

/-- **The guarded universal quantifier**: `∀ x ∈ s, (η → ψ)` is well-sorted when `ψ` and `η` are
well-sorted in the extended context and `η` contains the conjunct `x ∈ s`. -/
theorem wellSorted_all_guarded {m : ℕ} {sn : Fin m → SortTag} {s : SortTag}
    {η ψ : LRV.BoundedFormula α (m + 1)}
    (hη : WellSorted sα (Fin.snoc sn s) η) (hψ : WellSorted sα (Fin.snoc sn s) ψ)
    (hg : Occurs (Fin.last m) s η) :
    WellSorted sα sn (.all (η ⟹ ψ)) :=
  WellSorted.all sn (WellSorted.imp _ hη hψ) (Or.inl hg)
    (GuardTrue.of_inAntecedent hg)

/-- **The guarded existential quantifier** `∃ x ∈ s, ψ`.  (The encoding writes it as
`¬∀ x, ¬(x ∈ s ∧ ψ)`.) -/
def exSortedG {α : Type} {k : ℕ} (s : SortTag) (ψ : LRV.BoundedFormula α (k + 1)) :
    LRV.BoundedFormula α k :=
  BoundedFormula.ex (sortPredG s (Term.var (Sum.inr (Fin.last k))) ⊓ ψ)

theorem wellSorted_exSortedG {m : ℕ} {sn : Fin m → SortTag} {s : SortTag}
    {ψ : LRV.BoundedFormula α (m + 1)} (h : WellSorted sα (Fin.snoc sn s) ψ) :
    WellSorted sα sn (exSortedG s ψ) := by
  have hpred : WellSorted sα (Fin.snoc sn s)
      (sortPredG s (Term.var (Sum.inr (Fin.last m)))) :=
    wellSorted_sortPredG sα _ (by rw [tmSort_var_inr, Fin.snoc_last])
  refine WellSorted.imp sn (WellSorted.all sn
    (WellSorted.imp _ (wellSorted_inf sα _ hpred h) (WellSorted.falsum _))
    (Or.inl (InAntecedent.and_left (occurs_self α (Fin.last m) s)))
    (GuardTrue.of_inAntecedent (InAntecedent.and_left (α := α) InAntecedent.atom)))
    (WellSorted.falsum sn)


/-- **The `VF`-guarded universal quantifier** `∀ x ∈ VF, ψ` — the quantifier shape of
`RVElim.VFQ` (`allVF`) — is well-sorted when `ψ` is. -/
theorem wellSorted_all_pVF {m : ℕ} {sn : Fin m → SortTag} {ψ : Bf (m + 1)} {sα : Empty → SortTag}
    (h : WellSorted sα (Fin.snoc sn .vf) ψ) :
    WellSorted sα sn (BoundedFormula.all (pVF (tv m (Nat.lt_succ_self m)) ⟹ ψ)) :=
  wellSorted_all_guarded sα
    (η := pVF (tv m (Nat.lt_succ_self m)))
    (by
      have h' : TmSort sα (Fin.snoc sn .vf) (tv m (Nat.lt_succ_self m)) = some .vf := by
        show TmSort sα (Fin.snoc sn .vf) (Term.var (Sum.inr (Fin.last m))) = some .vf
        rw [tmSort_var_inr, Fin.snoc_last]
      exact wellSorted_pVFG sα _ h')
    h
    (occurs_self Empty (Fin.last m) .vf)

end FormulaLemmas
/-! #### The sort hypotheses `sortedHyps`, and the iterated guarded quantifier `alls` -/

section SortedHyps

variable (sα : Empty → SortTag)

theorem wellSorted_foldr_hyps {k : ℕ} (ss : Fin k → SortTag) (l : List (Fin k)) :
    ∀ (acc : Bf k), WellSorted sα ss acc →
      WellSorted sα ss (l.foldr (fun i acc => sortPred (ss i) (tv i.val i.isLt) ⊓ acc) acc) := by
  induction l with
  | nil => intro acc h; exact h
  | cons i l ih =>
    intro acc h
    simp only [List.foldr_cons]
    exact wellSorted_inf sα ss (wellSorted_sortPredG sα ss (tmSort_var_inr sα ss i)) (ih acc h)

/-- **`sortedHyps ss` is well-sorted** in the context whose sorts are `ss`. -/
theorem wellSorted_sortedHyps {k : ℕ} (ss : Fin k → SortTag) :
    WellSorted sα ss (sortedHyps ss) :=
  wellSorted_foldr_hyps sα ss (List.finRange k) ⊤ (wellSorted_top sα ss)

end SortedHyps

section OccursHyps

/-- In `sortedHyps ss` the atom `x_i ∈ ss i` occurs as a conjunct. -/
theorem occurs_foldr_hyps {k : ℕ} (ss : Fin k → SortTag) :
    ∀ (l : List (Fin k)) (acc : Bf k) (i : Fin k), i ∈ l →
      Occurs i (ss i) (l.foldr (fun j acc => sortPred (ss j) (tv j.val j.isLt) ⊓ acc) acc)
  | [], _, i, hi => by simp at hi
  | j :: l, acc, i, hi => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hi with rfl | hi'
    · exact Occurs.of_conj_left i (occurs_self Empty i (ss i))
    · exact InAntecedent.and_right (occurs_foldr_hyps ss l acc i hi')

theorem occurs_sortedHyps {k : ℕ} (ss : Fin k → SortTag) (i : Fin k) :
    Occurs i (ss i) (sortedHyps ss) :=
  occurs_foldr_hyps ss (List.finRange k) ⊤ i (List.mem_finRange i)

end OccursHyps

section Alls

/-- `Fin.snoc` of the restriction to `Fin.castSucc` and the last value is the whole tuple. -/
theorem fin_snoc_castSucc_last {k : ℕ} (ss : Fin (k + 1) → SortTag) :
    Fin.snoc (fun i : Fin k => ss (Fin.castSucc i)) (ss (Fin.last k)) = ss := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last]
  · intro j
    rw [Fin.snoc_castSucc]

/-- **The iterated guarded quantifier.**  If `χ` is well-sorted in the context `ss`, and every
variable of that context occurs as a guard `x_i ∈ ss i` in a conjunct of an antecedent of `χ`,
then `∀ x_0 … ∀ x_{k-1}, χ` is well-sorted.  (`BoundedFormula.alls` binds the variables in this
order, so the guard for the `d`-th binder is the occurrence at index `d`.) -/
theorem wellSorted_alls {k : ℕ} {sα : Empty → SortTag} {χ : Bf k} {ss : Fin k → SortTag}
    (h : WellSorted sα ss χ) (hg : ∀ d : Fin k, GuardsLast (ss d) d χ)
    (hj : ∀ d : Fin k, GuardTrue (ss d) d χ) :
    WellSorted sα (fun i : Fin 0 => i.elim0) (BoundedFormula.alls χ) := by
  induction k with
  | zero =>
    have hss : ss = fun i : Fin 0 => i.elim0 := funext (fun i => i.elim0)
    rwa [hss] at h
  | succ k ih =>
    show WellSorted sα (fun i : Fin 0 => i.elim0) (BoundedFormula.alls (BoundedFormula.all χ))
    refine ih (ss := fun d : Fin k => ss (Fin.castSucc d)) ?_ ?_ ?_
    · refine WellSorted.all _ ?_ (hg (Fin.last k)) (hj (Fin.last k))
      rw [fin_snoc_castSucc_last ss]
      exact h
    · intro d
      exact hg (Fin.castSucc d)
    · intro d
      exact GuardTrue.all (hj (Fin.castSucc d))

/-- **The guarded universal sentence `allSorted ss φ` is well-sorted.** -/
theorem wellSorted_allSorted {k : ℕ} {sα : Empty → SortTag} (ss : Fin k → SortTag) {φ : Bf k}
    (hφ : WellSorted sα ss φ) :
    WellSorted sα (fun i : Fin 0 => i.elim0) (allSorted ss φ) :=
  wellSorted_alls (WellSorted.imp ss (wellSorted_sortedHyps sα ss) hφ)
    (fun d => Or.inl (occurs_sortedHyps ss d))
    (fun d => GuardTrue.of_inAntecedent (occurs_sortedHyps ss d))

/-- `pInK t` is well-sorted at an `RV`-term. -/
theorem wellSorted_pInK {n : ℕ} {sα : Empty → SortTag} {sn : Fin n → SortTag}
    {t : Tm n} (h : TmSort sα sn t = some .rv) : WellSorted sα sn (pInK t) :=
  WellSorted.imp sn (WellSorted.imp sn (wellSorted_pUnitsG sα sn h) (WellSorted.falsum sn))
    (wellSorted_pEqG sα sn h (tmSort_rvZero sα sn))

theorem wellSorted_foldr_kHyps {k : ℕ} (sα : Empty → SortTag) (l : List (Fin k)) :
    ∀ (acc : Bf k), WellSorted sα (fun _ => .rv) acc →
      WellSorted sα (fun _ => .rv)
        (l.foldr (fun i acc => pInK (tv i.val i.isLt) ⊓ acc) acc) := by
  induction l with
  | nil => intro acc h; exact h
  | cons i l ih =>
    intro acc h
    simp only [List.foldr_cons]
    exact wellSorted_inf sα _ (wellSorted_pInK (tmSort_var_inr sα (fun _ => .rv) i)) (ih acc h)

theorem wellSorted_kHyps {k : ℕ} (sα : Empty → SortTag) :
    WellSorted sα (fun _ : Fin k => .rv) (kHyps : Bf k) :=
  wellSorted_foldr_kHyps (k := k) sα (List.finRange k) ⊤ (wellSorted_top sα _)

/-- **The guarded universal sentence `allSortedK ss φ` is well-sorted**, in the contexts where it
is used (`ss` constantly `RV`; `kHyps` constrains `RV`-variables only). -/
theorem wellSorted_allSortedK {k : ℕ} {sα : Empty → SortTag} {φ : Bf k}
    (hφ : WellSorted sα (fun _ => .rv) φ) :
    WellSorted sα (fun i : Fin 0 => i.elim0) (allSortedK (fun _ => .rv) φ) :=
  wellSorted_alls
    (WellSorted.imp _ (wellSorted_inf sα _ (wellSorted_sortedHyps sα _)
      (wellSorted_kHyps sα)) hφ)
    (fun d => Or.inl (InAntecedent.and_left (occurs_sortedHyps (fun _ => .rv) d)))
    (fun d => GuardTrue.of_inAntecedent
      (InAntecedent.and_left (occurs_sortedHyps (fun _ => .rv) d)))

/-- **The universal closure of a guarded formula in one variable is well-sorted.** -/
theorem wellSorted_allOne {sα : Empty → SortTag} {s : SortTag} {φ : Bf 1}
    (hφ : WellSorted sα (fun _ => s) φ) (hg : GuardsLast s 0 φ)
    (hj : GuardTrue s 0 φ) :
    WellSorted sα (fun i : Fin 0 => i.elim0) (allOne φ) :=
  wellSorted_alls (ss := fun _ => s) hφ (fun d => by
    have : d = 0 := by ext; omega
    rw [this]
    exact hg) (fun d => by
    have : d = 0 := by ext; omega
    rw [this]
    exact hj)

end Alls

/-! #### w1's additions to the block

The block above is m5's, verbatim (swarm `smw17pts2`, `.ultramath/smw17pts2/m5/WellSorted_block.lean`,
inserted after `def allOne` and inside `namespace LRV` as its README requires).  What follows is what
the audit of Part 6.1 needs on top of it: closure of `WellSorted` under the derived connectives
(`∼`, `⊔`, `⇔`), the encoding's guarded existentials `exSorted`/`exSortedK` in `WellSorted` form, and
the `TmSort` of the tree's term constructors (`tVFAdd`, `tRv`, `tRVPow`, `tVFNumeral`, …) as a
`simp` set.

Nothing here changes `WellSorted` or any of m5's statements: it is all addition. -/

section Connectives

variable {α : Type} (sα : α → SortTag) {n : ℕ} (sn : Fin n → SortTag)

/-- the negation of a well-sorted formula is well-sorted -/
theorem wellSorted_not {a : LRV.BoundedFormula α n} (h : WellSorted sα sn a) :
    WellSorted sα sn (∼a) :=
  WellSorted.imp sn h (WellSorted.falsum sn)

/-- the disjunction of two well-sorted formulas is well-sorted (`a ⊔ b` is `∼a ⟹ b`) -/
theorem wellSorted_sup {a b : LRV.BoundedFormula α n} (ha : WellSorted sα sn a)
    (hb : WellSorted sα sn b) : WellSorted sα sn (a ⊔ b) :=
  WellSorted.imp sn (wellSorted_not sα sn ha) hb

/-- the biconditional of two well-sorted formulas is well-sorted -/
theorem wellSorted_iff {a b : LRV.BoundedFormula α n} (ha : WellSorted sα sn a)
    (hb : WellSorted sα sn b) : WellSorted sα sn (a ⇔ b) :=
  wellSorted_inf sα sn (WellSorted.imp sn ha hb) (WellSorted.imp sn hb ha)

/-- a double negation -/
theorem wellSorted_not_not {a : LRV.BoundedFormula α n} (h : WellSorted sα sn a) :
    WellSorted sα sn (∼∼a) :=
  wellSorted_not sα sn (wellSorted_not sα sn h)

/-- **`∃ x ∈ s, φ` with an arbitrary guard**: if `η` is well-sorted, `ψ` is well-sorted and the
atom `x ∈ s` occurs in a conjunct of `η`, then `∃ x, η ∧ ψ` is well-sorted.  (`BoundedFormula.ex ψ`
is `¬∀x, ¬ψ` in the encoding.)  This generalises m5's `wellSorted_exSortedG`, and is what
`exSortedK` needs: its guard is the *conjunction* `x ∈ RV ∧ x ∈ K`, not the single sort predicate. -/
theorem wellSorted_ex_guarded {m : ℕ} {sn : Fin m → SortTag} {s : SortTag}
    {η ψ : LRV.BoundedFormula α (m + 1)}
    (hη : WellSorted sα (Fin.snoc sn s) η) (hψ : WellSorted sα (Fin.snoc sn s) ψ)
    (hg : Occurs (Fin.last m) s η) :
    WellSorted sα sn (BoundedFormula.ex (η ⊓ ψ)) :=
  WellSorted.imp sn (WellSorted.all sn
    (WellSorted.imp _ (wellSorted_inf sα _ hη hψ) (WellSorted.falsum _))
    (Or.inl (InAntecedent.and_left hg))
    (GuardTrue.of_inAntecedent (InAntecedent.and_left (α := α) hg)))
    (WellSorted.falsum sn)

end Connectives

section Variables

variable (sα : Empty → SortTag) {n : ℕ} (sn : Fin n → SortTag)

/-- the bound variable `i` has the sort `sn i` (the constructor form of m5's `tmSort_tv`) -/
@[simp] theorem tmSort_tv' (i : ℕ) (h : i < n) : TmSort sα sn (tv i h) = some (sn ⟨i, h⟩) :=
  tmSort_var_inr sα sn ⟨i, h⟩

/-- the last variable of the context `Fin.snoc ss .rv` is an `RV`-variable -/
@[simp] theorem tmSort_tv_last {k : ℕ} {ss : Fin k → SortTag} :
    TmSort sα (Fin.snoc ss .rv) (tv k (Nat.lt_succ_self k)) = some .rv := by
  rw [tmSort_tv']
  have h : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k := by ext; rfl
  rw [h, Fin.snoc_last]

end Variables

section Existentials

variable (sα : Empty → SortTag)

/-- the encoding's `∃ x ∈ s, φ` (Part 2) is well-sorted at a well-sorted body: it is m5's
`exSortedG`, the two are the same formula. -/
theorem wellSorted_exSorted {k : ℕ} {ss : Fin k → SortTag} {s : SortTag} {φ : Bf (k + 1)}
    (h : WellSorted sα (Fin.snoc ss s) φ) : WellSorted sα ss (exSorted s φ) :=
  wellSorted_exSortedG sα h

/-- the encoding's `∃ x ∈ s ∩ K, φ` (Part 2) is well-sorted at a well-sorted body; `pInK` is
well-sorted at an `RV`-term, and `exSortedK` is only used at `s = .rv`. -/
theorem wellSorted_exSortedK {k : ℕ} {ss : Fin k → SortTag} {φ : Bf (k + 1)}
    (h : WellSorted sα (Fin.snoc ss .rv) φ) : WellSorted sα ss (exSortedK .rv φ) :=
  wellSorted_ex_guarded sα
    (η := sortPred .rv (tv k (Nat.lt_succ_self k)) ⊓ pInK (tv k (Nat.lt_succ_self k)))
    (wellSorted_inf sα _
      (wellSorted_pRVG sα _ (t := tv k (Nat.lt_succ_self k)) (tmSort_tv_last sα))
      (wellSorted_pInK (t := tv k (Nat.lt_succ_self k)) (tmSort_tv_last sα)))
    h
    (InAntecedent.and_left (occurs_self Empty (Fin.last k) .rv))

/-- `exSortedK` at a context of `RV`-variables: the shape of `acfSchemeK`'s body -/
theorem wellSorted_exSortedK_k {k : ℕ} {φ : Bf (k + 1)}
    (h : WellSorted sα (fun _ : Fin (k + 1) => .rv) φ) :
    WellSorted sα (fun _ : Fin k => .rv) (exSortedK .rv φ) :=
  wellSorted_exSortedK sα (by
    simpa using (fin_snoc_castSucc_last (ss := fun _ : Fin (k + 1) => .rv) ▸ h))

end Existentials

section SortedHypsGeneric

variable (sα : Empty → SortTag)

/-- `kHyps` is well-sorted at **any** context of `RV`-variables, not only at the constant one
(m5's `wellSorted_kHyps` is the case `ss ≡ .rv`; the axioms of `Axioms.kField` are written with
`![.rv, …]`, which is not definitionally the constant assignment). -/
theorem wellSorted_foldr_kHyps_ss {k : ℕ} {ss : Fin k → SortTag} (hss : ∀ i, ss i = .rv)
    (l : List (Fin k)) :
    ∀ (acc : Bf k), WellSorted sα ss acc →
      WellSorted sα ss (l.foldr (fun i acc => pInK (tv i.val i.isLt) ⊓ acc) acc) := by
  induction l with
  | nil => intro acc h; exact h
  | cons i l ih =>
    intro acc h
    simp only [List.foldr_cons]
    exact wellSorted_inf sα ss (wellSorted_pInK (by rw [tmSort_tv', hss i])) (ih acc h)

/-- `kHyps` is well-sorted at a context of `RV`-variables -/
theorem wellSorted_kHyps_ss {k : ℕ} {ss : Fin k → SortTag} (hss : ∀ i, ss i = .rv) :
    WellSorted sα ss (kHyps : Bf k) :=
  wellSorted_foldr_kHyps_ss sα hss (List.finRange k) ⊤ (wellSorted_top sα ss)

/-- **`allSortedK ss φ` is well-sorted** for any assignment `ss` of `RV`-variables (m5's
`wellSorted_allSortedK` is the case `ss ≡ .rv`). -/
theorem wellSorted_allSortedK_ss {k : ℕ} {ss : Fin k → SortTag} {φ : Bf k}
    (hss : ∀ i, ss i = .rv) (hφ : WellSorted sα ss φ) :
    WellSorted sα (fun i : Fin 0 => i.elim0) (allSortedK ss φ) := by
  refine wellSorted_alls (WellSorted.imp ss ?_ hφ) ?_ ?_
  · exact wellSorted_inf sα ss (wellSorted_sortedHyps sα ss)
      (wellSorted_kHyps_ss sα hss)
  · intro d
    exact Or.inl (InAntecedent.and_left (occurs_sortedHyps ss d))
  · intro d
    exact GuardTrue.of_inAntecedent (InAntecedent.and_left (occurs_sortedHyps ss d))

end SortedHypsGeneric

/-! #### The `TmSort` of the tree's term constructors

Every axiom of `ACVF` is a formula over the *constructors* of Part 1 (`tVFAdd`, `tRv`, …), not over
the raw `Term.func` forms that m5's lemmas are stated for.  The constructors are definitions, so the
two are the same term — but `simp` matches syntactically, so the audit needs m5's `tmSort_*` restated
in constructor form.  That is all this section is. -/

section TmSortConstructors

attribute [simp] tmSort_var_inr

-- The constructors `tVFZero`, … are terms of `Tm n = LRV.Term (Empty ⊕ Fin n)`, so this section
-- is at `α = Empty`; m5's `tmSort_*` lemmas are the general-`α` forms of the same facts.
variable (sα : Empty → SortTag) {n : ℕ} (sn : Fin n → SortTag)

@[simp] theorem tmSort_tVFZero : TmSort sα sn (tVFZero (n := n)) = some .vf :=
  tmSort_func sα sn Fn.vfZero (fun i => i.elim0) (fun i => i.elim0)

@[simp] theorem tmSort_tVFOne : TmSort sα sn (tVFOne (n := n)) = some .vf :=
  tmSort_func sα sn Fn.vfOne (fun i => i.elim0) (fun i => i.elim0)

@[simp] theorem tmSort_tRVZero : TmSort sα sn (tRVZero (n := n)) = some .rv :=
  tmSort_func sα sn Fn.rvZero (fun i => i.elim0) (fun i => i.elim0)

@[simp] theorem tmSort_tRVOne : TmSort sα sn (tRVOne (n := n)) = some .rv :=
  tmSort_func sα sn Fn.rvOne (fun i => i.elim0) (fun i => i.elim0)

@[simp] theorem tmSort_tRVInfty : TmSort sα sn (tRVInfty (n := n)) = some .rv :=
  tmSort_tRVZero sα sn

@[simp] theorem tmSort_tVFAdd {t u : Tm n} :
    TmSort sα sn (tVFAdd t u) = some .vf ↔
      TmSort sα sn t = some .vf ∧ TmSort sα sn u = some .vf :=
  tmSort_bin_iff sα sn Fn.vfAdd

@[simp] theorem tmSort_tVFMul {t u : Tm n} :
    TmSort sα sn (tVFMul t u) = some .vf ↔
      TmSort sα sn t = some .vf ∧ TmSort sα sn u = some .vf :=
  tmSort_bin_iff sα sn Fn.vfMul

@[simp] theorem tmSort_tVFNeg {t : Tm n} :
    TmSort sα sn (tVFNeg t) = some .vf ↔ TmSort sα sn t = some .vf :=
  tmSort_un_iff sα sn Fn.vfNeg

@[simp] theorem tmSort_tRVMul {t u : Tm n} :
    TmSort sα sn (tRVMul t u) = some .rv ↔
      TmSort sα sn t = some .rv ∧ TmSort sα sn u = some .rv :=
  tmSort_bin_iff sα sn Fn.rvMul

@[simp] theorem tmSort_tRVInv {t : Tm n} :
    TmSort sα sn (tRVInv t) = some .rv ↔ TmSort sα sn t = some .rv :=
  tmSort_un_iff sα sn Fn.rvInv

@[simp] theorem tmSort_tKAdd {t u : Tm n} :
    TmSort sα sn (tKAdd t u) = some .rv ↔
      TmSort sα sn t = some .rv ∧ TmSort sα sn u = some .rv :=
  tmSort_bin_iff sα sn Fn.kAdd

@[simp] theorem tmSort_tKNeg {t : Tm n} :
    TmSort sα sn (tKNeg t) = some .rv ↔ TmSort sα sn t = some .rv :=
  tmSort_un_iff sα sn Fn.kNeg

/-- the constructor form of m5's `tmSort_tRv` (the prime avoids the clash with it) -/
@[simp] theorem tmSort_tRv' {t : Tm n} :
    TmSort sα sn (tRv t) = some .rv ↔ TmSort sα sn t = some .vf :=
  tmSort_un_iff sα sn Fn.rvMap

end TmSortConstructors

/-- `pRV t = ∼(t = 0)` is well-sorted at an `RV`-term (m5's `wellSorted_pRV` is the same
statement with the symbol `pRV`; it is re-stated here because the audit is at `α = Empty` and uses
the `[simp]` facts above). -/
theorem wellSorted_pRV' {n : ℕ} {sα : Empty → SortTag} {sn : Fin n → SortTag} {t : Tm n}
    (h : TmSort sα sn t = some .rv) : WellSorted sα sn (pRV t) :=
  wellSorted_not sα sn (wellSorted_pEqG (s := .rv) sα sn h (tmSort_tRVZero sα sn))

section Powers

variable (sα : Empty → SortTag) {n : ℕ} (sn : Fin n → SortTag)

@[simp] theorem tmSort_tVFPow {t : Tm n} (h : TmSort sα sn t = some .vf) :
    ∀ k : ℕ, TmSort sα sn (tVFPow t k) = some .vf
  | 0 => tmSort_tVFOne sα sn
  | k + 1 => by
    rw [tVFPow, tmSort_tVFMul]
    exact ⟨tmSort_tVFPow h k, h⟩

@[simp] theorem tmSort_tRVPow {t : Tm n} (h : TmSort sα sn t = some .rv) :
    ∀ k : ℕ, TmSort sα sn (tRVPow t k) = some .rv
  | 0 => tmSort_tRVOne sα sn
  | k + 1 => by
    rw [tRVPow, tmSort_tRVMul]
    exact ⟨tmSort_tRVPow h k, h⟩

@[simp] theorem tmSort_tVFNumeral : ∀ k : ℕ, TmSort sα sn (tVFNumeral (n := n) k) = some .vf
  | 0 => tmSort_tVFZero sα sn
  | k + 1 => by
    rw [tVFNumeral, tmSort_tVFAdd]
    exact ⟨tmSort_tVFNumeral k, tmSort_tVFOne sα sn⟩

end Powers


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

def sdRVInv : LRV.Sentence := allSorted ![.rv] (pRVsort (tRVInv &0))
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
    sdRVZero, sdRVInfty, sdRVOne, sdRVMul, sdRVInv, sdUnits, sdKAdd, sdKNeg, sdKMul]

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

/-! ### 3.6a The repaired axioms: `RV^×` is a group, the order scales, the residue field is
the residue field, and the valuation is nontrivial

Each sentence below is **added** to Definition 2.2's axioms, never substituted for one: every
`ACVF`-theorem proved before the repair stays proved, and each added sentence is true in the
intended structure.  They exist because the transcription of Definition 2.2 left four things unsaid,
and a model violating each of them refutes Theorem 2.3 (see `QE-PLAN.md` for the three explicit
refutations):

* `rvMulOneRV`, `rvMulInvRV` — item 2 makes `(RV^×, 1, ×)` a divisible **group**, i.e. decidability
  of `rv`-equality needs cancellation by any nonzero element, not only by units;
* `leMulCompatFull` — item 5 makes `RV/Kˣ = Γ` an **ordered** group, i.e. the order is invariant
  under scaling by any `c ≠ rv 0`, not only by `Kˣ` (which is the identity class of `Γ`);
* `kAddLink`, `kNegLink`, `rvEqLink`, `kJunkZero`, `kNegJunkZero` — items 3 and 6 say `K` is *the
  residue field* of `vv = vrv ∘ rv`; without a link through `rv`, `kAdd` may be any field addition
  on `K` sharing `×`, and twisting it by an automorphism of `(K^×, ·)` preserves every axiom while
  destroying quantifier elimination;
* `axNontrivialRV` — the target theorems are false for a trivially valued field: trivially and
  nontrivially valued fields of the same residue characteristic agree on every quantifier-free
  `L_RV` sentence, because closed terms are numerals and `rv` of numerals.
-/

/-- `1` is neutral for `×` on every nonzero `RV`-element. -/
def rvMulOneRV : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pEq (tRVMul tRVOne &0) &0)

/-- every nonzero `RV`-element is invertible in `RV^×`. -/
def rvMulInvRV : LRV.Sentence :=
  allSorted ![.rv] (pRV &0 ⟹ exSorted .rv (pRV &1 ⊓ pEq (tRVMul &1 &0) tRVOne))

/-- the order on `RV` is invariant under scaling by any `c ≠ rv 0`, in both directions.  The guards
on the first two variables are dropped because `∞ = rv 0` is absorbing and top, so both sides hold
there. -/
def leMulCompatFull : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv] (pRV &2 ⟹ (pLe &0 &1 ⇔ pLe (tRVMul &0 &2) (tRVMul &1 &2)))

/-- `kAdd` is the residue addition at units: `rv (x + y)` if that is a unit, and `0` if `x + y`
drops into the maximal ideal. -/
def kAddLink : LRV.Sentence :=
  allSorted ![.vf, .vf]
    (pUnits (tRv &0) ⟹ (pUnits (tRv &1) ⟹
      ((pUnits (tRv (tVFAdd &0 &1)) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) (tRv (tVFAdd &0 &1))) ⊓
        (∼(pUnits (tRv (tVFAdd &0 &1))) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) tRVZero))))

/-- `kNeg` is the residue negation at units. -/
def kNegLink : LRV.Sentence :=
  allSorted ![.vf] (pUnits (tRv &0) ⟹ pEq (tKNeg (tRv &0)) (tRv (tVFNeg &0)))

/-- two elements of `VF` have the same residue iff their difference has strictly larger value than
the second: `rv a = rv b ↔ ¬ (v (a - b) ≤ v b)`.  (The first transcription had the two `pLe`
arguments transposed, which made the axiom false at `a = b = 1` and the whole theory
inconsistent — see `QE-PLAN.md` and `.ultramath/smw163dd5/m5/Audit.lean`.) -/
def rvEqLink : LRV.Sentence :=
  allSorted ![.vf, .vf]
    (∼(pEq &1 tVFZero) ⟹
      (pEq (tRv &0) (tRv &1) ⇔ ∼(pLe (tRv (tVFAdd &0 (tVFNeg &1))) (tRv &1))))

/-- the junk convention for `kAdd` off `K`: the value is `0`. -/
def kJunkZero : LRV.Sentence :=
  allSorted ![.rv, .rv] ((∼(pInK &0) ⊔ ∼(pInK &1)) ⟹ pEq (tKAdd &0 &1) tRVZero)

/-- the junk convention for `kNeg` off `K`. -/
def kNegJunkZero : LRV.Sentence := allSorted ![.rv] (∼(pInK &0) ⟹ pEq (tKNeg &0) tRVZero)

/-- **Nontriviality**: some nonzero element of `VF` has value strictly below the value of `1`,
i.e. lies in the maximal ideal. -/
def axNontrivialRV : LRV.Sentence :=
  exSorted .vf (∼(pEq &0 tVFZero) ⊓ ∼(pLe (tRv &0) (tRv tVFOne)))

/-- The inverse operation fixes the absorbing element `0 = ∞`. -/
def rvInvZero : LRV.Sentence := pEq (tRVInv tRVZero) tRVZero

/-- The named inverse is a multiplicative inverse on the nonzero `RV` group. -/
def rvInvMul : LRV.Sentence :=
  allSorted ![.rv] (pRV &0 ⟹ pEq (tRVMul (tRVInv &0) &0) tRVOne)

/-- The added axioms, in one theory. -/
def repairRV : LRV.Theory :=
  ofList [rvMulOneRV, rvMulInvRV, leMulCompatFull, kAddLink, kNegLink, rvEqLink, kJunkZero,
    kNegJunkZero, axNontrivialRV, rvInvZero, rvInvMul]

/-- the paper's own content of `ACVF`: Definition 2.2, items 1–6 -/
def ACVFpaper : LRV.Theory :=
  vfField ∪ vfAlgClosed ∪ rvGroup ∪ kField ∪ kAlgClosed ∪ preorderRV ∪ rvAxioms ∪ repairRV ∪ repairRV

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

/-! ### 6.0 `WellSorted` is the recursive predicate of Part 2

Until this revision the file carried, here, a *second* definition of the well-sorted fragment: the
sorted syntax `STm`/`SBf` of the paper's two-sorted `L_RV`, its translation `STm.toLRV`/`SBf.toLRV`
into the one-sorted encoding, and `WellSorted sα sn φ := ∃ ψ : SBf sα sn, ψ.toLRV = φ`.  That
definition is **replaced** by the recursive predicate `LRV.WellSorted` of Part 2 (`TmSort` with
`none` = junk, `Occurs`, `GuardsLast`), and the sorted syntax is deleted: it is dead.

Why the replacement is safe, and in which direction:

* the recursive predicate accepts every atom of the image (`TmSort` is `some s` for a sorted term,
  and `GuardsLast` fires on the guard that `SBf.all` emits — `wellSorted_all_guarded`), and it is
  closed under the connectives (`wellSorted_inf`, `wellSorted_not`, …) and under the guarded
  quantifiers (`wellSorted_allSorted`, `wellSorted_allSortedK`, `wellSorted_allOne`,
  `wellSorted_exSortedK`), which is what the frozen statements and the QE tree consume;
* it is what the *proofs* can use: the paper's axioms and the tree's translations are formulas
  built by `allSorted`/`allSortedK`/`allOne` over sorted atoms, so what they need is a predicate
  that is closed under exactly those constructions — see Part 6.1 for `ACVF` sentence by sentence;
* where it is *narrower* is exactly the encoding's own three carrier sentences, and that costs
  nothing the paper stated: `Axioms.sdCover` (`∀x, x ∈ VF ∨ x ∈ RV`) and `Axioms.sdDisjoint`
  (`∀x, ¬(x ∈ VF ∧ x ∈ RV)`) mention one variable at **two** sorts, so no assignment of a sort to
  the bound variable makes the body well-sorted, and `Axioms.sdUnits` (`∀x, Kˣ(x) → x ∈ RV`) does
  have a well-sorted body (at `x : RV`) but no *guard* — its antecedent is `Kˣ(x)`, not the sort
  predicate of `x`, so `GuardsLast` does not fire.  These three describe the one-sorted carrier of
  the encoding and are not formulas of the paper's language, which is why `wellSorted_ACVF` in
  Part 6.1 excludes them and why `ACVF`'s axioms *of the paper* need no exclusion at all.

`WellSorted` is **not** guarded on the parameters syntactically: the frozen `HasQE` and
`IsCMinimalWS` keep the semantic relativisation by `sortEval` below, which is a statement about
*all* parameter types `α`, with no `[Fintype α]` and no `⋀ a, v a ∈ sα a` hypothesis.  The
recursive predicate does not mention `α`'s finiteness at all: the only place `α` enters is the
`Term.var (Sum.inl a)` clause of `TmSort`, which reads the declared sort `sα a`.  (A syntactic
parameter guard would have to be a finite conjunction, hence need `[Fintype α]`; the semantic
guard does not, and it is the one the frozen statements are written with.)
-/

open LRV
/-- Whether an element of a model has a given sort. -/
def sortEval {M : Type*} [LRV.Structure M] : SortTag → M → Prop
  | .vf => fun x => Structure.RelMap (L := LRV) Rel.memVF ![x]
  | .rv => fun x => Structure.RelMap (L := LRV) Rel.memRV ![x]

/-- A theory `T` of `L_RV` **admits quantifier elimination on the well-sorted fragment**: every
formula of the paper's two-sorted language — a `WellSorted` formula of the one-sorted encoding —
is `T`-equivalent, at tuples respecting the declared sorts, to a quantifier-free formula of the same
fragment.  This is the paper's Theorem 2.3 ("the theory `ACVF` admits quantifier elimination"),
stated for the two-sorted `L_RV` it is about: the encoding's carrier admits ill-sorted terms such
as `rv (rv x)`, whose values no axiom fixes, and those are not formulas of the paper's language. -/
def HasQE (T : LRV.Theory) : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (φ : LRV.BoundedFormula α n), WellSorted sα sn φ →
    ∃ ψ : LRV.BoundedFormula α n, ψ.IsQF ∧ WellSorted sα sn ψ ∧
      ∀ (M : Type) [LRV.Structure M], M ⊨ T → ∀ (v : α → M) (x : Fin n → M),
        (∀ a, sortEval (sα a) (v a)) → (∀ i, sortEval (sn i) (x i)) →
        (φ.Realize v x ↔ ψ.Realize v x)

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

/-- The interpretation of the named inverse on `RV`.  The suffix distinguishes this
symbol from any inverse constructed by choice in the algebraic transfer modules. -/
def iRVInvFn (x : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvInv ![x]

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

/-- **Theorem 2.3** (Yin, *Special transformations in algebraically closed valued
fields*, APAL 2010; quoted there from arXiv:1006.1393, Theorem 3.10): the theory `ACVF`
admits quantifier elimination. The theorem with the original name is proved
downstream in `QE/LocalQE/Theorem23.lean`, so the encoding does not import its
own proof dependencies. Its only hypotheses are the authorized standard
model-theoretic and valued-field results, stated explicitly there. -/
abbrev Theorem23Goal : Prop := HasQE ACVF

/-- **C-minimality over well-sorted parameters**: every subset of the `VF` sort defined by a
formula of the paper's two-sorted language — well-sorted `φ` with one free `VF`-variable and
parameters of declared sorts — is a finite Boolean combination of balls.  This is Definition 2.7
with the same restriction the target `HasQE` carries: the encoding's carrier admits ill-sorted
terms and ill-sorted parameters, and for those the statement is false, so the frozen target is
stated for the paper's own language. -/
def IsCMinimalWS (M : Type*) [LRV.Structure M] : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (φ : LRV.BoundedFormula α 1),
    WellSorted sα (fun _ => SortTag.vf) φ →
    ∀ (v : α → M), (∀ a, sortEval (sα a) (v a)) →
      IsBoolComb {b | IsBall b} {x : M | iVF x ∧ φ.Realize v ![x]}

/-- **Definability by a formula of the paper's language**: `s ⊆ VF` is cut out by a well-sorted
formula with one free `VF`-variable and parameters of declared sorts.  This is Mathlib's
`Set.Definable₁` restricted to the formulas the paper's two-sorted `L_RV` actually has — the encoding
admits ill-sorted terms, whose values no axiom fixes, so unrestricted definability is the wrong
notion here. -/
def DefinableVF (M : Type*) [LRV.Structure M] (s : Set M) : Prop :=
  ∃ (α : Type) (sα : α → SortTag) (φ : LRV.BoundedFormula α 1) (v : α → M),
    (∀ a, sortEval (sα a) (v a)) ∧ WellSorted sα (fun _ => SortTag.vf) φ ∧
      s = {x : M | iVF x ∧ φ.Realize v ![x]}

/-- **C-minimality in set form** — the well-sorted `IsCMinimalVF`: every subset of the `VF` sort
definable by a formula of the paper's language, with parameters from either sort, is a finite
Boolean combination of balls.  (m3's `IsCMinimalVF` is this with *unrestricted* definability, which
is stronger and can fail through junk terms; the direction of the implication below is therefore
`IsCMinimalWS → IsCMinimalVFWS`, not the converse.) -/
def IsCMinimalVFWS (M : Type*) [LRV.Structure M] : Prop :=
  ∀ s : Set M, DefinableVF M s → IsBoolComb {b | IsBall b} s

/-- **The frozen target implies the set form.** -/
theorem isCMinimalVFWS_of_isCMinimalWS {M : Type*} [LRV.Structure M]
    (h : IsCMinimalWS M) : IsCMinimalVFWS M := by
  rintro s ⟨α, sα, φ, v, hv, hws, hs⟩
  rw [hs]
  exact h α sα φ hws v hv

/-- **Theorem 2.8** (Yin, op. cit.; quoted from arXiv:1006.1393, Theorem 4.2):
`ACVF` is C-minimal, i.e. every model of `ACVF` is C-minimal in the sense of
Definition 2.7, for the formulas of the paper's two-sorted language (`IsCMinimalWS`). -/
theorem theorem_2_8_c_minimal :
    ∀ (M : Type) [LRV.Structure M] [Nonempty M], M ⊨ ACVF → IsCMinimalWS M := by
  sorry

/-! ## Part 6.1 The audit: `ACVF`'s axioms are well-sorted

`HasQE` and `IsCMinimalWS` above are stated over `WellSorted`.  Adopting the recursive predicate
(the replacement recorded in 6.0) would lose a theorem only if some sentence the earlier
image-of-sorted-syntax predicate accepted were rejected by the recursive one, and only if a proof
relied on that.  Nothing in the file was proved *about* `WellSorted` before — it occurs in the two
frozen statements only — so what has to be checked is that the previous definition's instances are
still instances.  This part does that on the objects the QE transfer consumes: **every sentence of
`ACVF`** (Definition 2.2, its sort discipline, and the `repairRV` sentences), plus the shapes of the
tree's syntactic translations (6.2).

Two facts about the shape of the audit:

* the axioms are `allSorted ss φ` / `allSortedK ss φ` / `allOne φ` / `exSorted` / `exSortedK`
  sentences over atoms built from the Part 1 constructors, and the recursive predicate has a clause
  for exactly those (`wellSorted_allSorted`, `wellSorted_allSortedK`, `wellSorted_allOne`,
  `wellSorted_exSortedK`), so "well-sorted" reduces to "every atom is sorted", which is `TmSort` of
  a constructor — a `simp` computation with the lemmas of Part 2b;
* the three sentences of the *sort discipline* are the interesting case, and they split:
  `sdCover` and `sdDisjoint` (whose guard is the encoding's own sort predicate) **are** well-sorted
  recursively and were **not** in the image of `SBf`; `sdUnits`, `∀x, Kˣ(x) → x ∈ RV`, is in
  neither (its antecedent is not the sort predicate of a variable, so no guard fires).  So the
  recursive predicate is strictly larger on these three, and `ACVF` = `sortAxioms ∪ ACVFpaper`
  contains exactly one sentence outside the fragment: `sdUnits`. -/

namespace Audit

open LRV Axioms

/-- `φ` is a well-sorted *sentence* of the paper's two-sorted language.  The parameter type is
`Empty` and the sort assignment there is the empty one; the choice of `sα : Empty → SortTag` is
irrelevant (`Empty` has one function into any type), and fixing it keeps the audit's statements
closed. -/
abbrev WSSent (φ : LRV.Sentence) : Prop :=
  WellSorted (fun i : Empty => Empty.elim i) (fun i : Fin 0 => i.elim0) φ

/-! ### 6.1.0 Transport and the Horner term -/

/-- transport `WellSorted` along an equality of sort assignments -/
theorem ws_congr {α : Type} {sα : α → SortTag} {n : ℕ} {sn sn' : Fin n → SortTag}
    {φ : LRV.BoundedFormula α n} (h : sn = sn') (hφ : WellSorted sα sn φ) :
    WellSorted sα sn' φ := h ▸ hφ

/-- the context a quantified body of `Axioms.acfScheme` lives in: `∀`-extension of a constant `VF`
tuple is the constant `VF` tuple -/
theorem snoc_const_vf (k : ℕ) :
    (Fin.snoc (fun _ : Fin k => SortTag.vf) SortTag.vf : Fin (k + 1) → SortTag) =
      fun _ => SortTag.vf := by
  simpa using fin_snoc_castSucc_last (ss := fun _ : Fin (k + 1) => SortTag.vf)

/-- the same for `RV` -/
theorem snoc_const_rv (k : ℕ) :
    (Fin.snoc (fun _ : Fin k => SortTag.rv) SortTag.rv : Fin (k + 1) → SortTag) =
      fun _ => SortTag.rv := by
  simpa using fin_snoc_castSucc_last (ss := fun _ : Fin (k + 1) => SortTag.rv)

/-- `Fin.snoc` of the one-variable `VF` context: the context an `∃`-quantified body lives in -/
theorem snoc_vf1 : (Fin.snoc ![SortTag.vf] SortTag.vf : Fin 2 → SortTag) =
    ![SortTag.vf, SortTag.vf] := by
  funext i; fin_cases i <;> simp [Fin.snoc]

/-- `Fin.snoc` of the one-variable `RV` context -/
theorem snoc_rv1 : (Fin.snoc ![SortTag.rv] SortTag.rv : Fin 2 → SortTag) =
    ![SortTag.rv, SortTag.rv] := by
  funext i; fin_cases i <;> simp [Fin.snoc]

/-- `Fin.snoc` of `RV` extended by a `VF`-variable (`rvSurj`) -/
theorem snoc_rv_vf : (Fin.snoc ![SortTag.rv] SortTag.vf : Fin 2 → SortTag) =
    ![SortTag.rv, SortTag.vf] := by
  funext i; fin_cases i <;> simp [Fin.snoc]

/-- `Fin.snoc` of the empty context (`axNontrivialRV`) -/
theorem snoc_empty_vf : (Fin.snoc (fun i : Fin 0 => i.elim0) SortTag.vf : Fin 1 → SortTag) =
    ![SortTag.vf] := by
  funext i; fin_cases i <;> simp [Fin.snoc]

/-- the Horner fold of `hornerPoly` preserves `TmSort … = some .vf` -/
theorem tmSort_hornerFoldl {n : ℕ} (x : Tm (n + 1 + 1))
    (hx : TmSort (fun i : Empty => Empty.elim i) (fun _ : Fin (n + 1 + 1) => .vf) x = some .vf) :
    ∀ (l : List (Fin n)) (acc : Tm (n + 1 + 1)),
      TmSort (fun i : Empty => Empty.elim i) (fun _ : Fin (n + 1 + 1) => .vf) acc = some .vf →
      TmSort (fun i : Empty => Empty.elim i) (fun _ : Fin (n + 1 + 1) => .vf)
        (l.foldl (fun acc i => tVFAdd (tVFMul acc x) (tv (n := n + 1 + 1) i.val (by omega))) acc) =
        some .vf
  | [], acc, hacc => hacc
  | i :: l, acc, hacc => by
    rw [List.foldl_cons]
    refine tmSort_hornerFoldl x hx l _ ?_
    rw [tmSort_tVFAdd, tmSort_tVFMul]
    exact ⟨⟨hacc, hx⟩, by simp⟩

/-- the Horner fold of `hornerPoly` at the residue field `K`: `TmSort … = some .rv` -/
theorem tmSort_hornerFoldlK {n : ℕ} (x : Tm (n + 1 + 1))
    (hx : TmSort (fun i : Empty => Empty.elim i) (fun _ : Fin (n + 1 + 1) => .rv) x = some .rv) :
    ∀ (l : List (Fin n)) (acc : Tm (n + 1 + 1)),
      TmSort (fun i : Empty => Empty.elim i) (fun _ : Fin (n + 1 + 1) => .rv) acc = some .rv →
      TmSort (fun i : Empty => Empty.elim i) (fun _ : Fin (n + 1 + 1) => .rv)
        (l.foldl (fun acc i => tKAdd (tRVMul acc x) (tv (n := n + 1 + 1) i.val (by omega))) acc) =
        some .rv
  | [], acc, hacc => hacc
  | i :: l, acc, hacc => by
    rw [List.foldl_cons]
    refine tmSort_hornerFoldlK x hx l _ ?_
    rw [tmSort_tKAdd, tmSort_tRVMul]
    exact ⟨⟨hacc, hx⟩, by simp⟩

/-- **the Horner polynomial of `K` is an `RV`-term** -/
@[simp] theorem tmSort_hornerPolyK (k : ℕ) :
    TmSort (fun i : Empty => Empty.elim i) (fun _ : Fin (k + 1) => .rv)
      (hornerPoly tKAdd tRVMul) = some .rv := by
  match k with
  | 0 => rw [hornerPoly]; exact tmSort_tv' _ _ 0 _
  | m + 1 =>
    rw [hornerPoly]
    refine tmSort_hornerFoldlK (n := m) (tv (n := m + 1 + 1) (m + 1) (by omega)) ?_ _ _ ?_
    · exact tmSort_tv' _ _ (m + 1) (by omega)
    · rw [tmSort_tKAdd]
      exact ⟨tmSort_tv' _ _ (m + 1) (by omega), tmSort_tv' _ _ m (by omega)⟩

/-- **the Horner polynomial is a `VF`-term** (of the context of the coefficients) -/
@[simp] theorem tmSort_hornerPoly (k : ℕ) :
    TmSort (fun i : Empty => Empty.elim i) (fun _ : Fin (k + 1) => .vf)
      (hornerPoly tVFAdd tVFMul) = some .vf := by
  match k with
  | 0 => rw [hornerPoly]; exact tmSort_tv' _ _ 0 _
  | m + 1 =>
    rw [hornerPoly]
    refine tmSort_hornerFoldl (n := m) (tv (n := m + 1 + 1) (m + 1) (by omega)) ?_ _ _ ?_
    · exact tmSort_tv' _ _ (m + 1) (by omega)
    · rw [tmSort_tVFAdd]
      exact ⟨tmSort_tv' _ _ (m + 1) (by omega), tmSort_tv' _ _ m (by omega)⟩

/-! ### 6.1.1 The sort discipline, `Axioms.sortClosure` -/

theorem wss_sdVFZero : WSSent Axioms.sdVFZero := by
  unfold Axioms.sdVFZero
  exact wellSorted_pVFG _ _ (by simp)

theorem wss_sdVFOne : WSSent Axioms.sdVFOne := by
  unfold Axioms.sdVFOne
  exact wellSorted_pVFG _ _ (by simp)

theorem wss_sdVFAdd : WSSent Axioms.sdVFAdd := by
  unfold Axioms.sdVFAdd
  apply wellSorted_allSorted
  exact wellSorted_pVFG _ _ (by simp)

theorem wss_sdVFNeg : WSSent Axioms.sdVFNeg := by
  unfold Axioms.sdVFNeg
  apply wellSorted_allSorted
  exact wellSorted_pVFG _ _ (by simp)

theorem wss_sdVFMul : WSSent Axioms.sdVFMul := by
  unfold Axioms.sdVFMul
  apply wellSorted_allSorted
  exact wellSorted_pVFG _ _ (by simp)

theorem wss_sdRv : WSSent Axioms.sdRv := by
  unfold Axioms.sdRv
  apply wellSorted_allSorted
  exact wellSorted_pRVG _ _ (by simp)

theorem wss_sdRVZero : WSSent Axioms.sdRVZero := by
  unfold Axioms.sdRVZero
  exact wellSorted_pRVG _ _ (by simp)

theorem wss_sdRVInfty : WSSent Axioms.sdRVInfty := by
  unfold Axioms.sdRVInfty
  exact wellSorted_pRVG _ _ (by simp)

theorem wss_sdRVOne : WSSent Axioms.sdRVOne := by
  unfold Axioms.sdRVOne
  exact wellSorted_pRVG _ _ (by simp)

theorem wss_sdRVMul : WSSent Axioms.sdRVMul := by
  unfold Axioms.sdRVMul
  apply wellSorted_allSorted
  exact wellSorted_pRVG _ _ (by simp)

theorem wss_sdRVInv : WSSent Axioms.sdRVInv := by
  unfold Axioms.sdRVInv
  apply wellSorted_allSorted
  exact wellSorted_pRVG _ _ (by simp)

theorem wss_sdKAdd : WSSent Axioms.sdKAdd := by
  unfold Axioms.sdKAdd
  apply wellSorted_allSorted
  exact WellSorted.imp _ (wellSorted_pInK (by simp)) (WellSorted.imp _ (wellSorted_pInK (by simp))
    (wellSorted_pInK (by simp)))

theorem wss_sdKNeg : WSSent Axioms.sdKNeg := by
  unfold Axioms.sdKNeg
  apply wellSorted_allSorted
  exact WellSorted.imp _ (wellSorted_pInK (by simp)) (wellSorted_pInK (by simp))

theorem wss_sdKMul : WSSent Axioms.sdKMul := by
  unfold Axioms.sdKMul
  apply wellSorted_allSorted
  exact WellSorted.imp _ (wellSorted_pInK (by simp)) (WellSorted.imp _ (wellSorted_pInK (by simp))
    (wellSorted_pInK (by simp)))

/-! ### 6.1.2 The two field axiom lists, `Axioms.fieldAxioms` -/

/-- the ten field axioms of `Axioms.fieldAxioms .vf …`, i.e. `Axioms.vfField` -/
theorem wss_vfField : ∀ t ∈ Axioms.vfField, WSSent t := by
  intro t ht
  simp only [Axioms.vfField, Axioms.ofList, Set.mem_ofPred_eq, Axioms.fieldAxioms,
    List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply wellSorted_allSorted
    exact wellSorted_pEqG (s := .vf) _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    exact wellSorted_pEqG (s := .vf) _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    exact wellSorted_pEqG (s := .vf) _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    exact wellSorted_pEqG (s := .vf) _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    exact wellSorted_pEqG (s := .vf) _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    exact wellSorted_pEqG (s := .vf) _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    exact wellSorted_pEqG (s := .vf) _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    exact wellSorted_pEqG (s := .vf) _ _ (by simp) (by simp)
  · exact wellSorted_not _ _ (wellSorted_pEqG (s := .vf) _ _ (by simp) (by simp))
  · apply wellSorted_allSorted
    refine wellSorted_sup _ _ (wellSorted_pEqG (s := .vf) _ _ (by simp) (by simp)) ?_
    refine wellSorted_exSorted _ (ss := ![SortTag.vf]) ?_
    rw [snoc_vf1]
    exact wellSorted_pEqG (s := .vf) _ _ (by simp) (by simp)

/-- `Axioms.vfAlgClosed`, the algebraic-closedness scheme of the `VF` sort -/
theorem wss_vfAlgClosed (k : ℕ) (_hk : 1 ≤ k) :
    WSSent (Axioms.acfScheme .vf tVFZero tVFAdd tVFMul k) := by
  unfold Axioms.acfScheme
  apply wellSorted_allSorted
  refine wellSorted_exSorted _ (ss := fun _ : Fin k => .vf) (s := .vf) ?_
  rw [snoc_const_vf]
  exact wellSorted_pEqG (s := .vf) _ _ (by simp) (by simp)

/-! ### 6.1.3 The residue field `K = K^× ∪ {0}`, `Axioms.kField` and `Axioms.acfSchemeK` -/

/-- the ten field axioms of `Axioms.kField`, guarded by `allSortedK` -/
theorem wss_kField : ∀ t ∈ Axioms.kField, WSSent t := by
  intro t ht
  simp only [Axioms.kField, Axioms.ofList, Set.mem_ofPred_eq, List.mem_cons,
    List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply wellSorted_allSortedK_ss _ (hss := by intro i; fin_cases i <;> rfl)
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · apply wellSorted_allSortedK_ss _ (hss := by intro i; fin_cases i <;> rfl)
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · apply wellSorted_allSortedK_ss _ (hss := by intro i; fin_cases i <;> rfl)
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · apply wellSorted_allSortedK_ss _ (hss := by intro i; fin_cases i <;> rfl)
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · apply wellSorted_allSortedK_ss _ (hss := by intro i; fin_cases i <;> rfl)
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · apply wellSorted_allSortedK_ss _ (hss := by intro i; fin_cases i <;> rfl)
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · apply wellSorted_allSortedK_ss _ (hss := by intro i; fin_cases i <;> rfl)
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · apply wellSorted_allSortedK_ss _ (hss := by intro i; fin_cases i <;> rfl)
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · exact wellSorted_not _ _ (wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp))
  · apply wellSorted_allSortedK_ss _ (hss := by intro i; fin_cases i <;> rfl)
    refine wellSorted_sup _ _ (wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)) ?_
    refine wellSorted_exSortedK _ ?_
    rw [snoc_rv1]
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)

/-- `Axioms.kAlgClosed`, the algebraic-closedness scheme of `K = K^× ∪ {0}` -/
theorem wss_kAlgClosed (k : ℕ) (_hk : 1 ≤ k) : WSSent (Axioms.acfSchemeK k) := by
  unfold Axioms.acfSchemeK
  apply wellSorted_allSortedK
  refine wellSorted_exSortedK_k _ ?_
  exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)

/-! ### 6.1.4 The `RV` group, `Axioms.rvGroup` -/

theorem wss_rvGroup : ∀ t ∈ Axioms.rvGroup, WSSent t := by
  intro t ht
  simp only [Axioms.rvGroup, Set.mem_union, Set.mem_ofPred_eq, Axioms.ofList,
    List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, _hk, hkk⟩
  · exact wellSorted_pUnitsG _ _ (by simp)
  · apply wellSorted_allSorted
    refine WellSorted.imp _ (wellSorted_pUnitsG _ _ (by simp)) (WellSorted.imp _ (wellSorted_pUnitsG _ _ (by simp)) ?_)
    exact wellSorted_pUnitsG _ _ (by simp)
  · apply wellSorted_allSorted
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    exact WellSorted.imp _ (wellSorted_pUnitsG _ _ (by simp))
      (wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp))
  · apply wellSorted_allSorted
    refine WellSorted.imp _ (wellSorted_pUnitsG _ _ (by simp)) ?_
    refine wellSorted_exSorted _ (ss := ![SortTag.rv]) ?_
    rw [snoc_rv1]
    exact wellSorted_inf _ _ (wellSorted_pUnitsG _ _ (by simp))
      (wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp))
  · apply wellSorted_allSorted
    refine WellSorted.imp _ (wellSorted_pInK (by simp)) ?_
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · rw [hkk]
    apply wellSorted_allSorted
    refine WellSorted.imp _ (wellSorted_pUnitsG _ _ (by simp)) ?_
    refine wellSorted_exSorted _ (ss := ![SortTag.rv]) ?_
    rw [snoc_rv1]
    refine wellSorted_inf _ _ (wellSorted_pUnitsG _ _ (by simp)) ?_
    exact wellSorted_pEqG (s := .rv) _ _ (by rw [tmSort_tRVPow]; exact (by simp))
      (by simp)

/-! ### 6.1.5 The preorder, `Axioms.preorderRV` -/

theorem wss_preorderRV : ∀ t ∈ Axioms.preorderRV, WSSent t := by
  intro t ht
  simp only [Axioms.preorderRV, Axioms.ofList, Set.mem_ofPred_eq, List.mem_cons,
    List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply wellSorted_allSorted
    exact WellSorted.imp _ (wellSorted_pRV' (by simp)) (wellSorted_pLeG _ _ (by simp) (by simp))
  · apply wellSorted_allSorted
    refine WellSorted.imp _ (wellSorted_pRV' (by simp)) (WellSorted.imp _ (wellSorted_pRV' (by simp))
      (WellSorted.imp _ (wellSorted_pRV' (by simp)) (WellSorted.imp _ (wellSorted_pLeG _ _ (by simp) (by simp))
      (WellSorted.imp _ (wellSorted_pLeG _ _ (by simp) (by simp)) ?_)))) 
    exact wellSorted_pLeG _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    refine WellSorted.imp _ (wellSorted_pRV' (by simp)) (WellSorted.imp _ (wellSorted_pRV' (by simp)) ?_)
    exact wellSorted_sup _ _ (wellSorted_pLeG _ _ (by simp) (by simp)) (wellSorted_pLeG _ _ (by simp) (by simp))
  · apply wellSorted_allSorted
    exact WellSorted.imp _ (wellSorted_pRV' (by simp)) (wellSorted_pLeG _ _ (by simp) (by simp))
  · apply wellSorted_allSorted
    refine WellSorted.imp _ (wellSorted_pRV' (by simp)) (WellSorted.imp _ (wellSorted_pLeG _ _ (by simp) (by simp)) ?_)
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    refine WellSorted.imp _ (wellSorted_pRV' (by simp)) ?_
    exact wellSorted_iff _ _ (wellSorted_pUnitsG _ _ (by simp))
      (wellSorted_inf _ _ (wellSorted_pLeG _ _ (by simp) (by simp)) (wellSorted_pLeG _ _ (by simp) (by simp)))
  · apply wellSorted_allSorted
    refine WellSorted.imp _ (wellSorted_pRV' (by simp)) (WellSorted.imp _ (wellSorted_pRV' (by simp))
      (WellSorted.imp _ (wellSorted_pRV' (by simp)) (WellSorted.imp _ (wellSorted_pUnitsG _ _ (by simp))
      (WellSorted.imp _ (wellSorted_pLeG _ _ (by simp) (by simp)) ?_))))
    exact wellSorted_pLeG _ _ (by simp) (by simp)

/-! ### 6.1.6 The projection `rv`, `Axioms.rvAxioms` -/

theorem wss_rvAxioms : ∀ t ∈ Axioms.rvAxioms, WSSent t := by
  intro t ht
  simp only [Axioms.rvAxioms, Axioms.ofList, Set.mem_ofPred_eq, List.mem_cons,
    List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    exact WellSorted.imp _ (wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp))
      (wellSorted_pEqG (s := .vf) _ _ (by simp) (by simp))
  · apply wellSorted_allSorted
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    refine WellSorted.imp _ (wellSorted_not _ _ (wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp))) ?_
    refine wellSorted_exSorted _ (ss := ![SortTag.rv]) ?_
    rw [snoc_rv_vf]
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    exact wellSorted_sup _ _ (wellSorted_pLeG _ _ (by simp) (by simp)) (wellSorted_pLeG _ _ (by simp) (by simp))

/-! ### 6.1.7 The repaired axioms, `Axioms.repairRV` -/

theorem wss_repairRV : ∀ t ∈ Axioms.repairRV, WSSent t := by
  intro t ht
  simp only [Axioms.repairRV, Axioms.ofList, Set.mem_ofPred_eq, List.mem_cons,
    List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply wellSorted_allSorted
    exact WellSorted.imp _ (wellSorted_pRV' (by simp)) (wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp))
  · apply wellSorted_allSorted
    refine WellSorted.imp _ (wellSorted_pRV' (by simp)) ?_
    refine wellSorted_exSorted _ (ss := ![SortTag.rv]) ?_
    rw [snoc_rv1]
    exact wellSorted_inf _ _ (wellSorted_pRV' (by simp)) (wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp))
  · apply wellSorted_allSorted
    refine WellSorted.imp _ (wellSorted_pRV' (by simp)) ?_
    exact wellSorted_iff _ _ (wellSorted_pLeG _ _ (by simp) (by simp)) (wellSorted_pLeG _ _ (by simp) (by simp))
  · apply wellSorted_allSorted
    refine WellSorted.imp _ (wellSorted_pUnitsG _ _ (by simp)) (WellSorted.imp _ (wellSorted_pUnitsG _ _ (by simp)) ?_)
    exact wellSorted_inf _ _ (WellSorted.imp _ (wellSorted_pUnitsG _ _ (by simp)) (wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)))
      (WellSorted.imp _ (wellSorted_not _ _ (wellSorted_pUnitsG _ _ (by simp))) (wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)))
  · apply wellSorted_allSorted
    exact WellSorted.imp _ (wellSorted_pUnitsG _ _ (by simp)) (wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp))
  · apply wellSorted_allSorted
    refine WellSorted.imp _ (wellSorted_not _ _ (wellSorted_pEqG (s := .vf) _ _ (by simp) (by simp))) ?_
    exact wellSorted_iff _ _ (wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp))
      (wellSorted_not _ _ (wellSorted_pLeG _ _ (by simp) (by simp)))
  · apply wellSorted_allSorted
    refine WellSorted.imp _ (wellSorted_sup _ _ (wellSorted_not _ _ (wellSorted_pInK (by simp)))
      (wellSorted_not _ _ (wellSorted_pInK (by simp)))) ?_
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    exact WellSorted.imp _ (wellSorted_not _ _ (wellSorted_pInK (by simp))) (wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp))
  · refine wellSorted_exSorted _ (ss := fun i : Fin 0 => i.elim0) (s := .vf) ?_
    rw [snoc_empty_vf]
    exact wellSorted_inf _ _ (wellSorted_not _ _ (wellSorted_pEqG (s := .vf) _ _ (by simp) (by simp)))
      (wellSorted_not _ _ (wellSorted_pLeG _ _ (by simp) (by simp)))
  · unfold Axioms.rvInvZero
    exact wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp)
  · apply wellSorted_allSorted
    exact WellSorted.imp _ (wellSorted_pRV' (by simp))
      (wellSorted_pEqG (s := .rv) _ _ (by simp) (by simp))

/-! ### 6.1.8 The sort discipline as a theory, and the characteristic -/

/-- every sentence of `Axioms.sortClosure` except `sdUnits` is well-sorted (`sdUnits` is the one
sentence of the sort discipline that the recursive predicate rejects: its antecedent is `Kˣ(x)`, not
the sort predicate of the variable, so no guard fires — see the discussion in 6.0) -/
theorem wss_sortClosure : ∀ t ∈ Axioms.sortClosure, t ≠ Axioms.sdUnits → WSSent t := by
  intro t ht hne
  simp only [Axioms.sortClosure, Axioms.ofList, Set.mem_ofPred_eq, List.mem_cons,
    List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact wss_sdVFZero
  · exact wss_sdVFOne
  · exact wss_sdVFAdd
  · exact wss_sdVFNeg
  · exact wss_sdVFMul
  · exact wss_sdRv
  · exact wss_sdRVZero
  · exact wss_sdRVInfty
  · exact wss_sdRVOne
  · exact wss_sdRVMul
  · exact wss_sdRVInv
  · exact absurd rfl hne
  · exact wss_sdKAdd
  · exact wss_sdKNeg
  · exact wss_sdKMul

/-- characteristic zero of the `VF` sort -/
theorem wss_charZeroVF (k : ℕ) : WSSent (Axioms.charZeroVF k) := by
  unfold Axioms.charZeroVF
  exact wellSorted_not _ _ (wellSorted_pEqG (s := .vf) _ _ (by simp) (by simp))

/-- residue characteristic zero -/
theorem wss_residueCharZero (p : ℕ) : WSSent (Axioms.residueCharZero p) := by
  unfold Axioms.residueCharZero pGtOne
  exact wellSorted_not _ _ (wellSorted_inf _ _ (wellSorted_pLeG _ _ (by simp) (by simp))
    (wellSorted_not _ _ (wellSorted_pLeG _ _ (by simp) (by simp))))

/-! ### 6.1.9 The audit, assembled -/

/-- **every sentence of `Axioms.ACVFpaper` is well-sorted** — this is Definition 2.2 items 1–6
together with the `repairRV` sentences, i.e. every axiom the paper actually states -/
theorem wellSorted_ACVFpaper : ∀ t ∈ Axioms.ACVFpaper, WSSent t := by
  intro t ht
  simp only [Axioms.ACVFpaper, Set.mem_union, Set.mem_ofPred_eq] at ht
  rcases ht with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
  · exact wss_vfField t h
  · obtain ⟨k, hk, rfl⟩ := h
    exact wss_vfAlgClosed k hk
  · exact wss_rvGroup t h
  · exact wss_kField t h
  · obtain ⟨k, hk, rfl⟩ := h
    exact wss_kAlgClosed k hk
  · exact wss_preorderRV t h
  · exact wss_rvAxioms t h
  · exact wss_repairRV t h
  · exact wss_repairRV t h

/-- **`ACVF`'s characteristic-zero theory is well-sorted** -/
theorem wellSorted_ACVF00paper : ∀ t ∈ Axioms.ACVF00paper, WSSent t := by
  intro t ht
  simp only [Axioms.ACVF00paper, Set.mem_union, Set.mem_ofPred_eq] at ht
  rcases ht with (h | ⟨k, rfl⟩) | ⟨p, _hp, rfl⟩
  · exact wellSorted_ACVFpaper t h
  · exact wss_charZeroVF k
  · exact wss_residueCharZero p

/-- **The audit, `ACVF` itself.**  `ACVF = sortAxioms ∪ ACVFpaper` and `sortAxioms` is
`sortClosure` together with the two carrier sentences `sdCover`, `sdDisjoint`; the paper's sentences
are all well-sorted (`wellSorted_ACVFpaper`), the closure sentences are (`wss_sortClosure`), and
the only sentence of `ACVF` the recursive predicate rejects is `sdUnits`.  (`sdCover` and
`sdDisjoint` are rejected too — both mention one variable at two sorts — and are excluded by the
hypotheses below.) -/
theorem wellSorted_ACVF {t : LRV.Sentence} (ht : t ∈ Axioms.ACVF)
    (h₁ : t ≠ Axioms.sdCover) (h₂ : t ≠ Axioms.sdDisjoint) (h₃ : t ≠ Axioms.sdUnits) : WSSent t := by
  simp only [Axioms.ACVF, Axioms.sortAxioms, Set.mem_union, Set.mem_ofPred_eq, Axioms.ofList,
    List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with (h | h) | h
  · exact wss_sortClosure t h h₃
  · rcases h with rfl | rfl
    · exact absurd rfl h₁
    · exact absurd rfl h₂
  · exact wellSorted_ACVFpaper t h

end Audit

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
