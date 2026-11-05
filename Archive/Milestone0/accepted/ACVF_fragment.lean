import Mathlib
/-!
# The intended `L_RV`-structure of a valued field: the verified fragment of `ACVF`, and `Γ`

Swarm `smw06c8tw`, member `m7`.  Target: Yimu Yin, *Special transformations in algebraically
closed valued fields*, arXiv:1006.2467, Definition 2.2 and the paragraph after it; milestone
1b (a model with nontrivial `Γ(S)`).

Parts 0–3 (below, up to the first `end Axioms`) are `Milestone0/Encoding.lean` at the frozen
commit `d608de6` (sha256 `78607b94…980be6`), copied verbatim from the repository except that
`LRV` is declared `abbrev` instead of `def` — the same term, definitionally the same language;
with `def` the simp lemmas `BoundedFormula.realize_rel₁/₂` do not fire and the realization
layer does not elaborate.

On top of the frozen syntax, for an **arbitrary** valuation `v : Valuation K Γ₀` of any field
`K` (`Γ₀` a linearly ordered commutative group with zero), this file builds

* the `RV` layer `RVUnit v = Kˣ ⧸ (1+𝔪)`, `RV`, `RV₀`, `rv`, `rvMul`, `vrv`, the order
  `rvLe t s := vrv s ≤ vrv t`, and `le0` on `RV₀`;
* the carrier `C v = K ⊕ RV₀ v` with the intended interpretation of all twelve function
  symbols and the four relation symbols (`instStructure`), and the `allSorted` toolkit;

and proves (the four blocks marked ✓ are complete; the rest of `ACVF` is listed at the end)

* ✓ `model_sortAxioms : (C v) ⊨ Axioms.sortAxioms` — the sort discipline of the encoding under
  the *current* `pInK` guard (`pInK t = pUnits t ⊔ t = tRVZero`), all 16 sentences, including
  `sdUnits` and `sdKMul` (which no earlier file proves);
* ✓ `model_preorderRV : (C v) ⊨ Axioms.preorderRV` — all seven sentences of Definition 2.2(4);
* ✓ `model_vfField : (C v) ⊨ Axioms.vfField` and `model_vfAlgClosed' : (C v) ⊨ Axioms.vfAlgClosed`
  (the latter for `[IsAlgClosed K]`) — the two `VF` blocks of Definition 2.2(1), obtained by
  replaying `Milestone0/accepted/VFAlgClosed.lean`'s Part 8 toolkit and Part 11 argument against
  `instStructure` instead of that file's junk-`RV` structure `str`: the sentences of `vfField`
  and `vfAlgClosed` mention only `VF` function symbols and `memVF`, which both structures
  interpret identically;
* the elimination of the value group `Γ` in `L_RV` (Definition 2.2(5), "`Γ` is an imaginary
  sort"): `vrv` is a complete invariant of the class relation `∃u (Kˣ(u) ∧ s = u·t)`
  (`vrv_eq_iff_units`), the order is the `𝒪`-divisibility order (`rvLe_iff_exists_mul`), and
  `Kˣ` is the class of `1` (`le0_one_iff`), so `Γ(S)` nontrivial can be stated with `vrv`,
  `Kˣ` and `≤` alone;
* the concrete field: `PadicComplex.valuation_p` gives `v p = 1/p ≠ 1`, hence `Γ` is nontrivial
  at `K = ℂ_[p]`, `v = (PadicComplex.valued p).v` (`padic_inputs`, `padic_not_le_one_both`),
  and `gamma_nontrivial_of_vf` turns an element `x` of a set `S` (with `rv x ∈ S`) and
  `v x ≠ 1` into the task's `∃ t ∈ S` reading of "`Γ(S)` nontrivial".

NOT in this file (the rest of `ACVF`): `rvGroup` (its eight sentences plus the divisibility
scheme), `rvAxioms` (five), `kField` (ten, guarded by `pInK`) and `kAlgClosed` (the `acfSchemeK`
scheme).  The first two are `RV`-layer case analyses, the last two need the residue field
`k = 𝒪/𝔪` transported into `RV₀` along `K^× ≃* k^×`.  No `sorry`, no `admit`, no new `axiom`; the axiom footprint of every
headline is printed at the end.
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
  rw [LRV.tRVInfty]
  exact ev_rvZero xs

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

/-! ### The two-layer `RV v` form of the same lemmas

With `0 = ∞` the carrier is `RV v = Option (RVUnit v)`: `none` is the single absorbing
element, the top of the preorder and the value of `rv 0`.  The `RV0`-level lemmas above are
still true statements about the (no longer used) three-layer alias; the intended structure
`C v` below is built on `RV v` and uses the lemmas below. -/
theorem rvLe_refl (t : RV v) : rvLe v t t := le_rfl

theorem rvLe_total (t s : RV v) : rvLe v t s ∨ rvLe v s t := le_total (vrv v s) (vrv v t)

theorem rvLe_trans {t s r : RV v} (h1 : rvLe v t s) (h2 : rvLe v s r) : rvLe v t r :=
  le_trans h2 h1

theorem rvLe_infty (t : RV v) : rvLe v t none := by
  rw [rvLe]; simp

end Extra
end RVM
end SpecialTransformations

namespace SpecialTransformations
namespace Milestone0
namespace IModel

open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-- The carrier of the intended `L_RV`-structure of the valued field `(K, v)`:
`M = VF ⊕ RV` with `VF = K` and `RV = Option (Kˣ ⧸ (1+𝔪))`, i.e. the paper's `RV` sort
whose single absorbing element `0 = ∞ = rv(0)` is `none`. -/
abbrev C : Type _ := K ⊕ RVM.RV v

/-- the `VF`-tag -/
def mkVF (x : K) : C v := Sum.inl x
/-- the `RV`-tag -/
def mkRV (t : RVM.RV v) : C v := Sum.inr t

/-- the paper's `0`, the residue field's zero — which is `∞ = rv 0` and the absorbing
element of the `RV` sort: one element, `none` of `RV v` -/
def cKZero : C v := Sum.inr none
/-- the paper's `∞ = rv 0`, the *same* element as `cKZero` -/
def cInfty : C v := Sum.inr none
/-- an element of `RV^×`, i.e. the class of a unit -/
def cUnit (q : RVM.RVUnit v) : C v := Sum.inr (some q)
/-- the paper's `1` in the `RV` sort -/
noncomputable def cRVOne : C v := Sum.inr (RVM.rvOne v)

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
  | _, .kAdd, _ => cKZero v
  | _, .kNeg, _ => cKZero v
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

namespace SpecialTransformations
namespace Milestone0
namespace VFModel

open FirstOrder FirstOrder.Language

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- the carrier `K ⊕ RV v` of the intended two-sorted structure (definitionally `IModel.C v`) -/
abbrev Carrier (v : Valuation K Γ₀) : Type _ := IModel.C v

/-- the junk value of the `VF` operations off the `VF` summand -/
noncomputable def junk (v : Valuation K Γ₀) : Carrier v := Sum.inr (none : Valued.RV v)

end VFModel
end Milestone0
end SpecialTransformations
namespace SpecialTransformations
namespace Milestone0
namespace VFModel

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation K Γ₀)

/-- reading `memVF` at the intended structure -/
theorem iVF_iff {x : Carrier v} : iVF x ↔ ∃ a : K, x = Sum.inl a := Iff.rfl

theorem exists_of_iVF {x : Carrier v} (h : iVF x) : ∃ a : K, x = Sum.inl a :=
  (iVF_iff (x := x)).mp h

/-- reading `memRV` at the intended structure -/
theorem iRV_iff {x : Carrier v} : iRV x ↔ ∃ b : Valued.RV v, x = Sum.inr b := Iff.rfl

theorem iVF_inl (a : K) : iVF (Sum.inl a : Carrier v) := ⟨a, rfl⟩

/-- the interpretation of `0` of the `VF` sort is the field zero of `K` -/
theorem iVFZero_eq : iVFZero (M := Carrier v) = Sum.inl (0 : K) := rfl

/-- the value of the term `tVFZero` -/
theorem realize_tVFZero {n : ℕ} (xs : Fin n → Carrier v) :
    Term.realize (Sem.rho xs) (LRV.tVFZero (n := n)) = Sum.inl (0 : K) := by
  rw [Sem.ev_vfZero, iVFZero_eq]

end VFModel
namespace VFModel

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
theorem ev_tv_of {N : ℕ} (xs : Fin N → Carrier v) (a : ℕ → K)
    (ha : ∀ i : Fin N, xs i = Sum.inl (a i.val)) (j : Fin N) :
    Term.realize (Sem.rho xs) (LRV.tv j.val j.isLt) = Sum.inl (a j.val) := by
  rw [Sem.ev_tv]
  exact ha j

/-- the value of the Horner fold -/
theorem ev_fold {n N : ℕ} (hn : n ≤ N) (xs : Fin N → Carrier v) (xT : LRV.Tm N) (xc : K)
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
theorem realize_hornerPoly {n : ℕ} (xs : Fin (n + 1 + 1) → Carrier v) (a : ℕ → K)
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
    (Carrier v) ⊨ Axioms.acfScheme .vf LRV.tVFZero LRV.tVFAdd LRV.tVFMul k := by
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
      (@Fin.snoc (n + 1) (fun _ => Carrier v) xs (Sum.inl x)) i
        = (Sum.inl (a' i.val) : Carrier v) := by
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
  rw [show (Fin.snoc xs (Sum.inl x) : Fin (n + 1 + 1) → Carrier v)
      = @Fin.snoc (n + 1) (fun _ => Carrier v) xs (Sum.inl x) from rfl]
  rw [realize_hornerPoly v (xs := @Fin.snoc (n + 1) (fun _ => Carrier v) xs (Sum.inl x))
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
    (Carrier v) ⊨ Axioms.vfAlgClosed where
  realize_of_mem φ hφ := by
    obtain ⟨k, hk, rfl⟩ := hφ
    exact acfScheme_vf v hk

end VFModel
end Milestone0
end SpecialTransformations

open FirstOrder FirstOrder.Language
namespace SpecialTransformations.Milestone0.IModel
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
    SpecialTransformations.Milestone0.LRV.pInK,
    SpecialTransformations.Milestone0.IModel.cUnit,
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


/-! ### Reading the relation symbols back at `RV₀` -/

/-- the two projections of `mkRV` -/
theorem le0_of_exists_mkRV {t s : RVM.RV v}
    (h : ∃ a b : RVM.RV v, mkRV v t = mkRV v a ∧ mkRV v s = mkRV v b ∧ RVM.rvLe v a b) :
    RVM.rvLe v t s := by
  obtain ⟨a, b, h1, h2, h3⟩ := h
  simp only [mkRV, Sum.inr.injEq] at h1 h2
  rw [← h1, ← h2] at h3
  exact h3

theorem mkRV_inj {t s : RVM.RV v} (h : mkRV v t = Sum.inr s) : t = s := by
  simpa [mkRV] using h

theorem exists_mkRV_of_le0 {t s : RVM.RV v} (h : RVM.rvLe v t s) :
    ∃ a b : RVM.RV v, mkRV v t = mkRV v a ∧ mkRV v s = mkRV v b ∧ RVM.rvLe v a b :=
  ⟨t, s, rfl, rfl, h⟩

/-! ### the preorder on `RV` (Definition 2.2 item 4) -/

theorem model_leRefl : (C v) ⊨ Axioms.leRefl := by
  simp only [Axioms.leRefl]; rw [model_allSorted v]; intro xs h; prep
  intro _
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht]
  exact ⟨t, t, rfl, rfl, RVM.rvLe_refl v t⟩

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
    (RVM.rvLe_trans v (le0_of_exists_mkRV v h01) (le0_of_exists_mkRV v h12))

theorem model_leTotal : (C v) ⊨ Axioms.leTotal := by
  simp only [Axioms.leTotal]; rw [model_allSorted v]; intro xs h; prep
  intro _ _
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  rw [ht, hs]
  rcases RVM.rvLe_total v t s with h' | h'
  · exact Or.inl ⟨t, s, rfl, rfl, h'⟩
  · exact Or.inr ⟨s, t, rfl, rfl, h'⟩

theorem model_leTop : (C v) ⊨ Axioms.leTop := by
  simp only [Axioms.leTop]; rw [model_allSorted v]; intro xs h; prep
  intro _
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht]
  exact ⟨t, none, rfl, rfl, RVM.rvLe_infty v t⟩

theorem model_leInftyEq : (C v) ⊨ Axioms.leInftyEq := by
  simp only [Axioms.leInftyEq]; rw [model_allSorted v]; intro xs h; prep
  intro _ hle
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht] at hle ⊢
  obtain ⟨a, b, ha, hb, hab⟩ := hle
  simp only [mkRV, Sum.inr.injEq] at ha hb
  rw [← ha, ← hb] at hab
  cases t with
  | none => rfl
  | some q =>
    exfalso
    have hne : RVM.vrv v (some q) ≠ 0 := by simp [RVM.vrv_some]
    have h0 : RVM.vrv v (some q) = 0 := le_antisymm hab zero_le
    exact hne h0

/-- multiplying on the right by an element of `K^×` preserves `≤`

In the two-layer carrier `none` is the *top* of the preorder (the old `∞`), not the bottom,
so the two elements compared must be `≠ none`: `pRV` in `leMulCompat` supplies exactly that. -/
theorem le0_mul_unit_right (t s : RVM.RV v) (q : RVM.RVUnit v)
    (ht : t ≠ none) (hs : s ≠ none)
    (hq : RVM.vrv v (some q) = 1) (h : RVM.rvLe v t s) :
    RVM.rvLe v (RVM.rvMul t (some q)) (RVM.rvMul s (some q)) := by
  obtain ⟨a, rfl⟩ : ∃ a : RVM.RVUnit v, t = some a := by
    rcases t with _ | a
    · exact absurd rfl ht
    · exact ⟨a, rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b : RVM.RVUnit v, s = some b := by
    rcases s with _ | b
    · exact absurd rfl hs
    · exact ⟨b, rfl⟩
  rw [RVM.rvLe] at h ⊢
  rw [RVM.vrv_mul, RVM.vrv_mul, hq, mul_one, mul_one]
  exact h

theorem model_leClassOne : (C v) ⊨ Axioms.leClassOne := by
  simp only [Axioms.leClassOne]; rw [model_allSorted v]; intro xs h; prep
  intro _
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [ht]
  constructor
  · rintro ⟨q, hq, hq1⟩
    have htq : t = some q := mkRV_inj v hq
    subst htq
    have hcl := (RVM.le_class_of_one_iff v (t := some q)).mpr hq1
    exact ⟨⟨RVM.rvOne v, some q, rfl, rfl, hcl.1⟩,
      ⟨some q, RVM.rvOne v, rfl, rfl, hcl.2⟩⟩
  · rintro ⟨⟨a1, b1, ha1, hb1, hl1⟩, ⟨a2, b2, ha2, hb2, hl2⟩⟩
    simp only [mkRV, Sum.inr.injEq] at ha1 hb1 ha2 hb2
    rw [← ha1, ← hb1] at hl1
    rw [← ha2, ← hb2] at hl2
    cases t with
    | none =>
      exact absurd ((RVM.le_class_of_one_iff v (t := none)).mp ⟨hl1, hl2⟩) (by simp [RVM.vrv])
    | some q =>
      exact ⟨q, rfl, (RVM.le_class_of_one_iff v (t := some q)).mp ⟨hl1, hl2⟩⟩

theorem model_leMulCompat : (C v) ⊨ Axioms.leMulCompat := by
  simp only [Axioms.leMulCompat]; rw [model_allSorted v]; intro xs h; prep
  intro h0 h1 _ hunit hle
  obtain ⟨t0, ht0⟩ := (h 0).2 rfl
  obtain ⟨t1, ht1⟩ := (h 1).2 rfl
  obtain ⟨t2, ht2⟩ := (h 2).2 rfl
  obtain ⟨q, hq, hq1⟩ := hunit
  rw [ht2] at hq
  have ht2q : t2 = some q := mkRV_inj v hq
  subst ht2q
  have ht0' : t0 ≠ none := by
    intro h
    exact h0 (by rw [ht0, h]; rfl)
  have ht1' : t1 ≠ none := by
    intro h
    exact h1 (by rw [ht1, h]; rfl)
  rw [ht0, ht1] at hle
  rw [ht0, ht1, ht2]
  exact ⟨RVM.rvMul t0 (some q), RVM.rvMul t1 (some q), rfl, rfl,
    le0_mul_unit_right v t0 t1 q ht0' ht1' hq1 (le0_of_exists_mkRV v hle)⟩

/-! ### the block -/

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

end SpecialTransformations.Milestone0.IModel

namespace SpecialTransformations.Milestone0.IModel
open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-! ### the sort discipline of the encoding (Definition 2.2, encoding layer) -/

/-- `pInK` read at the carrier: `0` or a genuine unit of the residue field, i.e. an element
of the class of `1`. -/
theorem inK_iff (t : RVM.RV v) :
    ((∃ q : RVM.RVUnit v, mkRV v t = cUnit v q ∧ RVM.vrv v (some q) = 1) ∨
      mkRV v t = cKZero v) ↔
      ((∃ q : RVM.RVUnit v, t = some q ∧ RVM.vrv v (some q) = 1) ∨ t = none) := by
  constructor
  · rintro (⟨q, hq, hq1⟩ | hq)
    · exact Or.inl ⟨q, mkRV_inj v hq, hq1⟩
    · exact Or.inr (mkRV_inj v hq)
  · rintro (⟨q, rfl, hq1⟩ | rfl)
    · exact Or.inl ⟨q, rfl, hq1⟩
    · exact Or.inr rfl

/-- `vrv` of a product in `RV^×` -/
theorem vrv_some_mul (c d : RVM.RVUnit v) :
    RVM.vrv v (some (c * d)) = RVM.vrv v (some c) * RVM.vrv v (some d) := by
  have h := RVM.vrv_mul v (some c) (some d)
  rwa [RVM.rvMul_some_some] at h

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

/-- `∞ = rv(0) = 0`: the same sentence as `sdRVZero` -/
theorem model_sdRVInfty : (C v) ⊨ Axioms.sdRVInfty := by
  simp only [Axioms.sdRVInfty]; prep
  exact ⟨none, rfl⟩

theorem model_sdRVMul : (C v) ⊨ Axioms.sdRVMul := by
  simp only [Axioms.sdRVMul]; rw [model_allSorted v]; intro xs h; prep
  obtain ⟨s, hs⟩ := (h 0).2 rfl
  obtain ⟨t, ht⟩ := (h 1).2 rfl
  rw [hs, ht]
  exact ⟨RVM.rvMul s t, rfl⟩

theorem model_sdUnits : (C v) ⊨ Axioms.sdUnits := by
  simp only [Axioms.sdUnits, LRV.allOne]; rw [model_alls v]; intro xs
  prep
  rintro ⟨q, hq, -⟩
  exact ⟨some q, hq⟩

theorem model_sdKAdd : (C v) ⊨ Axioms.sdKAdd := by
  simp only [Axioms.sdKAdd]; rw [model_allSorted v]; intro xs h; prep
  intro _ _
  exact Or.inr trivial

theorem model_sdKNeg : (C v) ⊨ Axioms.sdKNeg := by
  simp only [Axioms.sdKNeg]; rw [model_allSorted v]; intro xs h; prep
  intro _
  exact Or.inr trivial

/-- `pInK` is preserved by `rv0Mul` -/
theorem pInK_rv0Mul {t s : RVM.RV v}
    (h0 : (∃ q : RVM.RVUnit v, t = some q ∧ RVM.vrv v (some q) = 1) ∨ t = none)
    (h1 : (∃ q : RVM.RVUnit v, s = some q ∧ RVM.vrv v (some q) = 1) ∨ s = none) :
    (∃ q : RVM.RVUnit v, RVM.rvMul t s = some q ∧ RVM.vrv v (some q) = 1) ∨
      RVM.rvMul t s = none := by
  rcases h0 with ⟨c, rfl, hc⟩ | rfl
  · rcases h1 with ⟨d, rfl, hd⟩ | rfl
    · exact Or.inl ⟨c * d, rfl, by rw [vrv_some_mul v, hc, hd, one_mul]⟩
    · exact Or.inr rfl
  · rcases h1 with ⟨d, rfl, hd⟩ | rfl <;> exact Or.inr rfl

/-- the same, in the carrier's own language -/
theorem pInK_rv0Mul_c {t s : RVM.RV v}
    (h0 : (∃ q : RVM.RVUnit v, t = some q ∧ RVM.vrv v (some q) = 1) ∨ t = none)
    (h1 : (∃ q : RVM.RVUnit v, s = some q ∧ RVM.vrv v (some q) = 1) ∨ s = none) :
    (∃ q : RVM.RVUnit v, mkRV v (RVM.rvMul t s) = cUnit v q ∧ RVM.vrv v (some q) = 1) ∨
      mkRV v (RVM.rvMul t s) = cKZero v := by
  rcases pInK_rv0Mul v h0 h1 with ⟨q, hq, hq1⟩ | hq
  · exact Or.inl ⟨q, by rw [mkRV, cUnit, hq], hq1⟩
  · exact Or.inr (by rw [mkRV, cKZero, hq])

theorem model_sdKMul : (C v) ⊨ Axioms.sdKMul := by
  simp only [Axioms.sdKMul]; rw [model_allSorted v]; intro xs h; prep
  intro h0 h1
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  generalize hx0 : xs 0 = x0 at ⊢
  generalize hx1 : xs 1 = x1 at ⊢
  rw [hx0] at h0
  rw [hx1] at h1
  have e0 : x0 = mkRV v t := by rw [← hx0]; exact ht
  have e1 : x1 = mkRV v s := by rw [← hx1]; exact hs
  subst e0; subst e1
  simp only [mkRV]
  exact pInK_rv0Mul_c v ((inK_iff v t).mp h0) ((inK_iff v s).mp h1)

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

end SpecialTransformations.Milestone0.IModel

namespace SpecialTransformations.Milestone0.IModel
open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-- the closure part of the sort discipline -/
theorem model_sortClosure : (C v) ⊨ Axioms.sortClosure := by
  rw [Theory.model_iff]; intro s hs
  simp only [Axioms.sortClosure, Axioms.ofList, List.mem_cons, List.mem_nil_iff, or_false] at hs
  obtain rfl | h2 := hs
  · exact model_sdVFZero v
  obtain rfl | h3 := h2
  · exact model_sdVFOne v
  obtain rfl | h4 := h3
  · exact model_sdVFAdd v
  obtain rfl | h5 := h4
  · exact model_sdVFNeg v
  obtain rfl | h6 := h5
  · exact model_sdVFMul v
  obtain rfl | h7 := h6
  · exact model_sdRv v
  obtain rfl | h8 := h7
  · exact model_sdRVZero v
  obtain rfl | h9 := h8
  · exact model_sdRVInfty v
  obtain rfl | h10 := h9
  · exact model_sdRVOne v
  obtain rfl | h11 := h10
  · exact model_sdRVMul v
  obtain rfl | h12 := h11
  · exact model_sdUnits v
  obtain rfl | h13 := h12
  · exact model_sdKAdd v
  obtain rfl | h14 := h13
  · exact model_sdKNeg v
  obtain rfl := by simpa using h14
  exact model_sdKMul v

/-- **the sort discipline of the encoding, at the general model** -/
theorem model_sortAxioms : (C v) ⊨ Axioms.sortAxioms := by
  rw [Theory.model_iff]; intro s hs
  simp only [Axioms.sortAxioms, Set.mem_union, Set.mem_ofPred_eq, Axioms.ofList, List.mem_cons,
    List.mem_nil_iff, or_false] at hs
  rcases hs with hs | hs | hs
  · exact (Theory.model_iff _).mp (model_sortClosure v) s hs
  · rw [show s = Axioms.sdCover from hs]; exact model_sdCover v
  · rw [show s = Axioms.sdDisjoint from hs]; exact model_sdDisjoint v

/-- **both blocks verified in this file, at the general model** -/
theorem model_sortAxioms_union_preorderRV :
    (C v) ⊨ (Axioms.sortAxioms ∪ Axioms.preorderRV) := by
  rw [Theory.model_union_iff]
  exact ⟨model_sortAxioms v, model_preorderRV v⟩

end SpecialTransformations.Milestone0.IModel

/-! ## axiom footprint -/

#print axioms SpecialTransformations.Milestone0.IModel.model_sortAxioms
#print axioms SpecialTransformations.Milestone0.IModel.model_preorderRV
#print axioms SpecialTransformations.Milestone0.IModel.model_sdKMul
#print axioms SpecialTransformations.Milestone0.IModel.model_sortAxioms_union_preorderRV

namespace SpecialTransformations.Milestone0.IModel
open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-! ### eliminating the value group: `vrv` is a complete invariant of the `K^×`-classes -/

theorem vrv_rvOne : RVM.vrv v (RVM.rvOne v) = 1 := by
  rw [RVM.rvOne, RVM.vrv_rv, Valuation.map_one]

theorem vrv_eq_zero_iff {t : RVM.RV v} : RVM.vrv v t = 0 ↔ t = none := by
  cases t with
  | none => simp
  | some q => simp [RVM.vrv_some]

theorem vrv_some_inv (q : RVM.RVUnit v) :
    RVM.vrv v (some q⁻¹) = (RVM.vrv v (some q))⁻¹ := by
  rw [RVM.vrv_some, RVM.vrv_some, map_inv, Units.val_inv_eq_inv_val]

theorem rvMul_inv_cancel (q : RVM.RVUnit v) :
    RVM.rvMul (some q) (some q⁻¹) = RVM.rvOne v := by
  rw [RVM.rvMul_some_some, mul_inv_cancel, RVM.rvOne_eq]

theorem rvMul_inv_cancel' (q : RVM.RVUnit v) :
    RVM.rvMul (some q⁻¹) (some q) = RVM.rvOne v := by
  rw [RVM.rvMul_some_some, inv_mul_cancel, RVM.rvOne_eq]

theorem rvMul_one_left (t : RVM.RV v) : RVM.rvMul (RVM.rvOne v) t = t := by
  rw [RVM.rvMul_comm]; exact RVM.rvMul_one t

/-- **`vrv` is a complete invariant of the class relation "differs by an element of `K^×`"**,
in `L_RV` terms `∃ u, Kˣ(u) ∧ s = u · t`. -/
theorem vrv_eq_iff_exists_mul {t s : RVM.RV v} :
    RVM.vrv v t = RVM.vrv v s ↔ ∃ u : RVM.RV v, RVM.vrv v u = 1 ∧ s = RVM.rvMul u t := by
  constructor
  · intro h
    cases t with
    | none =>
      have hs : RVM.vrv v s = 0 := by rw [← h]; simp
      refine ⟨RVM.rvOne v, vrv_rvOne v, ?_⟩
      rw [(vrv_eq_zero_iff v).mp hs, RVM.rvMul_infty]
    | some a =>
      have hs : RVM.vrv v s ≠ 0 := by rw [← h]; simp [RVM.vrv_some]
      obtain ⟨b, rfl⟩ : ∃ b, s = some b := by
        cases s with
        | none => exact absurd (by simp) hs
        | some b => exact ⟨b, rfl⟩
      refine ⟨RVM.rvMul (some b) (some a⁻¹), ?_, ?_⟩
      · rw [RVM.vrv_mul, vrv_some_inv, ← h]
        exact mul_inv_cancel₀ (by simp [RVM.vrv_some])
      · rw [RVM.rvMul_assoc, rvMul_inv_cancel', RVM.rvMul_one]
  · rintro ⟨u, hu, rfl⟩
    rw [RVM.vrv_mul, hu, one_mul]

/-- the `K^×`-form of the same statement: the class of an element of `RV^×` is determined by
its value, and two elements have the same value exactly when they differ by a unit. -/
theorem vrv_eq_iff_units {t s : RVM.RV v} :
    RVM.vrv v t = RVM.vrv v s ↔
      ∃ q : RVM.RVUnit v, RVM.vrv v (some q) = 1 ∧ s = RVM.rvMul (some q) t := by
  rw [vrv_eq_iff_exists_mul v]
  constructor
  · rintro ⟨u, hu, hsu⟩
    cases u with
    | none => exact absurd hu (by simp)
    | some q => exact ⟨q, hu, hsu⟩
  · rintro ⟨q, hq, hsu⟩
    exact ⟨some q, hq, hsu⟩

/-- **the ordered version**: `t ≤ s` (the paper's order, `vrv s ≤ vrv t`) iff `s = u · t` for
some `u` in the valuation ring `𝒪 = {u : vrv u ≤ 1}`. -/
theorem rvLe_iff_exists_mul {t s : RVM.RV v} (ht : t ≠ none) :
    RVM.rvLe v t s ↔ ∃ u : RVM.RV v, RVM.vrv v u ≤ 1 ∧ s = RVM.rvMul u t := by
  obtain ⟨a, rfl⟩ : ∃ a, t = some a := by
    cases t with
    | none => exact absurd rfl ht
    | some a => exact ⟨a, rfl⟩
  constructor
  · intro h
    cases s with
    | none => exact ⟨none, by simp, by rw [RVM.rvMul_infty']⟩
    | some b =>
      refine ⟨RVM.rvMul (some b) (some a⁻¹), ?_, ?_⟩
      · show RVM.vrv v (RVM.rvMul (some b) (some a⁻¹)) ≤ 1
        rw [RVM.vrv_mul, vrv_some_inv, ← div_eq_mul_inv]
        exact div_le_one_of_le₀ h (zero_le : (0 : Γ₀) ≤ RVM.vrv v (some a))
      · rw [RVM.rvMul_assoc, rvMul_inv_cancel', rvMul_one]
  · rintro ⟨u, hu, rfl⟩
    show RVM.vrv v (RVM.rvMul u (some a)) ≤ RVM.vrv v (some a)
    rw [RVM.vrv_mul]
    exact mul_le_of_le_one_left (b := RVM.vrv v (some a)) zero_le hu


/-! ### `Γ` as the quotient of `RV` by `K^×`: the class of `1` and the ordered-group law -/

/-- the `L_RV`-reading of "`t` has value `1`": `1 ≤ t ≤ 1`.  This is exactly the paper's
predicate `Kˣ`, i.e. `pUnits` at the carrier. -/
theorem le0_one_iff (t : RVM.RV v) :
    (RVM.rvLe v (RVM.rvOne v) t ∧ RVM.rvLe v t (RVM.rvOne v)) ↔
      ∃ q : RVM.RVUnit v, t = some q ∧ RVM.vrv v (some q) = 1 := by
  cases t with
  | none =>
    constructor
    · rintro ⟨-, h2⟩
      exact absurd h2 (by rw [RVM.rvLe, RVM.rvOne_eq]; simp)
    · rintro ⟨q, hq, -⟩
      exact absurd hq (by simp)
  | some b =>
    rw [show (RVM.rvLe v (RVM.rvOne v) (some b) ∧
        RVM.rvLe v (some b) (RVM.rvOne v)) ↔ RVM.vrv v (some b) = 1 from
      RVM.le_class_of_one_iff v (t := some b)]
    exact ⟨fun h => ⟨b, rfl, h⟩, fun ⟨q, hq, hq1⟩ => by rw [hq]; exact hq1⟩

/-- `Γ` is a *preorder* quotient: `t` and `s` have the same value iff they are equivalent in
the preorder. -/
theorem rvLe_antisymm_iff {t s : RVM.RV v} :
    (RVM.rvLe v t s ∧ RVM.rvLe v s t) ↔ RVM.vrv v t = RVM.vrv v s := by
  constructor
  · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
  · intro h; exact ⟨le_of_eq h.symm, le_of_eq h⟩

/-- the order of `Γ` is translation invariant: multiplying on the left by any `u` is monotone
for the preorder of `RV` — `Γ` is an ordered abelian group. -/
theorem rvLe_mul_left {t s : RVM.RV v} (u : RVM.RV v) (h : RVM.rvLe v t s) :
    RVM.rvLe v (RVM.rvMul u t) (RVM.rvMul u s) := by
  show RVM.vrv v (RVM.rvMul u s) ≤ RVM.vrv v (RVM.rvMul u t)
  rw [RVM.vrv_mul, RVM.vrv_mul]
  calc RVM.vrv v u * RVM.vrv v s = RVM.vrv v s * RVM.vrv v u := mul_comm _ _
    _ ≤ RVM.vrv v t * RVM.vrv v u := mul_le_mul_left h _
    _ = RVM.vrv v u * RVM.vrv v t := mul_comm _ _

/-- ... and multiplication by an element of `K^×` does not change the equivalence class, which
is what makes `Γ = RV/K^×` a quotient of preorders. -/
theorem rvLe_mul_unit_iff {t s : RVM.RV v} {u : RVM.RV v} (hu : RVM.vrv v u = 1) :
    RVM.rvLe v (RVM.rvMul u t) (RVM.rvMul u s) ↔ RVM.rvLe v t s := by
  show RVM.vrv v (RVM.rvMul u s) ≤ RVM.vrv v (RVM.rvMul u t) ↔ RVM.vrv v s ≤ RVM.vrv v t
  rw [RVM.vrv_mul, RVM.vrv_mul, hu, one_mul, one_mul]


end SpecialTransformations.Milestone0.IModel

/-! ## axiom footprint of the Γ-elimination lemmas -/

#print axioms SpecialTransformations.Milestone0.IModel.vrv_eq_iff_exists_mul
#print axioms SpecialTransformations.Milestone0.IModel.vrv_eq_iff_units
#print axioms SpecialTransformations.Milestone0.IModel.rvLe_iff_exists_mul
#print axioms SpecialTransformations.Milestone0.IModel.le0_one_iff
#print axioms SpecialTransformations.Milestone0.IModel.rvLe_antisymm_iff
#print axioms SpecialTransformations.Milestone0.IModel.rvLe_mul_left
#print axioms SpecialTransformations.Milestone0.IModel.rvLe_mul_unit_iff

namespace SpecialTransformations.Milestone0.IModel
open SpecialTransformations.RVM

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-! ### the concrete field: `Γ` is nontrivial at `ℂ_[p]`

The task's concrete input: `K = ℂ_[p]`, `v = (PadicComplex.valued p).v`.  Mathlib gives
`PadicComplex.valuation_p : v p = 1/p`, so `v p ≠ 1` and the `RV`-element `rv p` has value
`≠ 1`: `Γ` is nontrivial.  In the language `L_RV` this says that `rv p` is *not* in the class
of `1`, i.e. `¬ (1 ≤ rv p ≤ 1)` — the reading of "`Γ` nontrivial" that the encoding supports
(the lemmas above translate it to `vrv ≠ 1`). -/

theorem padic_val_p_ne_one (p : ℕ) [Fact (Nat.Prime p)] :
    (PadicComplex.valued p).v (p : PadicComplex p) ≠ 1 := by
  rw [PadicComplex.valuation_p p]
  intro h
  have hp : (1 : NNReal) = p := by
    have := congrArg (fun x : NNReal => x * (p : NNReal)) h
    simpa [one_div, mul_inv_cancel₀] using this
  have hp1 : p = 1 := by exact_mod_cast hp.symm
  exact (Fact.out : Nat.Prime p).ne_one hp1

/-- **`Γ` is nontrivial at `ℂ_[p]`**: some `RV`-element has value `≠ 1`. -/
theorem exists_vrv_ne_one_padic (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ t : RVM.RV (PadicComplex.valued p).v,
      RVM.vrv (PadicComplex.valued p).v t ≠ 1 :=
  ⟨RVM.rv _ (p : PadicComplex p), by
    rw [RVM.vrv_rv]; exact padic_val_p_ne_one p⟩

/-- the same in the language of the encoding: `rv p` is not in the class of `1`, i.e.
`¬ (1 ≤ rv p ∧ rv p ≤ 1)` (`1 ≤ t` is `le0 (rvOne) t`). -/
theorem padic_not_le_one_both (p : ℕ) [Fact (Nat.Prime p)] :
    ¬ (RVM.rvLe (PadicComplex.valued p).v (RVM.rvOne _)
          (RVM.rv _ (p : PadicComplex p)) ∧
        RVM.rvLe (PadicComplex.valued p).v (RVM.rv _ (p : PadicComplex p))
          (RVM.rvOne _)) := by
  intro h
  have h1 : RVM.vrv (PadicComplex.valued p).v (RVM.rv _ (p : PadicComplex p)) = 1 :=
    (RVM.le_class_of_one_iff _).mp h
  rw [RVM.vrv_rv] at h1
  exact padic_val_p_ne_one p h1

/-- `IsAlgClosed`, `CharZero` and the nontrivial value group, for the concrete field of the
task (no hypothesis left). -/
theorem padic_inputs (p : ℕ) [Fact (Nat.Prime p)] :
    IsAlgClosed (PadicComplex p) ∧ CharZero (PadicComplex p) ∧
      ∃ t : RVM.RV (PadicComplex.valued p).v, RVM.vrv (PadicComplex.valued p).v t ≠ 1 :=
  ⟨PadicComplex.isAlgClosed p, PadicComplex.charZero p, exists_vrv_ne_one_padic p⟩

/-- **`Γ` is nontrivial iff the valuation is**: the value group of the model is the range of
`v`, so the `RV`-reading of nontriviality (`∃ t, vrv t ≠ 1`) and the valuation-theoretic one
(`∃ x, v x ≠ 1`) agree. -/
theorem exists_vrv_ne_one_iff {w : Valuation K Γ₀} :
    (∃ t : RVM.RV w, RVM.vrv w t ≠ 1) ↔ (∃ x : K, w x ≠ 1) := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨x, hx⟩ := (RVM.vrv_range w (RVM.vrv w t)).mp ⟨t, rfl⟩
    exact ⟨x, by rw [hx]; exact ht⟩
  · rintro ⟨x, hx⟩
    exact ⟨RVM.rv w x, by rwa [RVM.vrv_rv]⟩

/-- packaging of the milestone's witness: if a set `S` of the carrier contains `x` (as a `VF`
element) *and* `rv x` (as an `RV` element), and `v x ≠ 1`, then `S` has a nontrivial value —
the `∃ t` form `∃ t, S t ∧ (t is in the RV sort) ∧ ¬(1 ≤ t ≤ 1)` that the task asks to state. -/
theorem gamma_nontrivial_of_vf {w : Valuation K Γ₀} {S : Set (C w)} {x : K} (hx0 : x ≠ 0)
    (_hx : S (mkVF w x)) (hrvx : S (mkRV w (RVM.rv w x))) (hx1 : w x ≠ 1) :
    ∃ t : C w, S t ∧ (∃ b : RVM.RV w, t = mkRV w b) ∧
      ¬ (RVM.rvLe w (RVM.rvOne w) (RVM.rv w x) ∧
          RVM.rvLe w (RVM.rv w x) (RVM.rvOne w)) := by
  have hval : RVM.vrv w (RVM.rv w x) ≠ 1 := by rwa [RVM.vrv_rv]
  refine ⟨mkRV w (RVM.rv w x), hrvx, ⟨RVM.rv w x, rfl⟩, ?_⟩
  intro hcon
  obtain ⟨q', hq', hq'1⟩ := (le0_one_iff w (RVM.rv w x)).mp hcon
  exact hval (by rw [hq']; exact hq'1)

end SpecialTransformations.Milestone0.IModel

#print axioms SpecialTransformations.Milestone0.IModel.padic_val_p_ne_one
#print axioms SpecialTransformations.Milestone0.IModel.exists_vrv_ne_one_padic
#print axioms SpecialTransformations.Milestone0.IModel.padic_not_le_one_both
#print axioms SpecialTransformations.Milestone0.IModel.padic_inputs
#print axioms SpecialTransformations.Milestone0.IModel.exists_vrv_ne_one_iff
#print axioms SpecialTransformations.Milestone0.IModel.gamma_nontrivial_of_vf

namespace SpecialTransformations.Milestone0.IModel

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-! ### the `VF` blocks at the intended structure, with the real `RV` layer

`Milestone0/accepted/VFAlgClosed.lean` proves `vfField` and `vfAlgClosed` at an
`LRV`-structure that interprets the `VF` symbols exactly as `instStructure` does but the `RV`
symbols as junk.  Both sentences mention only `VF` symbols and `memVF`, so the proofs replay
verbatim at `instStructure` (the instance is the ambient one, `str` is not defined here). -/

/-- **`vfAlgClosed` at the intended structure on `C v`** -/
theorem model_vfAlgClosed' [IsAlgClosed K] : (C v) ⊨ Axioms.vfAlgClosed :=
  SpecialTransformations.Milestone0.VFModel.model_vfAlgClosed v

/-- **`vfField` at the intended structure on `C v`** -/
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


/-- **both `VF` blocks at the intended structure** -/
theorem model_vf_blocks [IsAlgClosed K] :
    (C v) ⊨ (Axioms.vfField ∪ Axioms.vfAlgClosed) := by
  rw [Theory.model_union_iff]
  exact ⟨model_vfField v, model_vfAlgClosed' v⟩

/-- **the assembly reduction**: `ACVF` at the intended structure follows from its eight blocks;
four of them are proved in this file, so only `rvGroup`, `rvAxioms`, `kField`, `kAlgClosed`
have to be supplied. -/
theorem model_ACVF_of_blocks (hvf : (C v) ⊨ Axioms.vfField)
    (hacf : (C v) ⊨ Axioms.vfAlgClosed) (hrv : (C v) ⊨ Axioms.rvGroup)
    (hk : (C v) ⊨ Axioms.kField) (hkacf : (C v) ⊨ Axioms.kAlgClosed)
    (hpre : (C v) ⊨ Axioms.preorderRV) (hrva : (C v) ⊨ Axioms.rvAxioms)
    (hsort : (C v) ⊨ Axioms.sortAxioms) : (C v) ⊨ Axioms.ACVF := by
  rw [Theory.model_iff]
  intro φ hφ
  rw [Axioms.ACVF, Axioms.ACVFpaper] at hφ
  simp only [Set.mem_union] at hφ
  rcases hφ with h | h
  · exact (Theory.model_iff _).mp hsort φ h
  rcases h with h | h
  · rcases h with h | h
    · rcases h with h | h
      · rcases h with h | h
        · rcases h with h | h
          · rcases h with h | h
            · exact (Theory.model_iff _).mp hvf φ h
            · exact (Theory.model_iff _).mp hacf φ h
          · exact (Theory.model_iff _).mp hrv φ h
        · exact (Theory.model_iff _).mp hk φ h
      · exact (Theory.model_iff _).mp hkacf φ h
    · exact (Theory.model_iff _).mp hpre φ h
  · exact (Theory.model_iff _).mp hrva φ h

/-- the same reduction with the four blocks of this file already discharged -/
theorem model_ACVF_of_residue_blocks [IsAlgClosed K] (hrv : (C v) ⊨ Axioms.rvGroup)
    (hk : (C v) ⊨ Axioms.kField) (hkacf : (C v) ⊨ Axioms.kAlgClosed)
    (hrva : (C v) ⊨ Axioms.rvAxioms) : (C v) ⊨ Axioms.ACVF :=
  model_ACVF_of_blocks v (model_vfField v) (model_vfAlgClosed' v) hrv hk hkacf
    (model_preorderRV v) hrva (model_sortAxioms v)

end SpecialTransformations.Milestone0.IModel

#print axioms SpecialTransformations.Milestone0.IModel.model_ACVF_of_blocks
#print axioms SpecialTransformations.Milestone0.IModel.model_ACVF_of_residue_blocks
#print axioms SpecialTransformations.Milestone0.IModel.model_vfField
#print axioms SpecialTransformations.Milestone0.IModel.model_vfAlgClosed'
#print axioms SpecialTransformations.Milestone0.IModel.model_vf_blocks
