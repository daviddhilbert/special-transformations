module
public import Mathlib
meta import all Lean.Meta.Match.Match
meta import Lean.Meta.Tactic.AuxLemma
@[expose] public section
/- Preserve the original module boundaries of two compiler-only caches.
   Otherwise Lean reuses a matcher from an earlier copied file and changes
   declaration names. This clears caches, not mathematical declarations. -/
open Lean Elab Command in
elab "reset_statement_module_caches" : command => do
  let cache : Name := `_private.Lean.Meta.Match.Match ++ .num .anonymous 0 ++ `Lean.Meta.Match.matcherExt
  unless (← getEnv).contains cache do throwError "Pinned Lean matcher cache is unavailable"
  elabCommand (← `(command| run_cmd do
    Lean.modifyEnv (fun env => Lean.EnvExtension.modifyState $(mkIdent cache)
      (Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})) (fun _ => {}))))
/-!
# Special transformations: core deformation statements
Author: Yimu Yin. This independent first submission states Theorem 5.5 and
Corollary 5.6. Definitions and signatures are extracted from the pinned
source, retaining their names and values. Supporting propositions supply
representation proofs and are not extra hypotheses of the main results.
The model has pure characteristic zero and genuine small-parameter
saturation; the parameter set S has cardinality below its saturation bound.
For Theorem 5.5, a special bijection A0 -> A and a polynomial whose every
coefficient lies in S are given. A further special bijection sends A to an
RV-pullback, the combined chain alternates, and the polynomial's RV value
is constant on each resulting RV fibre. Corollary 5.6 deforms every
S-definable subset of VF^n x RV^m to an RV-pullback over the same S.
Tuple arities may be zero. No strong-homogeneity or henselian-reference
hypothesis is imposed by these two statements.
The corrected released RV language has one absorbing element and named RV
inversion; VF inversion remains unnamed. The Jacobian and measured-lifting
results remain in the library but are outside this first Comparator claim.
Exact-snapshot independent compilation, comparison and full Palomar
mechanical verification are required before intake.
-/
reset_statement_module_caches
section
open FirstOrder FirstOrder.Language
namespace SpecialTransformations
namespace Milestone0
/-- The sorts of `L_RV`, as tags on the single carrier. -/ inductive SortTag where
  | vf
  | rv
  deriving DecidableEq, Repr
/-- Function symbols of `L_RV`, tagged by arity. -/ inductive Fn : ℕ → Type where/-- `0` of the ring language of the `VF` sort -/ | vfZero : Fn 0/-- `1` of the ring language of the `VF` sort -/ | vfOne : Fn 0/-- `+` of the ring language of the `VF` sort -/ | vfAdd : Fn 2/-- `-` of the ring language of the `VF` sort -/ | vfNeg : Fn 1/-- `×` of the ring language of the `VF` sort -/ | vfMul : Fn 2/-- `1` of the group language of the `RV` sort -/ | rvOne : Fn 0/-- the constant `0` of the `RV` sort: the residue field's zero, which is also `rv(0)` and the absorbing element of `RV`. The paper writes this element both as `0` and as `∞`; it is one element, so the language has one constant. -/ | rvZero : Fn 0/-- `×` of the `RV` sort -/ | rvMul : Fn 2/-- Multiplicative inverse on `RV`, totalized by `0⁻¹ = 0`. Naming this symbol is the author-approved correction to the inverse-free language specification before Convention 2.5, required for the intended QE result. It ensures that language substructures contain RV inverses. See LANGUAGE-ERRATA.md. -/ | rvInv : Fn 1/-- `+ : K² → K` of the `RV` sort -/ | kAdd : Fn 2/-- `- : K → K` of the `RV` sort -/ | kNeg : Fn 1/-- the projection `rv : VF → RV` -/ | rvMap : Fn 1
/-- Relation symbols of `L_RV`, tagged by arity. The first two are the sort predicates of the encoding (they are not part of the paper's signature); the last two are the paper's unary predicate `Kˣ` and its preorder `≤`. -/ inductive Rel : ℕ → Type where/-- encoding: the `VF` sort -/ | memVF : Rel 1/-- encoding: the `RV` sort -/ | memRV : Rel 1/-- the paper's unary predicate `Kˣ` -/ | memUnits : Rel 1/-- the paper's preorder `≤` on `RV` -/ | rvLe : Rel 2
/-- The corrected `L_RV`, with named RV inversion, in the tagged one-sorted encoding. -/ def LRV : Language := ⟨Fn, Rel⟩
namespace LRV
/-- Terms of `L_RV` whose (free) variables are indexed by `Fin n`. -/ abbrev Tm (n : ℕ) : Type := LRV.Term (Empty ⊕ Fin n)
/-- Bounded formulas of `L_RV` with `n` variables in scope and no free parameters. -/ abbrev Bf (n : ℕ) : Type := LRV.BoundedFormula Empty n
variable {n : ℕ}
/-- `0` of the `VF` sort -/ def tVFZero : Tm n := Term.func Fn.vfZero fun i => i.elim0
/-- `1` of the `VF` sort -/ def tVFOne : Tm n := Term.func Fn.vfOne fun i => i.elim0
/-- `+` of the `VF` sort -/ def tVFAdd (t u : Tm n) : Tm n := Term.func Fn.vfAdd ![t, u]
/-- `-` of the `VF` sort -/ def tVFNeg (t : Tm n) : Tm n := Term.func Fn.vfNeg ![t]
/-- `×` of the `VF` sort -/ def tVFMul (t u : Tm n) : Tm n := Term.func Fn.vfMul ![t, u]
/-- `1` of the `RV` sort -/ def tRVOne : Tm n := Term.func Fn.rvOne fun i => i.elim0
/-- `0` of the `RV` sort -/ def tRVZero : Tm n := Term.func Fn.rvZero fun i => i.elim0
/-- The paper's `∞` is `rv(0)`, i.e. the absorbing element `rvZero` of the `RV` sort: the paper's two symbols `0` and `∞` name one element. Kept as a definition so that the axioms can be read in the paper's notation. -/ def tRVInfty : Tm n := tRVZero
/-- `×` of the `RV` sort -/ def tRVMul (t u : Tm n) : Tm n := Term.func Fn.rvMul ![t, u]
/-- Multiplicative inverse on the `RV` sort, with `0⁻¹ = 0`. -/ def tRVInv (t : Tm n) : Tm n := Term.func Fn.rvInv ![t]
/-- `+ : K² → K` of the `RV` sort -/ def tKAdd (t u : Tm n) : Tm n := Term.func Fn.kAdd ![t, u]
/-- `- : K → K` of the `RV` sort -/ def tKNeg (t : Tm n) : Tm n := Term.func Fn.kNeg ![t]
/-- the projection `rv : VF → RV` -/ def tRv (t : Tm n) : Tm n := Term.func Fn.rvMap ![t]
/-- the bound variable of index `i < n` -/ def tv (i : ℕ) (h : i < n) : Tm n := Term.var (Sum.inr ⟨i, h⟩)
/-- the numeral `k · 1` of the `VF` sort -/ def tVFNumeral : ℕ → Tm n
  | 0 => tVFZero
  | k + 1 => tVFAdd (tVFNumeral k) tVFOne
/-- `t ^ k`, in the `RV` sort -/ def tRVPow (t : Tm n) : ℕ → Tm n
  | 0 => tRVOne
  | k + 1 => tRVMul (tRVPow t k) t
/-- `t ∈ VF`, the encoding's sort predicate for the `VF` sort -/ def pVF (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memVF t
/-- `t ∈ RV`, the encoding's sort predicate for the `RV` sort -/ def pRVsort (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memRV t
/-- the paper's unary predicate `Kˣ` -/ def pUnits (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memUnits t
/-- the paper's preorder `≤` -/ def pLe (t u : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₂ Rel.rvLe t u
/-- `t = u` -/ def pEq (t u : Tm n) : Bf n := t =' u
/-- the paper's `RV = RV-sort ∖ {0}` -/ def pRV (t : Tm n) : Bf n := ∼(pEq t tRVZero)
/-- the strict order `t > 1` of the `RV` sort -/ def pGtOne (t : Tm n) : Bf n := pLe tRVOne t ⊓ ∼(pLe t tRVOne)
/-- `t ∈ K = K^× ∪ {0}`, the residue field inside the `RV` sort. Not the same as `t ≠ 0`: when `Γ` is nontrivial the elements of `RV ∖ {0}` of value `≠ 1` are not in `K`, and the residue-field operations are junk there. Definition 2.1(d) defines `K` as `K^× ∪ {0}`, with `K^×` the predicate, i.e. axiom (4)'s class of `1`. The `0` here is `rv(0)`, the absorbing element of `RV`. -/ def pInK (t : Tm n) : Bf n := pUnits t ⊔ pEq t tRVZero
end LRV
namespace LRV
/-- the sort predicate of the sort `s`, as a formula -/ def sortPred (s : SortTag) (t : Tm n) : Bf n := match s with
  | .vf => pVF t
  | .rv => pRVsort t
/-- `⋀ i, x_i ∈ s_i`, for the variables `x_i` of index `i` -/ def sortedHyps {k : ℕ} (ss : Fin k → SortTag) : Bf k := (List.finRange k).foldr (fun i acc => sortPred (ss i) (tv i.val i.isLt) ⊓ acc) ⊤
/-- the guarded universal sentence `∀ x̄, (⋀ i, x_i ∈ s_i) → φ` -/ def allSorted {k : ℕ} (ss : Fin k → SortTag) (φ : Bf k) : LRV.Sentence := BoundedFormula.alls (sortedHyps ss ⟹ φ)
/-- the guarded existential formula `∃ x ∈ s, φ`, where `x` is the variable of index `k` -/ def exSorted {k : ℕ} (s : SortTag) (φ : Bf (k + 1)) : Bf k := BoundedFormula.ex (sortPred s (tv k (Nat.lt_succ_self k)) ⊓ φ)
/-- `⋀ i < k, x_i ∈ K`: the tuple lies in `K = K^× ∪ {0}` -/ def kHyps {k : ℕ} : Bf k := (List.finRange k).foldr (fun i acc => pInK (tv i.val i.isLt) ⊓ acc) ⊤
/-- the universal sentence `∀ x̄ ∈ s̄ ∩ K, φ` -/ def allSortedK {k : ℕ} (ss : Fin k → SortTag) (φ : Bf k) : LRV.Sentence := BoundedFormula.alls ((sortedHyps ss ⊓ kHyps) ⟹ φ)
/-- the guarded existential formula `∃ x ∈ s ∩ K, φ`, with `x` the variable of index `k` -/ def exSortedK {k : ℕ} (s : SortTag) (φ : Bf (k + 1)) : Bf k := BoundedFormula.ex (sortPred s (tv k (Nat.lt_succ_self k)) ⊓ pInK (tv k (Nat.lt_succ_self k)) ⊓ φ)
/-- the universal closure of a formula in a single variable -/ def allOne (φ : Bf 1) : LRV.Sentence := BoundedFormula.alls φ
/-- The result sort of a function symbol of `L_RV`. -/ def Fn.resSort : {l : ℕ} → Fn l → SortTag
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
/-- The sort of the `i`-th argument of a function symbol of `L_RV`. -/ def Fn.argSort : {l : ℕ} → (f : Fn l) → Fin l → SortTag
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
/-- Horner form `x^k + a_{k-1} x^{k-1} + ⋯ + a_0` of the monic polynomial of degree `k` whose coefficients are the variables `0, …, k-1` and whose variable is the variable `k`. The leading term is `x ^ k`, so `acfScheme` quantifies over *all* monic polynomials of degree `k`. (An earlier version started the Horner fold at `x` instead of at `x + a_{k-1}`, which silently produced `x^{k+1} + a_{k-1}x^{k-1} + ⋯ + a_0` — a monic polynomial of degree `k+1` with zero `x^k` coefficient, so the scheme covered only a proper subclass and did not give algebraic closedness.) For `k = 0` the value is immaterial: `acfScheme` is only used with `1 ≤ k`. -/ def hornerPoly {k : ℕ} (add mul : {n : ℕ} → Tm n → Tm n → Tm n) : Tm (k + 1) := match k with
  | 0 => tv 0 Nat.zero_lt_one
  | (n + 1) =>
    let x : Tm (n + 1 + 1) := tv (n + 1) (Nat.lt_succ_self (n + 1))
    (List.finRange n).reverse.foldl (fun acc i => add (mul acc x) (tv i.val (Nat.lt_trans i.isLt (Nat.lt.step (Nat.lt_succ_self n))))) (add x (tv n (Nat.lt.step (Nat.lt_succ_self n))))
end LRV
namespace Axioms
open LRV
/-- The sentences of a finite list, as a theory. -/ def ofList (l : List LRV.Sentence) : LRV.Theory := {s | s ∈ l}
/-- the carrier is covered by the two sorts -/ def sdCover : LRV.Sentence := allOne (pVF &0 ⊔ pRVsort &0)
/-- the two sorts are disjoint -/ def sdDisjoint : LRV.Sentence := allOne (∼(pVF &0 ⊓ pRVsort &0))
/-- `0` of the ring language lies in the `VF` sort -/ def sdVFZero : LRV.Sentence := pVF tVFZero
/-- `1` of the ring language lies in the `VF` sort -/ def sdVFOne : LRV.Sentence := pVF tVFOne
/-- the `VF` sort is closed under `+` -/ def sdVFAdd : LRV.Sentence := allSorted ![.vf, .vf] (pVF (tVFAdd &0 &1))
/-- the `VF` sort is closed under `-` -/ def sdVFNeg : LRV.Sentence := allSorted ![.vf] (pVF (tVFNeg &0))
/-- the `VF` sort is closed under `×` -/ def sdVFMul : LRV.Sentence := allSorted ![.vf, .vf] (pVF (tVFMul &0 &1))
/-- `rv` maps the `VF` sort into the `RV` sort -/ def sdRv : LRV.Sentence := allSorted ![.vf] (pRVsort (tRv &0))
/-- `0` of the `RV` sort lies in the `RV` sort -/ def sdRVZero : LRV.Sentence := pRVsort tRVZero
/-- `∞` lies in the `RV` sort -/ def sdRVInfty : LRV.Sentence := pRVsort tRVInfty
/-- `1` of the `RV` sort lies in the `RV` sort -/ def sdRVOne : LRV.Sentence := pRVsort tRVOne
/-- the `RV` sort is closed under `×` -/ def sdRVMul : LRV.Sentence := allSorted ![.rv, .rv] (pRVsort (tRVMul &0 &1))
def sdRVInv : LRV.Sentence := allSorted ![.rv] (pRVsort (tRVInv &0))
/-- The predicate `Kˣ` holds only of elements of the `RV` sort. Its actual content is axiom (4)'s `leClassOne`, which makes `Kˣ` the class of `1` — a *proper* subgroup of the multiplicative group `RV ∖ {0}` whenever `Γ` is nontrivial. Identifying `Kˣ` with all of `RV ∖ {0}` puts every `x ≠ 0` in the class of `1`, hence `1 ≤ x ≤ 1`, hence makes the preorder trivial and `Γ` trivial — contradicting the paper's standing hypothesis that `Γ(S)` is nontrivial. -/ def sdUnits : LRV.Sentence := allOne (pUnits &0 ⟹ pRVsort &0)
/-- `K = Kˣ ∪ {0}` is closed under `+` -/ def sdKAdd : LRV.Sentence := allSorted ![.rv, .rv] (pInK &0 ⟹ (pInK &1 ⟹ pInK (tKAdd &0 &1)))
/-- `K` is closed under unary `-` -/ def sdKNeg : LRV.Sentence := allSorted ![.rv] (pInK &0 ⟹ pInK (tKNeg &0))
/-- `K` is closed under `×`: the paper's `K = K^× ∪ {0}` is a field, so the product of two elements of `K` is in `K` and not `∞`. Without this the field axioms of `kField` (which are guarded by `pK`) constrain only the products that happen to land in `K`. -/ def sdKMul : LRV.Sentence := allSorted ![.rv, .rv] (pInK &0 ⟹ (pInK &1 ⟹ pInK (tRVMul &0 &1)))
/-- The closure part of the sort discipline: each sort is closed under its own symbols, and the two sorts are related through the symbols that cross them. -/ def sortClosure : LRV.Theory := ofList [sdVFZero, sdVFOne, sdVFAdd, sdVFNeg, sdVFMul, sdRv, sdRVZero, sdRVInfty, sdRVOne, sdRVMul, sdRVInv, sdUnits, sdKAdd, sdKNeg, sdKMul]
/-- the sort discipline of the encoding, as a theory -/ def sortAxioms : LRV.Theory := sortClosure ∪ ofList [sdCover, sdDisjoint]
/-- the field axioms for the sort `s`, with that sort's `0`, `1`, `+`, `-`, `×` -/ def fieldAxioms (s : SortTag) (zero one : {n : ℕ} → Tm n)
    (add mul : {n : ℕ} → Tm n → Tm n → Tm n) (neg : {n : ℕ} → Tm n → Tm n) :
    List LRV.Sentence := [ /- associativity of `+` -/
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
/-- the algebraic-closedness scheme for the sort `s`: `∀ a₀ … a_{k-1} ∃ x, x^k + a_{k-1} x^{k-1} + ⋯ + a₀ = 0` -/ def acfScheme (s : SortTag) (zero : {n : ℕ} → Tm n) (add mul : {n : ℕ} → Tm n → Tm n → Tm n) (k : ℕ) : LRV.Sentence := allSorted (fun _ : Fin k => s) (exSorted s (pEq (hornerPoly add mul) zero))
/-- Definition 2.2 item 1: `(VF, 0, 1, +, -, ×)` is an algebraically closed field. -/ def vfField : LRV.Theory := ofList (fieldAxioms .vf tVFZero tVFOne tVFAdd tVFMul tVFNeg)
/-- algebraic closedness of the `VF` sort -/ def vfAlgClosed : LRV.Theory := {s | ∃ k, 1 ≤ k ∧ s = acfScheme .vf tVFZero tVFAdd tVFMul k}
/-- Definition 2.2 item 3: `(K, 0, 1, +, -, ×)` is an algebraically closed field, where `K = K^× ∪ {0}`, the units of `RV` together with the absorbing element `0 = ∞ = rv 0`. Every quantifier is relativised to `K` (`allSortedK`, `exSortedK`), not merely to the `RV` sort. This is not cosmetic: `RV^×` also contains the elements of value `≠ 1`, where the residue operations are junk, so asserting the field axioms at every element of `RV` (equivalently at every `t ≠ ∞`, since `RV ∖ {0}` *is* the group) would force `Γ` trivial. -/ def kField : LRV.Theory := ofList
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
/-- the algebraic-closedness scheme for `K = K^× ∪ {0}`: coefficients and root in `K` -/ def acfSchemeK (k : ℕ) : LRV.Sentence := allSortedK (fun _ : Fin k => .rv) (exSortedK .rv (pEq (hornerPoly tKAdd tRVMul) tRVZero))
/-- algebraic closedness of `K = K^× ∪ {0}` -/ def kAlgClosed : LRV.Theory := {s | ∃ k, 1 ≤ k ∧ s = acfSchemeK k}
/-- `1 ∈ Kˣ` -/ def rvOneMem : LRV.Sentence := pUnits tRVOne
/-- `Kˣ` is closed under `×` -/ def rvMulMem : LRV.Sentence := allSorted ![.rv, .rv] (pUnits &0 ⟹ (pUnits &1 ⟹ pUnits (tRVMul &0 &1)))
/-- `×` is associative on `RV` -/ def rvMulAssoc : LRV.Sentence := allSorted ![.rv, .rv, .rv] (pEq (tRVMul (tRVMul &0 &1) &2) (tRVMul &0 (tRVMul &1 &2)))
/-- `×` is commutative on `RV` -/ def rvMulComm : LRV.Sentence := allSorted ![.rv, .rv] (pEq (tRVMul &0 &1) (tRVMul &1 &0))
/-- `1` is neutral for `×` on `Kˣ` -/ def rvMulOne : LRV.Sentence := allSorted ![.rv] (pUnits &0 ⟹ pEq (tRVMul tRVOne &0) &0)
/-- every element of `Kˣ` is invertible in `Kˣ` -/ def rvMulInv : LRV.Sentence := allSorted ![.rv] (pUnits &0 ⟹ exSorted .rv (pUnits &1 ⊓ pEq (tRVMul &1 &0) tRVOne))
/-- divisibility of `Kˣ`: for every `k ≥ 1`, `∀ x ∈ Kˣ ∃ y ∈ Kˣ, y^k = x` -/ def rvDivisible (k : ℕ) : LRV.Sentence := allSorted ![.rv] (pUnits &0 ⟹ exSorted .rv (pUnits &1 ⊓ pEq (tRVPow &1 k) &0))
/-- `t × 0 = 0` for `t ∈ K` -/ def rvMulZeroK : LRV.Sentence := allSorted ![.rv] (pInK &0 ⟹ pEq (tRVMul &0 tRVZero) tRVZero)
/-- `t × 0 = 0` for every `t` of the `RV` sort: the absorbing element. (This is the paper's `t × ∞ = ∞`; `∞ = rv 0 = 0`.) -/ def rvMulInfty : LRV.Sentence := allSorted ![.rv] (pEq (tRVMul &0 tRVInfty) tRVInfty)
/-- Definition 2.2 item 2: `(RV^×, 1, ×)` is a divisible abelian group, with `×` augmented by `t × 0 = 0`, i.e. `0 = ∞ = rv 0` absorbing. -/ def rvGroup : LRV.Theory := ofList [rvOneMem, rvMulMem, rvMulAssoc, rvMulComm, rvMulOne, rvMulInv, rvMulZeroK, rvMulInfty] ∪ {s | ∃ k, 1 ≤ k ∧ s = rvDivisible k}
/-- `≤` is reflexive on `RV` -/ def leRefl : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pLe &0 &0)
/-- `≤` is transitive on `RV` -/ def leTrans : LRV.Sentence := allSorted ![.rv, .rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pRV &2 ⟹ (pLe &0 &1 ⟹ (pLe &1 &2 ⟹ pLe &0 &2)))))
/-- `≤` is total on `RV` -/ def leTotal : LRV.Sentence := allSorted ![.rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pLe &0 &1 ⊔ pLe &1 &0)))
/-- `∞` is the top element of `RV` -/ def leTop : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pLe &0 tRVInfty)
/-- `∞ ≤ x` forces `x = ∞`, i.e. `∞` is alone in its class -/ def leInftyEq : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ (pLe tRVInfty &0 ⟹ pEq &0 tRVInfty))
/-- `Kˣ` is the equivalence class of `1` -/ def leClassOne : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ (pUnits &0 ⇔ (pLe tRVOne &0 ⊓ pLe &0 tRVOne)))
/-- `≤` is compatible with `×` on the left, i.e. the induced order on `RV/Kˣ` is a translation-invariant order -/ def leMulCompat : LRV.Sentence := allSorted ![.rv, .rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pRV &2 ⟹ (pUnits &2 ⟹ (pLe &0 &1 ⟹ pLe (tRVMul &0 &2) (tRVMul &1 &2))))))
/-- Definition 2.2 item 4: `≤` is a preorder on `RV` with `∞` the top element and `Kˣ` the equivalence class of `1`. -/ def preorderRV : LRV.Theory := ofList [leRefl, leTrans, leTotal, leTop, leInftyEq, leClassOne, leMulCompat]
/-- `rv(0) = ∞` -/ def rvZeroEq : LRV.Sentence := pEq (tRv tVFZero) tRVInfty
/-- `rv(x) = ∞` forces `x = 0` -/ def rvEqInfty : LRV.Sentence := allSorted ![.vf] (pEq (tRv &0) tRVInfty ⟹ pEq &0 tVFZero)
/-- `rv` is a group homomorphism on `VF^×` -/ def rvMulHom : LRV.Sentence := allSorted ![.vf, .vf] (pEq (tRv (tVFMul &0 &1)) (tRVMul (tRv &0) (tRv &1)))
/-- **`rv` is surjective**: every element of the `RV` sort other than `rv(0)` is `rv(x)` for some `x ∈ VF`. (Definition 2.2(6): `rv : VF^× → RV^×` is surjective, augmented by `rv(0) = ∞ = 0`. With `RV^× = RV ∖ {0}` this says: `RV = rv(VF^×) ∪ {0}`, so there are no `RV`-elements outside the image of `rv`.) -/ def rvSurj : LRV.Sentence := allSorted ![.rv] (∼(pEq &0 tRVZero) ⟹ exSorted .vf (pEq (tRv &1) &0))
/-- the ultrametric inequality for `vv = vrv ∘ rv`: `vv(x+y) ≥ min(vv x, vv y)` -/ def rvUltrametric : LRV.Sentence := allSorted ![.vf, .vf] (pLe (tRv &0) (tRv (tVFAdd &0 &1)) ⊔ pLe (tRv &1) (tRv (tVFAdd &0 &1)))
/-- Definition 2.2 item 6: `rv : VF^× → RV^×` is a surjective group homomorphism augmented by `rv(0) = ∞`, and `vv = vrv ∘ rv` is a valuation. (The valuation ring `O = rv⁻¹(RV^{≥1})` and the maximal ideal `M = rv⁻¹(RV^{>1})` are *defined* from `rv`, so — exactly as in the paper — they need no symbols of their own.) -/ def rvAxioms : LRV.Theory := ofList [rvZeroEq, rvEqInfty, rvMulHom, rvSurj, rvUltrametric]
/-- `1` is neutral for `×` on every nonzero `RV`-element. -/ def rvMulOneRV : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pEq (tRVMul tRVOne &0) &0)
/-- every nonzero `RV`-element is invertible in `RV^×`. -/ def rvMulInvRV : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ exSorted .rv (pRV &1 ⊓ pEq (tRVMul &1 &0) tRVOne))
/-- the order on `RV` is invariant under scaling by any `c ≠ rv 0`, in both directions. The guards on the first two variables are dropped because `∞ = rv 0` is absorbing and top, so both sides hold there. -/ def leMulCompatFull : LRV.Sentence := allSorted ![.rv, .rv, .rv] (pRV &2 ⟹ (pLe &0 &1 ⇔ pLe (tRVMul &0 &2) (tRVMul &1 &2)))
/-- `kAdd` is the residue addition at units: `rv (x + y)` if that is a unit, and `0` if `x + y` drops into the maximal ideal. -/ def kAddLink : LRV.Sentence := allSorted ![.vf, .vf]
    (pUnits (tRv &0) ⟹ (pUnits (tRv &1) ⟹
      ((pUnits (tRv (tVFAdd &0 &1)) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) (tRv (tVFAdd &0 &1))) ⊓
        (∼(pUnits (tRv (tVFAdd &0 &1))) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) tRVZero))))
/-- `kNeg` is the residue negation at units. -/ def kNegLink : LRV.Sentence := allSorted ![.vf] (pUnits (tRv &0) ⟹ pEq (tKNeg (tRv &0)) (tRv (tVFNeg &0)))
/-- two elements of `VF` have the same residue iff their difference has strictly larger value than the second: `rv a = rv b ↔ ¬ (v (a - b) ≤ v b)`. (The first transcription had the two `pLe` arguments transposed, which made the axiom false at `a = b = 1` and the whole theory inconsistent — see `QE-PLAN.md` and `.ultramath/smw163dd5/m5/Audit.lean`.) -/ def rvEqLink : LRV.Sentence := allSorted ![.vf, .vf]
    (∼(pEq &1 tVFZero) ⟹
      (pEq (tRv &0) (tRv &1) ⇔ ∼(pLe (tRv (tVFAdd &0 (tVFNeg &1))) (tRv &1))))
/-- the junk convention for `kAdd` off `K`: the value is `0`. -/ def kJunkZero : LRV.Sentence := allSorted ![.rv, .rv] ((∼(pInK &0) ⊔ ∼(pInK &1)) ⟹ pEq (tKAdd &0 &1) tRVZero)
/-- the junk convention for `kNeg` off `K`. -/ def kNegJunkZero : LRV.Sentence := allSorted ![.rv] (∼(pInK &0) ⟹ pEq (tKNeg &0) tRVZero)
/-- **Nontriviality**: some nonzero element of `VF` has value strictly below the value of `1`, i.e. lies in the maximal ideal. -/ def axNontrivialRV : LRV.Sentence := exSorted .vf (∼(pEq &0 tVFZero) ⊓ ∼(pLe (tRv &0) (tRv tVFOne)))
/-- The inverse operation fixes the absorbing element `0 = ∞`. -/ def rvInvZero : LRV.Sentence := pEq (tRVInv tRVZero) tRVZero
/-- The named inverse is a multiplicative inverse on the nonzero `RV` group. -/ def rvInvMul : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pEq (tRVMul (tRVInv &0) &0) tRVOne)
/-- The added axioms, in one theory. -/ def repairRV : LRV.Theory := ofList [rvMulOneRV, rvMulInvRV, leMulCompatFull, kAddLink, kNegLink, rvEqLink, kJunkZero, kNegJunkZero, axNontrivialRV, rvInvZero, rvInvMul]
/-- the paper's own content of `ACVF`: Definition 2.2, items 1–6 -/ def ACVFpaper : LRV.Theory := vfField ∪ vfAlgClosed ∪ rvGroup ∪ kField ∪ kAlgClosed ∪ preorderRV ∪ rvAxioms ∪ repairRV ∪ repairRV
/-- **The theory `ACVF` of Definition 2.2**, in the tagged encoding: items 1–6 plus the sort discipline of the encoding. -/ def ACVF : LRV.Theory := sortAxioms ∪ ACVFpaper
/-- characteristic zero of the `VF` sort -/ def charZeroVF (k : ℕ) : LRV.Sentence := ∼(pEq (tVFNumeral (k + 1)) tVFZero)
/-- residue characteristic zero: for each prime `p`, `p · 1` is a unit of the valuation ring, i.e. `¬ (1 < rv(p·1))` -/ def residueCharZero (p : ℕ) : LRV.Sentence := ∼(pGtOne (tRv (tVFNumeral p)))
/-- **The theory `ACVF(0,0)`**: `ACVF` with pure characteristic `0`, i.e. characteristic `0` for the valued field and characteristic `0` for its residue field. -/ def ACVF00 : LRV.Theory := ACVF ∪ {s | ∃ k, s = charZeroVF k} ∪ {s | ∃ p, p.Prime ∧ s = residueCharZero p}
end Axioms
open Axioms
open LRV
/-- Whether an element of a model has a given sort. -/ def sortEval {M : Type*} [LRV.Structure M] : SortTag → M → Prop
  | .vf => fun x => Structure.RelMap (L := LRV) Rel.memVF ![x]
  | .rv => fun x => Structure.RelMap (L := LRV) Rel.memRV ![x]
variable {M : Type*} [LRV.Structure M]
/-- `x` lies in the `VF` sort -/ def iVF (x : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memVF ![x]
/-- `x` lies in the `RV` sort -/ def iRV (x : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memRV ![x]
/-- the interpretation of `+` of the `VF` sort -/ def iVFAdd (x y : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfAdd ![x, y]
/-- the interpretation of `-` of the `VF` sort -/ def iVFNeg (x : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfNeg ![x]
/-- the interpretation of `×` of the `VF` sort -/ def iVFMul (x y : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfMul ![x, y]
/-- the interpretation of the projection `rv : VF → RV` -/ def iRv (x : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvMap ![x]
/-- the interpretation of `0` of the `RV` sort -/ def iRVZero : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvZero fun i => i.elim0
end Milestone0
end SpecialTransformations
end
reset_statement_module_caches
section
open Classical
open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Milestone0.Transfer
/-- `0` of the `VF` sort -/ def iVFZero {M : Type} [LRV.Structure M] : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfZero fun i => i.elim0
/-- `1` of the `VF` sort -/ def iVFOne {M : Type} [LRV.Structure M] : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfOne fun i => i.elim0
end SpecialTransformations.Milestone0.Transfer
set_option linter.unusedSimpArgs false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Milestone0.Transfer
variable {M : Type} [LRV.Structure M]
theorem rv_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iRV (iRv x) := by sorry
end SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Milestone0.Transfer
variable {M : Type} [LRV.Structure M]
theorem vf_zero_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iVF (iVFZero (M := M))  := by sorry
theorem vf_one_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iVF (iVFOne (M := M))  := by sorry
theorem vf_add_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVF (iVFAdd x y)  := by sorry
theorem vf_neg_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVF (iVFNeg x)  := by sorry
theorem vf_mul_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVF (iVFMul x y)  := by sorry
end SpecialTransformations.Milestone0.Transfer
end
reset_statement_module_caches
section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Milestone0
namespace Transfer
theorem vf_add_assoc {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFAdd (iVFAdd x y) z = iVFAdd x (iVFAdd y z) := by sorry
theorem vf_add_comm {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVFAdd x y = iVFAdd y x := by sorry
theorem vf_add_zero {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVFAdd x iVFZero = x := by sorry
theorem vf_add_neg {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVFAdd x (iVFNeg x) = iVFZero := by sorry
theorem vf_mul_assoc {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFMul (iVFMul x y) z = iVFMul x (iVFMul y z) := by sorry
theorem vf_mul_comm {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVFMul x y = iVFMul y x := by sorry
theorem vf_mul_one {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVFMul x iVFOne = x := by sorry
theorem vf_left_distrib {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFMul x (iVFAdd y z) = iVFAdd (iVFMul x y) (iVFMul x z) := by sorry
/-- `0 ≠ 1` on the `VF` sort. -/ theorem vf_zero_ne_one {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iVFZero (M := M) ≠ iVFOne := by sorry
/-- **The invertibility law**: a `VF`-element is `0` or has a multiplicative inverse. The encoding states it this way because the language has no inverse symbol. -/ theorem vf_mul_inv_or_zero {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : x = iVFZero ∨ ∃ y : M, iVF y ∧ iVFMul x y = iVFOne := by sorry
section VFField
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- The `VF` sort of an `ACVF`-model, as a type. -/ def VFType : Type := { x : M // iVF x }
instance vfInstZero : Zero (VFType (M := M)) := ⟨⟨iVFZero, vf_zero_mem hM⟩⟩
instance vfInstOne : One (VFType (M := M)) := ⟨⟨iVFOne, vf_one_mem hM⟩⟩
instance vfInstAdd : Add (VFType (M := M)) := ⟨fun x y => ⟨iVFAdd x.1 y.1, vf_add_mem hM x.2 y.2⟩⟩
instance vfInstNeg : Neg (VFType (M := M)) := ⟨fun x => ⟨iVFNeg x.1, vf_neg_mem hM x.2⟩⟩
instance vfInstMul : Mul (VFType (M := M)) := ⟨fun x y => ⟨iVFMul x.1 y.1, vf_mul_mem hM x.2 y.2⟩⟩
/-- The inverse on the `VF` sort: `0⁻¹ = 0`, and a nonzero element inverts by the invertibility law. -/ noncomputable def vfInvFun (x : VFType (M := M)) : VFType (M := M) := by
  classical
    exact
    if h : x.1 = iVFZero then 0
    else
      let w := (vf_mul_inv_or_zero hM x.2).resolve_left h
      ⟨Classical.choose w, (Classical.choose_spec w).1⟩
noncomputable instance vfInstInv : Inv (VFType (M := M)) := ⟨vfInvFun⟩
theorem vfInv_zero : (0 : VFType (M := M))⁻¹ = 0 := by sorry
theorem vfInv_val {x : VFType (M := M)} (hx : x ≠ 0) : iVFMul x.1 ((x⁻¹ : VFType (M := M))).1 = iVFOne := by sorry
/-- **The `VF` sort is a field.** -/ noncomputable def vfFieldOfModel : Field (VFType (M := M)) := Field.ofMinimalAxioms (VFType (M := M)) (fun a b c => Subtype.ext (vf_add_assoc hM a.2 b.2 c.2))
    (fun a =>
      Subtype.ext
        (by
          show iVFAdd iVFZero a.1 = a.1
          rw [vf_add_comm hM (vf_zero_mem hM) a.2]
          exact vf_add_zero hM a.2))
    (fun a =>
      Subtype.ext
        (by
          show iVFAdd (iVFNeg a.1) a.1 = iVFZero
          rw [vf_add_comm hM (vf_neg_mem hM a.2) a.2]
          exact vf_add_neg hM a.2))
    (fun a b c => Subtype.ext (vf_mul_assoc hM a.2 b.2 c.2)) (fun a b => Subtype.ext (vf_mul_comm hM a.2 b.2))
    (fun a =>
      Subtype.ext
        (by
          show iVFMul iVFOne a.1 = a.1
          rw [vf_mul_comm hM (vf_one_mem hM) a.2]
          exact vf_mul_one hM a.2))
    (fun a ha => Subtype.ext (vfInv_val ha)) vfInv_zero (fun a b c => Subtype.ext (vf_left_distrib hM a.2 b.2 c.2)) ⟨0, 1, fun h => vf_zero_ne_one hM (congrArg Subtype.val h)⟩
end VFField
end Transfer
end SpecialTransformations.Milestone0
end
reset_statement_module_caches
section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Milestone0.VFValued
section Model
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- The `Field` structure on the `VF` sort, as an instance, so that `IsValPred`'s `CommRing` requirement is discharged by typeclass search. -/ noncomputable instance instFieldVFType : Field (Transfer.VFType (M := M)) := Transfer.vfFieldOfModel (M := M) (hM := hM)
end Model
end SpecialTransformations.Milestone0.VFValued
end
reset_statement_module_caches
section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section5
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
abbrev VF := VFType (M := M)
abbrev RV := { t : M // iRV t }
abbrev Point (n m : ℕ) := (Fin n → VF (M := M)) × (Fin m → RV (M := M))
abbrev Key (n m : ℕ) := (Fin n → RV (M := M)) × (Fin m → RV (M := M))
def rv (x : VF (M := M)) : RV (M := M) := ⟨iRv x.val, rv_mem hM x.property⟩
def key {n m : ℕ} (p : Point (M := M) n m) : Key (M := M) n m := (fun i => rv (p.1 i), p.2)
def SameRV {n m : ℕ} (p q : Point (M := M) n m) : Prop := key p = key q
def hull {n m : ℕ} (A : Set (Point (M := M) n m)) : Set (Point (M := M) n m) := {q | ∃ p ∈ A, SameRV p q}
def IsRVPullback {n m : ℕ} (A : Set (Point (M := M) n m)) : Prop := hull A = A
/-- The canonical bijection appends all current VF leading terms. -/ def canonical {n m : ℕ} (p : Point (M := M) n m) : Point (M := M) n (n + m) := (p.1, Fin.append (fun i => rv (p.1 i)) p.2)
end SpecialTransformations.Section5
end
reset_statement_module_caches
section
open FirstOrder FirstOrder.Language
namespace SpecialTransformations.DefinableGeometry
variable {L : Language} {M : Type} [L.Structure M]
structure Space (L : Language) (M : Type) [L.Structure M] where
  Carrier : Type
  Index : Type
  finiteIndex : Finite Index
  domain : Set (Index → M)
  domain_definable : (∅ : Set M).Definable L domain
  decode : domain → Carrier
  onto : Function.Surjective decode
  diagonal_definable : (∅ : Set M).Definable L {z : Index ⊕ Index → M | ∃ hx : z ∘ Sum.inl ∈ domain, ∃ hy : z ∘ Sum.inr ∈ domain, decode ⟨z ∘ Sum.inl, hx⟩ = decode ⟨z ∘ Sum.inr, hy⟩}
attribute [instance] Space.finiteIndex
namespace Space
variable (P Q R : Space L M)
def preimage (A : Set P.Carrier) : Set (P.Index → M) := {z | ∃ hz : z ∈ P.domain, P.decode ⟨z, hz⟩ ∈ A}
def relation (r : P.Carrier → Q.Carrier → Prop) : Set (P.Index ⊕ Q.Index → M) := {z | ∃ hx : z ∘ Sum.inl ∈ P.domain, ∃ hy : z ∘ Sum.inr ∈ Q.domain, r (P.decode ⟨z ∘ Sum.inl, hx⟩) (Q.decode ⟨z ∘ Sum.inr, hy⟩)}
def Definable (S : Set M) (A : Set P.Carrier) : Prop := S.Definable L (P.preimage A)
def RelationDefinable (S : Set M) (r : P.Carrier → Q.Carrier → Prop) : Prop := S.Definable L (P.relation Q r)
theorem definable_univ (S : Set M) : P.Definable S Set.univ := by sorry
theorem Definable.inter {S : Set M} {A B : Set P.Carrier} (hA : P.Definable S A) (hB : P.Definable S B) : P.Definable S (A ∩ B) := by sorry
theorem Definable.sdiff {S : Set M} {A B : Set P.Carrier} (hA : P.Definable S A) (hB : P.Definable S B) : P.Definable S (A \ B) := by sorry
theorem relation_eq_definable (S : Set M) : P.RelationDefinable P S Eq := by sorry
theorem RelationDefinable.congr {S : Set M} {r t : P.Carrier → Q.Carrier → Prop} (hr : P.RelationDefinable Q S r) (h : ∀ x y, r x y ↔ t x y) : P.RelationDefinable Q S t := by sorry
theorem RelationDefinable.inter {S : Set M} {r t : P.Carrier → Q.Carrier → Prop} (hr : P.RelationDefinable Q S r) (ht : P.RelationDefinable Q S t) : P.RelationDefinable Q S (fun x y => r x y ∧ t x y) := by sorry
theorem RelationDefinable.union {S : Set M} {r t : P.Carrier → Q.Carrier → Prop} (hr : P.RelationDefinable Q S r) (ht : P.RelationDefinable Q S t) : P.RelationDefinable Q S (fun x y => r x y ∨ t x y) := by sorry
theorem Definable.left_relation {S : Set M} {A : Set P.Carrier} (hA : P.Definable S A) : P.RelationDefinable Q S (fun x _ => x ∈ A) := by sorry
theorem RelationDefinable.swap {S : Set M} {r : P.Carrier → Q.Carrier → Prop} (hr : P.RelationDefinable Q S r) : Q.RelationDefinable P S (fun y x => r x y) := by sorry
theorem RelationDefinable.comp {S : Set M} {r : P.Carrier → Q.Carrier → Prop} {t : Q.Carrier → R.Carrier → Prop} (hr : P.RelationDefinable Q S r) (ht : Q.RelationDefinable R S t) : P.RelationDefinable R S (fun x z => ∃ y, r x y ∧ t y z) := by sorry
end Space
namespace Space
variable (P Q : Space L M)
/-- Product presentations use every pair of real codes. -/ def prod : Space L M where
  Carrier := P.Carrier × Q.Carrier
  Index := P.Index ⊕ Q.Index
  finiteIndex := inferInstance
  domain := {z | z ∘ Sum.inl ∈ P.domain ∧ z ∘ Sum.inr ∈ Q.domain}
  domain_definable := (P.domain_definable.preimage_comp Sum.inl).inter (Q.domain_definable.preimage_comp Sum.inr)
  decode z := (P.decode ⟨z.val ∘ Sum.inl, z.property.1⟩, Q.decode ⟨z.val ∘ Sum.inr, z.property.2⟩)
  onto := by
    rintro ⟨x, y⟩
    obtain ⟨c, rfl⟩ := P.onto x
    obtain ⟨d, rfl⟩ := Q.onto y
    exact ⟨⟨Sum.elim c.val d.val, c.property, d.property⟩, rfl⟩
  diagonal_definable := by
    have hp := P.diagonal_definable.preimage_comp (Sum.map (Sum.inl : P.Index → P.Index ⊕ Q.Index) (Sum.inl : P.Index → P.Index ⊕ Q.Index))
    have hq := Q.diagonal_definable.preimage_comp (Sum.map (Sum.inr : Q.Index → P.Index ⊕ Q.Index) (Sum.inr : Q.Index → P.Index ⊕ Q.Index))
    convert hp.inter hq using 1
    ext z
    constructor
    · rintro ⟨hx, hy, he⟩
      exact ⟨⟨hx.1, hy.1, congrArg Prod.fst he⟩, ⟨hx.2, hy.2, congrArg Prod.snd he⟩⟩
    · rintro ⟨⟨hx, hy, hp⟩, ⟨hx', hy', hq⟩⟩
      exact ⟨⟨hx, hx'⟩, ⟨hy, hy'⟩, Prod.ext hp hq⟩
theorem Definable.prod {S : Set M} {A : Set P.Carrier} {B : Set Q.Carrier} (hA : P.Definable S A) (hB : Q.Definable S B) : (P.prod Q).Definable S (A ×ˢ B) := by sorry
end Space
/-- A definable set retains its actual carrier and original parameter base. -/ structure DefSet (P : Space L M) (S : Set M) where
  carrier : Set P.Carrier
  definable : P.Definable S carrier
namespace DefSet
variable {P Q : Space L M} {S : Set M}
instance : CoeSort (DefSet P S) Type := ⟨fun A => A.carrier⟩
def univ (P : Space L M) (S : Set M) : DefSet P S := ⟨Set.univ, P.definable_univ S⟩
def prod (A : DefSet P S) (B : DefSet Q S) : DefSet (P.prod Q) S := ⟨A.carrier ×ˢ B.carrier, A.definable.prod P Q B.definable⟩
end DefSet
/-- A genuine function of subtypes, with its entire graph definable. -/ structure Map {P Q : Space L M} {S : Set M} (A : DefSet P S) (B : DefSet Q S) where
  toFun : A → B
  graph_definable : P.RelationDefinable Q S (fun x y => ∃ a : A, a.val = x ∧ (toFun a).val = y)
namespace Map
variable {P Q R : Space L M} {S : Set M}
variable {A : DefSet P S} {B : DefSet Q S} {C : DefSet R S}
instance : CoeFun (Map A B) (fun _ => A → B) := ⟨Map.toFun⟩
def id (A : DefSet P S) : Map A A where
  toFun := _root_.id
  graph_definable :=   ((A.definable.left_relation P P).inter P P (P.relation_eq_definable S)).congr P P
      (by
        intro x y
        constructor
        · rintro ⟨hx, rfl⟩
          exact ⟨⟨x, hx⟩, rfl, rfl⟩
        · rintro ⟨a, rfl, rfl⟩
          exact ⟨a.property, rfl⟩)
def comp (g : Map B C) (f : Map A B) : Map A C where
  toFun a := g (f a)
  graph_definable :=   (f.graph_definable.comp P Q R g.graph_definable).congr P R
      (by
        intro x z
        constructor
        · rintro ⟨y, ⟨a, rfl, rfl⟩, ⟨b, hb, hg⟩⟩
          have he : b = f a := Subtype.ext hb
          subst b
          exact ⟨a, rfl, hg⟩
        · rintro ⟨a, rfl, hg⟩
          exact ⟨(f a).val, ⟨a, rfl, rfl⟩, ⟨f a, rfl, hg⟩⟩)
def inclusion {A' : DefSet P S} (h : A'.carrier ⊆ A.carrier) : Map A' A where
  toFun a := ⟨a.val, h a.property⟩
  graph_definable :=   ((A'.definable.left_relation P P).inter P P (P.relation_eq_definable S)).congr P P
      (by
        intro x y
        constructor
        · rintro ⟨hx, rfl⟩
          exact ⟨⟨x, hx⟩, rfl, rfl⟩
        · rintro ⟨a, rfl, rfl⟩
          exact ⟨a.property, rfl⟩)
theorem definable_image (f : Map A B) : Q.Definable S (Set.range (fun a => (f a).val)) := by sorry
end Map
end SpecialTransformations.DefinableGeometry
end
reset_statement_module_caches
section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
namespace CanonicalStructure
variable {M : Type} [sM : LRV.Structure M]
def sortZero (s : SortTag) : M := match s with
  | .vf => Transfer.iVFZero
  | .rv => iRVZero
/-- Correctly sorted applications retain their original interpretation. Wrong-sort applications return the named zero of the result sort. -/ @[instance_reducible]
noncomputable def normalize : LRV.Structure M where
  funMap f xs := if ∀ i, sortEval (Fn.argSort f i) (xs i) then Structure.funMap (L := LRV) f xs else sortZero (Fn.resSort f)
  RelMap r
    xs :=   match r with
    | .memVF => Structure.RelMap (L := LRV) Rel.memVF xs
    | .memRV => Structure.RelMap (L := LRV) Rel.memRV xs
    | .memUnits => Structure.RelMap (L := LRV) Rel.memUnits xs
    | .rvLe => (∀ i, sortEval .rv (xs i)) ∧ Structure.RelMap (L := LRV) Rel.rvLe xs
end CanonicalStructure
end
reset_statement_module_caches
section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M]
def FinitelySatisfiable {α : Type} {n : ℕ} (v : α → M) (p : Set (LRV.BoundedFormula α n)) : Prop := ∀ l : List (LRV.BoundedFormula α n), (∀ φ ∈ l, φ ∈ p) → ∃ x : Fin n → M, ∀ φ ∈ l, φ.Realize v x
def Saturated (M : Type) [LRV.Structure M] (κ : Cardinal) : Prop := ∀ (α : Type) (v : α → M), Cardinal.mk α < κ → ∀ {n : ℕ} (p : Set (LRV.BoundedFormula α n)), FinitelySatisfiable v p → ∃ x : Fin n → M, ∀ φ ∈ p, φ.Realize v x
end SpecialTransformations.Section3
end
reset_statement_module_caches
section
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.Coordinates
variable {M : Type} [LRV.Structure M] {ι : Type}
abbrev Tuple (σ : ι → SortTag) := ∀ i, { x : M // sortEval (σ i) x }
end SpecialTransformations.Section3.Coordinates
end
reset_statement_module_caches
section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace SpecialTransformations.Section4
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
abbrev Space := @DefinableGeometry.Space LRV M (CanonicalStructure.normalize (M := M))
abbrev RawDefinable (S : Set M) {ι : Type} (A : Set (ι → M)) := @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ι A
theorem coordinate_equality_definable (S : Set M) {ι : Type} (i j : ι) : RawDefinable S {z : ι → M | z i = z j} := by sorry
theorem tuple_domain_definable (S : Set M) {ι : Type} [Finite ι] (σ : ι → SortTag) : RawDefinable S {z : ι → M | ∀ i, sortEval (σ i) (z i)} := by sorry
/-- The full finite product of any specified real sorts. -/ def realSpace {ι : Type} [Finite ι] (σ : ι → SortTag) : Space (M := M) := by
  let X := Coordinates.Tuple (M := M) σ
  let D : Set (ι → M) := {z | ∀ i, sortEval (σ i) (z i)}
  have hD := tuple_domain_definable (M := M) ∅ σ
  have hx := @Set.Definable.preimage_comp M ∅ LRV (CanonicalStructure.normalize (M := M)) ι (ι ⊕ ι) Sum.inl D hD
  have hy := @Set.Definable.preimage_comp M ∅ LRV (CanonicalStructure.normalize (M := M)) ι (ι ⊕ ι) Sum.inr D hD
  have he (i : ι) := coordinate_equality_definable (M := M) ∅ (Sum.inl i : ι ⊕ ι) (Sum.inr i)
  letI := CanonicalStructure.normalize (M := M)
  exact
    { Carrier := X
      Index := ι
      finiteIndex := inferInstance
      domain := D
      domain_definable := hD
      decode z i := ⟨z.val i, z.property i⟩
      onto x := ⟨⟨fun i => (x i).val, fun i => (x i).property⟩, rfl⟩
      diagonal_definable := by
        have hall := Set.definable_iInter_of_finite he
        convert hx.inter (hy.inter hall) using 1
        ext z
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
        constructor
        · rintro ⟨hx, hy, he⟩
          exact ⟨hx, hy, fun i => congrArg Subtype.val (congrFun he i)⟩
        · rintro ⟨hx, hy, he⟩
          exact ⟨hx, hy, funext (fun i => Subtype.ext (he i))⟩ }
abbrev vfSpace (n : ℕ) : Space (M := M) := realSpace (fun _ : Fin n => .vf)
abbrev rvSpace (n : ℕ) : Space (M := M) := realSpace (fun _ : Fin n => .rv)
end SpecialTransformations.Section4
end
reset_statement_module_caches
section
open FirstOrder FirstOrder.Language
namespace SpecialTransformations.DefinableGeometry
variable {L : Language} {M : Type} [L.Structure M]
namespace Space
variable (P Q R : Space L M)
theorem RelationDefinable.pair {S : Set M} {r : P.Carrier → Q.Carrier → Prop} {t : P.Carrier → R.Carrier → Prop} (hr : P.RelationDefinable Q S r) (ht : P.RelationDefinable R S t) : P.RelationDefinable (Q.prod R) S (fun x yz => r x yz.1 ∧ t x yz.2) := by sorry
end Space
namespace Map
variable {P Q R : Space L M} {S : Set M}
variable {A : DefSet P S} {B : DefSet Q S} {C : DefSet R S}
def pair (f : Map A B) (g : Map A C) : Map A (B.prod C) where
  toFun a := ⟨((f a).val, (g a).val), (f a).property, (g a).property⟩
  graph_definable :=   (f.graph_definable.pair P Q R g.graph_definable).congr P (Q.prod R)
      (by
        intro x yz
        constructor
        · rintro ⟨⟨a, rfl, hf⟩, ⟨b, hb, hg⟩⟩
          have he : b = a := Subtype.ext hb
          subst b
          exact ⟨a, rfl, Prod.ext hf hg⟩
        · rintro ⟨a, rfl, he⟩
          exact ⟨⟨a, rfl, congrArg Prod.fst he⟩, ⟨a, rfl, congrArg Prod.snd he⟩⟩)
def image (f : Map A B) : DefSet Q S := ⟨Set.range (fun a => (f a).val), f.definable_image⟩
def toImage (f : Map A B) : Map A f.image where
  toFun a := ⟨(f a).val, Set.mem_range_self a⟩
  graph_definable := f.graph_definable
end Map
end SpecialTransformations.DefinableGeometry
end
reset_statement_module_caches
section
open Classical FirstOrder FirstOrder.Language
namespace SpecialTransformations.DefinableGeometry
variable {L : Language} {M : Type} [L.Structure M]
namespace Map
variable {P Q : Space L M} {S : Set M}
/-- A definable real-code map which descends to the presented values gives a definable map. Its graph includes every target representative. -/ def ofCodes (A : DefSet P S) (f : P.Carrier → Q.Carrier) (F : (P.Index → M) → Q.Index → M) (hF : S.DefinableMap L F) (hdom : ∀ c : P.domain, F c.val ∈ Q.domain) (hdecode : ∀ c : P.domain, Q.decode ⟨F c.val, hdom c⟩ = f (P.decode c)) : Map A (DefSet.univ Q S) where
  toFun a := ⟨f a.val, Set.mem_univ _⟩
  graph_definable := by
    let T (z : P.Index ⊕ Q.Index → M) : Q.Index ⊕ Q.Index → M := Sum.elim (F (z ∘ Sum.inl)) (z ∘ Sum.inr)
    have hT : S.DefinableMap L T := by
      intro i
      cases i with
      | inl i => exact (hF i).comp (show S.DefinableMap L (fun z : P.Index ⊕ Q.Index → M => z ∘ Sum.inl) from fun _ => Set.DefinableFun.proj L)
      | inr i => exact Set.DefinableFun.proj L
    have hdiag := (Q.diagonal_definable.mono (Set.empty_subset S)).preimage_map hT
    have hA := A.definable.preimage_comp (Sum.inl : P.Index → P.Index ⊕ Q.Index)
    change S.Definable L _
    convert hA.inter hdiag using 1
    ext z
    constructor
    · rintro ⟨hc, hd, a, ha, he⟩
      have hmem : P.decode ⟨z ∘ Sum.inl, hc⟩ ∈ A.carrier := ha ▸ a.property
      refine ⟨⟨hc, hmem⟩, hdom ⟨z ∘ Sum.inl, hc⟩, hd, ?_⟩
      change Q.decode ⟨F (z ∘ Sum.inl), hdom ⟨z ∘ Sum.inl, hc⟩⟩ = Q.decode ⟨z ∘ Sum.inr, hd⟩
      rw [hdecode ⟨z ∘ Sum.inl, hc⟩]
      exact (congrArg f ha).symm.trans he
    · rintro ⟨⟨hc, ha⟩, hf, hd, he⟩
      refine ⟨hc, hd, ⟨P.decode ⟨z ∘ Sum.inl, hc⟩, ha⟩, rfl, ?_⟩
      change f (P.decode ⟨z ∘ Sum.inl, hc⟩) = Q.decode ⟨z ∘ Sum.inr, hd⟩
      rw [← hdecode ⟨z ∘ Sum.inl, hc⟩]
      exact he
end Map
end SpecialTransformations.DefinableGeometry
end
reset_statement_module_caches
section
open Classical FirstOrder FirstOrder.Language CategoryTheory
namespace SpecialTransformations.DefinableGeometry
variable {L : Language} {M : Type} [L.Structure M]
namespace Map
variable {P Q : Space L M} {S : Set M} {A : DefSet P S} {B : DefSet Q S}
/-- A definable bijection has a definable inverse over the same base. -/ noncomputable def inverse (f : Map A B) (hf : Function.Bijective f) : Map B A where
  toFun := (Equiv.ofBijective f hf).symm
  graph_definable :=   (f.graph_definable.swap P Q).congr Q P
      (by
        intro y x
        let e : A ≃ B := Equiv.ofBijective f hf
        constructor
        · rintro ⟨a, ha, hf⟩
          refine ⟨e a, hf, ?_⟩
          change (e.symm (e a)).val = x
          simpa only [Equiv.symm_apply_apply] using ha
        · rintro ⟨b, hb, hi⟩
          refine ⟨e.symm b, hi, ?_⟩
          change (e (e.symm b)).val = y
          simpa only [Equiv.apply_symm_apply] using hb)
end Map
end SpecialTransformations.DefinableGeometry
end
reset_statement_module_caches
section
noncomputable section
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section5
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n m : ℕ}
noncomputable def replace (j : Fin n) (p : Point (M := M) n m) (a : VF (M := M)) : Point (M := M) n m := (Function.update p.1 j a, p.2)
noncomputable def erase (j : Fin n) (p : Point (M := M) n m) : Point (M := M) n m := replace j p 0
def Tagged (A : Set (Point (M := M) n m)) (j : Fin n) (k : Fin m) : Prop := ∀ p ∈ A, p.2 k = rv (p.1 j)
structure FocusGeometry (A : Set (Point (M := M) n m)) (j : Fin n) (k : Fin m) where
  tagged : Tagged A j k
  locus : Set (Point (M := M) n m)
  locus_pullback : IsRVPullback locus
  locus_subset : locus ⊆ hull A
  center : Point (M := M) n m → VF (M := M)
  independent : ∀ p ∈ A ∩ locus, ∀ q ∈ A ∩ locus, erase j p = erase j q → center p = center q
  center_mem : ∀ p ∈ A ∩ locus, replace j p (center p) ∈ locus
namespace FocusGeometry
variable {A : Set (Point (M := M) n m)} {j : Fin n} {k : Fin m}
noncomputable def eta (D : FocusGeometry A j k) (p : Point (M := M) n m) : Point (M := M) n m := if p ∈ D.locus then replace j p (p.1 j - D.center p) else p
end FocusGeometry
end SpecialTransformations.Section5
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
namespace SpecialTransformations.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
abbrev PresentedSpace := @DefinableGeometry.Space LRV M (CanonicalStructure.normalize (M := M))
abbrev pointSpace (n m : ℕ) : PresentedSpace (M := M) := @DefinableGeometry.Space.prod LRV M (CanonicalStructure.normalize (M := M)) (Section4.vfSpace n) (Section4.rvSpace m)
abbrev PresentedSet (P : PresentedSpace (M := M)) (S : Set M) := @DefinableGeometry.DefSet LRV M (CanonicalStructure.normalize (M := M)) P S
abbrev spaceProd (P Q : PresentedSpace (M := M)) : PresentedSpace (M := M) := @DefinableGeometry.Space.prod LRV M (CanonicalStructure.normalize (M := M)) P Q
abbrev Carrier (P : PresentedSpace (M := M)) := @DefinableGeometry.Space.Carrier LRV M (CanonicalStructure.normalize (M := M)) P
abbrev SetDefinable (P : PresentedSpace (M := M)) (S : Set M) (A : Set (Carrier P)) := @DefinableGeometry.Space.Definable LRV M (CanonicalStructure.normalize (M := M)) P S A
abbrev RelationDefinable (P Q : PresentedSpace (M := M)) (S : Set M) (r : Carrier P → Carrier Q → Prop) := @DefinableGeometry.Space.RelationDefinable LRV M (CanonicalStructure.normalize (M := M)) P Q S r
abbrev DefSet (S : Set M) (n m : ℕ) := PresentedSet (pointSpace (M := M) n m) S
abbrev carrier {P : PresentedSpace (M := M)} {S : Set M} (A : PresentedSet P S) := @DefinableGeometry.DefSet.carrier LRV M (CanonicalStructure.normalize (M := M)) P S A
abbrev setDefinable {P : PresentedSpace (M := M)} {S : Set M} (A : PresentedSet P S) := @DefinableGeometry.DefSet.definable LRV M (CanonicalStructure.normalize (M := M)) P S A
abbrev Map {P Q : PresentedSpace (M := M)} {S : Set M} (A : PresentedSet P S) (B : PresentedSet Q S) := @DefinableGeometry.Map LRV M (CanonicalStructure.normalize (M := M)) P Q S A B
namespace PresentedSet
abbrev mk := @DefinableGeometry.DefSet.mk LRV M (CanonicalStructure.normalize (M := M))
abbrev univ := @DefinableGeometry.DefSet.univ LRV M (CanonicalStructure.normalize (M := M))
abbrev prod := @DefinableGeometry.DefSet.prod LRV M (CanonicalStructure.normalize (M := M))
end PresentedSet
namespace Map
abbrev mk := @DefinableGeometry.Map.mk LRV M (CanonicalStructure.normalize (M := M))
abbrev ofCodes := @DefinableGeometry.Map.ofCodes LRV M (CanonicalStructure.normalize (M := M))
abbrev id := @DefinableGeometry.Map.id LRV M (CanonicalStructure.normalize (M := M))
abbrev comp := @DefinableGeometry.Map.comp LRV M (CanonicalStructure.normalize (M := M))
abbrev pair := @DefinableGeometry.Map.pair LRV M (CanonicalStructure.normalize (M := M))
abbrev image := @DefinableGeometry.Map.image LRV M (CanonicalStructure.normalize (M := M))
abbrev toImage := @DefinableGeometry.Map.toImage LRV M (CanonicalStructure.normalize (M := M))
abbrev inverse := @DefinableGeometry.Map.inverse LRV M (CanonicalStructure.normalize (M := M))
abbrev inclusion := @DefinableGeometry.Map.inclusion LRV M (CanonicalStructure.normalize (M := M))
abbrev graph_definable := @DefinableGeometry.Map.graph_definable LRV M (CanonicalStructure.normalize (M := M))
end Map
namespace SetDefinable
abbrev inter := @DefinableGeometry.Space.Definable.inter LRV M (CanonicalStructure.normalize (M := M))
abbrev sdiff := @DefinableGeometry.Space.Definable.sdiff LRV M (CanonicalStructure.normalize (M := M))
end SetDefinable
namespace RelationDefinable
abbrev congr := @DefinableGeometry.Space.RelationDefinable.congr LRV M (CanonicalStructure.normalize (M := M))
abbrev union := @DefinableGeometry.Space.RelationDefinable.union LRV M (CanonicalStructure.normalize (M := M))
end RelationDefinable
abbrev RawFun (S : Set M) (α : Type) (f : (α → M) → M) := @Set.DefinableFun M LRV (CanonicalStructure.normalize (M := M)) α S f
theorem rawProj (S : Set M) {α : Type} (i : α) : RawFun S α (fun z => z i) := by sorry
def rvCode (x : M) : M := @iRv M (CanonicalStructure.normalize (M := M)) x
def subCode (x y : M) : M := @iVFAdd M (CanonicalStructure.normalize (M := M)) x (@iVFNeg M (CanonicalStructure.normalize (M := M)) y)
public def vfSub (x y : VF (M := M)) : VF (M := M) := x - y
theorem rvCode_eq (x : M) (hx : iVF x) : rvCode x = iRv x := by sorry
theorem subCode_eq (x y : VF (M := M)) : subCode x.val y.val = (x - y).val := by sorry
theorem rvCode_definable (S : Set M) {α : Type} (i : α) : RawFun S α (fun z => rvCode (z i)) := by sorry
theorem subCode_definable (S : Set M) {α : Type} (i j : α) : RawFun S α (fun z => subCode (z i) (z j)) := by sorry
def canonicalCodes {n m : ℕ} (z : Fin n ⊕ Fin m → M) : Fin n ⊕ Fin (n + m) → M := Sum.elim (z ∘ Sum.inl) (Fin.append (fun i => rvCode (z (.inl i))) (z ∘ Sum.inr))
def canonicalMap {n m : ℕ} {S : Set M} (A : DefSet (M := M) S n m) : Map A (PresentedSet.univ (pointSpace n (n + m)) S) := Map.ofCodes (M := M) (sM := sM) (P := pointSpace n m) (Q := pointSpace n (n + m)) A (@canonical M sM hM n m) (canonicalCodes (M := M) (sM := sM) (n := n) (m := m))
    (by
      intro i
      cases i with
      | inl i => exact rawProj S (Sum.inl i : Fin n ⊕ Fin m)
      | inr i =>
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa [canonicalCodes] using rvCode_definable S (Sum.inl j : Fin n ⊕ Fin m)
        · simpa [canonicalCodes] using rawProj S (Sum.inr j : Fin n ⊕ Fin m))
    (by
      intro c
      change (∀ i, iVF (canonicalCodes c.val (.inl i))) ∧ ∀ i, iRV (canonicalCodes c.val (.inr i))
      refine ⟨c.property.1, ?_⟩
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [canonicalCodes, Sum.elim_inr, Fin.append_left]
        rw [rvCode_eq (sM := sM) (c.val (Sum.inl j)) (by simpa [Function.comp_def, sortEval, iVF] using c.property.1 j)]
        exact rv_mem hM (c.property.1 j)
      · simpa [canonicalCodes, Function.comp_def, sortEval, iRV] using c.property.2 j)
    (by
      intro c
      refine Prod.ext ?_ ?_
      · rfl
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · apply Subtype.ext
        simpa [canonicalCodes, canonical, rv] using rvCode_eq (sM := sM) (c.val (Sum.inl j)) (by simpa [Function.comp_def, sortEval, iVF] using c.property.1 j)
      · simp [canonicalCodes, canonical])
def canonicalImage {n m : ℕ} {S : Set M} (A : DefSet (M := M) S n m) : DefSet (M := M) S n (n + m) := Map.image (canonicalMap A)
end SpecialTransformations.Section5
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
namespace SpecialTransformations.Section5
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}
structure Focus (A : DefSet (M := M) S n m) (j : Fin n) (k : Fin m) extends FocusGeometry (carrier A) j k where
  locus_definable : SetDefinable (pointSpace n m) S locus
  center_graph : RelationDefinable (pointSpace n m) (Section4.vfSpace 1) S (fun p z => p ∈ carrier A ∩ locus ∧ z 0 = center p)
def subtractCodes (j : Fin n) (z : ((Fin n ⊕ Fin m) ⊕ Fin 1) → M) : Fin n ⊕ Fin m → M := Sum.elim (fun i => if i = j then subCode (z (.inl (.inl j))) (z (.inr 0)) else z (.inl (.inl i))) (fun i => z (.inl (.inr i)))
def subtractMap (j : Fin n) (A : PresentedSet (spaceProd (pointSpace (M := M) n m) (Section4.vfSpace 1)) S) : Map A (PresentedSet.univ (pointSpace n m) S) := Map.ofCodes (M := M) (P := spaceProd (pointSpace n m) (Section4.vfSpace 1)) (Q := pointSpace n m) A (fun p => replace j p.1 (vfSub (p.1.1 j) (p.2 0))) (subtractCodes j)
    (by
      intro i
      cases i with
      | inl i =>
        by_cases hi : i = j
        · subst i
          simpa [subtractCodes] using subCode_definable S (Sum.inl (Sum.inl j) : (Fin n ⊕ Fin m) ⊕ Fin 1) (Sum.inr 0)
        · simpa [subtractCodes, hi] using rawProj S (Sum.inl (Sum.inl i) : (Fin n ⊕ Fin m) ⊕ Fin 1)
      | inr i => exact rawProj S (Sum.inl (Sum.inr i) : (Fin n ⊕ Fin m) ⊕ Fin 1))
    (by
      intro c
      refine ⟨?_, c.property.1.2⟩
      intro i
      by_cases hi : i = j
      · subst i
        simp only [subtractCodes, Sum.elim_inl, if_pos rfl, Function.comp_apply]
        change iVF (subCode (c.val (.inl (.inl j))) (c.val (.inr 0)))
        let x : VF (M := M) := ⟨c.val (.inl (.inl j)), by simpa [Function.comp_def, sortEval, iVF] using c.property.1.1 j⟩
        let y : VF (M := M) := ⟨c.val (.inr 0), by simpa [Function.comp_def, sortEval, iVF] using c.property.2 0⟩
        have hs : subCode (c.val (.inl (.inl j))) (c.val (.inr 0)) = (x - y).val := subCode_eq x y
        rw [hs]
        exact (x - y).property
      · simpa [subtractCodes, hi] using c.property.1.1 i)
    (by
      intro c
      refine Prod.ext ?_ ?_
      swap
      · rfl
      funext i
      by_cases hi : i = j
      · subst i
        apply Subtype.ext
        simpa [subtractCodes, replace, vfSub] using (subCode_eq (⟨c.val (.inl (.inl j)), c.property.1.1 j⟩ : VF (M := M)) (⟨c.val (.inr 0), c.property.2 0⟩ : VF (M := M)))
      · simp [subtractCodes, replace, hi])
namespace Focus
variable {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}
def active (D : Focus A j k) : DefSet (M := M) S n m := PresentedSet.mk (carrier A ∩ D.locus) (SetDefinable.inter _ (setDefinable A) D.locus_definable)
def inactive (D : Focus A j k) : DefSet (M := M) S n m := PresentedSet.mk (carrier A \ D.locus) (SetDefinable.sdiff _ (setDefinable A) D.locus_definable)
def centerMap (D : Focus A j k) : Map D.active (PresentedSet.univ (Section4.vfSpace 1) S) := Map.mk (fun p => ⟨![D.center p.val], Set.mem_univ _⟩)
    (RelationDefinable.congr _ _ D.center_graph
      (by
        intro p z
        constructor
        · rintro ⟨hp, hz⟩
          refine ⟨⟨p, hp⟩, rfl, ?_⟩
          funext i
          fin_cases i
          exact hz.symm
        · rintro ⟨a, rfl, rfl⟩
          exact ⟨a.property, rfl⟩))
def activeMap (D : Focus A j k) : Map D.active (PresentedSet.univ (pointSpace n m) S) := Map.comp (subtractMap j (PresentedSet.prod D.active (PresentedSet.univ (Section4.vfSpace 1) S))) (Map.pair (Map.id D.active) D.centerMap)
def inactiveMap (D : Focus A j k) : Map D.inactive (PresentedSet.univ (pointSpace n m) S) := Map.inclusion (Set.subset_univ _)
@[simp] theorem activeMap_apply (D : Focus A j k) (p : D.active) : (D.activeMap p).val = replace j p.val (vfSub (p.val.1 j) (D.center p.val)) := by sorry
@[simp] theorem inactiveMap_apply (D : Focus A j k) (p : D.inactive) : (D.inactiveMap p).val = p.val := by sorry
noncomputable def etaMap (D : Focus A j k) : Map A (PresentedSet.univ (pointSpace n m) S) := Map.mk (fun p => ⟨D.toFocusGeometry.eta p.val, Set.mem_univ _⟩)
    (RelationDefinable.congr _ _ (RelationDefinable.union _ _ (Map.graph_definable D.activeMap) (Map.graph_definable D.inactiveMap))
      (by
        intro p q
        constructor
        · rintro (⟨a, rfl, he⟩ | ⟨a, rfl, he⟩)
          · refine ⟨⟨a.val, a.property.1⟩, rfl, ?_⟩
            simpa [FocusGeometry.eta, vfSub, a.property.2] using he
          · refine ⟨⟨a.val, a.property.1⟩, rfl, ?_⟩
            simpa [FocusGeometry.eta, a.property.2] using he
        · rintro ⟨a, rfl, he⟩
          by_cases hc : a.val ∈ D.locus
          · left
            refine ⟨⟨a.val, a.property, hc⟩, rfl, ?_⟩
            simpa [FocusGeometry.eta, vfSub, hc] using he
          · right
            refine ⟨⟨a.val, a.property, hc⟩, rfl, ?_⟩
            simpa [FocusGeometry.eta, hc] using he))
noncomputable def etaImage (D : Focus A j k) : DefSet (M := M) S n m := Map.image D.etaMap
end Focus
end SpecialTransformations.Section5
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
namespace SpecialTransformations.Section5
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
inductive Primitive (S : Set M) (n : ℕ) : {m l : ℕ} → DefSet (M := M) S n m → DefSet (M := M) S n l → Type where
  | canonical {m : ℕ} (A : DefSet (M := M) S n m) : Primitive S n A (canonicalImage A)
  | centripetal {m : ℕ} {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m} (D : Focus A j k) : Primitive S n A D.etaImage
namespace Primitive
variable {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
noncomputable def toMap : Primitive S n A B → Map A B
  | .canonical A => Map.toImage (canonicalMap A)
  | .centripetal D => Map.toImage D.etaMap
end Primitive
inductive Chain (S : Set M) (n : ℕ) : {m l : ℕ} → DefSet (M := M) S n m → DefSet (M := M) S n l → Type where
  | nil {m : ℕ} (A : DefSet (M := M) S n m) : Chain S n A A
  | cons {m l k : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l} {C : DefSet (M := M) S n k} (p : Primitive S n A B) (tail : Chain S n B C) : Chain S n A C
namespace Chain
variable {S : Set M} {n m l k : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l} {C : DefSet (M := M) S n k}
noncomputable def toMap {m₁ m₂ : ℕ} {X : DefSet (M := M) S n m₁} {Y : DefSet (M := M) S n m₂} : Chain S n X Y → Map X Y
  | .nil A => Map.id A
  | .cons p tail => Map.comp tail.toMap p.toMap
/-- `none` permits either initial step. Thereafter `true` means centripetal and `false` canonical, so both sorts of repeated adjacent step are excluded. -/ def Alternating {m₁ m₂ : ℕ} {X : DefSet (M := M) S n m₁} {Y : DefSet (M := M) S n m₂} (previous : Option Bool) : Chain S n X Y → Prop
  | .nil _ => True
  | .cons (.canonical _) tail => previous ≠ some false ∧ tail.Alternating (some false)
  | .cons (.centripetal _) tail => previous ≠ some true ∧ tail.Alternating (some true)
def append {m₁ m₂ m₃ : ℕ} {X : DefSet (M := M) S n m₁} {Y : DefSet (M := M) S n m₂} {Z : DefSet (M := M) S n m₃} (t : Chain S n X Y) (u : Chain S n Y Z) : Chain S n X Z := match t with
  | .nil _ => u
  | .cons p tail => .cons p (tail.append u)
end Chain
structure SpecialBijection {S : Set M} {n m l : ℕ} (A : DefSet (M := M) S n m) (B : DefSet (M := M) S n l) where
  chain : Chain S n A B
  alternating : chain.Alternating none
namespace SpecialBijection
variable {S : Set M} {n m l k : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l} {C : DefSet (M := M) S n k}
noncomputable def toMap (T : SpecialBijection A B) : Map A B := T.chain.toMap
theorem bijective (T : SpecialBijection A B) : Function.Bijective T.toMap := by sorry
/-- The inverse, including a single centrifugal transformation, has its full graph definable over the original base. -/ noncomputable def inverseMap (T : SpecialBijection A B) : Map B A := Map.inverse T.toMap T.bijective
end SpecialBijection
def IsDeformedRVPullback {S : Set M} {n m : ℕ} (A : DefSet (M := M) S n m) : Prop := ∃ l : ℕ, ∃ B : DefSet (M := M) S n l, Nonempty (SpecialBijection A B) ∧ IsRVPullback (carrier B)
end SpecialTransformations.Section5
end
end
reset_statement_module_caches
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- A typed coordinate accessor keeps the shared VF field instance visible when a point is carried by a definable presentation. -/ def vfAt {n m : ℕ} (p : Point (M := M) n m) (i : Fin n) : VF (M := M) := p.1 i
end SpecialTransformations.Section5
end
end
reset_statement_module_caches
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace SpecialTransformations.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)
namespace Paper
theorem theorem_5_5 {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : Set M} (hsmall : Cardinal.mk S < κ) {n m : ℕ}
    {A₀ : DefSet (M := M) S n 0} {A : DefSet (M := M) S n m}
    (τ : SpecialBijection A₀ A) (p : MvPolynomial (Fin n) (VF (M := M)))
    (hc : ∀ d, (p.coeff d).val ∈ S) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S n r, ∃ T : SpecialBijection A B,
      (τ.chain.append T.chain).Alternating none ∧ IsRVPullback (carrier B) ∧
        ∀ b c : B, SameRV b.val c.val →
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (T.inverseMap b)).val) p) =
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (T.inverseMap c)).val) p)  := by sorry
theorem corollary_5_6 {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : Set M} (hsmall : Cardinal.mk S < κ) {n m : ℕ}
    (A : DefSet (M := M) S n m) : IsDeformedRVPullback A  := by sorry
end Paper
end SpecialTransformations.Section5
end
end
