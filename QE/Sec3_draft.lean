/-
Draft, not part of the build: this file is the Section 3 statement draft and imports a compiled
`Milestone0/Encoding.lean`.  To check it:

  mkdir -p .scratch2/sec3 && cp Milestone0/Encoding.lean .scratch2/sec3/Enc.lean
  cd .scratch2/sec3 && lean -o Enc.olean Enc.lean
  cp ../../QE/Sec3_draft.lean Sec3.lean && LEAN_PATH=$PWD:$LEAN_PATH lean Sec3.lean
-/
import Enc
open FirstOrder FirstOrder.Language
namespace SpecialTransformations.Milestone0

/-!
# Section 3 of the paper, over sorted parameter pairs — draft statements

`paper.tex` §3 ("Some structural properties", line 659) proves the closure-theoretic facts that §4
and §5 consume: transfer of algebraic closure between the sorts (`acl:VF:transfer:acl:RV`),
`dcl:to:ac`, the finiteness of an `RV`-definable function into `VF`
(`function:rv:to:vf:finite:image`), exchange (`exchange`), the average lemma
(`average:0:rv:not:constant`), the finiteness of the `VF`-projection of an `RV`-definable set
(`finite:VF:project:RV`), effectiveness (`effectiveness`), the proper-subball/center lemmas, the
definability of ball centres (`algebraic:balls:definable:centers`), and `aclS:model`.

## REC — the sorted parameter pair

Every statement below quantifies over *parameters split by sort*, never over an arbitrary
`Set M` or a tuple of carrier elements.  The record `SP` is that pair: a `VF`-tuple and an
`RV`-tuple, each of its own length, each sorted.  A definition in this file writes `S : SP M`
for such a pair, `S.vf`/`S.rv` for its halves, and `paramSet S : Set M` for the union of the two
halves' ranges — which is the parameter set the paper writes `\bar a, \bar t`.

## SWL — the naming of the well-sorted statements

Each statement of §3 is named `swl_<paper-label>`, where `swl` marks that it is the well-sorted
version: parameters are an `S : SP M`, and every formula occurring in the statement is
`WellSorted` (from `Milestone0/Encoding.lean`).  The plain name without `swl_` is reserved for a
statement over arbitrary parameters, and where both exist the `swl` one is the target — the
unrestricted one is either false or says nothing about the paper's language, for the reason
recorded in `QE-PLAN.md`.
-/

/-- **REC**: a sorted parameter pair — a `VF`-tuple and an `RV`-tuple, each sorted. -/
structure SP (M : Type*) [LRV.Structure M] where
  /-- length of the `VF`-part -/
  n : ℕ
  /-- length of the `RV`-part -/
  m : ℕ
  /-- the `VF`-part -/
  vf : Fin n → M
  /-- the `RV`-part -/
  rv : Fin m → M
  vf_sorted : ∀ i, iVF (vf i)
  rv_sorted : ∀ j, iRV (rv j)

namespace SP

variable {M : Type*} [LRV.Structure M]

/-- The parameter set of a sorted pair: the union of the two halves' ranges, `\bar a` and `\bar t`
in the paper's notation. -/
def paramSet (S : SP M) : Set M := Set.range S.vf ∪ Set.range S.rv

/-- The parameter tuple as one function from `Fin n ⊕ Fin m`. -/
def toFun (S : SP M) : Fin S.n ⊕ Fin S.m → M := Sum.elim S.vf S.rv

/-- The sort map of a sorted pair: a `VF`-part followed by an `RV`-part. -/
def sortMap (S : SP M) : Fin S.n ⊕ Fin S.m → SortTag
  | Sum.inl _ => .vf
  | Sum.inr _ => .rv

/-- `S`-definability of a subset of the `VF` sort: defined by a well-sorted formula in one free
`VF`-variable whose parameters are `S`'s — the paper's "`\bar a, \bar t`-definable". -/
def DefinableVF (S : SP M) (s : Set M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1,
    WellSorted S.sortMap (fun _ => SortTag.vf) φ ∧
      s = {y | iVF y ∧ φ.Realize S.toFun ![y]}

/-- `S`-definability of a subset of the `RV` sort, likewise. -/
def DefinableRV (S : SP M) (s : Set M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1,
    WellSorted S.sortMap (fun _ => SortTag.rv) φ ∧
      s = {y | iRV y ∧ φ.Realize S.toFun ![y]}

end SP



/-!
## The inventory of §3's statements, with the shape each takes over `SP`

`acl` and `dcl` are *not* in Mathlib for this setting, so each statement below is recorded with the
definition it needs; the ones that need nothing new are stated and (will be) proved first.

| paper label | content | Lean shape | needs |
| --- | --- | --- | --- |
| (unnamed, first lemma) | `s ∈ acl(a)` for all `a ∈ A` ⟹ `s ∈ acl(∅)` | `swl_acl_const_of_fibres` | `acl S x` |
| `acl:VF:transfer:acl:RV` | `t̄`-definable `A ⊆ rv⁻¹(t̄)`; `x ∈ acl(a)` for all `a ∈ A` ⟹ `x ∈ acl(t̄)`; dual for `Γ` | `swl_acl_VF_transfer_acl_RV`, `swl_acl_Gamma_transfer` | `acl`, `rvOf`/`vrvOf` on `SP` |
| `dcl:to:ac` | `b ∈ acl(ā, t̄)` with `b ∈ VF` ⟹ `b ∈ VF(S)(ā)^{alg}` | `swl_dcl_to_ac` | `acl`, field-theoretic `AlgebraicClosure` of the generated field |
| (corollary) | transcendental degrees of `VF(S)(ā)`, `VF(⟨ā, B⟩)`, `VF(acl(ā, B))` equal | `swl_trdeg_acl_eq` | `acl`, `trdeg` |
| `function:rv:to:vf:finite:image` | `A ⊆ RV^m`, `f : A → VF^n` definable ⟹ `f(A)` finite | `swl_function_rv_to_vf_finite_image` | definable functions on tuples over `SP` |
| `exchange` | the exchange property for `acl` (Yin `QE:ACVF:min` 4.3) | `swl_exchange` | `acl` |
| `alg:ind:imag` | algebraic independence and images | `swl_alg_ind_image` | `acl`, `trdeg` |
| `average:0:rv:not:constant` | the average lemma: an `RV`-definable function is not constant on a ball | `swl_average_zero_rv_not_constant` | `acl`, balls, definable functions |
| `finite:VF:project:RV` | the `VF`-projection of an `RV`-definable set is finite | `swl_finite_VF_project_RV` | definable functions over `SP` |
| `effectiveness` | effectiveness of definable closure | `swl_effectiveness` | `acl`, `dcl` |
| `ball:proper:sub:center`, `ball:RV:finite` | proper subballs have centres in the parameter set; finitely many `RV`-balls | `swl_ball_proper_sub_center`, `swl_ball_RV_finite` | `IsBall`, `SP` (no `acl`) — **statable now** |
| `algebraic:balls:definable:centers`, `aclS:model` | centres of algebraic balls are definable; `acl(S)` is a model | `swl_algebraic_balls_definable_centers`, `swl_aclS_model` | `acl` |
| `inf:RV:def:gam` | `∞` is definable in `RV` from `Γ` | `swl_inf_RV_def_gam` | `vrv` on `SP` |

Two decisions this table forces, and neither is mine to take silently:

1. **`acl`'s definition.** `x ∈ acl(S)` means: some well-sorted formula `φ(y, S)` with a *finite*
   solution set contains `x`.  That is the paper's use, and it must be stated over `SP` with
   `WellSorted` — not over an arbitrary `Set M`, or §3 inherits the junk problem.
2. **Whether §3 is done over an arbitrary model `M ⊨ ACVF` or over the substructure `S`.**  The
   paper's §3 statements are about a *fixed* substructure `S` of a model (the notation `VF(S)`,
   `acl(ā)` presupposes it).  In the encoding, `S` is `SP M` for a model `M`, so the statements are
   `M ⊨ ACVF → SP M → …`, and the `S`-relative notions (`VF(S)(ā)`, `Γ(S)`) must be built from
   `SP` — which is the one genuinely new construction §3 needs and it is not in the tree.
-/

end SpecialTransformations.Milestone0
