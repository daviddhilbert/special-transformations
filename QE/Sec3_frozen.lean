/-
Draft: Section 3's frozen statements over sorted parameter pairs (`SP`), with `acl`/`dcl`.
To check: build `Milestone0/Encoding.lean` to an olean named `Enc` beside this file (see
`QE/Sec3_draft.lean`'s header for the two commands), then `LEAN_PATH=$PWD:$LEAN_PATH lean` it.
The five `sorry`s are deliberate: these are *frozen targets*.  The paper cites most of the
proofs from arXiv:1006.1393, so they are quoted theorems unless re-proved here.
-/
import Enc
open FirstOrder FirstOrder.Language
namespace SpecialTransformations.Milestone0

/-! ## `acl`, `dcl`, and the frozen Section 3 statements (SWL naming)

The paper's Section 3 cites its proofs from arXiv:1006.1393 (`Yin:QE:ACVF:min`): exchange is Lemma
4.3 there, the average lemma 4.9, the finiteness of the `VF`-projection 4.10, the finite image of an
`RV`-definable function 4.12, effectiveness 4.15, the algebraic balls 4.17, Corollary 4.18.  Those are
therefore *quoted* theorems: the statements below are the frozen targets, and their proofs are
external to this formalization unless re-proved here. -/

structure SP (M : Type*) [LRV.Structure M] where
  n : ℕ
  m : ℕ
  vf : Fin n → M
  rv : Fin m → M
  vf_sorted : ∀ i, iVF (vf i)
  rv_sorted : ∀ j, iRV (rv j)

namespace SP

variable {M : Type*} [LRV.Structure M]

def paramSet (S : SP M) : Set M := Set.range S.vf ∪ Set.range S.rv

def toFun (S : SP M) : Fin S.n ⊕ Fin S.m → M := Sum.elim S.vf S.rv

def sortMap (S : SP M) : Fin S.n ⊕ Fin S.m → SortTag
  | Sum.inl _ => .vf
  | Sum.inr _ => .rv

/-- The empty parameter pair. -/
def base : SP M := ⟨0, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun j => j.elim0⟩

/-- Extend a sorted pair by one `VF`-parameter, the sortedness of the extended tuple supplied by
the caller (the `Fin.snoc` transport is left to the use site, where the shape is known). -/
def extendVF (S : SP M) (vs : Fin (S.n + 1) → M) (hvs : ∀ i, iVF (vs i)) : SP M :=
  ⟨S.n + 1, S.m, vs, S.rv, hvs, S.rv_sorted⟩

/-- Extend a sorted pair by one `RV`-parameter, likewise. -/
def extendRV (S : SP M) (ts : Fin (S.m + 1) → M) (hts : ∀ j, iRV (ts j)) : SP M :=
  ⟨S.n, S.m + 1, S.vf, ts, S.vf_sorted, hts⟩

/-- **Algebraic closure over `S`**: `x` satisfies a well-sorted formula in one free variable whose
parameter is `S` and whose solution set is finite.  This is the paper's `x ∈ acl(ā, t̄)`. -/
def acl (S : SP M) (x : M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1,
    WellSorted S.sortMap (fun _ => SortTag.vf) φ ∧
      ({y | iVF y ∧ φ.Realize S.toFun ![y]} : Set M).Finite ∧
        iVF x ∧ φ.Realize S.toFun ![x]

/-- **Definable closure over `S`**. -/
def dcl (S : SP M) (x : M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1,
    WellSorted S.sortMap (fun _ => SortTag.vf) φ ∧
      ({y | iVF y ∧ φ.Realize S.toFun ![y]} : Set M) = {x}

/-- `S`-definability of a subset of one sort. -/
def DefinableVF (S : SP M) (s : Set M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1,
    WellSorted S.sortMap (fun _ => SortTag.vf) φ ∧ s = {y | iVF y ∧ φ.Realize S.toFun ![y]}

def DefinableRV (S : SP M) (s : Set M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1,
    WellSorted S.sortMap (fun _ => SortTag.rv) φ ∧ s = {y | iRV y ∧ φ.Realize S.toFun ![y]}

section Frozen

variable [Nonempty M] (hM : M ⊨ Axioms.ACVF)

/-- First lemma of §3 (no label in the paper): if `s` is algebraically definable over every `VF`
point of a definable `A`, then `s ∈ acl(∅)`. -/
theorem swl_acl_const_of_fibres (S : SP M) (A : Set M) (s : M) (hA : DefinableVF S A)
    (h : ∀ a : M, iVF a → a ∈ A → acl S s) : acl (base (M := M)) s := by
  sorry

/-- `acl:VF:transfer:acl:RV`, `VF` half: for an `RV`-definable `A` whose points are all `RV`-sorted,
if `x ∈ acl` over every point of `A` then `x ∈ acl(t̄)`. -/
theorem swl_acl_VF_transfer_acl_RV (S : SP M) (A : Set M) (hA : DefinableRV S A) (x : M)
    (h : ∀ a : M, iRV a → a ∈ A → acl S x) : acl S x := by
  sorry

/-- `exchange` (Yin, QE:ACVF:min, Lemma 4.3), over sorted parameter pairs. -/
theorem swl_exchange (S S₁ S₂ : SP M) (a b : M) (ha : iVF a) (hb : iVF b)
    (h : acl S₁ b) : acl S b ∨ dcl S₂ a := by
  sorry

/-- `function:rv:to:vf:finite:image` (Yin, Lemma 4.12): a definable function from a definable
`A ⊆ RV` into the `VF` sort has finite image. -/
theorem swl_function_rv_to_vf_finite_image (S : SP M) (A : Set M) (hA : DefinableRV S A)
    (f : M → M) (hf : ∀ a : M, a ∈ A → iVF (f a)) :
    (Set.range (fun a : {a // a ∈ A} => f a.1)).Finite := by
  sorry

/-- `finite:VF:project:RV` (Yin, Lemma 4.10): the `VF`-projection of an `RV`-definable set is
finite. -/
theorem swl_finite_VF_project_RV (S : SP M) (B : Set (M × M)) (hB : DefinableRV S {t | ∃ x, (x, t) ∈ B}) :
    ({x : M | iVF x ∧ ∃ t : M, iRV t ∧ (x, t) ∈ B} : Set M).Finite := by
  sorry

end Frozen

end SP

end SpecialTransformations.Milestone0
