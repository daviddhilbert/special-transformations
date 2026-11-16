module

public import CanonicalStructure
public import CanonicalRV

@[expose] public section

/-!
# The paragraph immediately after Theorem 2.3

A VF equality is an RV equality at the difference polynomial; negating gives
the inequality literal. These results preserve all original parameters and
do not identify equality of valuations with equality of leading terms.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section3

variable {M : Type} [LRV.Structure M]

private theorem realize_func1 {β : Type} (f : Fn 1) (t : LRV.Term β) (v : β → M) :
    (Term.func f ![t]).realize v = Structure.funMap (L := LRV) f ![t.realize v] := by
  change Structure.funMap (L := LRV) f (fun i => (![t] i).realize v) = _
  congr 1
  funext i; fin_cases i; rfl

private theorem realize_func2 {β : Type} (f : Fn 2) (t u : LRV.Term β) (v : β → M) :
    (Term.func f ![t, u]).realize v = Structure.funMap (L := LRV) f ![t.realize v, u.realize v] := by
  change Structure.funMap (L := LRV) f (fun i => (![t, u] i).realize v) = _
  congr 1
  funext i; fin_cases i <;> rfl

private theorem realize_func0 {β : Type} (f : Fn 0) (v : β → M) :
    (Term.func f Fin.elim0 : LRV.Term β).realize v = Structure.funMap (L := LRV) f Fin.elim0 := by
  change Structure.funMap (L := LRV) f (fun i => (Fin.elim0 i : LRV.Term β).realize v) = _
  congr 1
  funext i; exact i.elim0

variable [hM : M ⊨ Axioms.ACVF]

theorem vf_equal_iff_rv_difference_zero (x y : VFType (M := M)) :
    x = y ↔ iRv (x - y).val = iRVZero :=
  (CanonicalRV.encodedRv_zero_iff (x - y)).trans sub_eq_zero |>.symm

def rvEquality {α : Type} {n : ℕ} (t u : LRV.Term (α ⊕ Fin n)) :
    LRV.BoundedFormula α n :=
  .equal (.func Fn.rvMap ![.func Fn.vfAdd ![t, .func Fn.vfNeg ![u] ] ])
    (.func Fn.rvZero Fin.elim0)

theorem rvEquality_wellSorted {α : Type} {n : ℕ} (sα : α → SortTag)
    (sn : Fin n → SortTag) (t u : LRV.Term (α ⊕ Fin n))
    (ht : TmSort sα sn t = some .vf) (hu : TmSort sα sn u = some .vf) :
    WellSorted sα sn (rvEquality t u) := by
  apply WellSorted.equal sn (s := .rv)
  · apply tmSort_func sα sn Fn.rvMap
    intro i; fin_cases i
    apply tmSort_func sα sn Fn.vfAdd
    intro j; fin_cases j
    · exact ht
    · apply tmSort_func sα sn Fn.vfNeg
      intro k; fin_cases k; exact hu
  · apply tmSort_func sα sn Fn.rvZero
    intro i; exact i.elim0

theorem realize_rvEquality {α : Type} {n : ℕ} (sα : α → SortTag)
    (sn : Fin n → SortTag) (v : α → M) (x : Fin n → M)
    (hv : ∀ a, sortEval (sα a) (v a)) (hx : ∀ i, sortEval (sn i) (x i))
    (t u : LRV.Term (α ⊕ Fin n))
    (ht : TmSort sα sn t = some .vf) (hu : TmSort sα sn u = some .vf) :
    (t.bdEqual u).Realize v x ↔ (rvEquality t u).Realize v x := by
  let a : VFType (M := M) := ⟨t.realize (Sum.elim v x),
    CanonicalStructure.term_sort hM sα sn v x hv hx t ht⟩
  let b : VFType (M := M) := ⟨u.realize (Sum.elim v x),
    CanonicalStructure.term_sort hM sα sn v x hv hx u hu⟩
  simp only [rvEquality, BoundedFormula.Realize,
    realize_func1, realize_func2, realize_func0]
  change a.val = b.val ↔ iRv (iVFAdd a.val (iVFNeg b.val)) = iRVZero
  exact Subtype.val_inj.trans (vf_equal_iff_rv_difference_zero a b)

end SpecialTransformations.Section3
