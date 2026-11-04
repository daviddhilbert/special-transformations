/-
Section 3 of Yin, *Special transformations in algebraically closed valued fields*
(arXiv:1006.2467): **`finite:VF:project:RV`** (`paper.tex:716`, Yin QE:ACVF:min Lemma 4.10,
`qe.tex:1070`) in its honest form.

The paper:

> Let `A` be a definable finite subset of `VF^n`.  Then there is a definable injection
> `f : A → RV^m` for some `m`.

Two corrections to the frozen form `QE/Sec3_frozen.lean:215` are made here, and they are exactly
what Yin's proof produces (`qe.tex:1070`):

* the target is `RV^k` for a `k` that grows with `A` — the frozen form has a single `RV` value,
  and Yin's induction produces `m + 1` from `m` at the base step and `2m` at the outer step;
* the parameters are the elements of `A` (the enumeration `c`), not only the parameters of `A`:
  Yin's base step translates `A` by its average and then reads off the `rv`'s of the elements
  themselves, and the glued function is definable over those.

At `n = 1` this file proves the corrected statement outright, for an arbitrary finite `A`,
enumerated by an injective `c : Fin k → M` with `iVF` values:

`x ↦ (rv (x - c₀), …, rv (x - c_{k-1}))`

is `(paramPair c)`-definable (its graph is the conjunction of the `k` term equations
`yᵢ = rv (x - cᵢ)`) and injective on `{c₀, …, c_{k-1}}`: the `i`-th coordinate of `cᵢ` is
`rv 0 = 0` while the `i`-th coordinate of `cⱼ` (`j ≠ i`) is `rv (cⱼ - cᵢ) ≠ 0`, since `rv x = 0`
forces `x = 0` (`rvEqInfty`).

## What is proved here (`#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`)

* `DefinableFunVFRV` — the multi-valued definability notion the paper's `f : A → RV^m` needs:
  a well-sorted graph formula over `S` with one `VF` and `k` `RV` free variables.
* `paramPair` — the parameter pair whose `VF`-parameters are the tuple `c` (and no `RV`-parameters).
* `wellSorted_diffForm`, `realize_diffForm` — the graph formula
  `⋀_{i<k} (yᵢ = rv (x - cᵢ))` is well-sorted and realizes as the tuple of `rv`'s of the
  differences from the `cᵢ`.
* `definableFunVFRV_diff` — `x ↦ (rv (x - cᵢ))ᵢ` is `paramPair c`-definable.
* `swl_finite_VF_project_RV_range` — its values are `RV`-sorted and it is injective on `{cᵢ}`.
* `exists_enumeration` — a finite set is the range of an injective `c : Fin k → M`.
* `swl_finite_VF_project_RV_corrected` — **`finite:VF:project:RV` at `n = 1`, corrected and
  proved**: every finite `A ⊆ VF` admits `k`, an enumeration `c` of `A`, and a function
  `f : VF → RV^k` that is definable over `A`'s elements and injective on `A` with `RV`-sorted
  values.

Not proved here: `n > 1` (Yin's induction on `n` uses the projection to the last coordinate and
his `n = 1` step; the `n > 1` step is pure bookkeeping over `Fin n × Fin k` coordinates), and of
course the paper's own parameter discipline (definability over the parameters of `A` alone) —
which is *not* what Yin's proof gives, and which fails in general (two points conjugate over `S`
cannot be separated by an `S`-definable function).
-/
import M8FinImage
import Sec3Frozen
import RVCalc
import Sec4Dim

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
open LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Milestone0.RVCalc

namespace SP

variable {M : Type} [LRV.Structure M]

/-! ## Multi-valued definability: functions `VF → RV^k` -/

/-- **`f : VF → RV^k` is `S`-definable**: its graph is cut out by a well-sorted formula over the
parameters `S`, one `VF`-sort and `k` `RV`-sort free variables.  This is the shape of the target of
`finite:VF:project:RV` (`RV^m`, not a single `RV` value). -/
def DefinableFunVFRV (S : SP M) {k : ℕ} (f : M → Fin k → M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) (1 + k),
    WellSorted S.sortMap (Fin.append (fun _ : Fin 1 => SortTag.vf)
      (fun _ : Fin k => SortTag.rv)) φ ∧
      ∀ (x : M) (y : Fin k → M),
        (φ.Realize S.toFun (Fin.append (fun _ : Fin 1 => x) y) ↔ f x = y)

/-- The parameter pair consisting of the finite tuple `c ⊆ VF`. -/
def paramPair {k : ℕ} (c : Fin k → M) (hVF : ∀ i, iVF (c i)) : SP M :=
  ⟨k, 0, c, Fin.elim0, hVF, fun j => j.elim0⟩

/-- the free variable `x` of the graph formula -/
def diffXTerm (k : ℕ) : LRV.Term ((Fin k ⊕ Fin 0) ⊕ Fin (1 + k)) :=
  Term.var (Sum.inr (Fin.castAdd k (0 : Fin 1)))

/-- the parameter `cᵢ` -/
def diffParamTerm (k : ℕ) (i : Fin k) : LRV.Term ((Fin k ⊕ Fin 0) ⊕ Fin (1 + k)) :=
  Term.var (Sum.inl (Sum.inl i))

/-- the term `-cᵢ` -/
def diffNegTerm (k : ℕ) (i : Fin k) : LRV.Term ((Fin k ⊕ Fin 0) ⊕ Fin (1 + k)) :=
  Term.func Fn.vfNeg ![diffParamTerm k i]

/-- the term `x - cᵢ` -/
def diffSubTerm (k : ℕ) (i : Fin k) : LRV.Term ((Fin k ⊕ Fin 0) ⊕ Fin (1 + k)) :=
  Term.func Fn.vfAdd ![diffXTerm k, diffNegTerm k i]

/-- the term `rv (x - cᵢ)` -/
def diffFormTerm (k : ℕ) (i : Fin k) : LRV.Term ((Fin k ⊕ Fin 0) ⊕ Fin (1 + k)) :=
  Term.func Fn.rvMap ![diffSubTerm k i]

/-- the `i`-th conjunct `yᵢ = rv (x - cᵢ)` -/
def diffConj (k : ℕ) (i : Fin k) : LRV.BoundedFormula (Fin k ⊕ Fin 0) (1 + k) :=
  pEqG (Term.var (Sum.inr (Fin.natAdd 1 i))) (diffFormTerm k i)

/-- the graph formula -/
def diffForm (k : ℕ) : LRV.BoundedFormula (Fin k ⊕ Fin 0) (1 + k) :=
  Sec4Dim.conjFin (diffConj k)

/-- the sort assignment of the free variables of `diffForm`: `x` at `VF`, the `yᵢ` at `RV` -/
def diffSorts (k : ℕ) : Fin (1 + k) → SortTag :=
  Fin.append (fun _ : Fin 1 => SortTag.vf) (fun _ : Fin k => SortTag.rv)

/-- **`diffForm` is well-sorted.** -/
theorem wellSorted_diffForm {k : ℕ} (c : Fin k → M) (hVF : ∀ i, iVF (c i)) :
    WellSorted (paramPair c hVF).sortMap (diffSorts k) (diffForm k) := by
  refine Sec4Dim.wellSorted_conjFin (fun i => ?_)
  refine wellSorted_pEqG (s := SortTag.rv) _ _ ?_ ?_
  · show TmSort (paramPair c hVF).sortMap (diffSorts k)
      (Term.var (Sum.inr (Fin.natAdd 1 i))) = some SortTag.rv
    rw [tmSort_var_inr]
    simp only [diffSorts, Fin.append_right]
  · show TmSort (paramPair c hVF).sortMap (diffSorts k) (diffFormTerm k i) = some SortTag.rv
    rw [diffFormTerm, tmSort_tRv, diffSubTerm, tmSort_vfAdd]
    refine ⟨?_, ?_⟩
    · rw [diffXTerm, tmSort_var_inr]
      simp only [diffSorts, Fin.append_left]
    · rw [diffNegTerm, tmSort_vfNeg, diffParamTerm, tmSort_var_inl]
      rfl

/-- **Realization of `diffForm`**: at `x` and the tuple `y`, it says `yᵢ = rv (x - cᵢ)` for all `i`. -/
theorem realize_diffForm {k : ℕ} (c : Fin k → M) (hVF : ∀ i, iVF (c i)) (x : M)
    (y : Fin k → M) :
    (diffForm k).Realize (paramPair c hVF).toFun (Fin.append (fun _ : Fin 1 => x) y) ↔
      ∀ i, y i = iRv (iVFAdd x (iVFNeg (c i))) := by
  rw [diffForm, Sec4Dim.realize_conjFin]
  constructor
  · intro h i
    have hi := h i
    simp only [diffConj, pEqG, BoundedFormula.realize_bdEqual, diffFormTerm, diffSubTerm,
      diffXTerm, diffNegTerm, diffParamTerm, TermRealize.realize_rvMap,
      TermRealize.realize_vfAdd, TermRealize.realize_vfNeg, Term.realize_var,
      Sum.elim_inl, Sum.elim_inr, Fin.append_left, Fin.append_right, paramPair, toFun] at hi
    exact hi
  · intro h i
    simp only [diffConj, pEqG, BoundedFormula.realize_bdEqual, diffFormTerm, diffSubTerm,
      diffXTerm, diffNegTerm, diffParamTerm, TermRealize.realize_rvMap,
      TermRealize.realize_vfAdd, TermRealize.realize_vfNeg, Term.realize_var,
      Sum.elim_inl, Sum.elim_inr, Fin.append_left, Fin.append_right, paramPair, toFun]
    exact h i

/-- **The graph of `x ↦ (rv (x - cᵢ))ᵢ` is definable over the parameters `c`.** -/
theorem definableFunVFRV_diff {k : ℕ} (c : Fin k → M) (hVF : ∀ i, iVF (c i)) :
    DefinableFunVFRV (paramPair c hVF) (fun x i => iRv (iVFAdd x (iVFNeg (c i)))) := by
  refine ⟨diffForm k, wellSorted_diffForm c hVF, fun x y => ?_⟩
  rw [realize_diffForm]
  constructor
  · intro h
    funext i
    exact (h i).symm
  · intro h i
    exact (congrFun h i).symm

/-- **`finite:VF:project:RV`** (`paper.tex:716`, Yin QE:ACVF:min Lemma 4.10) **at `n = 1`, in the
form Yin's proof produces**: for a finite `A ⊆ VF` enumerated injectively by `c : Fin k → M`, the
map `x ↦ (rv (x - cᵢ))ᵢ` is definable over the parameters `c` (= the elements of `A`) and injective
on `A`, with values at `RV`-elements.

The frozen form `QE/Sec3_frozen.lean:215` differs in exactly two points, both recorded in the
file header: it asks for a *single* `RV` value rather than `RV^k`, and it asks for definability
over the parameters of `A` alone rather than over `A`'s elements.  Yin's induction
(`qe.tex:1070`) needs `RV^m` with `m` growing, and produces the function over the elements of `A`;
this theorem is the `n = 1` case of the corrected statement, with no hypothesis left over. -/
theorem swl_finite_VF_project_RV_range (hM : M ⊨ Axioms.ACVF) {k : ℕ} (c : Fin k → M)
    (hc : Function.Injective c) (hVF : ∀ i, iVF (c i)) :
    ∃ f : M → Fin k → M, DefinableFunVFRV (paramPair c hVF) f ∧
      (∀ x : M, x ∈ Set.range c → ∀ i, iRV (f x i)) ∧ Set.InjOn f (Set.range c) := by
  refine ⟨fun x i => iRv (iVFAdd x (iVFNeg (c i))), definableFunVFRV_diff c hVF, ?_, ?_⟩
  · intro x hx i
    obtain ⟨j, rfl⟩ := hx
    exact rv_mem (M := M) hM (vf_add_mem (M := M) hM (hVF j) (vf_neg_mem (M := M) hM (hVF i)))
  · exact rvDiffTuple_injOn_range hM c hc hVF

omit [LRV.Structure M] in
/-- **A finite set admits an injective enumeration by `Fin k`.** -/
theorem exists_enumeration {A : Set M} (hA : A.Finite) :
    ∃ (k : ℕ) (c : Fin k → M), Function.Injective c ∧ Set.range c = A := by
  refine ⟨hA.toFinset.card, fun i => (hA.toFinset.equivFin.symm i : M), ?_, ?_⟩
  · intro i j hij
    exact hA.toFinset.equivFin.symm.injective (Subtype.ext hij)
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      have hmem : ((hA.toFinset.equivFin.symm i : M)) ∈ hA.toFinset :=
        (hA.toFinset.equivFin.symm i).2
      rwa [hA.mem_toFinset] at hmem
    · intro hx
      have hx' : x ∈ hA.toFinset := by rwa [hA.mem_toFinset]
      refine ⟨hA.toFinset.equivFin ⟨x, hx'⟩, ?_⟩
      simp

/-- **`finite:VF:project:RV`** (`paper.tex:716`, Yin QE:ACVF:min Lemma 4.10) **at `n = 1`,
corrected**: every finite `A ⊆ VF` admits `k : ℕ`, an enumeration `c` of `A`, and a function
`f : VF → RV^k` that is definable over the parameter pair `paramPair c` (whose parameters are
exactly the elements of `A`) and injective on `A`, with `RV`-sorted values.

The two corrections with respect to the frozen form `QE/Sec3_frozen.lean:215` — the target
`RV^k` instead of a single `RV` value, and the parameters `A`'s elements instead of `A`'s own
parameters — are the two points on which Yin's proof (`qe.tex:1070`) and the frozen statement
disagree; see the file header. -/
theorem swl_finite_VF_project_RV_corrected (hM : M ⊨ Axioms.ACVF) (A : Set M) (hA : A.Finite)
    (hVF : ∀ x : M, x ∈ A → iVF x) :
    ∃ (k : ℕ) (c : Fin k → M) (h : ∀ i, iVF (c i)) (f : M → Fin k → M),
      Set.range c = A ∧ DefinableFunVFRV (paramPair c h) f ∧
        (∀ x : M, x ∈ A → ∀ i, iRV (f x i)) ∧ Set.InjOn f A := by
  obtain ⟨k, c, hcinj, hcr⟩ := exists_enumeration hA
  have h : ∀ i, iVF (c i) := fun i => hVF (c i) (by rw [← hcr]; exact Set.mem_range_self i)
  refine ⟨k, c, h, fun x i => iRv (iVFAdd x (iVFNeg (c i))), hcr,
    definableFunVFRV_diff c h, ?_, ?_⟩
  · intro x hx i
    rw [← hcr] at hx
    obtain ⟨j, rfl⟩ := hx
    exact rv_mem (M := M) hM (vf_add_mem (M := M) hM (h j) (vf_neg_mem (M := M) hM (h i)))
  · rw [← hcr]
    exact rvDiffTuple_injOn_range hM c hcinj h

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.SP.exists_enumeration
#print axioms SpecialTransformations.Milestone0.SP.swl_finite_VF_project_RV_corrected

end SP

end SpecialTransformations.Milestone0
