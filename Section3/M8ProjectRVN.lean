/-
Section 3 of Yin, *Special transformations in algebraically closed valued fields*
(arXiv:1006.2467): **`finite:VF:project:RV`** (`paper.tex:716`, Yin QE:ACVF:min Lemma 4.10,
`qe.tex:1070`) for `A ⊆ VF^n` with `n` arbitrary, in the form Yin's proof produces.

The companion file `M8ProjectRV.lean` proves the `n = 1` case.  This file does the paper's own
induction step on `n` in the only way it is needed once `n = 1` is known: the injection of a finite
`A ⊆ VF^n` into `RV^{n·k}` is the tuple of the `n = 1` injections of all the coordinate projections,
`x ↦ (rv (xᵢ - cⱼᵢ))_{i<n, j<k}`, and it is definable by the conjunction of the `n·k` term
equations of `M8ProjectRV.lean`'s `diffForm`.

Proved here (`#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`):
`SP.DefinableFunTupRV` (the `VF^n → RV^k` definability notion), `paramTupleN`,
`wellSorted_formN`, `realize_formN`, `definableFunTupRV_diff`, `diffTupleNFun_injOn`, and
`swl_finite_VF_project_RV_n` — the corrected `finite:VF:project:RV` for `A ⊆ VF^n`.  Injectivity: if `cⱼ ≠ cₗ` then some coordinate `i`
separates them, and at the pair `(i, j)` the two values are `rv (cⱼᵢ - cⱼᵢ) = 0` and
`rv (cₗᵢ - cⱼᵢ) ≠ 0`.
-/
import M8ProjectRV

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
open LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Milestone0.RVCalc

namespace SP

variable {M : Type} [LRV.Structure M]

/-! ## Functions `VF^n → RV^k` -/

/-- **`f : VF^n → RV^k` is `S`-definable**: a well-sorted graph formula over `S` with `n` `VF` and
`k` `RV` free variables.  (`DefinableFunVFRV` is the case `n = 1`.) -/
def DefinableFunTupRV (S : SP M) {n k : ℕ} (f : (Fin n → M) → Fin k → M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) (n + k),
    WellSorted S.sortMap
      (Fin.append (fun _ : Fin n => SortTag.vf) (fun _ : Fin k => SortTag.rv)) φ ∧
      ∀ (x : Fin n → M) (y : Fin k → M),
        (φ.Realize S.toFun (Fin.append x y) ↔ f x = y)

/-- The flattening of the tuple of `VF^n`-points `c` into `n·k` `VF`-parameters. -/
def paramTupleN {n k : ℕ} (c : Fin k → Fin n → M) : Fin (n * k) → M :=
  fun t => c (finProdFinEquiv.symm t).2 (finProdFinEquiv.symm t).1

/-- the first coordinate of the `t`-th flattened pair -/
def coordOfN {n k : ℕ} (t : Fin (n * k)) : Fin n := (finProdFinEquiv.symm t).1

/-- the second coordinate of the `t`-th flattened pair -/
def pointOfN {n k : ℕ} (t : Fin (n * k)) : Fin k := (finProdFinEquiv.symm t).2

/-! ### The graph formula -/

/-- the free variable `xᵢ` -/
def xTermN (n k : ℕ) (t : Fin (n * k)) : LRV.Term ((Fin (n * k) ⊕ Fin 0) ⊕ Fin (n + n * k)) :=
  Term.var (Sum.inr (Fin.castAdd (n * k) (coordOfN t)))

/-- the parameter `cⱼᵢ` -/
def paramTermN (n k : ℕ) (t : Fin (n * k)) : LRV.Term ((Fin (n * k) ⊕ Fin 0) ⊕ Fin (n + n * k)) :=
  Term.var (Sum.inl (Sum.inl t))

/-- the term `-cⱼᵢ` -/
def negTermN (n k : ℕ) (t : Fin (n * k)) : LRV.Term ((Fin (n * k) ⊕ Fin 0) ⊕ Fin (n + n * k)) :=
  Term.func Fn.vfNeg ![paramTermN n k t]

/-- the term `xᵢ - cⱼᵢ` -/
def subTermN (n k : ℕ) (t : Fin (n * k)) : LRV.Term ((Fin (n * k) ⊕ Fin 0) ⊕ Fin (n + n * k)) :=
  Term.func Fn.vfAdd ![xTermN n k t, negTermN n k t]

/-- the term `rv (xᵢ - cⱼᵢ)` -/
def rvTermN (n k : ℕ) (t : Fin (n * k)) : LRV.Term ((Fin (n * k) ⊕ Fin 0) ⊕ Fin (n + n * k)) :=
  Term.func Fn.rvMap ![subTermN n k t]

/-- the `t`-th conjunct `y_t = rv (xᵢ - cⱼᵢ)` -/
def conjN (n k : ℕ) (t : Fin (n * k)) : LRV.BoundedFormula (Fin (n * k) ⊕ Fin 0) (n + n * k) :=
  pEqG (Term.var (Sum.inr (Fin.natAdd n t))) (rvTermN n k t)

/-- the graph formula of `x ↦ (rv (xᵢ - cⱼᵢ))_{i, j}` -/
def formN (n k : ℕ) : LRV.BoundedFormula (Fin (n * k) ⊕ Fin 0) (n + n * k) :=
  Sec4Dim.conjFin (conjN n k)

/-- the sort assignment of the free variables: `x` at `VF`, `y` at `RV` -/
def sortsN (n k : ℕ) : Fin (n + n * k) → SortTag :=
  Fin.append (fun _ : Fin n => SortTag.vf) (fun _ : Fin (n * k) => SortTag.rv)

theorem sortsN_eq (n k : ℕ) :
    sortsN n k = Fin.append (fun _ : Fin n => SortTag.vf) (fun _ : Fin (n * k) => SortTag.rv) :=
  rfl

/-- **`formN` is well-sorted.** -/
theorem wellSorted_formN {n k : ℕ} (c : Fin k → Fin n → M) (hpar : ∀ t, iVF (paramTupleN c t)) :
    WellSorted (paramPair (paramTupleN c) hpar).sortMap (sortsN n k) (formN n k) := by
  refine Sec4Dim.wellSorted_conjFin (fun t => ?_)
  refine wellSorted_pEqG (s := SortTag.rv) _ _ ?_ ?_
  · rw [tmSort_var_inr]
    simp only [sortsN, Fin.append_right]
  · rw [rvTermN, tmSort_tRv, subTermN, tmSort_vfAdd]
    refine ⟨?_, ?_⟩
    · rw [xTermN, tmSort_var_inr]
      simp only [sortsN, Fin.append_left]
    · rw [negTermN, tmSort_vfNeg, paramTermN, tmSort_var_inl]
      rfl

/-- **Realization of `formN`.** -/
theorem realize_formN {n k : ℕ} (c : Fin k → Fin n → M) (hpar : ∀ t, iVF (paramTupleN c t))
    (x : Fin n → M) (y : Fin (n * k) → M) :
    (formN n k).Realize (paramPair (paramTupleN c) hpar).toFun (Fin.append x y) ↔
      ∀ t, y t = iRv (iVFAdd (x (coordOfN t)) (iVFNeg (paramTupleN c t))) := by
  rw [formN, Sec4Dim.realize_conjFin]
  constructor
  · intro h t
    have ht := h t
    simp only [conjN, pEqG, BoundedFormula.realize_bdEqual, rvTermN, subTermN, xTermN,
      negTermN, paramTermN, TermRealize.realize_rvMap, TermRealize.realize_vfAdd,
      TermRealize.realize_vfNeg, Term.realize_var, Sum.elim_inl, Sum.elim_inr,
      Fin.append_left, Fin.append_right, paramPair, toFun] at ht
    exact ht
  · intro h t
    simp only [conjN, pEqG, BoundedFormula.realize_bdEqual, rvTermN, subTermN, xTermN,
      negTermN, paramTermN, TermRealize.realize_rvMap, TermRealize.realize_vfAdd,
      TermRealize.realize_vfNeg, Term.realize_var, Sum.elim_inl, Sum.elim_inr,
      Fin.append_left, Fin.append_right, paramPair, toFun]
    exact h t

/-! ### The function and its two properties -/

/-- the tuple `x ↦ (rv (xᵢ - cⱼᵢ))_{i, j}` -/
def diffTupleNFun {n k : ℕ} (c : Fin k → Fin n → M) (x : Fin n → M) : Fin (n * k) → M :=
  fun t => iRv (iVFAdd (x (coordOfN t)) (iVFNeg (paramTupleN c t)))

/-- **The graph of `diffTupleNFun` is definable over the parameters `c`.** -/
theorem definableFunTupRV_diff {n k : ℕ} (c : Fin k → Fin n → M)
    (hpar : ∀ t, iVF (paramTupleN c t)) :
    DefinableFunTupRV (paramPair (paramTupleN c) hpar) (diffTupleNFun c) := by
  refine ⟨formN n k, ?_, fun x y => ?_⟩
  · rw [← sortsN_eq]
    exact wellSorted_formN c hpar
  rw [realize_formN]
  constructor
  · intro h
    funext t
    exact (h t).symm
  · intro h t
    exact (congrFun h t).symm

/-- **Injectivity of `diffTupleNFun` on a finite set of `VF^n`-points.** -/
theorem diffTupleNFun_injOn {n k : ℕ} (hM : M ⊨ Axioms.ACVF) (c : Fin k → Fin n → M)
    (hc : Function.Injective c) (hVF : ∀ j i, iVF (c j i)) :
    Set.InjOn (diffTupleNFun c) (Set.range c) := by
  rintro x ⟨j, rfl⟩ y ⟨l, rfl⟩ hxy
  by_cases hjl : j = l
  · rw [hjl]
  · exfalso
    have hne : c j ≠ c l := fun h => hjl (hc h)
    have hsep : ∃ i, c j i ≠ c l i := by
      by_contra h
      apply hne
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hsep
    have hcoord := congrFun hxy (finProdFinEquiv (i, j))
    simp only [diffTupleNFun, coordOfN, Equiv.symm_apply_apply, paramTupleN] at hcoord
    have hni : iVF (iVFNeg (c j i)) := vf_neg_mem (M := M) hM (hVF j i)
    have hli : iVF (iVFAdd (c l i) (iVFNeg (c j i))) :=
      vf_add_mem (M := M) hM (hVF l i) hni
    have hzero : iVFAdd (c j i) (iVFNeg (c j i)) = iVFZero (M := M) := vf_add_neg hM (hVF j i)
    have h1 : iRv (iVFAdd (c j i) (iVFNeg (c j i))) = iRVZero := by
      rw [hzero, rv_zero_eq hM]
    rw [h1] at hcoord
    have h2 : iVFAdd (c l i) (iVFNeg (c j i)) = iVFZero (M := M) := by
      refine vf_eq_zero_of_rv_eq_zero (M := M) hM hli ?_
      exact hcoord.symm
    apply hi
    have h3 : iVFAdd (c l i) (iVFNeg (c j i)) = iVFAdd (c j i) (iVFNeg (c j i)) := by
      rw [h2, hzero]
    have h4 : iVFAdd (iVFNeg (c j i)) (c l i) = iVFAdd (iVFNeg (c j i)) (c j i) := by
      rw [vf_add_comm hM hni (hVF l i), vf_add_comm hM hni (hVF j i)]
      exact h3
    exact (vf_add_left_cancel (a := iVFNeg (c j i)) (b := c l i) (c := c j i) hM hni
      (hVF l i) (hVF j i) h4).symm

/-! ## `finite:VF:project:RV` for `A ⊆ VF^n` -/

/-- **`finite:VF:project:RV`** (`paper.tex:716`, Yin QE:ACVF:min Lemma 4.10) **for `A ⊆ VF^n`**,
corrected: a finite `A ⊆ VF^n` enumerated injectively by `c : Fin k → Fin n → M` admits a function
`f : VF^n → RV^{n·k}`, definable over the parameter pair whose parameters are the coordinates of the
points of `A`, with `RV`-sorted values and injective on `A`.

The two corrections of the frozen form `QE/Sec3_frozen.lean:215` (target `RV^m` rather than one
`RV` value; parameters `A`'s points rather than `A`'s own parameters) are the ones Yin's proof
(`qe.tex:1070`) produces; see the header of `M8ProjectRV.lean`. -/
theorem swl_finite_VF_project_RV_n {n k : ℕ} (hM : M ⊨ Axioms.ACVF) (c : Fin k → Fin n → M)
    (hc : Function.Injective c) (hVF : ∀ j i, iVF (c j i)) :
    ∃ (hpar : ∀ t, iVF (paramTupleN c t)) (f : (Fin n → M) → Fin (n * k) → M),
      DefinableFunTupRV (paramPair (paramTupleN c) hpar) f ∧
        (∀ x : Fin n → M, x ∈ Set.range c → ∀ t, iRV (f x t)) ∧
          Set.InjOn f (Set.range c) := by
  have hpar : ∀ t, iVF (paramTupleN c t) := fun t => hVF _ _
  refine ⟨hpar, diffTupleNFun c, definableFunTupRV_diff c hpar, ?_, ?_⟩
  · intro x hx t
    obtain ⟨j, rfl⟩ := hx
    exact rv_mem (M := M) hM
      (vf_add_mem (M := M) hM (hVF j _) (vf_neg_mem (M := M) hM (hVF _ _)))
  · exact diffTupleNFun_injOn hM c hc hVF

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.SP.wellSorted_formN
#print axioms SpecialTransformations.Milestone0.SP.realize_formN
#print axioms SpecialTransformations.Milestone0.SP.definableFunTupRV_diff
#print axioms SpecialTransformations.Milestone0.SP.diffTupleNFun_injOn
#print axioms SpecialTransformations.Milestone0.SP.swl_finite_VF_project_RV_n

end SP

end SpecialTransformations.Milestone0
