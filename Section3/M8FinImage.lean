/-
Legacy partial results for Corollary 3.5 and Lemma 3.9 of Yin,
Special transformations in algebraically closed valued fields.

The proof declarations below give the two-point finite coding case and the
finite-domain case of the finite-image statement. They do not establish the
full paper statements. See FiniteImage.lean for the new full-arities proof
of Corollary 3.5 over the original base, using genuine saturation.

The paper's compactness argument is valid: a definable set contained in acl(S)
is finite in a sufficiently saturated ambient model. AlgebraicFinite.lean
proves this fact. Infinitude of acl(S) does not refute it.

The enumeration-based maps in M8ProjectRV and M8ProjectRVN are definable over
the elements being enumerated. This is a limitation of those constructions,
not the parameter discipline of Lemma 3.9. Conjugate VF points can have
distinct conjugate RV images under a function definable over the original
base. The paper's Lemma 3.9 is not disproved by conjugacy.
-/
import Enc
import Sec3Frozen
import RVCalc

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
open LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Milestone0.RVCalc

/-! ## Term realization for the constructors of the encoding -/

namespace TermRealize

variable {M : Type} [LRV.Structure M] {α : Type} {n : ℕ}

@[simp] theorem realize_vfAdd (v : α ⊕ Fin n → M) (t u : LRV.Term (α ⊕ Fin n)) :
    (Term.func Fn.vfAdd ![t, u]).realize v = iVFAdd (t.realize v) (u.realize v) := by
  show Structure.funMap (L := LRV) Fn.vfAdd (fun i => Term.realize v (![t, u] i))
      = iVFAdd (t.realize v) (u.realize v)
  rw [show (fun i => Term.realize v (![t, u] i)) = ![t.realize v, u.realize v] from by
    funext i; fin_cases i <;> simp]
  rfl

@[simp] theorem realize_vfNeg (v : α ⊕ Fin n → M) (t : LRV.Term (α ⊕ Fin n)) :
    (Term.func Fn.vfNeg ![t]).realize v = iVFNeg (t.realize v) := by
  show Structure.funMap (L := LRV) Fn.vfNeg (fun i => Term.realize v (![t] i))
      = iVFNeg (t.realize v)
  rw [show (fun i => Term.realize v (![t] i)) = ![t.realize v] from by
    funext i; fin_cases i; simp]
  rfl

@[simp] theorem realize_rvMap (v : α ⊕ Fin n → M) (t : LRV.Term (α ⊕ Fin n)) :
    (Term.func Fn.rvMap ![t]).realize v = iRv (t.realize v) := by
  show Structure.funMap (L := LRV) Fn.rvMap (fun i => Term.realize v (![t] i))
      = iRv (t.realize v)
  rw [show (fun i => Term.realize v (![t] i)) = ![t.realize v] from by
    funext i; fin_cases i; simp]
  rfl

@[simp] theorem realize_rvZero (v : α ⊕ Fin n → M) :
    (Term.func (L := LRV) Fn.rvZero (fun i : Fin 0 => i.elim0)).realize v = iRVZero := by
  show Structure.funMap (L := LRV) Fn.rvZero (fun i => Term.realize v ((fun j : Fin 0 => j.elim0) i))
      = iRVZero
  rw [show (fun i => Term.realize v ((fun j : Fin 0 => j.elim0) i)) = (fun i => i.elim0) from by
    funext i; exact i.elim0]
  rfl

end TermRealize

namespace SP

variable {M : Type} [LRV.Structure M]

/-! ## The definable function `x ↦ rv (x - a)`

Yin's base step in `finite:VF:project:RV` (`qe.tex:1075`) needs exactly one definable map
`VF → RV`, the projection `rv` after translating `A` by its average.  At the parameter pair
`SP.singleVF a` (whose only parameter is `a`) that map is `x ↦ rv (x - a)`, and it is definable by
a *term*, so no compactness is needed. -/

/-- The parameter `a` of `SP.singleVF a`, as a term: the only `VF`-parameter. -/
def rvSubParamTerm : LRV.Term ((Fin 1 ⊕ Fin 0) ⊕ Fin 2) :=
  Term.var (Sum.inl (Sum.inl (0 : Fin 1)))

/-- the free variable `x` of the graph formula -/
def rvSubXTerm : LRV.Term ((Fin 1 ⊕ Fin 0) ⊕ Fin 2) := Term.var (Sum.inr (0 : Fin 2))

/-- the free variable `y` of the graph formula -/
def rvSubYTerm : LRV.Term ((Fin 1 ⊕ Fin 0) ⊕ Fin 2) := Term.var (Sum.inr (1 : Fin 2))

/-- the term `-a` -/
def rvSubNegTerm : LRV.Term ((Fin 1 ⊕ Fin 0) ⊕ Fin 2) := Term.func Fn.vfNeg ![rvSubParamTerm]

/-- the term `x - a` -/
def rvSubDiffTerm : LRV.Term ((Fin 1 ⊕ Fin 0) ⊕ Fin 2) :=
  Term.func Fn.vfAdd ![rvSubXTerm, rvSubNegTerm]

/-- the term `rv (x - a)` -/
def rvSubValueTerm : LRV.Term ((Fin 1 ⊕ Fin 0) ⊕ Fin 2) :=
  Term.func Fn.rvMap ![rvSubDiffTerm]

/-- The graph formula of `x ↦ rv (x - a)` in the context `(x : VF, y : RV)`, the parameter `a`
being the single `VF`-parameter `Sum.inl (Sum.inl 0)` of `SP.singleVF a`. -/
def rvSubForm : LRV.BoundedFormula (Fin 1 ⊕ Fin 0) 2 := pEqG rvSubYTerm rvSubValueTerm

/-- the sort assignment of the two free variables of `rvSubForm` -/
def rvSubSorts : Fin 2 → SortTag := fun i => if i = 0 then SortTag.vf else SortTag.rv

theorem rvSubSorts_zero : rvSubSorts 0 = SortTag.vf := rfl

theorem rvSubSorts_one : rvSubSorts 1 = SortTag.rv := rfl

/-- **`rvSubForm` is well-sorted** (over the parameter pair with one `VF`-parameter). -/
theorem wellSorted_rvSubForm_aux :
    WellSorted (fun _ : Fin 1 ⊕ Fin 0 => SortTag.vf) rvSubSorts rvSubForm := by
  refine wellSorted_pEqG (s := SortTag.rv) _ _ ?_ ?_
  · simp [rvSubYTerm, rvSubSorts]
  · simp [rvSubValueTerm, rvSubDiffTerm, rvSubXTerm, rvSubNegTerm, rvSubParamTerm, rvSubSorts,
      tmSort_tRv, tmSort_vfAdd, tmSort_vfNeg, tmSort_var_inl]

/-- the sort map of the parameter pair `SP.singleVF a` is constantly `VF` -/
theorem singleVF_sortMap (a : M) (ha : iVF a) :
    (singleVF a ha).sortMap = fun _ => SortTag.vf := by
  funext i
  rcases i with i | j
  · rfl
  · exact j.elim0

/-- **`rvSubForm` is well-sorted** over `SP.singleVF a`. -/
theorem wellSorted_rvSubForm (a : M) (ha : iVF a) :
    WellSorted (singleVF a ha).sortMap rvSubSorts rvSubForm := by
  have h := wellSorted_rvSubForm_aux
  rw [singleVF_sortMap a ha]
  exact h

/-- **Realization of `rvSubForm`**: at `(x, y)`, the formula says `y = rv (x - a)`. -/
theorem realize_rvSubForm (a : M) (ha : iVF a) (x y : M) :
    rvSubForm.Realize (singleVF a ha).toFun ![x, y] ↔ y = iRv (iVFAdd x (iVFNeg a)) := by
  simp only [rvSubForm, rvSubValueTerm, rvSubDiffTerm, rvSubNegTerm, rvSubXTerm, rvSubYTerm,
    rvSubParamTerm,
    pEqG, BoundedFormula.realize_bdEqual, TermRealize.realize_rvMap, TermRealize.realize_vfAdd,
    TermRealize.realize_vfNeg, iRv, iVFAdd, iVFNeg, singleVF, toFun, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **`x ↦ rv (x - a)`**, as a named function. -/
def rvSubFun (a : M) : M → M := fun x => iRv (iVFAdd x (iVFNeg a))

/-- **`x ↦ rv (x - a)` is definable over `a`** in the sense of `SP.DefinableFun`. -/
theorem rvSubDefinableFun (a : M) (ha : iVF a) :
    DefinableFun (singleVF a ha) (rvSubFun a) :=
  ⟨rvSubForm, wellSorted_rvSubForm a ha, fun x y => realize_rvSubForm a ha x y⟩

/-! ## Constant functions are definable -/

/-- The graph formula of the constant function with value `rv 0`. -/
def constZeroForm (S : SP M) : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 2 :=
  pEqG (Term.var (Sum.inr (1 : Fin 2))) (Term.func Fn.rvZero fun i => i.elim0)

/-- **Constant `RV`-valued functions are definable.** -/
theorem definableFun_const (S : SP M) : DefinableFun S (fun _ => iRVZero) := by
  refine ⟨constZeroForm S, ?_, ?_⟩
  · refine wellSorted_pEqG (s := SortTag.rv) _ _ ?_ ?_
    · rw [tmSort_var_inr]
      rfl
    · exact tmSort_rvZero _ _
  · intro x y
    simp only [constZeroForm, pEqG, BoundedFormula.realize_bdEqual, TermRealize.realize_rvZero,
      Term.realize_var, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero, iRVZero]

/-! ## `finite:VF:project:RV` for a two-element set -/

/-- **`finite:VF:project:RV`** (`paper.tex:716`, Yin 4.10) **for `A = {a, b}`**: the two-element
set `{a, b} ⊆ VF` (`a ≠ b`) admits a definable injection into `RV`, namely `x ↦ rv (x - a)`:
`rv (a - a) = rv 0 = 0` while `rv (b - a) ≠ 0` because `rv x = 0` forces `x = 0`
(`RVCalc.vf_eq_zero_of_rv_eq_zero`, the axiom `rvEqInfty`).

This is the sharp case of the paper's lemma: Yin's induction produces an injection into `RV^m`
with `m` growing (`m+1` at the base step, `2m` at the outer step, `qe.tex:1090`), so the
single-value form frozen at `QE/Sec3_frozen.lean:215` is a strengthening of the paper's statement
and holds here only because `♯A = 2`.  The parameters are the `singleVF a` pair: the injection is
definable over `S` *together with* the point `a` used by the map, which is the parameter discipline
Yin's proof actually produces. -/
theorem swl_finite_VF_project_RV_pair (hM : M ⊨ Axioms.ACVF) (a b : M) (ha : iVF a) (hb : iVF b)
    (hne : a ≠ b) :
    ∃ f : M → M, DefinableFun (singleVF a ha) f ∧
      (∀ x : M, x ∈ ({a, b} : Set M) → iRV (f x)) ∧ Set.InjOn f ({a, b} : Set M) := by
  refine ⟨rvSubFun a, rvSubDefinableFun a ha, ?_, ?_⟩
  · intro x hx
    have hx' : x = a ∨ x = b := by simpa using hx
    rcases hx' with h | h
    · rw [h]
      show iRV (iRv (iVFAdd a (iVFNeg a)))
      rw [vf_add_neg hM ha]
      exact rv_mem (M := M) hM (vf_zero_mem (M := M) hM)
    · rw [h]
      exact rv_mem (M := M) hM (vf_add_mem (M := M) hM hb (vf_neg_mem (M := M) hM ha))
  · intro x hx y hy hxy
    have hx' : x = a ∨ x = b := by simpa using hx
    have hy' : y = a ∨ y = b := by simpa using hy
    have hna : iVF (iVFNeg a) := vf_neg_mem (M := M) hM ha
    have hbVF : iVF (iVFAdd b (iVFNeg a)) := vf_add_mem (M := M) hM hb hna
    have hsub : iVFAdd b (iVFNeg a) ≠ iVFZero (M := M) := by
      intro h
      apply hne
      have hab : iVFAdd b (iVFNeg a) = iVFAdd a (iVFNeg a) := by rw [h, vf_add_neg hM ha]
      have hab' : iVFAdd (iVFNeg a) b = iVFAdd (iVFNeg a) a := by
        rw [vf_add_comm hM hna hb, vf_add_comm hM hna ha]
        exact hab
      exact (vf_add_left_cancel (a := iVFNeg a) (b := b) (c := a) hM hna hb ha hab').symm
    rcases hx' with h | h <;> rcases hy' with h' | h'
    · rw [h, h']
    · rw [h, h'] at hxy
      exfalso
      refine hsub (vf_eq_zero_of_rv_eq_zero (M := M) hM hbVF ?_)
      simp only [rvSubFun] at hxy
      rw [← hxy, vf_add_neg hM ha, rv_zero_eq hM]
    · rw [h, h'] at hxy
      exfalso
      refine hsub (vf_eq_zero_of_rv_eq_zero (M := M) hM hbVF ?_)
      simp only [rvSubFun] at hxy
      rw [hxy, vf_add_neg hM ha, rv_zero_eq hM]
    · rw [h, h']

/-! ## `function:rv:to:vf:finite:image` for finite `A` -/

omit [LRV.Structure M] in
/-- **`function:rv:to:vf:finite:image`** (`paper.tex:687`, Yin 4.12) **for finite `A`**: the image
of a finite set is finite, with no definability needed.  This is the half of the paper's statement
that does not use `C`-minimality; the infinite case is Yin's Lemma 4.12, proved from
`C`-minimality and quantifier elimination (`qe.tex:1101`), see the file header. -/
theorem swl_function_rv_to_vf_finite_image_of_finite {A : Set M} (hA : A.Finite) (f : M → M) :
    (f '' A).Finite := hA.image f

/-! ## The injection behind `finite:VF:project:RV` for an arbitrary finite set

Yin's `finite:VF:project:RV` (`qe.tex:1070`) has two halves: an **injection** of the finite
`A ⊆ VF` into some `RV^k`, and its **definability**.  The injection is pure valuation theory and is
proved here for an arbitrary finite `A`, enumerated by `c : Fin k → M`:

`x ↦ (rv (x - c₀), …, rv (x - c_{k-1}))`

is injective on `{c₀, …, c_{k-1}}`, because the `i`-th coordinate of `cᵢ` is `rv 0 = 0` while the
`i`-th coordinate of `cⱼ` (`j ≠ i`) is `rv (cⱼ - cᵢ) ≠ 0` (`rv x = 0` forces `x = 0`).  This is the
"translate by the average and read off the `rv`'s" step of Yin's induction, made explicit about its
parameters: the coordinates are indexed by the elements of `A`, so the function is definable over
`S` *together with* `A` — which is why the frozen single-parameter form of
`QE/Sec3_frozen.lean:215` needs the correction recorded in the header.
-/

/-- The `k`-tuple of `rv`'s of the differences from the enumeration `c`. -/
def rvDiffTuple (c : Fin k → M) (x : M) : Fin k → M := fun i => iRv (iVFAdd x (iVFNeg (c i)))

/-- **The injection of a finite `A ⊆ VF` into `RV^k`** (`finite:VF:project:RV`, injectivity half,
with the elements of `A` among the parameters). -/
theorem rvDiffTuple_injOn_range (hM : M ⊨ Axioms.ACVF) {k : ℕ} (c : Fin k → M)
    (hc : Function.Injective c) (hVF : ∀ i, iVF (c i)) :
    Set.InjOn (rvDiffTuple (M := M) c) (Set.range c) := by
  rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ hxy
  by_cases hij : i = j
  · rw [hij]
  · exfalso
    have hne : c j ≠ c i := fun h => hij (hc h).symm
    have hni : iVF (iVFNeg (c i)) := vf_neg_mem (M := M) hM (hVF i)
    have hji : iVF (iVFAdd (c j) (iVFNeg (c i))) := vf_add_mem (M := M) hM (hVF j) hni
    have hzero : iVFAdd (c i) (iVFNeg (c i)) = iVFZero (M := M) := vf_add_neg hM (hVF i)
    have hcoord := congrFun hxy i
    simp only [rvDiffTuple] at hcoord
    have h1 : iRv (iVFAdd (c i) (iVFNeg (c i))) = iRVZero := by
      rw [hzero, rv_zero_eq hM]
    rw [h1] at hcoord
    have h2 : iVFAdd (c j) (iVFNeg (c i)) = iVFZero (M := M) := by
      refine vf_eq_zero_of_rv_eq_zero (M := M) hM hji ?_
      exact hcoord.symm
    -- `c j - c i = 0` forces `c j = c i`
    apply hne
    have h3 : iVFAdd (c j) (iVFNeg (c i)) = iVFAdd (c i) (iVFNeg (c i)) := by rw [h2, hzero]
    have h4 : iVFAdd (iVFNeg (c i)) (c j) = iVFAdd (iVFNeg (c i)) (c i) := by
      rw [vf_add_comm hM hni (hVF j), vf_add_comm hM hni (hVF i)]
      exact h3
    exact vf_add_left_cancel (a := iVFNeg (c i)) (b := c j) (c := c i) hM hni (hVF j) (hVF i) h4

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.SP.rvSubDefinableFun
#print axioms SpecialTransformations.Milestone0.SP.definableFun_const
#print axioms SpecialTransformations.Milestone0.SP.swl_finite_VF_project_RV_pair
#print axioms SpecialTransformations.Milestone0.SP.rvDiffTuple_injOn_range
#print axioms SpecialTransformations.Milestone0.SP.swl_function_rv_to_vf_finite_image_of_finite

end SP

end SpecialTransformations.Milestone0
