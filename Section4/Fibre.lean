module

/-
**`dim:VF:pullback`, the "trivial" half, made unconditional by `DefinableFun`-composition.**

`QE/Sec4Polydisc.lean`'s `dimVF_fibre_le` — *"`dim_VF (fib A tbar) ≤ dim_VF A`"*, the paper's
*"the other direction is trivial"* in Lemma `dim:VF:pullback` (`paper.tex:842`) — carries

  `hcomp : ∀ G, DefinableFun S A G → DefinableFun S (fibre A t) (fun x => G (concat x t))`

because in this encoding the fibre lives in `VF^n × RV^0`, not inside `A ⊆ VF^n × RV^m`, so the
passage from `G` to `x ↦ G (x, tbar)` is a *composition*, not a restriction.

`Compose.lean`'s `DefinableFun.comp_of_mapsTo` discharges `hcomp` from the definability of the one
map `x ↦ (x, tbar)`, which this file proves: its graph is the conjunction, over the `n + m`
coordinates of the target, of `y_i = x_i` (the `VF`-coordinates) and `y_{n+j} = tau_j` (the
`RV`-coordinates, held as *parameters*).  Nothing is quantified, so no `exsG` is needed here — the
padding map is where the composition wall is cheap.

The one thing the parameters must supply is the tuple `tbar` itself: `τ : Fin m → Fin S.n ⊕ Fin S.m`
with `S.sortMap (τ j) = .rv` and `S.toFun (τ j) = t (Sum.inr j)`.  That is exactly the paper's
parameter discipline — the fibre `fib(A, tbar)` is definable over `S` together with `tbar` — and it
is the only hypothesis left.

No `sorry`, no `axiom`, no `native_decide`.
-/
public import Compose
public import Sec4Polydisc

@[expose] public section

set_option linter.unusedVariables false
open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
open LRV

namespace Sec4FunComp

open Sec4Dim Sec4Compose Sec4

variable {M : Type} [LRV.Structure M]

/-! ## Reading `pairAssign` at the two blocks of the padding graph -/

theorem pairAssign_vf {n m : ℕ} (x : Tup M n 0) (y : Tup M n m) (i₀ : Fin n) :
    pairAssign x y (Fin.castAdd (n + m) (Fin.castAdd 0 i₀)) = x (Sum.inl i₀) := by
  rw [pairAssign_left]
  show x (finSumFinEquiv.symm (Fin.castAdd 0 i₀)) = x (Sum.inl i₀)
  rw [finSumFinEquiv_symm_apply_castAdd]

theorem pairAssign_yvf {n m : ℕ} (x : Tup M n 0) (y : Tup M n m) (i₀ : Fin n) :
    pairAssign x y (Fin.natAdd (n + 0) (Fin.castAdd m i₀)) = y (Sum.inl i₀) := by
  rw [pairAssign_right]
  show y (finSumFinEquiv.symm (Fin.castAdd m i₀)) = y (Sum.inl i₀)
  rw [finSumFinEquiv_symm_apply_castAdd]

theorem pairAssign_yrv {n m : ℕ} (x : Tup M n 0) (y : Tup M n m) (j : Fin m) :
    pairAssign x y (Fin.natAdd (n + 0) (Fin.natAdd n j)) = y (Sum.inr j) := by
  rw [pairAssign_right]
  show y (finSumFinEquiv.symm (Fin.natAdd n j)) = y (Sum.inr j)
  rw [finSumFinEquiv_symm_apply_natAdd]

/-! ## The graph of the padding map `x ↦ (x, tbar)` -/

/-- The `i`-th conjunct of the padding graph: for a `VF`-coordinate, output = input; for an
`RV`-coordinate, the output is the parameter `τ j`. -/
def padConj (S : SP M) (n m : ℕ) (τ : Fin m → Fin S.n ⊕ Fin S.m) (i : Fin (n + m)) :
    LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) ((n + 0) + (n + m)) :=
  Fin.addCases
    (fun i₀ : Fin n => pEqG (Term.var (Sum.inr (Fin.natAdd (n + 0) (Fin.castAdd m i₀))))
      (Term.var (Sum.inr (Fin.castAdd (n + m) (Fin.castAdd 0 i₀)))))
    (fun j : Fin m => pEqG (Term.var (Sum.inr (Fin.natAdd (n + 0) (Fin.natAdd n j))))
      (Term.var (Sum.inl (τ j))))
    i

@[simp]
theorem padConj_castAdd (S : SP M) (n m : ℕ) (τ : Fin m → Fin S.n ⊕ Fin S.m) (i₀ : Fin n) :
    padConj S n m τ (Fin.castAdd m i₀) =
      pEqG (Term.var (Sum.inr (Fin.natAdd (n + 0) (Fin.castAdd m i₀))))
        (Term.var (Sum.inr (Fin.castAdd (n + m) (Fin.castAdd 0 i₀)))) :=
  Fin.addCases_left _

@[simp]
theorem padConj_natAdd (S : SP M) (n m : ℕ) (τ : Fin m → Fin S.n ⊕ Fin S.m) (j : Fin m) :
    padConj S n m τ (Fin.natAdd n j) =
      pEqG (Term.var (Sum.inr (Fin.natAdd (n + 0) (Fin.natAdd n j))))
        (Term.var (Sum.inl (τ j))) :=
  Fin.addCases_right _

/-- **The graph formula of `x ↦ (x, tbar)`**: the conjunction of the `n + m` coordinate
equalities. -/
def padForm (S : SP M) (n m : ℕ) (τ : Fin m → Fin S.n ⊕ Fin S.m) :
    LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) ((n + 0) + (n + m)) :=
  conjFin (padConj S n m τ)

theorem wellSorted_padForm (S : SP M) (n m : ℕ) (τ : Fin m → Fin S.n ⊕ Fin S.m)
    (hτs : ∀ j, S.sortMap (τ j) = SortTag.rv) :
    WellSorted S.sortMap (Fin.append (fSort n 0) (fSort n m)) (padForm S n m τ) := by
  refine wellSorted_conjFin (fun i => ?_)
  refine Fin.addCases (fun i₀ => ?_) (fun j => ?_) i
  · simp only [padConj_castAdd]
    refine wellSorted_pEqG (s := SortTag.vf) S.sortMap
      (Fin.append (fSort n 0) (fSort n m)) ?_ ?_
    · simp only [tmSort_var_inr, Fin.append_right, fSort, finSumFinEquiv_symm_apply_castAdd]
      rfl
    · simp only [tmSort_var_inr, Fin.append_left, fSort, finSumFinEquiv_symm_apply_castAdd]
      rfl
  · simp only [padConj_natAdd]
    refine wellSorted_pEqG (s := SortTag.rv) S.sortMap
      (Fin.append (fSort n 0) (fSort n m)) ?_ ?_
    · simp only [tmSort_var_inr, Fin.append_right, fSort, finSumFinEquiv_symm_apply_natAdd]
      rfl
    · rw [tmSort_var_inl, hτs j]

theorem realize_padForm (S : SP M) (n m : ℕ) (τ : Fin m → Fin S.n ⊕ Fin S.m)
    (t : Tup M 0 m) (hτv : ∀ j, S.toFun (τ j) = t (Sum.inr j))
    (x : Tup M n 0) (y : Tup M n m) :
    (padForm S n m τ).Realize S.toFun (pairAssign x y) ↔ concat x t = y := by
  rw [padForm, realize_conjFin]
  constructor
  · intro h
    refine Subtype.ext (funext fun i => ?_)
    rcases i with i₀ | j
    · have hi := h (Fin.castAdd m i₀)
      simp only [padConj_castAdd, pEqG, BoundedFormula.realize_bdEqual, Term.realize_var,
        Sum.elim_inr, pairAssign_yvf, pairAssign_vf] at hi
      rw [concat_inl, hi]
    · have hj := h (Fin.natAdd n j)
      simp only [padConj_natAdd, pEqG, BoundedFormula.realize_bdEqual, Term.realize_var,
        Sum.elim_inr, Sum.elim_inl, pairAssign_yrv] at hj
      rw [concat_inr, ← hτv j]
      exact hj.symm
  · intro hsub i
    subst hsub
    refine Fin.addCases (fun i₀ => ?_) (fun j => ?_) i
    · simp only [padConj_castAdd, pEqG, BoundedFormula.realize_bdEqual, Term.realize_var,
        Sum.elim_inr, pairAssign_yvf, pairAssign_vf, concat_inl]
    · simp only [padConj_natAdd, pEqG, BoundedFormula.realize_bdEqual, Term.realize_var,
        Sum.elim_inr, Sum.elim_inl, pairAssign_yrv, concat_inr]
      exact (hτv j).symm

/-- **The padding map `x ↦ (x, tbar)` is definable.**  The only hypothesis is that the parameters
name `tbar`, which is the paper's own parameter discipline for `fib(A, tbar)`. -/
theorem definableFun_concat (S : SP M) {n m : ℕ} (A : Set (Tup M n m)) (t : Tup M 0 m)
    (τ : Fin m → Fin S.n ⊕ Fin S.m) (hτs : ∀ j, S.sortMap (τ j) = SortTag.rv)
    (hτv : ∀ j, S.toFun (τ j) = t (Sum.inr j)) :
    DefinableFun S (fibre A t) (fun x : Tup M n 0 => concat x t) :=
  ⟨padForm S n m τ, wellSorted_padForm S n m τ hτs,
    fun x _ y => realize_padForm S n m τ t hτv x y⟩

/-- **`dim_VF (fib(A, tbar)) ≤ dim_VF A` with no composition hypothesis**: the `hcomp` of
`Sec4.dimVF_fibre_le` is discharged by `DefinableFun.comp_of_mapsTo` applied to the definable
padding map.  The only hypothesis is that the parameters name `tbar`. -/
theorem dimVF_fibre_le (S : SP M) {n m : ℕ} (A : Set (Tup M n m)) (t : Tup M 0 m)
    (τ : Fin m → Fin S.n ⊕ Fin S.m) (hτs : ∀ j, S.sortMap (τ j) = SortTag.rv)
    (hτv : ∀ j, S.toFun (τ j) = t (Sum.inr j)) :
    dimVF S (fibre A t) ≤ dimVF S A :=
  Sec4.dimVF_fibre_le S A t
    (fun {k l} G hG =>
      DefinableFun.comp_of_mapsTo (definableFun_concat S A t τ hτs hτv) hG (fun x hx => hx))

/-- The `m = 0` case of `dimVF_fibre_le`, with the parameter hypothesis visibly vacuous: no
hypothesis at all.  (This is the shape in which the paper's `dim:VF:pullback` is applied to a
`VF^n × RV^0`-set.) -/
theorem dimVF_fibre_le_zero (S : SP M) {n : ℕ} (A : Set (Tup M n 0)) (t : Tup M 0 0) :
    dimVF S (fibre A t) ≤ dimVF S A :=
  dimVF_fibre_le S A t (fun j => j.elim0) (fun j => j.elim0) (fun j => j.elim0)

/-- **Finite-to-one maps do not raise `dim_VF`, with no composition hypothesis.**  This is
`Sec4.hasDim_of_finFib` with its `hcomp` (a hypothesis quantifying over *every* definable `G`)
replaced by the definability of the single map `φ` — which is what `DefinableFun.comp` buys. -/
theorem hasDim_of_finFib' (S : SP M) {n m n' m' : ℕ} {A : Set (Tup M n m)}
    {B : Set (Tup M n' m')} (φ : Tup M n' m' → Tup M n m) (hφd : DefinableFun S B φ)
    (hφ : ∀ b ∈ B, φ b ∈ A)
    (hfib : ∀ a : Tup M n m, {b : Tup M n' m' | b ∈ B ∧ φ b = a}.Finite)
    {k : ℕ} (h : HasDim S A k) : HasDim S B k :=
  Sec4.hasDim_of_finFib S φ hφ hfib
    (fun {_ _} G hG => DefinableFun.comp_of_mapsTo hφd hG hφ) h

/-- **`dim_VF` does not increase along a definable finite-to-one map**, with no `hcomp`. -/
theorem dimVF_le_of_finFib' (S : SP M) {n m n' m' : ℕ} {A : Set (Tup M n m)}
    {B : Set (Tup M n' m')} (φ : Tup M n' m' → Tup M n m) (hφd : DefinableFun S B φ)
    (hφ : ∀ b ∈ B, φ b ∈ A)
    (hfib : ∀ a : Tup M n m, {b : Tup M n' m' | b ∈ B ∧ φ b = a}.Finite) :
    dimVF S B ≤ dimVF S A :=
  (dimVF_le_iff S B (dimVF S A)).2
    (hasDim_of_finFib' S φ hφd hφ hfib ((dimVF_le_iff S A (dimVF S A)).1 le_rfl))

end Sec4FunComp

end SpecialTransformations.Milestone0

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.Sec4FunComp.wellSorted_padForm
#print axioms SpecialTransformations.Milestone0.Sec4FunComp.realize_padForm
#print axioms SpecialTransformations.Milestone0.Sec4FunComp.definableFun_concat
#print axioms SpecialTransformations.Milestone0.Sec4FunComp.dimVF_fibre_le
#print axioms SpecialTransformations.Milestone0.Sec4FunComp.dimVF_fibre_le_zero
#print axioms SpecialTransformations.Milestone0.Sec4FunComp.hasDim_of_finFib'
#print axioms SpecialTransformations.Milestone0.Sec4FunComp.dimVF_le_of_finFib'
