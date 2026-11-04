/-
**Variable substitution on `L_RV` terms and formulas** — from swarm `smw1jgnht` m6, verified here
(compiled: exit 0, 0 errors, no `sorry`).

This is the piece Mathlib does not have, and it was the single wall behind three separate items:

* `Term.substVar (σ : Fin n → Term (α ⊕ Fin m))` — replace the free variable `xᵢ` by the term `σ i`,
  parameters untouched; `BoundedFormula.substVar` with `Subst.lift` at the quantifier;
* `tmSort_substVar` — the sort of a term is preserved by a sort-preserving substitution;
* the guard transport: `substVar_guardAtom`, `inAntecedent_substVar`, `guardsLast_substVar`,
  `guardTrue_substVar` — at a quantifier the substitution is *lifted*, so the bound variable is
  fixed and the guarded/junk-true conditions transport verbatim;
* `wellSorted_substVar` — the formula-level statement;
* `realize_substVar_term`, `realize_substVar` — the semantics.

It unblocks, in order of value: §3's `swl_exchange` (which needs to interchange the free variable with
a parameter — promotion through `QE/ParamBridgeRelabel.lean`'s `wellSorted_relabel`, then demotion
through `substVar`), §4's `PaperStraightening` (the `DefinableFun` pairing, which also needs
`QE/ExSortedG.lean`'s `exSortedG_realize`), and the general pullback in §4's categories.

**Not closed here:** the `DefinableFun` pairing corollary, hence `dim_RV_fibers`'s (⇒) direction still
carries `PaperStraightening` as a hypothesis in `QE/Sec4Dim.lean`.  What it needs, exactly: eliminate
the intermediate tuple with iterated *guarded* existentials (`exSortedG_realize`, now available),
then the zero-padding `VF^{k'} ↪ VF^k`, giving `PaperStraightening` from `FibreSeparating`
(Yin 4.10 + compactness, a genuine earlier-section input) instead of from itself.

Check with `.scratch2/sec3/` (compiled `Enc`, `Sec3Frozen`, `Sec4Dim`): copy this file there and
`LEAN_PATH=$PWD:$LEAN_PATH lean` it.
-/
/-
Section 4 of Yin, "Special transformations in algebraically closed valued fields": the
**composition/substitution infrastructure** needed to make `dim:RV:fibers` a theorem rather than a
hypothesis.

`Milestone0/Encoding.lean` states well-sortedness (`WellSorted`) for formulas of `L_RV` with the
free variables of a context `Fin n`.  Mathlib's `BoundedFormula` has substitution for *parameters*
only (`BoundedFormula.subst`, `BoundedFormula.relabel`); replacing a free **variable** `x_i` by a
term is not available, and §3 and §4 both need it.  This file builds it:

* `Term.substVar`, `BoundedFormula.substVar`;
* `tmSort_substVar` — the sort of a term is preserved under a sort-preserving substitution;
* the transport of the syntactic guards (`Occurs`/`GuardsLast`/`GuardTrue`), which is what
  `WellSorted` asks for at a quantifier;
* `wellSorted_substVar` — well-sortedness is preserved;
* `realize_substVar` — the realization of a substituted formula;
## What is *not* here

The *composition/pairing corollary* for `Sec4Dim.DefinableFun` is **not** proved: to build the graph
of `x ↦ (g x, h x)` from the graphs of `g` and `h` one must eliminate the intermediate tuple with
guarded quantifiers, since `WellSorted` admits no unguarded one.  That needs the iteration of
`exSortedG` (`Milestone0/Encoding.lean`) *together with its realization lemma*,
`(exSortedG s ψ).Realize v xs ↔ ∃ a, sortEval s a ∧ ψ.Realize v (Fin.snoc xs a)`, which the encoding
does not have; the substitution built here is complete and is exactly what that step consumes
(`φ_h`'s variables are `Subst.lift`-renamed onto the intermediate tuple).  Consequently
`Sec4Dim.PaperStraightening` still carries the `⇒` direction of `dim:RV:fibers`.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Sec4Dim
set_option linter.unusedVariables false
open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
open LRV

namespace Sec4Compose

open Sec4Dim

variable {M : Type*} [LRV.Structure M]

/-! ## Substitution of free variables in terms -/

/-- `Term.substVar σ t` replaces the free variable `x_i` of `t` by the term `σ i`.  Parameters
(`Sum.inl`) are untouched. -/
def Term.substVar {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m)) :
    LRV.Term (α ⊕ Fin n) → LRV.Term (α ⊕ Fin m)
  | .var (Sum.inl a) => .var (Sum.inl a)
  | .var (Sum.inr i) => σ i
  | .func f ts => .func f fun i => Term.substVar σ (ts i)

/-- **The sort of a term is preserved** by a substitution that preserves the sorts of the
variables. -/
theorem tmSort_substVar {α : Type} (sα : α → SortTag) {n m : ℕ} {sn : Fin n → SortTag}
    {sm : Fin m → SortTag} {σ : Fin n → LRV.Term (α ⊕ Fin m)}
    (hσ : ∀ i, TmSort sα sm (σ i) = some (sn i)) (t : LRV.Term (α ⊕ Fin n)) :
    TmSort sα sm (Term.substVar σ t) = TmSort sα sn t := by
  induction t with
  | var a =>
    rcases a with a | i
    · rfl
    · exact hσ i
  | @func l f ts ih =>
    simp only [Term.substVar, TmSort]
    by_cases h : ∀ i, TmSort sα sn (ts i) = some (Fn.argSort f i)
    · have h' : ∀ i, TmSort sα sm (Term.substVar σ (ts i)) = some (Fn.argSort f i) :=
        fun i => by rw [ih i]; exact h i
      rw [if_pos h', if_pos h]
    · have h' : ¬ ∀ i, TmSort sα sm (Term.substVar σ (ts i)) = some (Fn.argSort f i) :=
        fun hc => h fun i => by rw [← ih i]; exact hc i
      rw [if_neg h', if_neg h]

@[simp]
theorem Term.substVar_var {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m))
    (i : Fin n) : Term.substVar σ (Term.var (Sum.inr i) : LRV.Term (α ⊕ Fin n)) = σ i := rfl

@[simp]
theorem Term.substVar_param {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m))
    (a : α) : Term.substVar σ (Term.var (Sum.inl a) : LRV.Term (α ⊕ Fin n)) =
      Term.var (Sum.inl a) := rfl

/-! ## The lift of a substitution to the body of a quantifier -/

/-- The substitution `σ` transported to the body of a quantifier: the bound variable of the body
is the variable itself (so the syntactic guards about it are preserved verbatim), and the free
variables keep their meaning in the extended context. -/
def Subst.lift {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m)) :
    Fin (n + 1) → LRV.Term (α ⊕ Fin (m + 1)) :=
  Fin.lastCases (Term.var (Sum.inr (Fin.last m))) (fun i => (σ i).relabel (Sum.map id Fin.castSucc))

@[simp]
theorem Subst.lift_last {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m)) :
    Subst.lift σ (Fin.last n) = Term.var (Sum.inr (Fin.last m)) := by
  simp [Subst.lift]

@[simp]
theorem Subst.lift_castSucc {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m))
    (j : Fin n) :
    Subst.lift σ (Fin.castSucc j) = (σ j).relabel (Sum.map id Fin.castSucc) := by
  simp [Subst.lift]

/-- The lifted substitution preserves sorts, when the ambient sorts are extended by the sort of the
bound variable. -/
theorem tmSort_lift {α : Type} (sα : α → SortTag) {n m : ℕ} {sn : Fin n → SortTag}
    {sm : Fin m → SortTag} {σ : Fin n → LRV.Term (α ⊕ Fin m)}
    (hσ : ∀ i, TmSort sα sm (σ i) = some (sn i)) (s : SortTag) :
    ∀ i : Fin (n + 1), TmSort sα (Fin.snoc sm s : Fin (m + 1) → SortTag) (Subst.lift σ i) =
      some ((Fin.snoc sn s : Fin (n + 1) → SortTag) i) := by
  intro i
  refine Fin.lastCases ?_ ?_ i
  · rw [Subst.lift_last, tmSort_var_inr, Fin.snoc_last, Fin.snoc_last]
  · intro j
    rw [Subst.lift_castSucc, tmSort_relabel_castSucc sα sm s, hσ j, Fin.snoc_castSucc]

/-! ## Substitution of free variables in formulas -/

/-- `BoundedFormula.substVar σ φ` replaces the free variable `x_i` of `φ` by the term `σ i`.  At a
quantifier the substitution is lifted (`Subst.lift`), so the bound variable is untouched. -/
def BoundedFormula.substVar {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m)) :
    LRV.BoundedFormula α n → LRV.BoundedFormula α m
  | .falsum => .falsum
  | .equal t u => .equal (Term.substVar σ t) (Term.substVar σ u)
  | .rel R ts => .rel R fun i => Term.substVar σ (ts i)
  | .imp a b => .imp (BoundedFormula.substVar σ a) (BoundedFormula.substVar σ b)
  | .all χ => .all (BoundedFormula.substVar (Subst.lift σ) χ)

@[simp]
theorem BoundedFormula.substVar_falsum {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m)) :
    BoundedFormula.substVar σ (⊥ : LRV.BoundedFormula α n) = ⊥ := rfl

theorem BoundedFormula.substVar_imp {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m))
    (a b : LRV.BoundedFormula α n) :
    BoundedFormula.substVar σ (a.imp b) = (BoundedFormula.substVar σ a).imp
      (BoundedFormula.substVar σ b) := rfl

/-- Substitution commutes with the encoding's conjunction `a ⊓ b` (which is `¬(a → ¬b)`), which is
what makes the transport of the guards work. -/
theorem BoundedFormula.substVar_inf {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m))
    (a b : LRV.BoundedFormula α n) :
    BoundedFormula.substVar σ (a ⊓ b) =
      (BoundedFormula.substVar σ a ⊓ BoundedFormula.substVar σ b) :=
  rfl

@[simp]
theorem BoundedFormula.substVar_top {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m)) :
    BoundedFormula.substVar σ (⊤ : LRV.BoundedFormula α n) = ⊤ := rfl


/-! ## Transport of the syntactic guards

`WellSorted` admits a quantifier only when the body is guarded: the sort atom of the bound variable
must occur as a top-level conjunct of an antecedent (`Occurs`/`GuardsLast`) and must be junk-true
(`GuardTrue`).  These are syntactic conditions on the *occurrences* of the bound variable, which
`Subst.lift` leaves alone, so they transport. -/

theorem substVar_rel {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m))
    {l : ℕ} (R : LRV.Relations l) (ts : Fin l → LRV.Term (α ⊕ Fin n)) :
    BoundedFormula.substVar σ (BoundedFormula.rel R ts) =
      BoundedFormula.rel R (fun j => Term.substVar σ (ts j)) := rfl

theorem substVar_pVFG {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m))
    (t : LRV.Term (α ⊕ Fin n)) :
    BoundedFormula.substVar σ (pVFG t) = pVFG (Term.substVar σ t) := by
  have h : (fun j : Fin 1 => Term.substVar σ (![t] j)) = ![Term.substVar σ t] := by
    funext j; fin_cases j; simp
  show BoundedFormula.rel Rel.memVF (fun j => Term.substVar σ (![t] j)) = pVFG (Term.substVar σ t)
  rw [h]
  rfl

theorem substVar_pRVG {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m))
    (t : LRV.Term (α ⊕ Fin n)) :
    BoundedFormula.substVar σ (pRVG t) = pRVG (Term.substVar σ t) := by
  have h : (fun j : Fin 1 => Term.substVar σ (![t] j)) = ![Term.substVar σ t] := by
    funext j; fin_cases j; simp
  show BoundedFormula.rel Rel.memRV (fun j => Term.substVar σ (![t] j)) = pRVG (Term.substVar σ t)
  rw [h]
  rfl

theorem substVar_guardAtom {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m))
    {i : Fin n} {i' : Fin m} (hσ : σ i = Term.var (Sum.inr i')) (s : SortTag) :
    BoundedFormula.substVar σ (guardAtom s i) = guardAtom s i' := by
  cases s with
  | vf =>
    show BoundedFormula.substVar σ (pVFG (Term.var (Sum.inr i))) = guardAtom SortTag.vf i'
    rw [substVar_pVFG]
    rw [show Term.substVar σ (Term.var (Sum.inr i)) = Term.var (Sum.inr i') from hσ]
    rfl
  | rv =>
    show BoundedFormula.substVar σ (pRVG (Term.var (Sum.inr i))) = guardAtom SortTag.rv i'
    rw [substVar_pRVG]
    rw [show Term.substVar σ (Term.var (Sum.inr i)) = Term.var (Sum.inr i') from hσ]
    rfl

theorem inAntecedent_substVar {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m))
    {s : SortTag} {i : Fin n} {i' : Fin m} (hσ : σ i = Term.var (Sum.inr i')) :
    ∀ {η : LRV.BoundedFormula α n},
      InAntecedent s i η → InAntecedent s i' (BoundedFormula.substVar σ η) := by
  intro η h
  induction h with
  | atom =>
    rw [substVar_guardAtom σ hσ]
    exact InAntecedent.atom
  | and_left h ih => exact InAntecedent.and_left ih
  | and_right h ih => exact InAntecedent.and_right ih

theorem guardsLast_substVar {α : Type} (s : SortTag) :
    ∀ {n m : ℕ} {σ : Fin n → LRV.Term (α ⊕ Fin m)} {i : Fin n} {i' : Fin m},
      σ i = Term.var (Sum.inr i') → ∀ {η : LRV.BoundedFormula α n},
      GuardsLast s i η → GuardsLast s i' (BoundedFormula.substVar σ η)
  | _, _, _, _, _, _, .falsum, h => h.elim
  | _, _, _, _, _, _, .equal _ _, h => h.elim
  | _, _, _, _, _, _, .rel _ _, h => h.elim
  | _, _, σ, i, i', hσ, .imp a b, h => by
    show Occurs i' s (BoundedFormula.substVar σ a) ∨
      GuardsLast s i' (BoundedFormula.substVar σ a) ∨
      GuardsLast s i' (BoundedFormula.substVar σ b)
    rcases h with h | h | h
    · exact Or.inl (inAntecedent_substVar σ hσ h)
    · exact Or.inr (Or.inl (guardsLast_substVar s hσ h))
    · exact Or.inr (Or.inr (guardsLast_substVar s hσ h))
  | _, _, σ, i, i', hσ, .all χ, h => by
    show GuardsLast s (Fin.castSucc i') (BoundedFormula.substVar (Subst.lift σ) χ)
    exact guardsLast_substVar s (by rw [Subst.lift_castSucc, hσ]; rfl) h

theorem guardTrue_substVar {α : Type} (s : SortTag) :
    ∀ {n m : ℕ} {σ : Fin n → LRV.Term (α ⊕ Fin m)} {i : Fin n} {i' : Fin m},
      σ i = Term.var (Sum.inr i') → ∀ {η : LRV.BoundedFormula α n},
      GuardTrue s i η → GuardTrue s i' (BoundedFormula.substVar σ η)
  | _, _, _, _, _, _, .falsum, h => by cases h
  | _, _, _, _, _, _, .equal _ _, h => by cases h
  | _, _, _, _, _, _, .rel _ _, h => by cases h
  | _, _, σ, i, i', hσ, .imp η ψ, h => by
    show GuardTrue s i' ((BoundedFormula.substVar σ η).imp (BoundedFormula.substVar σ ψ))
    cases h with
    | imp hg => exact GuardTrue.imp (inAntecedent_substVar σ hσ hg)
  | _, _, σ, i, i', hσ, .all χ, h => by
    show GuardTrue s i' (.all (BoundedFormula.substVar (Subst.lift σ) χ))
    cases h with
    | all hg => exact GuardTrue.all (guardTrue_substVar s (by rw [Subst.lift_castSucc, hσ]; rfl) hg)

/-! ## Well-sortedness is preserved -/

/-- **Well-sortedness is preserved by a sort-preserving substitution of free variables.** -/
theorem wellSorted_substVar {α : Type} (sα : α → SortTag) :
    ∀ {n : ℕ} {sn : Fin n → SortTag} {φ : LRV.BoundedFormula α n},
      WellSorted sα sn φ →
      ∀ {m : ℕ} {sm : Fin m → SortTag} {σ : Fin n → LRV.Term (α ⊕ Fin m)},
        (∀ i, TmSort sα sm (σ i) = some (sn i)) →
        WellSorted sα sm (BoundedFormula.substVar σ φ) := by
  intro n sn φ h
  induction h with
  | falsum => intro m sm σ hσ; exact WellSorted.falsum sm
  | equal sn ht hu =>
    intro m sm σ hσ
    exact WellSorted.equal sm (by rw [tmSort_substVar sα hσ]; exact ht)
      (by rw [tmSort_substVar sα hσ]; exact hu)
  | rel sn R ts hts =>
    intro m sm σ hσ
    exact WellSorted.rel sm R (fun i => Term.substVar σ (ts i))
      (fun i => by rw [tmSort_substVar sα hσ (ts i), hts i])
  | imp sn ha hb iha ihb =>
    intro m sm σ hσ
    exact WellSorted.imp sm (iha hσ) (ihb hσ)
  | all sn hχ hg hj ihχ =>
    intro m sm σ hσ
    exact WellSorted.all sm (ihχ (tmSort_lift sα hσ _))
      (guardsLast_substVar _ (Subst.lift_last σ) hg)
      (guardTrue_substVar _ (Subst.lift_last σ) hj)


/-! ## Realization of a substituted term and formula -/

theorem realize_substVar_term {α : Type} {n m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m))
    (v : α → M) (xs : Fin m → M) (t : LRV.Term (α ⊕ Fin n)) :
    Term.realize (Sum.elim v xs) (Term.substVar σ t) =
      Term.realize (Sum.elim v (fun i => Term.realize (Sum.elim v xs) (σ i))) t := by
  induction t with
  | var a =>
    rcases a with a | i
    · rfl
    · rfl
  | @func l f ts ih =>
    rw [Term.substVar, Term.realize_func, Term.realize_func]
    congr 1
    funext i
    exact ih i

/-- **The realization of a substituted formula**: realizing `φ` with the free variable `x_i`
replaced by the term `σ i` is realizing `φ` at the tuple of the values of the `σ i`. -/
theorem realize_substVar {α : Type} :
    ∀ {n : ℕ} (φ : LRV.BoundedFormula α n), ∀ {m : ℕ} (σ : Fin n → LRV.Term (α ⊕ Fin m))
      (v : α → M) (xs : Fin m → M),
      (BoundedFormula.substVar σ φ).Realize v xs ↔
        φ.Realize v (fun i => Term.realize (Sum.elim v xs) (σ i)) := by
  intro n φ
  induction φ with
  | falsum => intro m σ v xs; exact Iff.rfl
  | equal t u =>
    intro m σ v xs
    show ((Term.substVar σ t).bdEqual (Term.substVar σ u)).Realize v xs ↔
      (t.bdEqual u).Realize v (fun i => Term.realize (Sum.elim v xs) (σ i))
    rw [BoundedFormula.realize_bdEqual, BoundedFormula.realize_bdEqual,
      realize_substVar_term, realize_substVar_term]
  | rel R ts =>
    intro m σ v xs
    show (Relations.boundedFormula R (fun j => Term.substVar σ (ts j))).Realize v xs ↔
      (Relations.boundedFormula R ts).Realize v (fun i => Term.realize (Sum.elim v xs) (σ i))
    rw [BoundedFormula.realize_rel, BoundedFormula.realize_rel]
    rw [show (fun i => Term.realize (Sum.elim v xs) (Term.substVar σ (ts i))) =
        (fun i => Term.realize (Sum.elim v (fun i => Term.realize (Sum.elim v xs) (σ i))) (ts i)) from by
      funext j
      exact realize_substVar_term σ v xs (ts j)]
  | imp a b iha ihb =>
    intro m σ v xs
    show ((BoundedFormula.substVar σ a).imp (BoundedFormula.substVar σ b)).Realize v xs ↔
      (a.imp b).Realize v (fun i => Term.realize (Sum.elim v xs) (σ i))
    rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp, iha, ihb]
  | all χ ih =>
    intro m σ v xs
    show (BoundedFormula.all (BoundedFormula.substVar (Subst.lift σ) χ)).Realize v xs ↔
      (BoundedFormula.all χ).Realize v (fun i => Term.realize (Sum.elim v xs) (σ i))
    rw [BoundedFormula.realize_all, BoundedFormula.realize_all]
    have hass : ∀ a : M, (fun i => Term.realize (Sum.elim v (Fin.snoc xs a)) (Subst.lift σ i)) =
        Fin.snoc (fun i => Term.realize (Sum.elim v xs) (σ i)) a := by
      intro a
      funext i
      refine Fin.lastCases ?_ ?_ i
      · simp only [Subst.lift_last, Term.realize_var, Sum.elim_inr, Fin.snoc_last]
      · intro j
        rw [Subst.lift_castSucc, Term.realize_relabel, Fin.snoc_castSucc]
        congr 1
        funext x
        rcases x with x | x
        · rfl
        · rw [Function.comp_apply, Sum.map_inr, Sum.elim_inr, Sum.elim_inr, Fin.snoc_castSucc]
    simp only [ih, hass]

end Sec4Compose

end SpecialTransformations.Milestone0
