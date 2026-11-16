module

/-
**§4 `full:dim:open:poly`, its base case, and two corollaries — plus one negative result that is
worth more than the positives** — from swarm `smw1jgnht` m2, verified here (compiled: exit 0, 0 errors,
no `sorry`; axioms within {propext, Classical.choice, Quot.sound}).

Everything is about the paper's notion (`paper.tex:807`): `Tup M n m`, `DefinableFun S A f`,
`FibreFinite`, `HasDim`, `dimVF` as the *least* `k`.  This is a corrected resubmission — the first
version had a combinatorial `DimLe` with no definability constraint, which is a different notion.

Proved: `full_dim_open_poly_if`/`_if'`/`_if_fibre` — the "if" of `full:dim:open:poly` (`dim_VF A = n`
if some fibre contains an open polydisc), with the sole hypothesis `PolydiscDim` (= `VF:dim:tran:deg`
for a polydisc); `full_dim_open_poly_base` — the "only if" at `n = 1`, from C-minimality, with
`dimVF_ne_one_of_finite` supplying the paper's "since `A` is infinite"; `VF_dim_mono` (Cor. 865) from
`VF:dim:tran:deg` plus `td` on finite images; `dim_ge_of_contains_rvPolydisc` (Cor. 908);
`dimVF_eq_zero_of_finite`.

**The negative result.**  Under the definability constraint: `dim_VF A ≤ n`, monotonicity and
*finite ⟹ 0* survive — but **transfer along a finite-to-one map does not**:
`hasDim_of_finFib`/`dimVF_le_of_finFib` need `DefinableFun`-composition, and `dimVF_fibre_le` (the
trivial half of `dim:VF:pullback`) fails for a *representation* reason — a fibre lives in
`VF^n × RV^0`, not inside `A`.  The composition is carried as the explicit hypothesis `hcomp`, which
is right (contrast the earlier `PaperStraightening`, which absorbed the conclusion).  `hcomp` is now
buildable: `QE/SubstVar.lean` + `QE/ExSortedG.lean`.

**Open**: the general "only if" of `full:dim:open:poly`, recorded as `def FullDimOpenPoly` and assumed
nowhere; its induction needs `dim:VF:pullback` and `VF:dim:tran:deg` over `dcl(b̄)`, so it should be
restated in terms of those when they exist rather than left as a bare `def`.

Check with `.scratch2/sec3/` (compiled `Enc`, `Sec3Frozen`, `Sec4Dim`): copy this file there and
`LEAN_PATH=$PWD:$LEAN_PATH lean` it.
-/
/-
# Yin, "Special transformations in algebraically closed valued fields" (arXiv:1006.2467), §4:
  `VF`-dimension, the open-polydisc criterion, and `VF:dim:mono` (`paper.tex` 865, 880--908)

Built on `QE/Sec4Dim.lean` (swarm `smw1jgnht` m6), so that **`dim_VF` is the paper's notion**:

> **Definition** (`paper.tex:807`). The *`VF`-dimension* of `A ⊆ VF^n × RV^m`, denoted by `dim_VF(A)`,
> is the smallest number `k` such that there is a **definable** finite-to-one function
> `f : A → VF^k × RV_Γ^l`.

`Sec4Dim.HasDim S A k` is that definition's "there is a definable finite-to-one `f` into
`VF^{k'} × RV^l`, `k' ≤ k`", and `Sec4Dim.dimVF S A` is its least `k` (`Sec4Dim.dimVF_le_iff`
says `dimVF S A ≤ k ↔ HasDim S A k`).  So every statement below is about the paper's `dim_VF`,
not about a combinatorial surrogate.

## What this file proves

Purely internal (no mathematics assumed; hypotheses only where marked):

* `dimVF_eq_zero_of_finite` — a **finite** definable `A` has `dim_VF A = 0`: the constant map to
  `RV^0` (the paper's `RV^0 = {∞}`, here the one-point tuple type `Tup M 0 0`) has graph `⊤`, hence
  is definable, and its only fibre is `A`.  This is the step that survives the definability
  constraint, because no substitution is needed.
* `dimVF_ne_one_of_finite` — hence a finite set does not have `dim_VF = 1`; this is the paper's
  *"since `A` is infinite"* in the base case `n = 1` of `full:dim:open:poly`.
* `full_dim_open_poly_if` — Lemma `full:dim:open:poly`, **"if" direction**
  (`paper.tex:880`: *"`dim_VF(A) = n` if and only if there is a `tbar ∈ RV^m` such that
  `fib(A, tbar)` contains an open polydisc"*), from the single hypothesis
  `hPoly : n ≤ dim_VF(polydisc)`, which is the paper's Lemma `VF:dim:tran:deg` for the polydisc
  (`paper.tex:852`).  The paper: *"The `if` direction is immediate by Lemma `VF:dim:tran:deg`."*
  Proof: `dim_VF A ≤ n` is `Sec4Dim.dimVF_le_self`; the polydisc sits in `A`
  (`polydisc_subset_fibre_iff`), so `n ≤ dim_VF(polydisc) ≤ dim_VF A` by `Sec4Dim.dimVF_mono`.
* `polydisc_subset_fibre_iff` — `polydiscAt c r t ⊆ A ↔ polydisc c r ⊆ fibre A t`: the paper's
  "the fibre over `tbar` contains an open polydisc" in the ambient tuple shape, where
  `Sec4Dim.dimVF_mono` applies.
* `full_dim_open_poly_base` — the same lemma's **"only if" direction at `n = 1`**
  (`paper.tex:890`: *"For the base case `n = 1`, since `A` is infinite, the lemma simply follows
  from `C`-minimality"*), from `C`-minimality in the form the sentence uses (`CMinimalDisc`).
* `dim_ge_of_contains_rvPolydisc` — Corollary `VF:dim:rv:polydisc` (`paper.tex:908`), from the
  `RV`-side polydisc dimension `hRvPoly`.

## What does *not* go through, and why (the interesting output)

* `hasDim_of_finFib` / `dimVF_le_of_finFib` — "a finite-to-one map `φ : B → A` does not raise
  `dim_VF`".  The combinatorial half is proved (the fibre of the composite is a finite union of
  finite fibres of `φ`), but the definability half needs **`DefinableFun` to compose**: from a
  definable graph of `G` on `A` one must define the graph of `b ↦ G(φ b)`, i.e. substitute the
  terms of `φ`'s defining formula for the free variables of `G`'s — the substitution/renaming
  lemma for `LRV.BoundedFormula` together with invariance of `WellSorted` under it, which neither
  the encoding nor `Sec4Dim` builds.  It is carried as the explicit hypothesis `hcomp`.  This is
  also why the paper's "the other direction is trivial" in `dim:VF:pullback`
  (`dim_VF(fib(A,tbar)) ≤ dim_VF(A)`) is *not* trivial in this encoding: `fib(A,tbar)` lives in
  `VF^n × RV^0`, not inside `A ⊆ VF^n × RV^m`, so the comparison is exactly a composition with
  `x ↦ (x, tbar)`; stated as `dimVF_fibre_le`, with the same `hcomp`.
* `VF_dim_mono` — Corollary `VF:dim:mono` (`paper.tex:865`), from Lemma `VF:dim:tran:deg`
  (`dim_VF = td`) and `td`'s behaviour on finite images, both as explicit hypotheses.

No `axiom`, no `sorry`, no `native_decide`.
-/
public import Sec4Dim

@[expose] public section

set_option linter.unusedVariables false

open FirstOrder FirstOrder.Language
open Set

namespace SpecialTransformations.Milestone0
open LRV

namespace Sec4

open Sec4Dim

variable {M : Type*} [LRV.Structure M]

/-! ## 1. The paper's tuples: `VF^n × RV^m`, fibres, and assembling them -/

/-- Assemble a `VF^n`-tuple and an `RV^m`-tuple into a `VF^n × RV^m`-tuple (the paper's
`(ā, t̄)`). -/
def concat {n m : ℕ} (x : Tup M n 0) (t : Tup M 0 m) : Tup M n m :=
  ⟨fun i => Sum.elim (fun a => x (Sum.inl a)) (fun b => t (Sum.inr b)) i, by
    intro i
    rcases i with a | b
    · exact x.2 (Sum.inl a)
    · exact t.2 (Sum.inr b)⟩

@[simp] theorem concat_inl {n m : ℕ} (x : Tup M n 0) (t : Tup M 0 m) (i : Fin n) :
    concat x t (Sum.inl i) = x (Sum.inl i) := rfl

@[simp] theorem concat_inr {n m : ℕ} (x : Tup M n 0) (t : Tup M 0 m) (j : Fin m) :
    concat x t (Sum.inr j) = t (Sum.inr j) := rfl

/-- `x ↦ (x, tbar)` is injective: fixing the `RV`-coordinates determines the tuple. -/
theorem concat_injective {n m : ℕ} (t : Tup M 0 m) :
    Function.Injective (fun x : Tup M n 0 => concat x t) := by
  intro x y hxy
  refine Subtype.ext (funext fun i => ?_)
  rcases i with a | b
  · have h := congrArg (fun z : Tup M n m => z (Sum.inl a)) hxy
    simpa using h
  · exact b.elim0

/-- The `VF`-coordinates of a tuple, as an element of `VF^n` (the `RV`-coordinates are dropped). -/
def vfPart {n m : ℕ} (x : Tup M n m) : Tup M n 0 :=
  ⟨fun i => x (Sum.inl (Sum.elim (fun a : Fin n => a) (fun b : Fin 0 => b.elim0) i)), by
    intro i
    rcases i with a | b
    · exact x.2 (Sum.inl a)
    · exact b.elim0⟩

@[simp] theorem vfPart_apply {n m : ℕ} (x : Tup M n m) (i : Fin n) :
    vfPart x (Sum.inl i) = x (Sum.inl i) := rfl

/-- Re-assembling the `VF`-coordinates of `x` with an `RV`-tuple gives `x` back, provided the
`RV`-tuple is `x`'s own `RV`-part. -/
theorem concat_vfPart {n m : ℕ} (x : Tup M n m) (t : Tup M 0 m)
    (hx : ∀ j, x (Sum.inr j) = t (Sum.inr j)) : concat (vfPart x) t = x := by
  refine Subtype.ext (funext fun i => ?_)
  rcases i with a | b
  · rfl
  · simpa using (hx b).symm

/-- The unique tuple of `VF^0 × RV^0` — the paper's `RV^0 = {∞}` shape. -/
def emptyTup : Tup M 0 0 :=
  ⟨fun i => Sum.elim (fun a : Fin 0 => a.elim0) (fun b : Fin 0 => b.elim0) i, by
    intro i
    rcases i with a | b
    · exact a.elim0
    · exact b.elim0⟩

theorem subsingleton_emptyTup : Subsingleton (Tup M 0 0) :=
  ⟨fun x y => Subtype.ext (funext fun i => by
    rcases i with a | b
    · exact a.elim0
    · exact b.elim0)⟩

/-- The paper's fibre `fib(A, tbar)`, inside `VF^n` (i.e. `VF^n × RV^0`). -/
def fibre {n m : ℕ} (A : Set (Tup M n m)) (t : Tup M 0 m) : Set (Tup M n 0) :=
  {x | concat x t ∈ A}

/-! ## 2. Open balls and open polydiscs

In the paper's value-group order (`iLe`), the closed ball of radius `t` around `a` is
`{x : t ≤ vv (x - a)}`; the open ball is `{x : t ≤ vv (x - a) ∧ ¬ vv (x - a) ≤ t}` (strict
inequality in a preorder), which is the encoding's `IsOpenBall`. -/

/-- The open ball `O(a, t)`. -/
def openBall (a t : M) : Set M :=
  {x | iVF x ∧ iLe t (iRv (iVFAdd x (iVFNeg a))) ∧ ¬ iLe (iRv (iVFAdd x (iVFNeg a))) t}

/-- `openBall a t` is an open ball in the sense of Definition 2.6 of the encoding. -/
theorem isOpenBall_openBall {a t : M} (ha : iVF a) (ht : iRV t) (hne : t ≠ iRVZero) :
    IsOpenBall (openBall a t) :=
  Or.inl ⟨a, t, ha, ht, hne, rfl⟩

/-- The open polydisc in `VF^n` with centre `c` and radii `r`. -/
def polydisc {n : ℕ} (c r : Fin n → M) : Set (Tup M n 0) :=
  {x | ∀ i, x (Sum.inl i) ∈ openBall (c i) (r i)}

/-- The same open polydisc placed in `VF^n × RV^m` at the `RV`-tuple `t`: the paper's
"`fib(A, tbar)` contains an open polydisc", in the ambient shape where the dimension lemmas
apply. -/
def polydiscAt {n m : ℕ} (c r : Fin n → M) (t : Tup M 0 m) : Set (Tup M n m) :=
  {x | (∀ i, x (Sum.inl i) ∈ openBall (c i) (r i)) ∧ (∀ j, x (Sum.inr j) = t (Sum.inr j))}

/-- `P ⊆ VF^n` is an open polydisc: a product of open balls with radii `≠ 0`
(`≠ ∞`, i.e. `≠ iRVZero` in the encoding, where `rv 0 = ∞` is the absorbing element). -/
def IsOpenPolydisc {n : ℕ} (P : Set (Tup M n 0)) : Prop :=
  ∃ c r : Fin n → M, (∀ i, iVF (c i)) ∧ (∀ i, iRV (r i) ∧ r i ≠ iRVZero) ∧ P = polydisc c r

/-- Some fibre of `A ⊆ VF^n × RV^m` contains an open polydisc — the conclusion of Lemma
`full:dim:open:poly`. -/
def HasOpenPolydiscInFibre {n m : ℕ} (A : Set (Tup M n m)) : Prop :=
  ∃ t : Tup M 0 m, ∃ P : Set (Tup M n 0), IsOpenPolydisc P ∧ P ⊆ fibre A t

theorem mem_polydisc_iff {n : ℕ} {c r : Fin n → M} {x : Tup M n 0} :
    x ∈ polydisc c r ↔ ∀ i, x (Sum.inl i) ∈ openBall (c i) (r i) :=
  Iff.rfl

theorem mem_polydiscAt_iff {n m : ℕ} {c r : Fin n → M} {t : Tup M 0 m} {x : Tup M n m} :
    x ∈ polydiscAt c r t ↔
      (∀ i, x (Sum.inl i) ∈ openBall (c i) (r i)) ∧ (∀ j, x (Sum.inr j) = t (Sum.inr j)) :=
  Iff.rfl

/-- The fibre shape and the ambient shape of "contains an open polydisc" agree: placing the
polydisc in `A` at the `RV`-tuple `t` is the same condition as its sitting in the fibre
`fib(A, tbar)`. -/
theorem polydisc_subset_fibre_iff {n m : ℕ} {c r : Fin n → M} {t : Tup M 0 m}
    {A : Set (Tup M n m)} : polydiscAt c r t ⊆ A ↔ polydisc c r ⊆ fibre A t := by
  constructor
  · intro h x hx
    rw [mem_polydisc_iff] at hx
    exact h ⟨hx, fun j => rfl⟩
  · intro h x hx
    rw [mem_polydiscAt_iff] at hx
    have hmem : vfPart x ∈ polydisc c r := by
      rw [mem_polydisc_iff]
      intro i
      rw [vfPart_apply]
      exact hx.1 i
    have hx' : concat (vfPart x) t ∈ A := h hmem
    rw [concat_vfPart x t hx.2] at hx'
    exact hx'

/-! ## 3. Finite sets have `VF`-dimension `0`

The paper's `RV^0` is the singleton `{∞}`, which in the encoding is the one-point tuple type
`Tup M 0 0`.  A finite `A` maps to it constantly; the graph is `⊤`, so the map is *definable*.
This is the one place where the definability constraint costs nothing: no substitution is needed.
(Contrast `hasDim_of_finFib` below, where it is exactly what fails.) -/

theorem dimVF_eq_zero_of_finite (S : SP M) {n m : ℕ} {A : Set (Tup M n m)} (hA : A.Finite) :
    dimVF S A = 0 := by
  haveI : Subsingleton (Tup M 0 0) := subsingleton_emptyTup (M := M)
  have h0 : HasDim S A 0 := by
    refine ⟨0, le_rfl, 0, fun _ => emptyTup, ?_, ?_⟩
    · refine ⟨⊤, wellSorted_top S.sortMap (Fin.append (fSort n m) (fSort 0 0)), ?_⟩
      intro x _ y
      rw [BoundedFormula.realize_top]
      exact ⟨fun _ => Subsingleton.elim _ _, fun _ => trivial⟩
    · intro y
      exact hA.subset (fun x hx => hx.1)
  exact le_antisymm ((dimVF_le_iff S A 0).2 h0) (Nat.zero_le _)

/-- A finite set has `VF`-dimension `0`, so not `1`: the paper's *"since `A` is infinite"*. -/
theorem dimVF_ne_one_of_finite (S : SP M) {n m : ℕ} {A : Set (Tup M n m)} (hA : A.Finite) :
    dimVF S A ≠ 1 := by
  rw [dimVF_eq_zero_of_finite S hA]
  exact Nat.zero_ne_one

/-! ## 4. Finite-to-one maps, and where `DefinableFun` composition is needed -/

/-- **Finite-to-one maps do not raise `dim_VF`**, combinatorial half: if `φ` maps `B` into `A` with
finite fibres and the composite of `φ` with a definable finite-to-one `G` on `A` is again
definable, then `HasDim S A k` transfers to `B`.  `hcomp` is exactly the missing
`DefinableFun`-composition (substitution) lemma — see the file header. -/
theorem hasDim_of_finFib (S : SP M) {n m n' m' : ℕ} {A : Set (Tup M n m)}
    {B : Set (Tup M n' m')} (φ : Tup M n' m' → Tup M n m) (hφ : ∀ b ∈ B, φ b ∈ A)
    (hfib : ∀ a : Tup M n m, {b : Tup M n' m' | b ∈ B ∧ φ b = a}.Finite)
    (hcomp : ∀ {k l : ℕ} (G : Tup M n m → Tup M k l), DefinableFun S A G →
      DefinableFun S B (fun b => G (φ b)))
    {k : ℕ} (h : HasDim S A k) : HasDim S B k := by
  obtain ⟨k', hk', l, G, hG, hfin⟩ := h
  refine ⟨k', hk', l, fun b => G (φ b), hcomp G hG, ?_⟩
  intro y
  have hsub : {b : Tup M n' m' | b ∈ B ∧ G (φ b) = y} ⊆
      ⋃ a ∈ {a : Tup M n m | a ∈ A ∧ G a = y}, {b : Tup M n' m' | b ∈ B ∧ φ b = a} := by
    intro b hb
    have h1 : φ b ∈ {a : Tup M n m | a ∈ A ∧ G a = y} := ⟨hφ b hb.1, hb.2⟩
    have h2 : b ∈ {b : Tup M n' m' | b ∈ B ∧ φ b = φ b} := ⟨hb.1, rfl⟩
    exact Set.mem_iUnion.2 ⟨φ b, Set.mem_iUnion.2 ⟨h1, h2⟩⟩
  exact Set.Finite.subset (Set.Finite.biUnion (hfin y) (fun a _ => hfib a)) hsub

/-- **`dim_VF` does not increase along a finite-to-one map** (same `hcomp` hypothesis). -/
theorem dimVF_le_of_finFib (S : SP M) {n m n' m' : ℕ} {A : Set (Tup M n m)}
    {B : Set (Tup M n' m')} (φ : Tup M n' m' → Tup M n m) (hφ : ∀ b ∈ B, φ b ∈ A)
    (hfib : ∀ a : Tup M n m, {b : Tup M n' m' | b ∈ B ∧ φ b = a}.Finite)
    (hcomp : ∀ {k l : ℕ} (G : Tup M n m → Tup M k l), DefinableFun S A G →
      DefinableFun S B (fun b => G (φ b))) :
    dimVF S B ≤ dimVF S A :=
  (dimVF_le_iff S B (dimVF S A)).2
    (hasDim_of_finFib S φ hφ hfib hcomp ((dimVF_le_iff S A (dimVF S A)).1 le_rfl))

/-- **`dim_VF(fib(A, tbar)) ≤ dim_VF(A)`** — *"the other direction is trivial"* in the paper's
`dim:VF:pullback` (`paper.tex:842`).  In this encoding it is not trivial: the fibre lives in
`VF^n × RV^0`, not inside `A`, so the comparison is a composition with `x ↦ (x, tbar)`, and
definability of the composite is the `hcomp` hypothesis.  The combinatorial half — the composite is
finite-to-one because `x ↦ (x, tbar)` is injective — is proved. -/
theorem dimVF_fibre_le (S : SP M) {n m : ℕ} (A : Set (Tup M n m)) (t : Tup M 0 m)
    (hcomp : ∀ {k l : ℕ} (G : Tup M n m → Tup M k l), DefinableFun S A G →
      DefinableFun S (fibre A t) (fun x => G (concat x t))) :
    dimVF S (fibre A t) ≤ dimVF S A :=
  dimVF_le_of_finFib S (fun x => concat x t) (fun _ hx => hx)
    (fun a => Subsingleton.finite (fun x hx y hy => concat_injective t (hx.2.trans hy.2.symm)))
    hcomp

/-! ## 5. Lemma `full:dim:open:poly`, "if" direction

Paper (`paper.tex:880`): *"`dim_VF(A) = n` if and only if there is a `tbar ∈ RV^m` such that
`fib(A, tbar)` contains an open polydisc."*  The paper's proof of the "if" direction: *"The `if`
direction is immediate by Lemma `VF:dim:tran:deg`."* — an open polydisc in `VF^n` has
`VF`-dimension `n` (`hPoly`), and `dim_VF` is monotone under inclusion (`Sec4Dim.dimVF_mono`). -/

/-- **`full:dim:open:poly`, "if" direction** (ambient shape): if `A ⊆ VF^n × RV^m` contains an open
polydisc with `n` coordinates, and a polydisc has `VF`-dimension `n` (paper Lemma
`VF:dim:tran:deg`), then `dim_VF A = n`. -/
theorem full_dim_open_poly_if (S : SP M) {n m : ℕ} {A : Set (Tup M n m)} {t : Tup M 0 m}
    {c r : Fin n → M} (hsub : polydiscAt c r t ⊆ A)
    (hPoly : n ≤ dimVF S (polydiscAt c r t)) :
    dimVF S A = n :=
  le_antisymm (dimVF_le_self S A) (hPoly.trans (dimVF_mono S hsub))

/-- **`full:dim:open:poly`, "if" direction, in the paper's fibre shape**: if the fibre of `A` over
`tbar` contains an open polydisc, then `dim_VF A = n`. -/
theorem full_dim_open_poly_if_fibre (S : SP M) {n m : ℕ} {A : Set (Tup M n m)} {t : Tup M 0 m}
    {c r : Fin n → M} (hsub : polydisc c r ⊆ fibre A t)
    (hPoly : n ≤ dimVF S (polydiscAt c r t)) :
    dimVF S A = n :=
  full_dim_open_poly_if S ((polydisc_subset_fibre_iff).2 hsub) hPoly

/-- **Paper Lemma `VF:dim:tran:deg` for an open polydisc** (`paper.tex:852`, `dim_VF(A) = td(A)`),
in the form the "if" direction of `full:dim:open:poly` uses: *an open polydisc of `VF^n` has
`VF`-dimension `n`*.  This is the one geometric input of that direction; the paper invokes it as
*"The `if` direction is immediate by Lemma `VF:dim:tran:deg`."*  Recorded as a `Prop` (used as a
hypothesis, never assumed globally). -/
def PolydiscDim (S : SP M) : Prop :=
  ∀ (n m : ℕ) (c r : Fin n → M) (t : Tup M 0 m), (∀ i, iVF (c i)) →
    (∀ i, iRV (r i) ∧ r i ≠ iRVZero) → dimVF S (polydiscAt c r t) = n

/-- **`full:dim:open:poly`, "if" direction, with the polydisc dimension as a single hypothesis.** -/
theorem full_dim_open_poly_if' (S : SP M) (hPoly : PolydiscDim S) {n m : ℕ}
    {A : Set (Tup M n m)} {t : Tup M 0 m} {c r : Fin n → M}
    (hc : ∀ i, iVF (c i)) (hr : ∀ i, iRV (r i) ∧ r i ≠ iRVZero)
    (hsub : polydiscAt c r t ⊆ A) :
    dimVF S A = n :=
  full_dim_open_poly_if S hsub (le_of_eq (hPoly n m c r t hc hr).symm)

/-! ## 6. Lemma `full:dim:open:poly`, "only if" direction at `n = 1`

Paper: *"For the ``only if'' direction, by compactness, it is enough to show the case
`A ⊆ VF^n`.  We do induction on `n`.  For the base case `n = 1`, since `A` is infinite, the lemma
simply follows from `C`-minimality."*

The dimension half is proved: `dim_VF A = 1` forces `A` infinite (`dimVF_ne_one_of_finite`).
The `C`-minimality half is the hypothesis `CMinimalDisc`: every infinite subset of `VF` contains an
open ball, i.e. `Milestone0/Encoding.lean`'s `IsCMinimalWS`/`IsCMinimalVFWS` (every definable subset
of `VF` is a finite Boolean combination of balls) after the ball combinatorics — the step that
needs the nesting/density of balls in a model of `ACVF`. -/

/-- **`C`-minimality in the form the base case of `full:dim:open:poly` uses**: every infinite subset
of `VF` (all that `C`-minimality must be applied to) contains an open disc. -/
def CMinimalDisc (M : Type*) [LRV.Structure M] : Prop :=
  ∀ A : Set (Tup M 1 0), A.Infinite →
    ∃ c r : Fin 1 → M, (∀ i, iVF (c i)) ∧ (∀ i, iRV (r i) ∧ r i ≠ iRVZero) ∧
      polydiscAt c r (emptyTup (M := M)) ⊆ A

/-- **`full:dim:open:poly` at `n = 1`, "only if" direction**: if `A ⊆ VF × RV^0` has
`VF`-dimension `1`, some fibre (here: `A` itself, over the empty `RV`-tuple) contains an open
polydisc. -/
theorem full_dim_open_poly_base (S : SP M) {A : Set (Tup M 1 0)}
    (hCM : CMinimalDisc M) (h : dimVF S A = 1) :
    ∃ (t : Tup M 0 0) (c r : Fin 1 → M), (∀ i, iVF (c i)) ∧
      (∀ i, iRV (r i) ∧ r i ≠ iRVZero) ∧ polydisc c r ⊆ fibre A t := by
  have hinf : A.Infinite := fun hfin => dimVF_ne_one_of_finite S hfin h
  obtain ⟨c, r, hc, hr, hsub⟩ := hCM A hinf
  exact ⟨emptyTup, c, r, hc, hr, (polydisc_subset_fibre_iff).1 hsub⟩

/-! ## 7. Corollary `VF:dim:mono`

Paper (`paper.tex:865`): *"If `f : A → P(VF^{n'} × RV^{m'})` is a definable function with finite
images then `dim_VF(A) ≥ dim_VF(⋃ f(A))`."*  The paper gets this from Lemma `VF:dim:tran:deg`
(`dim_VF = td`): each `b ∈ ⋃ f(A)` is algebraic over a single `a ∈ A`, and algebraic elements do
not raise the transcendental degree.  Both are hypotheses here: `hDimTd` is the paper's
`VF:dim:tran:deg`, `hTdImage` is the standard `td`-fact (not a paper lemma). -/

/-- **`VF:dim:mono`**: images of finite-image maps do not raise the `VF`-dimension. -/
theorem VF_dim_mono (S : SP M) (td : (p q : ℕ) → Set (Tup M p q) → ℕ)
    {n m n' m' : ℕ} {A : Set (Tup M n m)} {B : Set (Tup M n' m')}
    {f : Tup M n m → Set (Tup M n' m')} (hfin : ∀ a ∈ A, (f a).Finite) (hB : B = ⋃ a ∈ A, f a)
    (hDimTd : ∀ (p q : ℕ) (X : Set (Tup M p q)), dimVF S X = td p q X)
    (hTdImage : td n' m' B ≤ td n m A) :
    dimVF S B ≤ dimVF S A := by
  rw [hDimTd n' m' B, hDimTd n m A]
  exact hTdImage

/-! ## 8. Corollary `VF:dim:rv:polydisc`

Paper (`paper.tex:908`): *"Suppose that `A` contains an `rv`-polydisc of the form
`{(0, ..., 0)} × rv^{-1}(tbar) × {sbar}`, where `tbar ∈ (RV^{×})^k`.  Then `dim_VF(A) ≥ k`."*
Same monotonicity argument as §5, with the `RV`-side polydisc dimension as the hypothesis. -/

/-- The `rv`-polydisc `rv^{-1}(tbar) × {sbar}` inside `VF^k × RV^m`. -/
def rvPolydiscAt {k m : ℕ} (u : Fin k → M) (s : Tup M 0 m) : Set (Tup M k m) :=
  {x | (∀ i, iRv (x (Sum.inl i)) = u i) ∧ (∀ j, x (Sum.inr j) = s (Sum.inr j))}

/-- **`VF:dim:rv:polydisc`**: if `A` contains the `rv`-polydisc `rv^{-1}(tbar) × {sbar}` and that
polydisc has `VF`-dimension `k` (hypothesis `hRvPoly`, the `RV`-side counterpart of `hPoly`), then
`dim_VF A ≥ k`. -/
theorem dim_ge_of_contains_rvPolydisc (S : SP M) {k m : ℕ} {A : Set (Tup M k m)}
    {u : Fin k → M} {s : Tup M 0 m} (hsub : rvPolydiscAt u s ⊆ A)
    (hRvPoly : k ≤ dimVF S (rvPolydiscAt u s)) :
    k ≤ dimVF S A :=
  hRvPoly.trans (dimVF_mono S hsub)

/-! ## 9. The open statement, recorded

The paper's Lemma `full:dim:open:poly`, "only if" direction in general, as a `Prop` — assumed
nowhere.  This file proves the "if" direction (`full_dim_open_poly_if`) and the "only if" direction
at `n = 1` (`full_dim_open_poly_base`).  The general "only if" is the paper's induction on `n`,
whose step needs Lemma `dim:VF:pullback` (`paper.tex:840`) and `VF:dim:tran:deg` over `dcl(b̄)`;
that is where the proof stops. -/
def FullDimOpenPoly (M : Type*) [LRV.Structure M] : Prop :=
  ∀ (S : SP M) (n m : ℕ) (A : Set (Tup M n m)), dimVF S A = n → HasOpenPolydiscInFibre A

/-! ## 10. Axiom audit -/

#print axioms isOpenBall_openBall
#print axioms concat_injective
#print axioms subsingleton_emptyTup
#print axioms polydisc_subset_fibre_iff
#print axioms dimVF_eq_zero_of_finite
#print axioms dimVF_ne_one_of_finite
#print axioms hasDim_of_finFib
#print axioms dimVF_le_of_finFib
#print axioms dimVF_fibre_le
#print axioms full_dim_open_poly_if
#print axioms full_dim_open_poly_if'
#print axioms full_dim_open_poly_if_fibre
#print axioms full_dim_open_poly_base
#print axioms VF_dim_mono
#print axioms dim_ge_of_contains_rvPolydisc

end Sec4

end SpecialTransformations.Milestone0
