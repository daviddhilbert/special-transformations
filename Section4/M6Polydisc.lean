/-
**§4 `full:dim:open:poly` at `n = 1` for arbitrary `RV`-arity, coordinate maps, and the correct
statement of the "only if" direction** — swarm `smw1qqem3` m6 (direction d5: the polydisc /
full-dimension cluster of `paper.tex` 868 and 885).

This file is the polydisc layer of §4 made **self-contained** (it imports only `Sec4Dim`, whose olean
is in the build directory; `QE/Sec4Polydisc.lean` has none, so the layer is reproduced verbatim here
with its proofs — credit for §1–§10 is the earlier swarm `smw1jgnht` m2) and then extended by §11–§17.

## What is new here

* **§11 `coordinate maps are definable, unconditionally.***  `definableFun_coordMap`: for any
  `VF`/`RV`-sort-preserving `σ`, the map `x ↦ (x_{σ i})_i` is `S`-definable on *every* set.  The graph
  is a conjunction `⋀ᵢ yᵢ = x_{σ i}` of equations between variables (`coordForm`, in the style of
  `Sec4Dim.idForm`), so — unlike `DefinableFun`-composition — it needs no substitution at all.
* **§12 `dimVF_le_of_projLast_fibre_finite`**: finite fibres of the projection
  `VF^{n+1} × RV^m → VF^n × RV^m` (the coordinate projection that drops the last `VF`-coordinate)
  force `dim_VF A ≤ n`.  Unconditional.
* **§13 `dimVF_eq_zero_of_fibre_finite`**: for `A ⊆ VF × RV^m`, finite `RV`-fibres force
  `dim_VF A = 0`.  The fibre transfer is a *bijection* (`x ↦ vfPart x`, with `concat_vfPart`), not a
  substitution — this is where `QE/Sec4Polydisc.lean`'s `dimVF_fibre_le` needed its `hcomp` and this
  does not.
* **§14 `full_dim_open_poly_base_any`**: the base case `n = 1` of Lemma `full:dim:open:poly` for
  **arbitrary** `m` (the earlier file has only `m = 0`).  The paper reaches `A ⊆ VF` at `n = 1` only
  *"by compactness"*; here `C`-minimality is applied fibre by fibre and §13 finishes, so the
  compactness step disappears at `n = 1`.  Sole hypothesis: `CMinimalDisc` (= `C`-minimality).
* **§15 `dimVF_le_of_last_coord_const`**: a constant `VF`-coordinate does not contribute to
  `dim_VF`; unconditional.
* **§16, §21** Corollary `VF:dim:rv:polydisc` (`paper.tex:885`), including **the paper's own shape**
  `{0}^k × rv^{-1}(t̄) × {s̄}` (`rvShaped c u s ⊆ VF^{k+k} × RV^m`): the polydisc has `dim_VF ≤ k`
  unconditionally (§18 applied to the injection that forgets the `k` constant coordinates), so the
  paper's `≥ k` is an **equality**; the lower bound itself is the paper's `VF:dim:tran:deg` input and
  is a named hypothesis, not restated.
* **§18** `dimVF_le_of_coordMap_injOn`: any definable coordinate injection into `VF^k × RV^l` bounds
  `dim_VF` by `k` — the general form of §12 and §15.
* **§19** `exists_infinite_fibre_of_dimVF`: a set of `VF`-dimension `n+1` has an infinite fibre over
  the projection to its first `n` `VF`-coordinates (the positive content of §12, unconditional).
* **§20** `full_dim_open_poly_iff_one`: at `n = 1` the paper's lemma in **both** directions, for every
  `RV`-arity, from `C`-minimality plus `DiscDim` (= the `n = 1` case of `VF:dim:tran:deg`, and
  `discDim_of_polydiscDim` shows it is the `n = 1` instance of the `PolydiscDim` hypothesis that the
  `n`-dimensional "if" direction already carries).
* **§17 — a refutation.**  The recorded `def FullDimOpenPoly` (the "only if" of
  `full:dim:open:poly` for all `n`) is **false**: at `n = 0` take `A = ∅ ⊆ VF^0 × RV^0`, which has
  `dim_VF A = 0 = n`, but the `0`-dimensional open polydisc is the *nonempty* set `{∞}`, so no fibre
  of `∅` contains one.  `not_fullDimOpenPoly` proves this, and `FullDimOpenPoly'` records the
  corrected statement with the proviso `1 ≤ n`.  `FullDimOpenPoly` should not be quoted as the
  paper's lemma.

Everything below is about the paper's own notion (`paper.tex:807`, `Sec4Dim.dimVF`), it uses no
`axiom`, no `sorry`, no `native_decide`, and every theorem is checked by `#print axioms` at the end.

Build (the olean for `Sec4Dim` is in `.scratch2/sec3/`):
`cp M6Polydisc.lean .scratch2/sec3/ && cd .scratch2/sec3 && LEAN_PATH=$PWD:$LEAN_PATH lean M6Polydisc.lean`
-/

import Sec4Dim

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
  have : Subsingleton (Tup M 0 0) := subsingleton_emptyTup (M := M)
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


/-! ## 11. Coordinate maps, and their definability without any substitution

The graphs of the paper's elementary maps — "keep a block of coordinates", "drop one", "insert the
constant `0`" — are conjunctions `⋀ᵢ yᵢ = x_{σ i}` of equations between *variables*, so their
definability is a direct construction in the style of `Sec4Dim.idForm` and needs none of the
`DefinableFun`-composition machinery.  Everything in this section is unconditional.
-/

/-- The **coordinate map** induced by `σ : Idx k l → Idx n m`: read off the coordinates selected by
`σ`.  Its graph is `⋀ᵢ yᵢ = x_{σ i}`. -/
def coordMap {n m k l : ℕ} (σ : Idx k l → Idx n m) (hσ : ∀ j, idxSort k l j = idxSort n m (σ j))
    (x : Tup M n m) : Tup M k l :=
  ⟨fun i => x (σ i), fun i => by rw [hσ i]; exact x.2 (σ i)⟩

@[simp] theorem coordMap_apply {n m k l : ℕ} (σ : Idx k l → Idx n m)
    (hσ : ∀ j, idxSort k l j = idxSort n m (σ j)) (x : Tup M n m)
    (i : Idx k l) : coordMap σ hσ x i = x (σ i) := rfl

/-- `σ` read through the flattening `Fin k ⊕ Fin l ≃ Fin (k+l)`. -/
def flatσ {n m k l : ℕ} (σ : Idx k l → Idx n m) : Fin (k + l) → Fin (n + m) :=
  fun i => finSumFinEquiv (σ (finSumFinEquiv.symm i))

theorem fSort_flatσ {n m k l : ℕ} (σ : Idx k l → Idx n m) (i : Fin (k + l)) :
    fSort n m (flatσ σ i) = idxSort n m (σ (finSumFinEquiv.symm i)) := by
  simp only [flatσ, fSort, Equiv.symm_apply_apply]

/-- **The graph formula of the coordinate map `σ`**: `⋀ᵢ yᵢ = x_{σ i}`, the `x`-block first. -/
def coordForm (α : Type) (n m k l : ℕ) (σ : Idx k l → Idx n m) :
    LRV.BoundedFormula α ((n + m) + (k + l)) :=
  conjFin (fun i : Fin (k + l) =>
    pEqG (Term.var (Sum.inr (Fin.natAdd (n + m) i)))
      (Term.var (Sum.inr (Fin.castAdd (k + l) (flatσ σ i)))))

/-- `coordForm σ` is well sorted as soon as `σ` preserves the `VF`/`RV` tag of every coordinate. -/
theorem wellSorted_coordForm {α : Type} (sα : α → SortTag) {n m k l : ℕ}
    {σ : Idx k l → Idx n m} (hσ : ∀ j, idxSort k l j = idxSort n m (σ j)) :
    WellSorted sα (Fin.append (fSort n m) (fSort k l)) (coordForm α n m k l σ) := by
  refine wellSorted_conjFin (fun i => ?_)
  refine wellSorted_pEqG (s := fSort k l i) sα (Fin.append (fSort n m) (fSort k l)) ?_ ?_
  · rw [tmSort_var_inr, Fin.append_right]
  · rw [tmSort_var_inr, Fin.append_left, fSort_flatσ]
    exact (congrArg some (hσ (finSumFinEquiv.symm i))).symm

/-- The realization of `coordForm σ` is the graph of `coordMap σ`. -/
theorem realize_coordForm {α : Type} (v : α → M) {n m k l : ℕ} (σ : Idx k l → Idx n m)
    (hσ : ∀ j, idxSort k l j = idxSort n m (σ j)) (x : Tup M n m) (y : Tup M k l) :
    (coordForm α n m k l σ).Realize v (pairAssign x y) ↔ coordMap σ hσ x = y := by
  rw [coordForm, realize_conjFin]
  constructor
  · intro h
    refine Subtype.ext (funext fun t => ?_)
    have h' := h (finSumFinEquiv t)
    simp only [pEqG, BoundedFormula.realize_bdEqual, Term.realize_var, Sum.elim_inr,
      pairAssign_left, pairAssign_right, flatσ, Equiv.symm_apply_apply] at h'
    exact h'.symm
  · intro h i
    subst h
    simp only [pEqG, BoundedFormula.realize_bdEqual, Term.realize_var, Sum.elim_inr,
      pairAssign_left, pairAssign_right, flatσ, Equiv.symm_apply_apply, coordMap_apply]

/-- **Coordinate maps are `S`-definable on every set**, unconditionally: the graph formula is a
conjunction of variable equations, so no substitution is involved. -/
theorem definableFun_coordMap (S : SP M) {n m k l : ℕ} (σ : Idx k l → Idx n m)
    (hσ : ∀ j, idxSort k l j = idxSort n m (σ j)) (A : Set (Tup M n m)) :
    DefinableFun S A (coordMap σ hσ) :=
  ⟨coordForm (Fin S.n ⊕ Fin S.m) n m k l σ, wellSorted_coordForm S.sortMap hσ,
    fun x _ y => realize_coordForm S.toFun σ hσ x y⟩

/-! ## 12. The projection that drops the last `VF`-coordinate

`VF^{n+1} × RV^m → VF^n × RV^m`.  Finite fibres of this projection bound `dim_VF` by `n`; that is the
content of `dimVF_le_of_projLast_fibre_finite` below, and it is what the paper's base case
*"since `A` is infinite, the lemma simply follows from `C`-minimality"* of `full:dim:open:poly`
uses. -/

/-- Keep the first `n` `VF`-coordinates and all `RV`-coordinates; drop the last `VF`-coordinate. -/
def idxProjLast (n m : ℕ) : Idx n m → Idx (n + 1) m
  | Sum.inl i => Sum.inl (Fin.castSucc i)
  | Sum.inr j => Sum.inr j

theorem idxSort_idxProjLast (n m : ℕ) (j : Idx n m) :
    idxSort n m j = idxSort (n + 1) m (idxProjLast n m j) := by
  rcases j with i | j <;> rfl

/-- The projection `VF^{n+1} × RV^m → VF^n × RV^m` dropping the last `VF`-coordinate. -/
def projLast {n m : ℕ} (x : Tup M (n + 1) m) : Tup M n m :=
  coordMap (idxProjLast n m) (idxSort_idxProjLast n m) x

@[simp] theorem projLast_inl {n m : ℕ} (x : Tup M (n + 1) m) (i : Fin n) :
    projLast x (Sum.inl i) = x (Sum.inl (Fin.castSucc i)) := rfl

@[simp] theorem projLast_inr {n m : ℕ} (x : Tup M (n + 1) m) (j : Fin m) :
    projLast x (Sum.inr j) = x (Sum.inr j) := rfl

/-- Two tuples with the same projection agree on every coordinate except the last `VF`-one. -/
theorem projLast_eq_iff {n m : ℕ} {x : Tup M (n + 1) m} {y : Tup M n m} :
    projLast x = y ↔
      (∀ i, x (Sum.inl (Fin.castSucc i)) = y (Sum.inl i)) ∧
        (∀ j, x (Sum.inr j) = y (Sum.inr j)) := by
  constructor
  · intro h
    exact ⟨fun i => by rw [← projLast_inl, h], fun j => by rw [← projLast_inr, h]⟩
  · rintro ⟨h1, h2⟩
    refine Subtype.ext (funext fun t => ?_)
    rcases t with i | j
    · rw [projLast_inl, h1 i]
    · rw [projLast_inr, h2 j]

/-- **Finite fibres over the projection `VF^{n+1} × RV^m → VF^n × RV^m` bound `dim_VF` by `n`.**

The projection is a definable coordinate map (`definableFun_coordMap`), and an injection is
finite-to-one, so `HasDim S A n` holds outright — no substitution, no hypothesis. -/
theorem dimVF_le_of_projLast_fibre_finite (S : SP M) {n m : ℕ} {A : Set (Tup M (n + 1) m)}
    (h : ∀ y : Tup M n m, {x : Tup M (n + 1) m | x ∈ A ∧ projLast x = y}.Finite) :
    dimVF S A ≤ n :=
  (dimVF_le_iff S A n).2
    ⟨n, le_rfl, m, projLast,
      definableFun_coordMap S (idxProjLast n m) (idxSort_idxProjLast n m) A, h⟩

/-! ## 13. Finite `RV`-fibres force `dim_VF A = 0` (for `A ⊆ VF × RV^m`)

This is the case `n = 0` of §12, with the fibre finiteness transferred from the paper's `fib(A, t̄)`
(inside `VF^n`, i.e. `VF^n × RV^0`) to the ambient shape `VF^n × RV^m`.  The transfer is a
*bijection* rather than a substitution: `x ↦ vfPart x` is injective on `{x : RV-part = t̄}`, with
`x = concat (vfPart x) t̄` (`concat_vfPart`). -/

/-- `concat z (emptyTup) = z`: with no `RV`-coordinates, assembling is the identity. -/
theorem concat_emptyTup {n : ℕ} (z : Tup M n 0) : concat z (emptyTup (M := M)) = z := by
  refine Subtype.ext (funext fun t => ?_)
  rcases t with a | b
  · rfl
  · exact b.elim0

/-- With no `RV`-coordinates the ambient and fibre shapes of an open polydisc agree. -/
theorem polydiscAt_emptyTup_subset_iff {n : ℕ} {c r : Fin n → M} {B : Set (Tup M n 0)} :
    polydiscAt c r (emptyTup (M := M)) ⊆ B ↔ polydisc c r ⊆ B := by
  constructor
  · intro h x hx
    exact h ⟨hx, fun j => j.elim0⟩
  · intro h x hx
    exact h ((mem_polydiscAt_iff (M := M)).1 hx).1

/-- **If every `RV`-fibre of `A ⊆ VF × RV^m` is finite then `dim_VF A = 0`.** -/
theorem dimVF_eq_zero_of_fibre_finite (S : SP M) {m : ℕ} {A : Set (Tup M 1 m)}
    (h : ∀ t : Tup M 0 m, (fibre A t).Finite) : dimVF S A = 0 := by
  have hle : dimVF S A ≤ 0 := by
    refine dimVF_le_of_projLast_fibre_finite S (fun y => ?_)
    have hinj : Set.InjOn vfPart {x : Tup M (0 + 1) m | x ∈ A ∧ projLast x = y} := by
      intro x hx x' hx' hvv
      have h1 : concat (vfPart x) y = x :=
        concat_vfPart x y (fun j => ((projLast_eq_iff (x := x) (y := y)).1 hx.2).2 j)
      have h2 : concat (vfPart x') y = x' :=
        concat_vfPart x' y (fun j => ((projLast_eq_iff (x := x') (y := y)).1 hx'.2).2 j)
      rw [← h1, ← h2, hvv]
    have himg : vfPart '' {x : Tup M (0 + 1) m | x ∈ A ∧ projLast x = y} ⊆ fibre A y := by
      rintro z ⟨x, hx, rfl⟩
      have h1 : concat (vfPart x) y = x :=
        concat_vfPart x y (fun j => ((projLast_eq_iff (x := x) (y := y)).1 hx.2).2 j)
      show concat (vfPart x) y ∈ A
      rw [h1]
      exact hx.1
    exact Set.Finite.of_finite_image ((h y).subset himg) hinj
  exact le_antisymm hle (Nat.zero_le _)

/-! ## 14. `full:dim:open:poly`, "only if" direction at `n = 1` for **arbitrary** `RV`-arity

`QE/Sec4Polydisc.lean` proves the base case `n = 1` of Lemma `full:dim:open:poly` only for
`A ⊆ VF` (`m = 0`).  The paper's base case is `A ⊆ VF` too, but only after *"by compactness, it is
enough to show the case `A ⊆ VF^n`"* — the point of the theorem below is that at `n = 1` that
compactness step is not needed: `C`-minimality applies to each `RV`-fibre separately, and §13 turns
"all fibres finite" into `dim_VF A ≤ 0`.

*"For the base case `n = 1`, since `A` is infinite, the lemma simply follows from `C`-minimality"*
(`paper.tex:890`). -/

/-- **`full:dim:open:poly`, "only if" at `n = 1`, for every `RV`-arity `m`**: if `A ⊆ VF × RV^m` has
`VF`-dimension `1`, then some `RV`-fibre of `A` contains an open disc.  The only input is
`C`-minimality (`CMinimalDisc`). -/
theorem full_dim_open_poly_base_any (S : SP M) {m : ℕ} {A : Set (Tup M 1 m)}
    (hCM : CMinimalDisc M) (h : dimVF S A = 1) : HasOpenPolydiscInFibre A := by
  by_contra hno
  have hfib : ∀ t : Tup M 0 m, (fibre A t).Finite := by
    intro t
    by_contra hinf
    obtain ⟨c, r, hc, hr, hsub⟩ := hCM (fibre A t) hinf
    exact hno ⟨t, polydisc c r, ⟨c, r, hc, hr, rfl⟩,
      (polydiscAt_emptyTup_subset_iff (M := M) (B := fibre A t)).1 hsub⟩
  have h0 : dimVF S A = 0 := dimVF_eq_zero_of_fibre_finite S hfib
  omega

/-- The `m = 0` statement of `QE/Sec4Polydisc.lean` (`full_dim_open_poly_base`) **is the case
`m = 0` of `full_dim_open_poly_base_any`**: the general base case is a strict strengthening. -/
theorem full_dim_open_poly_base_of_any (S : SP M) {A : Set (Tup M 1 0)}
    (hCM : CMinimalDisc M) (h : dimVF S A = 1) :
    ∃ (t : Tup M 0 0) (c r : Fin 1 → M), (∀ i, iVF (c i)) ∧
      (∀ i, iRV (r i) ∧ r i ≠ iRVZero) ∧ polydisc c r ⊆ fibre A t := by
  obtain ⟨t, P, ⟨c, r, hc, hr, rfl⟩, hsub⟩ := full_dim_open_poly_base_any S hCM h
  exact ⟨t, c, r, hc, hr, hsub⟩

/-! ## 15. A constant `VF`-coordinate does not contribute to `dim_VF`

§12 with the extra observation that "drop the last coordinate" is *injective* on a set where that
coordinate is constant.  The paper uses the corresponding fact silently when it writes the
`rv`-polydisc `{(0, …, 0)} × rv^{-1}(t̄) × {s̄}` in `VF^k × RV^m` (Cor. `VF:dim:rv:polydisc`). -/

/-- **If the last `VF`-coordinate is constant on `A ⊆ VF^{n+1} × RV^m` then `dim_VF A ≤ n`.** -/
theorem dimVF_le_of_last_coord_const (S : SP M) {n m : ℕ} {A : Set (Tup M (n + 1) m)} {c : M}
    (hA : ∀ x ∈ A, x (Sum.inl (Fin.last n)) = c) : dimVF S A ≤ n := by
  refine dimVF_le_of_projLast_fibre_finite S (fun y => ?_)
  have hsub : {x : Tup M (n + 1) m | x ∈ A ∧ projLast x = y}.Subsingleton := by
    intro x hx x' hx'
    refine Subtype.ext (funext fun t => ?_)
    rcases t with i | j
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [← projLast_inl x i', ← projLast_inl x' i', hx.2, hx'.2]
      · rw [hA x hx.1, hA x' hx'.1]
    · rw [← projLast_inr x j, ← projLast_inr x' j, hx.2, hx'.2]
  exact hsub.finite

/-! ## 16. Corollary `VF:dim:rv:polydisc` (`paper.tex:885`): the `RV`-polydisc has `VF`-dimension
exactly `k` once the paper's lower bound is granted

The paper: *"Suppose that `A` contains an `rv`-polydisc of the form
`{(0, …, 0)} × rv^{-1}(t̄) × {s̄}`, where `t̄ ∈ (RV^{×})^k`.  Then `dim_VF(A) ≥ k`."*

The *lower* bound `k ≤ dim_VF(rv^{-1}(t̄) × {s̄})` is the paper's `VF:dim:tran:deg` input
(`dim_VF = td`, with `k` algebraically independent coordinates), and the file carries it as a named
hypothesis rather than restating it.  The *upper* bound is free — the identity is a definable
injection into `VF^k × RV^m` — so the corollary's bound is **exact**, not merely a bound.  This is
the sharp form of `dim_ge_of_contains_rvPolydisc` above. -/

/-- The `VF`-dimension of an `rv`-polydisc is at most the number of its `VF`-coordinates. -/
theorem dimVF_rvPolydiscAt_le (S : SP M) {k m : ℕ} (u : Fin k → M) (s : Tup M 0 m) :
    dimVF S (rvPolydiscAt u s) ≤ k :=
  dimVF_le_self S _

/-- **Corollary `VF:dim:rv:polydisc`, sharp form**: the `rv`-polydisc has `VF`-dimension exactly `k`
as soon as the paper's lower bound (`VF:dim:tran:deg` for `k` independent `rv`-coordinates) is
granted.  Combined with `dim_ge_of_contains_rvPolydisc`, a set containing an `rv`-polydisc then has
`dim_VF ≥ k` and, if it *is* the polycdisc, `dim_VF = k`. -/
theorem dimVF_rvPolydiscAt_eq (S : SP M) {k m : ℕ} (u : Fin k → M) (s : Tup M 0 m)
    (hRvPoly : k ≤ dimVF S (rvPolydiscAt u s)) :
    dimVF S (rvPolydiscAt u s) = k :=
  le_antisymm (dimVF_rvPolydiscAt_le S u s) hRvPoly

/-! ## 17. The recorded `FullDimOpenPoly` is **false** at `n = 0`

`FullDimOpenPoly M` (the paper's Lemma `full:dim:open:poly`, "only if", recorded as a `Prop` in
`QE/Sec4Polydisc.lean` and assumed nowhere) quantifies over all `n : ℕ`, `n = 0` included.  At
`n = 0` it is *refutable*: `A = ∅ ⊆ VF^0 × RV^0` has `dim_VF A = 0 = n`, but no fibre of `∅` contains
an open polydisc — the `0`-dimensional polydisc `VF^0` is the nonempty set `{∞}`.

So the paper's lemma needs the proviso `n ≥ 1` (equivalently `A ≠ ∅`, since `dim_VF ∅ = 0`).  This is
why `FullDimOpenPoly'` below carries `1 ≤ n`; `FullDimOpenPoly` itself should not be quoted as the
paper's statement. -/

/-- The `0`-dimensional open polydisc `VF^0` is nonempty: its only point is `emptyTup`. -/
theorem mem_polydisc_zero (c r : Fin 0 → M) : emptyTup (M := M) ∈ polydisc c r :=
  fun i => i.elim0

/-- **Lemma `full:dim:open:poly` is false at `n = 0`**: `∅ ⊆ VF^0 × RV^0` has `VF`-dimension `0`,
yet no fibre of it contains an open polydisc. -/
theorem not_fullDimOpenPoly (S : SP M) :
    ¬ FullDimOpenPoly M := by
  intro h
  have hdim : dimVF S (∅ : Set (Tup M 0 0)) = 0 :=
    dimVF_eq_zero_of_finite S (A := (∅ : Set (Tup M 0 0))) Set.finite_empty
  obtain ⟨t, P, ⟨c, r, hc, hr, hP⟩, hsub⟩ := h S 0 0 ∅ hdim
  have hmem : emptyTup (M := M) ∈ P := by
    rw [hP]
    exact mem_polydisc_zero c r
  exact hsub hmem

/-- `concat x t = t` when there are no `VF`-coordinates: assembling a point with `t` gives `t`. -/
theorem concat_zero {m : ℕ} (x : Tup M 0 0) (t : Tup M 0 m) : concat x t = t := by
  refine Subtype.ext (funext fun i => ?_)
  rcases i with a | b
  · exact a.elim0
  · rfl

/-- **At `n = 0` every nonempty `A ⊆ RV^m` contains an open polydisc** (the `0`-dimensional one,
`VF^0 = {∞}`): its fibre over any `t ∈ A` is everything, because `concat x t = t`.  Together with
`not_fullDimOpenPoly` this pins the failure of the recorded `FullDimOpenPoly` down exactly: it is the
pair `n = 0`, `A = ∅`, and nothing else refutable at `n = 0`. -/
theorem hasOpenPolydiscInFibre_of_nonempty {m : ℕ} {A : Set (Tup M 0 m)} (hA : A.Nonempty) :
    HasOpenPolydiscInFibre A := by
  obtain ⟨s, hs⟩ := hA
  refine ⟨s, polydisc (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0),
    ⟨fun i : Fin 0 => i.elim0, fun i : Fin 0 => i.elim0, fun i => i.elim0,
      fun i => i.elim0, rfl⟩, ?_⟩
  intro x _
  show concat x s ∈ A
  rw [concat_zero]
  exact hs

/-- **The corrected form of the paper's Lemma `full:dim:open:poly` "only if"**, with the proviso
`1 ≤ n` that the `n = 0` refutation `not_fullDimOpenPoly` forces.  Assumed nowhere; recorded so that
the open part of the lemma is stated in a form that is not already refutable. -/
def FullDimOpenPoly' (M : Type*) [LRV.Structure M] : Prop :=
  ∀ (S : SP M) (n m : ℕ) (A : Set (Tup M n m)), 1 ≤ n → dimVF S A = n → HasOpenPolydiscInFibre A

/-! ## 18. Definable coordinate injections bound `dim_VF` — the general form of §§12 and 15

Both `dimVF_le_of_projLast_fibre_finite` and `dimVF_le_of_last_coord_const` are instances of one
principle: *a definable injection into `VF^k × RV^l` bounds `dim_VF` by `k`* (the easy direction of
`dim:RV:fibers`), and a coordinate map is always definable (§11). -/

/-- **A definable coordinate injection into `VF^k × RV^l` bounds `dim_VF` by `k`.** -/
theorem dimVF_le_of_coordMap_injOn (S : SP M) {n m k l : ℕ} (σ : Idx k l → Idx n m)
    (hσ : ∀ j, idxSort k l j = idxSort n m (σ j)) {A : Set (Tup M n m)}
    (hinj : InjOn A (coordMap σ hσ)) : dimVF S A ≤ k :=
  dimVF_le_of_injOn S ⟨k, le_rfl, l, coordMap σ hσ, definableFun_coordMap S σ hσ A, hinj⟩

/-! ## 19. A set of dimension `n + 1` has an infinite fibre over its first `n` `VF`-coordinates

This is the *positive* content of §12: the paper's Lemma `full:dim:open:poly` starts from
*"there is a `t̄` such that `fib(A, t̄)` contains an open polydisc"*, and at `n = 1` §14 upgrades
"infinite fibre" to "contains an open disc" by `C`-minimality.  For every `n`, the infinite fibre is
unconditional. -/

/-- **A set of `VF`-dimension `n + 1` has an infinite fibre over the projection to its first `n`
`VF`-coordinates** (the contrapositive of `dimVF_le_of_projLast_fibre_finite`). -/
theorem exists_infinite_fibre_of_dimVF (S : SP M) {n m : ℕ} {A : Set (Tup M (n + 1) m)}
    (h : dimVF S A = n + 1) :
    ∃ y : Tup M n m, {x : Tup M (n + 1) m | x ∈ A ∧ projLast x = y}.Infinite := by
  by_contra hno
  push Not at hno
  have hle : dimVF S A ≤ n := dimVF_le_of_projLast_fibre_finite S hno
  omega

/-! ## 20. Lemma `full:dim:open:poly` at `n = 1`, **both** directions

The "only if" is unconditional given `C`-minimality (§14).  The "if" is the paper's *"immediate by
Lemma `VF:dim:tran:deg`"*, whose `n = 1` instance is `DiscDim` below: an open disc has
`VF`-dimension `1`.  So at `n = 1` the paper's lemma is a theorem modulo exactly that one geometric
input — the same input (`VF:dim:tran:deg` for a polydisc) as the `n`-dimensional "if" direction. -/

/-- `VF:dim:tran:deg` for the open disc: *an open disc in `VF × RV^m` has `VF`-dimension `1`*.  Used
as a hypothesis, never assumed globally; `discDim_of_polydiscDim` shows it is the `n = 1` case of the
`PolydiscDim` hypothesis `QE/Sec4Polydisc.lean` already carries. -/
def DiscDim (S : SP M) : Prop :=
  ∀ (m : ℕ) (c r : Fin 1 → M) (t : Tup M 0 m), (∀ i, iVF (c i)) →
    (∀ i, iRV (r i) ∧ r i ≠ iRVZero) → dimVF S (polydiscAt c r t) = 1

/-- **Lemma `full:dim:open:poly` (`paper.tex:868`) at `n = 1`**, for every `RV`-arity:
`dim_VF(A) = 1` **iff** some `RV`-fibre of `A` contains an open disc. -/
theorem full_dim_open_poly_iff_one (S : SP M) {m : ℕ} {A : Set (Tup M 1 m)}
    (hCM : CMinimalDisc M) (hDisc : DiscDim S) :
    dimVF S A = 1 ↔ HasOpenPolydiscInFibre A := by
  constructor
  · exact full_dim_open_poly_base_any S hCM
  · rintro ⟨t, P, ⟨c, r, hc, hr, rfl⟩, hsub⟩
    exact full_dim_open_poly_if_fibre S hsub (le_of_eq (hDisc m c r t hc hr).symm)

/-! ## 21. Corollary `VF:dim:rv:polydisc` in the paper's own shape

The paper (`paper.tex:885`): *"Suppose that `A` contains an `rv`-polydisc of the form
`{(0, …, 0)} × rv^{-1}(t̄) × {s̄}`, where `t̄ ∈ (RV^{×})^k`.  Then `dim_VF(A) ≥ k`."*  The shape is
written out below in `VF^{k+k} × RV^m`: `k` constant `VF`-coordinates (the paper's zeros — any
constant `c` works, and the bound only uses constancy), then `k` `VF`-coordinates with prescribed
`rv`, then the fixed `RV`-part.

`dimVF_rvShaped_le` says the `rv`-polydisc itself has `dim_VF ≤ k` — *unconditionally*, by §18: the
coordinate injection that forgets the `k` constant coordinates is definable and injective on the
shape.  So the paper's `≥ k` is an **equality** for the polydisc
(`dimVF_rvShaped_eq`), and for a set containing it (`dim_ge_of_contains_rvShaped`, which carries the
paper's `VF:dim:tran:deg` lower bound as a named hypothesis, not as its own conclusion). -/

/-- The `rv`-polydisc `{c}^k × rv^{-1}(u) × {s}` of `VF^{k} × VF^{k} × RV^m`: `k` constant
`VF`-coordinates, `k` `VF`-coordinates with prescribed `rv` (the paper's `rv^{-1}(t̄)`), and a fixed
`RV`-tuple.  The paper's shape is the case `c = 0`. -/
def rvShaped {k m : ℕ} (c : M) (u : Fin k → M) (s : Tup M 0 m) : Set (Tup M (k + k) m) :=
  {x | (∀ i : Fin k, x (Sum.inl (Fin.castAdd k i)) = c) ∧
    (∀ i : Fin k, iRv (x (Sum.inl (Fin.natAdd k i))) = u i) ∧
    (∀ j : Fin m, x (Sum.inr j) = s (Sum.inr j))}

/-- Read off the second `VF`-block (the `rv^{-1}(t̄)` one) and the `RV`-part. -/
def idxRvShape (k m : ℕ) : Idx k m → Idx (k + k) m
  | Sum.inl i => Sum.inl (Fin.natAdd k i)
  | Sum.inr j => Sum.inr j

@[simp] theorem idxRvShape_inl (k m : ℕ) (i : Fin k) :
    idxRvShape k m (Sum.inl i) = Sum.inl (Fin.natAdd k i) := rfl

@[simp] theorem idxRvShape_inr (k m : ℕ) (j : Fin m) :
    idxRvShape k m (Sum.inr j) = Sum.inr j := rfl

theorem idxSort_idxRvShape (k m : ℕ) (j : Idx k m) :
    idxSort k m j = idxSort (k + k) m (idxRvShape k m j) := by
  rcases j with i | j <;> rfl

/-- **The `rv`-polydisc injects into `VF^k × RV^m`**: forgetting the `k` constant coordinates is
injective, since those are determined. -/
theorem rvShaped_injOn {k m : ℕ} (c : M) (u : Fin k → M) (s : Tup M 0 m) :
    InjOn (rvShaped c u s) (coordMap (idxRvShape k m) (idxSort_idxRvShape k m)) := by
  intro x hx x' hx' h
  refine Subtype.ext (funext fun t => ?_)
  rcases t with i | j
  · refine Fin.addCases (m := k) (n := k) (motive := fun i => x (Sum.inl i) = x' (Sum.inl i))
      ?_ ?_ i
    · intro i'
      rw [hx.1 i', hx'.1 i']
    · intro i'
      have h2 := congrArg (fun z => z (Sum.inl i')) h
      simpa only [coordMap_apply, idxRvShape_inl] using h2
  · have h2 := congrArg (fun z => z (Sum.inr j)) h
    simpa only [coordMap_apply, idxRvShape_inr] using h2

/-- **Corollary `VF:dim:rv:polydisc`, upper half, in the paper's shape**: the `rv`-polydisc has
`VF`-dimension at most `k`.  Unconditional. -/
theorem dimVF_rvShaped_le (S : SP M) {k m : ℕ} (c : M) (u : Fin k → M) (s : Tup M 0 m) :
    dimVF S (rvShaped c u s) ≤ k :=
  dimVF_le_of_coordMap_injOn S (idxRvShape k m) (idxSort_idxRvShape k m) (rvShaped_injOn c u s)

/-- **Corollary `VF:dim:rv:polydisc`** (`paper.tex:885`) in the paper's shape: if `A` contains the
`rv`-polydisc and the polydisc has `VF`-dimension at least `k` (hypothesis `hTd` — the paper's
`VF:dim:tran:deg`, the only unproved input of the corollary), then `dim_VF A ≥ k`. -/
theorem dim_ge_of_contains_rvShaped (S : SP M) {k m : ℕ} {A : Set (Tup M (k + k) m)} {c : M}
    {u : Fin k → M} {s : Tup M 0 m} (hsub : rvShaped c u s ⊆ A)
    (hTd : k ≤ dimVF S (rvShaped c u s)) : k ≤ dimVF S A :=
  hTd.trans (dimVF_mono S hsub)

/-- **The paper's bound is exact**: the `rv`-polydisc has `VF`-dimension exactly `k` as soon as the
paper's lower bound (`VF:dim:tran:deg`) is granted. -/
theorem dimVF_rvShaped_eq (S : SP M) {k m : ℕ} (c : M) (u : Fin k → M) (s : Tup M 0 m)
    (hTd : k ≤ dimVF S (rvShaped c u s)) : dimVF S (rvShaped c u s) = k :=
  le_antisymm (dimVF_rvShaped_le S c u s) hTd

/-! ## 18. Consistency of the named inputs

`DiscDim` (an open disc is `1`-dimensional) is the `n = 1` instance of `PolydiscDim` — the paper's
`VF:dim:tran:deg` for a polydisc that `QE/Sec4Polydisc.lean` already isolates.  So the `n = 1` form
of `full:dim:open:poly` below needs exactly the input the `n`-dimensional "if" direction already
uses, and nothing weaker. -/

theorem discDim_of_polydiscDim (S : SP M) (h : PolydiscDim S) : DiscDim S :=
  fun m c r t hc hr => h 1 m c r t hc hr

/-! ## 19. Axiom audit -/

#print axioms concat_emptyTup
#print axioms polydiscAt_emptyTup_subset_iff
#print axioms full_dim_open_poly_base
#print axioms full_dim_open_poly_if'
#print axioms dim_ge_of_contains_rvPolydisc
#print axioms coordMap_apply
#print axioms wellSorted_coordForm
#print axioms realize_coordForm
#print axioms definableFun_coordMap
#print axioms projLast_eq_iff
#print axioms dimVF_le_of_projLast_fibre_finite
#print axioms dimVF_le_of_coordMap_injOn
#print axioms dimVF_eq_zero_of_fibre_finite
#print axioms full_dim_open_poly_base_any
#print axioms full_dim_open_poly_base_of_any
#print axioms dimVF_le_of_last_coord_const
#print axioms exists_infinite_fibre_of_dimVF
#print axioms full_dim_open_poly_iff_one
#print axioms dimVF_rvPolydiscAt_le
#print axioms dimVF_rvPolydiscAt_eq
#print axioms idxSort_idxRvShape
#print axioms rvShaped_injOn
#print axioms dimVF_rvShaped_le
#print axioms dim_ge_of_contains_rvShaped
#print axioms dimVF_rvShaped_eq
#print axioms mem_polydisc_zero
#print axioms concat_zero
#print axioms hasOpenPolydiscInFibre_of_nonempty
#print axioms not_fullDimOpenPoly
#print axioms discDim_of_polydiscDim

end Sec4

end SpecialTransformations.Milestone0
