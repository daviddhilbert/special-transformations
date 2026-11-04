/-
# Yin, "Special transformations in algebraically closed valued fields": §8,
  Lemma `fun:almost:cont` (`paper.tex:1864`) and Lemma `fun:almost:loc:con` (`paper.tex:1883`)

Part 1 of 2 (part 2 is `Sec8Top.lean`, which imports this file): the vocabulary, the paper's own
statements, and the **dimension drop** that is the heart of `fun:almost:cont`.

## The paper's sentences

`fun:almost:cont` (`paper.tex:1864`): *"Let `f : VF^n → VF^m` be a definable function.  Then there is a
definable closed subset `A ⊆ VF^n` with `dim_VF(A) < n` such that `f ↾ (VF^n ∖ A)` is continuous with
respect to the valuation topology."*  (Stated and proved in `Sec8Top.lean` as `fun_almost_cont`.)

`fun:almost:loc:con` (`paper.tex:1883`): *"Let `f : VF^n → P(RV^m)` be a definable function.  Then `f`
is locally constant almost everywhere."*

Both are quoted verbatim in the docstrings of the corresponding definitions and theorems.

## What is where

* `goBox` / `goPoly` — the open polydiscs `go(ā, γ)`; `AdmRadius` is the radius condition;
* `BallFacts` — the elementary facts about the ball vocabulary (a `Prop`: `LRV.Structure M` alone fixes
  nothing about `iLe`/`iRv`);
* `GoContAt`, `GoContAtPaper`, `GoContOn`, `IsClosedVF` — continuity and closedness in the valuation
  topology, in the paper's `ε`-δ language; `goContAt_iff_paper` shows the two forms agree;
* `DiscSet f` — the paper's set of discontinuous points, with `mem_discSet_iff` proving the paper's own
  description of it (`paper.tex:1866--1868`);
* `AlmostEverywhere` (`paper.tex:1806`), `LocallyConstantAt` / `LocallyConstantOn` (`paper.tex:1879`),
  `Fibre`, `pairTup` — the vocabulary of `fun:almost:loc:con`;
* `FullDimOpenPoly` (Lemma `full:dim:open:poly`), `DimUnion` (§4 subadditivity), `RegAway` (Lemma
  `VF:fun:reg:away`) — the dimension input of `fun:almost:cont`;
* `dimVF_inter_eq`, `dimVF_discSet_lt` — **proved**: the dimension drop `dim_VF(DiscSet f) < n`, by the
  paper's argument (the docstring of `dimVF_discSet_lt` walks through it);
* `goContAt_congr`, `goContAt_of_locally_const` — continuity is local, so a function constant on a
  polydisc is continuous at its centre (the paper's step, `paper.tex:1928`);
* `fun_almost_loc_con_closed` — the closed/local form of `fun:almost:loc:con`, from the paper's
  statement `FunAlmostLocCon` and the closure step `ClosureHyp`;
* `definable_empty`, `hasDim_empty`, `dimVF_empty`, `discSet_const`, `fun_almost_loc_con_const` —
  consistency: `dim_VF(∅) = 0`, a constant function has no discontinuous points, and the statement of
  `fun:almost:loc:con` holds for a function that is locally constant everywhere.

`Sec8Top.lean` builds the valuation topology on `VF^n` as a Mathlib `TopologicalSpace` and proves
`fun_almost_cont` with its conclusion literally `IsClosed A ∧ ContinuousOn f Aᶜ`.

## How to check

    LEAN_PATH=<repo>/.scratch2/sec3:$PWD:$LEAN_PATH lean -o Sec8AlmostCont.olean Sec8AlmostCont.lean
    LEAN_PATH=<repo>/.scratch2/sec3:$PWD:$LEAN_PATH lean Sec8Top.lean

No `sorry`, no `axiom`, no `native_decide`; every reported theorem's `#print axioms` is a subset of
{`propext`, `Classical.choice`, `Quot.sound`}.
-/
import Sec4Dim

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 (SP)

namespace SpecialTransformations.Milestone0
open LRV

namespace Sec8

open Sec4Dim

variable {M : Type*} [LRV.Structure M]

/-! ## §A. The `VF`-coordinates of `VF^n`, and the paper's `rv` of a difference -/

/-- The `i`-th `VF`-coordinate of a point of `VF^n` (i.e. of a `Tup M n 0`). -/
def coord {n : ℕ} (x : Tup M n 0) (i : Fin n) : M := x (Sum.inl i)

/-- Every coordinate of a point of `VF^n` lies in the `VF` sort. -/
theorem coord_sorted {n : ℕ} (x : Tup M n 0) (i : Fin n) : iVF (coord x i) :=
  x.2 (Sum.inl i)

/-- `rv(y_i - x_i)`: the `i`-th coordinate of the `rv`-difference of two points of `VF^n`.  This is
the quantity the paper writes `vv(b̄ - ā)`, coordinatewise. -/
def rvSub {n : ℕ} (y x : Tup M n 0) (i : Fin n) : M :=
  iRv (iVFAdd (coord y i) (iVFNeg (coord x i)))

/-- **`y` lies in `go(x, r̄)`**: `rᵢ < rv(yᵢ - xᵢ)` strictly, in every coordinate.  The strict
`<` of the paper's value-group order is `r ≤ rv(y - x) ∧ ¬ rv(y - x) ≤ r`, exactly as in
`LRV.IsOpenBall` of `Milestone0/Encoding.lean` (the order is a preorder, so the second conjunct
cannot be dropped). -/
def GoMem {n : ℕ} (y x : Tup M n 0) (r : Fin n → M) : Prop :=
  ∀ i, iLe (r i) (rvSub y x i) ∧ ¬ iLe (rvSub y x i) (r i)

/-- **`go(ā, r̄)`**, the open polydisc with one radius per coordinate: the paper's `go(ā, γ)` when
all the radii are the same (`goPoly`), and the base of the product of the valuation topologies on
the `n` coordinates. -/
def goBox {n : ℕ} (x : Tup M n 0) (r : Fin n → M) : Set (Tup M n 0) :=
  {y | GoMem y x r}

/-- **`go(ā, γ)`**, the paper's open polydisc: one radius `γ` for all coordinates. -/
def goPoly {n : ℕ} (x : Tup M n 0) (γ : M) : Set (Tup M n 0) :=
  goBox x (fun _ => γ)

/-- A radius family is **admissible**: all entries are `RV`-elements other than `0 = ∞`, i.e. lie
in the paper's `Γ` (`Milestone0/DECISION.md`: `rv 0 = ∞` is the one absorbing element). -/
def AdmRadius {n : ℕ} (r : Fin n → M) : Prop :=
  (∀ i, iRV (r i)) ∧ ∀ i, r i ≠ iRVZero

/-! ## §B. The elementary facts about the ball vocabulary

`L_RV` has `+`, `-` on the `VF` sort, `rv : VF → RV` and the preorder `≤` on `RV`.  The §4 layer
assumes nothing about the interpretation (`QE/Sec4Dim.lean` is stated for an arbitrary
`LRV.Structure M`), so the few order-theoretic facts that the paper uses about balls without comment
are collected here as one named `Prop`.  All four conjuncts are consequences of the axioms of `ACVF`
(`Milestone0/Encoding.lean` Part 2) in a model of the paper's theory; they are **not** consequences
of `LRV.Structure M` alone, hence they are a hypothesis, not a lemma. -/
def BallFacts (M : Type*) [LRV.Structure M] : Prop :=
  -- the order is transitive (it is a preorder on `RV`)
  (∀ a b c : M, iLe a b → iLe b c → iLe a c) ∧
  -- `rv 0 = ∞` is the top: a point lies in every open polydisc around it
  (∀ {n : ℕ} (x : Tup M n 0) (r : Fin n → M), AdmRadius r → x ∈ goBox x r) ∧
  -- two open polydiscs around a point contain one: `rv` of a product is at least each factor
  (∀ {n : ℕ} (x : Tup M n 0) (r s : Fin n → M), AdmRadius r → AdmRadius s →
    ∃ t : Fin n → M, AdmRadius t ∧ goBox x t ⊆ goBox x r ∩ goBox x s) ∧
  -- finite sets of admissible radii have an admissible upper bound
  (∀ {n : ℕ} (x : Tup M n 0) (r : Fin n → M), AdmRadius r →
    ∃ γ : M, iRV γ ∧ γ ≠ iRVZero ∧ ∀ i, iLe (r i) γ)

/-- Transitivity of the paper's order on `RV`. -/
theorem iLe_trans (hbf : BallFacts M) : ∀ a b c : M, iLe a b → iLe b c → iLe a c := hbf.1

/-- A point lies in every open polydisc around it (`rv 0 = ∞` is the top). -/
theorem mem_goBox_self (hbf : BallFacts M) {n : ℕ} (x : Tup M n 0) {r : Fin n → M}
    (hr : AdmRadius r) : x ∈ goBox x r :=
  hbf.2.1 x r hr

/-- Open polydiscs shrink when the radii grow (in the paper's order). -/
theorem goBox_mono (hbf : BallFacts M) {n : ℕ} {x : Tup M n 0} {r s : Fin n → M}
    (h : ∀ i, iLe (r i) (s i)) : goBox x s ⊆ goBox x r := by
  intro y hy i
  obtain ⟨h1, h2⟩ := hy i
  exact ⟨hbf.1 _ _ _ (h i) h1, fun hc => h2 (hbf.1 _ _ _ hc (h i))⟩

/-- The single-radius polydiscs shrink when the radius grows. -/
theorem goPoly_mono (hbf : BallFacts M) {n : ℕ} {x : Tup M n 0} {γ γ' : M}
    (h : iLe γ' γ) : goPoly x γ ⊆ goPoly x γ' :=
  goBox_mono hbf (fun _ => h)

/-- Two open polydiscs around a point contain an open polydisc around that point. -/
theorem goBox_inter (hbf : BallFacts M) {n : ℕ} (x : Tup M n 0) {r s : Fin n → M}
    (hr : AdmRadius r) (hs : AdmRadius s) :
    ∃ t : Fin n → M, AdmRadius t ∧ goBox x t ⊆ goBox x r ∩ goBox x s :=
  hbf.2.2.1 x r s hr hs

/-- An open polydisc `go(x, r̄)` with coordinatewise radii contains a single-radius polydisc
`go(x, γ)` around the same point.  This is the fact that the paper's `go(ā, γ)` presentation and
the product topology's coordinatewise presentation agree. -/
theorem goPoly_subset_goBox (hbf : BallFacts M) {n : ℕ} (x : Tup M n 0) {r : Fin n → M}
    (hr : AdmRadius r) :
    ∃ γ : M, iRV γ ∧ γ ≠ iRVZero ∧ goPoly x γ ⊆ goBox x r := by
  obtain ⟨γ, h1, h2, h3⟩ := hbf.2.2.2 x r hr
  exact ⟨γ, h1, h2, fun y hy i => goPoly_mono hbf (h3 i) hy i⟩

/-! ## §C. Continuity at a point in the valuation topology

Two renderings: `GoContAt` with one radius per coordinate (the product topology's `ε`-`δ`), and
`GoContAtPaper` with the paper's single `γ` for the target and single `δ` for the source.  They agree
(`goContAt_iff_paper`), which is what makes "continuous with respect to the valuation topology" mean
what the paper means. -/

/-- **`f` is continuous at `x`** in the valuation topology: for every open polydisc `go(f(x), r̄)`
around the value there is an open polydisc `go(x, s̄)` around `x` that `f` maps into it. -/
def GoContAt {n m : ℕ} (f : Tup M n 0 → Tup M m 0) (x : Tup M n 0) : Prop :=
  ∀ r : Fin m → M, AdmRadius r →
    ∃ s : Fin n → M, AdmRadius s ∧ ∀ y : Tup M n 0, y ∈ goBox x s → f y ∈ goBox (f x) r

/-- **`f` is continuous at `x`**, in the paper's own `go(ā, γ)`-language: for every `γ` there is `δ`
such that `f` maps `go(x, δ)` into `go(f(x), γ)`. -/
def GoContAtPaper {n m : ℕ} (f : Tup M n 0 → Tup M m 0) (x : Tup M n 0) : Prop :=
  ∀ γ : M, iRV γ → γ ≠ iRVZero →
    ∃ δ : M, iRV δ ∧ δ ≠ iRVZero ∧
      ∀ y : Tup M n 0, y ∈ goPoly x δ → f y ∈ goPoly (f x) γ

/-- **The two forms of continuity at a point agree.**  (`⇐` is immediate: a single-radius polydisc is
a polydisc with equal coordinate radii.  `⇒` is where `BallFacts` is used, twice: to refine the
coordinatewise polydisc `go(f(x), r̄)` to a single-radius one, and to dominate the coordinate
radii by one admissible `γ`.) -/
theorem goContAt_iff_paper (hbf : BallFacts M) {n m : ℕ} {f : Tup M n 0 → Tup M m 0}
    {x : Tup M n 0} : GoContAt f x ↔ GoContAtPaper f x := by
  constructor
  · -- box form ⟹ the paper's form
    intro hc γ hγ hγ0
    obtain ⟨s, hs, hfs⟩ := hc (fun _ => γ) ⟨fun _ => hγ, fun _ => hγ0⟩
    obtain ⟨δ, hδ1, hδ2, hsub⟩ := goPoly_subset_goBox hbf x hs
    exact ⟨δ, hδ1, hδ2, fun y hy => hfs y (hsub hy)⟩
  · -- the paper's form ⟹ box form
    intro hc r hr
    obtain ⟨γ, hγ1, hγ0, hdom⟩ := hbf.2.2.2 (f x) r hr
    obtain ⟨δ, hδ1, hδ2, hfd⟩ := hc γ hγ1 hγ0
    refine ⟨fun _ => δ, ⟨fun _ => hδ1, fun _ => hδ2⟩, fun y hy => ?_⟩
    exact fun i => goPoly_mono hbf (hdom i) (hfd y hy) i

/-- The `ε`-`δ` form of continuity on a set: `f` is continuous at `x` *relative to* `A`. -/
def GoContAtWithin {n m : ℕ} (f : Tup M n 0 → Tup M m 0) (A : Set (Tup M n 0))
    (x : Tup M n 0) : Prop :=
  ∀ r : Fin m → M, AdmRadius r →
    ∃ s : Fin n → M, AdmRadius s ∧
      ∀ y : Tup M n 0, y ∈ A → y ∈ goBox x s → f y ∈ goBox (f x) r

/-- **`f` is continuous on `A`** in the valuation topology. -/
def GoContOn {n m : ℕ} (f : Tup M n 0 → Tup M m 0) (A : Set (Tup M n 0)) : Prop :=
  ∀ x ∈ A, GoContAtWithin f A x

/-- Continuity at a point implies continuity there relative to any set containing the point. -/
theorem goContAtWithin_of_goContAt {n m : ℕ} {f : Tup M n 0 → Tup M m 0}
    {A : Set (Tup M n 0)} {x : Tup M n 0} (h : GoContAt f x) : GoContAtWithin f A x := by
  intro r hr
  obtain ⟨s, hs, hfs⟩ := h r hr
  exact ⟨s, hs, fun y _ hy => hfs y hy⟩

/-- Continuity on a set follows from continuity at every point of it. -/
theorem goContOn_of_forall {n m : ℕ} {f : Tup M n 0 → Tup M m 0} {A : Set (Tup M n 0)}
    (h : ∀ x, GoContAt f x) : GoContOn f A :=
  fun x _ => goContAtWithin_of_goContAt (h x)

/-- Continuity on a set restricts to a smaller set. -/
theorem GoContOn.mono {n m : ℕ} {f : Tup M n 0 → Tup M m 0} {A B : Set (Tup M n 0)}
    (h : GoContOn f A) (hBA : B ⊆ A) : GoContOn f B := by
  intro x hx r hr
  obtain ⟨s, hs, hfs⟩ := h x (hBA hx) r hr
  exact ⟨s, hs, fun y hyA hy => hfs y (hBA hyA) hy⟩

/-! ## §D. The set of discontinuous points, and the paper's description of it -/

/-- The paper's set `A` of *discontinuous points* of `f`, in the paper's own words: `ā ∈ A` iff there
is a `γ ∈ Γ` such that `f⁻¹(go(f(ā), γ))` fails to contain any open polydisc around `ā`
(`paper.tex:1866--1868`).  `mem_discSet_iff` proves that this is the same as "`f` is not continuous
at `ā`". -/
def DiscSet {n m : ℕ} (f : Tup M n 0 → Tup M m 0) : Set (Tup M n 0) :=
  {x | ¬ GoContAtPaper f x}

/-- **The paper's description of `A`** (`paper.tex:1866--1868`): `ā` is a point of discontinuity if and
only if there is a radius `γ` such that `f⁻¹(go(f(ā), γ))` contains no open polydisc around `ā`. -/
theorem mem_discSet_iff {n m : ℕ} (f : Tup M n 0 → Tup M m 0) (x : Tup M n 0) :
    x ∈ DiscSet f ↔ ∃ γ : M, iRV γ ∧ γ ≠ iRVZero ∧
      ∀ δ : M, iRV δ → δ ≠ iRVZero →
        ∃ y : Tup M n 0, y ∈ goPoly x δ ∧ f y ∉ goPoly (f x) γ := by
  unfold DiscSet GoContAtPaper
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    push Not at h
    exact h
  · intro h
    push Not
    exact h

/-- The discontinuity set in the box form of continuity: the two forms agree, given `BallFacts`. -/
theorem mem_discSet_box_iff (hbf : BallFacts M) {n m : ℕ} (f : Tup M n 0 → Tup M m 0)
    (x : Tup M n 0) : x ∈ DiscSet f ↔ ¬ GoContAt f x := by
  show ¬ GoContAtPaper f x ↔ ¬ GoContAt f x
  rw [goContAt_iff_paper hbf]

/-- **The paper's step** (`paper.tex:1876`: *"So it is enough to show that `dim_VF(Ā) < n`"*): once
the set of discontinuous points is contained in `A`, the function is continuous on `VF^n ∖ A`.
(The paper takes `A` to be the topological closure of the discontinuity set and uses that the
discontinuity set is contained in its closure; only the inclusion is used here.) -/
theorem goContOn_compl_of_discSet_subset (hbf : BallFacts M) {n m : ℕ}
    {f : Tup M n 0 → Tup M m 0} {A : Set (Tup M n 0)} (h : DiscSet f ⊆ A) :
    GoContOn f Aᶜ := by
  intro x hx
  refine goContAtWithin_of_goContAt ?_
  rw [goContAt_iff_paper hbf]
  by_contra hcon
  exact hx (h (show x ∈ DiscSet f from hcon))

/-! ## §E. Closedness in the valuation topology -/

/-- **`A` is closed** in the valuation topology, in the paper's `go`-language: every point outside
`A` has an open polydisc around it that misses `A`.  (For the valuation topology this is equivalent
to `IsClosed`; see the file header on why no `TopologicalSpace` instance is built.) -/
def IsClosedVF {n : ℕ} (A : Set (Tup M n 0)) : Prop :=
  ∀ x : Tup M n 0, x ∉ A →
    ∃ s : Fin n → M, AdmRadius s ∧ ∀ y : Tup M n 0, y ∈ goBox x s → y ∉ A

/-- The complement of a closed set is open in the valuation topology: every point of it has an open
polydisc around it inside the complement. -/
theorem IsClosedVF.compl_open {n : ℕ} {A : Set (Tup M n 0)} (h : IsClosedVF A) :
    ∀ x ∈ Aᶜ, ∃ s : Fin n → M, AdmRadius s ∧ goBox x s ⊆ Aᶜ := by
  intro x hx
  obtain ⟨s, hs, hsub⟩ := h x hx
  exact ⟨s, hs, fun y hy => hsub y hy⟩

/-- From closedness and a polydisc `go(x, r̄)` at a point `x ∉ A` we get a polydisc
`go(x, t̄) ⊆ go(x, r̄) ∩ Aᶜ`. -/
theorem exists_goBox_subset_compl_inter (hbf : BallFacts M) {n : ℕ} {A : Set (Tup M n 0)}
    (hcl : IsClosedVF A) {x : Tup M n 0} (hx : x ∉ A) {r : Fin n → M} (hr : AdmRadius r) :
    ∃ t : Fin n → M, AdmRadius t ∧ goBox x t ⊆ Aᶜ ∩ goBox x r := by
  obtain ⟨s, hs, hsA⟩ := hcl x hx
  obtain ⟨t, ht, hsub⟩ := goBox_inter hbf x hs hr
  refine ⟨t, ht, fun y hy => ⟨?_, (hsub hy).2⟩⟩
  exact hsA y (hsub hy).1

/-! ## §F. "Almost everywhere" (`paper.tex:1806`) -/

/-- **Almost everywhere** (`paper.tex:1806`, verbatim): *"A property holds almost everywhere on `A`
or for almost every element in `A` if there is a definable subset `B ⊆ A` with `dim_VF(B) < n` such
that the property holds with respect to `A ∖ B`"* — here for `A = VF^n`, so `n = dim_VF(A)`, and the
property is a predicate on `VF^n`. -/
def AlmostEverywhere (S : SP M) {n : ℕ} (N : ℕ) (P : Tup M n 0 → Prop) : Prop :=
  ∃ B : Set (Tup M n 0), Definable S B ∧ dimVF S B < N ∧ ∀ x : Tup M n 0, x ∉ B → P x

/-! ## §G. The dimension input of `fun:almost:cont` -/

/-- **Lemma `full:dim:open:poly`** (`paper.tex:868`), verbatim: *"`dim_VF(A) = n` if and only if there
is a `t̄ ∈ RV^m` such that `fib(A, t̄)` contains an open polydisc."*  Recorded here for `m = 0`
(`A ⊆ VF^n`) and in the direction the proof of `fun:almost:cont` uses — the "only if" direction: a
definable `A ⊆ VF^n` of `VF`-dimension exactly `n` contains an open polydisc.  (The "if" direction is
`full_dim_open_poly_if` of `QE/Sec4Polydisc.lean`.) -/
def FullDimOpenPoly (S : SP M) : Prop :=
  ∀ {n : ℕ} (A : Set (Tup M n 0)), dimVF S A = n →
    ∃ x : Tup M n 0, ∃ r : Fin n → M, AdmRadius r ∧ goBox x r ⊆ A

/-- **`dim_VF` is subadditive for finite unions**: `dim_VF(A ∪ B) ≤ max(dim_VF(A), dim_VF(B))`.  A §4
dimension fact the paper uses without comment; `QE/Sec4Dim.lean` has monotonicity (`dimVF_mono`) but
not subadditivity, so it is carried as an explicit hypothesis. -/
def DimUnion (S : SP M) : Prop :=
  ∀ {n m : ℕ} (A B : Set (Tup M n m)), dimVF S (A ∪ B) ≤ max (dimVF S A) (dimVF S B)

/-- **Lemma `VF:fun:reg:away`** (`paper.tex:1819`), verbatim: *"Let `f : VF^n × VF^k → VF^m` be a
definable function.  Then there are a definable subset `A ⊆ VF^n × VF^k` over `VF^k` and a positive
rational number `k` such that: (1) `dim_VF(VF^n ∖ fib(A, b̄)) < n` for all `b̄ ∈ VF^k`; (2) for every
`x̄ = (ā, b̄) ∈ A` there are `x̄`-definable `ε, δ ∈ Γ` such that for any `ā' ∈ go(ā, δ)`,
`vv(f(ā', b̄) − f(ā, b̄)) ≥ ε + k vv(ā' − ā)`."*

Stated here for `k = 0` (`f : VF^n → VF^m`) and in the **form of its conclusion that the proof of
`fun:almost:cont` uses**, the paper's arithmetic (`ε + k δ > γ`, `paper.tex:1872`) being absorbed into
the choice of the radius: on a set `A` whose complement has smaller `VF`-dimension, for every target
radius `γ` and every polydisc `go(x, r̄)` there is a smaller polydisc `go(x, s̄) ⊆ go(x, r̄)` such that
`f` takes every *other* point of it outside `go(f(x), γ)`.  The paper obtains this from (2) by
*enlarging* `δ`, which shrinks `go(x, δ)` and keeps (2) by monotonicity, until `ε + k δ > γ` (`k > 0`
and `Γ` unbounded above).  The value-group arithmetic `ε + k vv` is not a term of the encoding — `Γ`
is a definable quotient of `RV`, not a sort (`Milestone0/DECISION.md`) — so that step cannot be
delegated to Lean here. -/
def RegAway (S : SP M) {n m : ℕ} (f : Tup M n 0 → Tup M m 0) : Prop :=
  ∃ A : Set (Tup M n 0), Definable S A ∧ dimVF S Aᶜ < n ∧
    ∀ (γ : M), iRV γ → γ ≠ iRVZero → ∀ x : Tup M n 0, x ∈ A →
      ∀ r : Fin n → M, AdmRadius r →
        ∃ s : Fin n → M, AdmRadius s ∧ (∀ i, iLe (r i) (s i)) ∧
          ∀ y : Tup M n 0, y ∈ goBox x s → y ≠ x → f y ∈ goPoly (f x) γ

/-- If `dim_VF(A) = k` and `dim_VF(Bᶜ) < k` then `dim_VF(A ∩ B) = k`: cutting `A` by a set whose
complement has smaller dimension cannot lower the dimension.  (The paper uses this when passing from
`A` to the `A' ⊆ A` of Lemma `VF:fun:reg:away`: *"Since `dim_VF(A') = n`…"*, `paper.tex:1871`.) -/
theorem dimVF_inter_eq (S : SP M) (hdimu : DimUnion S) {n m : ℕ}
    {A B : Set (Tup M n m)} {k : ℕ} (hA : dimVF S A = k) (hB : dimVF S Bᶜ < k) :
    dimVF S (A ∩ B) = k := by
  refine le_antisymm ?_ ?_
  · rw [← hA]
    exact dimVF_mono S Set.inter_subset_left
  · by_contra hcon
    have hlt : dimVF S (A ∩ B) < k := lt_of_not_ge hcon
    have hsub : A ⊆ (A ∩ B) ∪ Bᶜ := by
      intro x hx
      by_cases hxB : x ∈ B
      · exact Or.inl ⟨hx, hxB⟩
      · exact Or.inr hxB
    have hle : dimVF S A ≤ max (dimVF S (A ∩ B)) (dimVF S Bᶜ) :=
      le_trans (dimVF_mono S hsub) (hdimu (A ∩ B) Bᶜ)
    rw [hA] at hle
    have hmax : max (dimVF S (A ∩ B)) (dimVF S Bᶜ) < k := max_lt hlt hB
    exact absurd (lt_of_le_of_lt hle hmax) (lt_irrefl k)

/-- **The dimension statement behind `fun:almost:cont`** (`paper.tex:1866--1876`): the set of
discontinuous points of a definable `f : VF^n → VF^m` has `VF`-dimension `< n`.

This is the paper's argument: suppose `dim_VF(A) = n` for the discontinuous set `A`; let `A' ⊆ A` be the
definable set of Lemma `VF:fun:reg:away` (`RegAway`), so `dim_VF(A') = n` by `dimVF_inter_eq`; by Lemma
`full:dim:open:poly` (`FullDimOpenPoly`) `A'` contains an open polydisc; take a point `ā` of it — since
`ā` is discontinuous there is `γ` with `f⁻¹(go(f(ā), γ))` containing no open polydisc around `ā` — and
apply `VF:fun:reg:away` at `ā` with target `γ` to get an open polydisc `go(ā, s̄)` inside that inverse
image, a contradiction. -/
theorem dimVF_discSet_lt (S : SP M) {n m : ℕ} (f : Tup M n 0 → Tup M m 0)
    (hbf : BallFacts M) (hdimu : DimUnion S) (hfdop : FullDimOpenPoly S)
    (hreg : RegAway S f) (hD : Definable S (DiscSet f)) :
    dimVF S (DiscSet f) < n := by
  by_contra hcon
  have hge : n ≤ dimVF S (DiscSet f) := Nat.le_of_not_lt hcon
  have hdim : dimVF S (DiscSet f) = n := le_antisymm (dimVF_le_self S _) hge
  obtain ⟨A, hAdef, hAdim, hAreg⟩ := hreg
  have hinter : dimVF S (DiscSet f ∩ A) = n := dimVF_inter_eq S hdimu hdim hAdim
  obtain ⟨x, r, hr, hsub⟩ := hfdop (DiscSet f ∩ A) hinter
  have hx : x ∈ goBox x r := mem_goBox_self hbf x hr
  have hxD : x ∈ DiscSet f := (hsub hx).1
  have hxA : x ∈ A := (hsub hx).2
  obtain ⟨γ, hγ, hγ0, hfail⟩ := (mem_discSet_iff f x).mp hxD
  obtain ⟨s, hs, -, hgrowth⟩ := hAreg γ hγ hγ0 x hxA r hr
  obtain ⟨γ', hγ'1, hγ'0, hγ'sub⟩ := goPoly_subset_goBox hbf x hs
  obtain ⟨y, hy, hfy⟩ := hfail γ' hγ'1 hγ'0
  rcases eq_or_ne y x with heq | hne
  · rw [heq] at hfy
    exact hfy (mem_goBox_self hbf (f x) ⟨fun _ => hγ, fun _ => hγ0⟩)
  · exact hfy (hgrowth y (hγ'sub hy) hne)

/-! ## §H. Lemma `fun:almost:loc:con` (set-valued definable functions)

The paper's `f : VF^n → P(RV^m)` is a definable *set-valued* function, i.e. a definable relation
`D ⊆ VF^n × RV^m` read as `ā ↦ {b̄ : (ā, b̄) ∈ D}`. -/

/-- A point of `VF^n` and a point of `RV^m` read as a point of `VF^n × RV^m`. -/
def pairTup {n m : ℕ} (x : Tup M n 0) (y : Tup M 0 m) : Tup M n m where
  val := fun i =>
    match i with
    | Sum.inl j => x (Sum.inl j)
    | Sum.inr j => y (Sum.inr j)
  property := by
    intro i
    match i with
    | Sum.inl j => exact x.2 (Sum.inl j)
    | Sum.inr j => exact y.2 (Sum.inr j)

/-- The value `f(ā) ⊆ RV^m` of the set-valued function whose graph is `D`. -/
def Fibre {n m : ℕ} (D : Set (Tup M n m)) (x : Tup M n 0) : Set (Tup M 0 m) :=
  {y | pairTup x y ∈ D}

/-- **Locally constant at `ā`** (`paper.tex:1879`, verbatim): *"A function `f : VF^n → P(RV^m)` is
locally constant at `ā` if there is an open subset `U_ā ⊆ VF^n` containing `ā` such that
`f ↾ U_ā` is constant."*  The open set is an open polydisc `go(ā, r̄)`. -/
def LocallyConstantAt {n m : ℕ} (D : Set (Tup M n m)) (x : Tup M n 0) : Prop :=
  ∃ r : Fin n → M, AdmRadius r ∧ ∀ y : Tup M n 0, y ∈ goBox x r → Fibre D y = Fibre D x

/-- **Locally constant on `A`** (`paper.tex:1879--1881`, verbatim): *"If `f` is locally constant at
every point in an open subset `A` then `f` is locally constant on `A`."* -/
def LocallyConstantOn {n m : ℕ} (D : Set (Tup M n m)) (A : Set (Tup M n 0)) : Prop :=
  ∀ x ∈ A, ∃ r : Fin n → M, AdmRadius r ∧ goBox x r ⊆ A ∧
    ∀ y : Tup M n 0, y ∈ goBox x r → Fibre D y = Fibre D x

/-- **The closure step of the paper's proofs**: the topological closure of a definable subset of
`VF^n` is definable, and if `dim_VF(B) < n` then some definable closed `C ⊇ B` also has
`dim_VF(C) < n`.  The paper uses the second half as *"which, by Lemma `full:dim:open:poly`, is
equivalent to showing that `dim_VF(A) < n`"* (`paper.tex:1874`); the first half is *"Let `Ā` be the
topological closure of `A`, which is definable"* (`paper.tex:1869`).  Both are §4-and-`C`-minimality
content, so they are carried as one explicit hypothesis. -/
def ClosureHyp (S : SP M) (n : ℕ) : Prop :=
  ∀ B : Set (Tup M n 0), Definable S B → dimVF S B < n →
    ∃ C : Set (Tup M n 0), Definable S C ∧ IsClosedVF C ∧ dimVF S C < n ∧ B ⊆ C

/-- The paper's conclusion of `fun:almost:loc:con` in the paper's "almost everywhere" terminology
(`paper.tex:1806`): *"Then `f` is locally constant almost everywhere."* -/
def FunAlmostLocCon (S : SP M) {n m : ℕ} (D : Set (Tup M n m)) : Prop :=
  AlmostEverywhere S n (LocallyConstantAt D)

/-- **Lemma `fun:almost:loc:con`** (`paper.tex:1883`), verbatim: *"Let `f : VF^n → P(RV^m)` be a
definable function.  Then `f` is locally constant almost everywhere."*

The set-valued function is the definable relation `D ⊆ VF^n × RV^m` (`Fibre`); `FunAlmostLocCon S D`
is the paper's conclusion in the paper's "almost everywhere" terminology, and the statement proved
here is its closed-set form, which is what "locally constant on the open set `VF^n ∖ B`" requires.
The hypothesis `h` is the lemma as the paper proves it (by induction on `n`, from `C`-minimality and
Lemma `fun:quo:rep`); `ClosureHyp` is the closure step of that proof. -/
theorem fun_almost_loc_con_closed (S : SP M) {n m : ℕ} (D : Set (Tup M n m))
    (hbf : BallFacts M) (hD : Definable S D) (hcl : ClosureHyp S n) (h : FunAlmostLocCon S D) :
    ∃ B : Set (Tup M n 0), Definable S B ∧ IsClosedVF B ∧ dimVF S B < n ∧
      LocallyConstantOn D Bᶜ := by
  obtain ⟨B, hB, hdim, hP⟩ := h
  obtain ⟨C, hC, hCclosed, hCdim, hBC⟩ := hcl B hB hdim
  refine ⟨C, hC, hCclosed, hCdim, fun x hx => ?_⟩
  -- `x ∉ C`, so `x ∉ B` and `f` is locally constant at `x`
  have hxB : x ∉ B := fun hmem => hx (hBC hmem)
  obtain ⟨r, hr, hconst⟩ := hP x hxB
  -- and `x` has a polydisc inside the open set `Cᶜ`
  obtain ⟨t, ht, htsub⟩ := exists_goBox_subset_compl_inter hbf hCclosed hx hr
  exact ⟨t, ht, fun y hy => (htsub hy).1, fun y hy => hconst y (htsub hy).2⟩

/-! ## §I. Continuity is local; locally constant functions are continuous -/

/-- There is an **admissible radius** (in a model of `ACVF`, `rv 1 ≠ 0`): the index type of radius
families is inhabited.  A consequence of the `ACVF` axioms, hence a hypothesis. -/
def AdmExists (M : Type*) [LRV.Structure M] : Prop :=
  ∃ γ : M, iRV γ ∧ γ ≠ iRVZero

/-- **Continuity is a local property**: if `f` agrees with the continuous `g` on an open polydisc
around `x`, then `f` is continuous at `x`.  This is the step the paper uses in the proof of
`fun:almost:loc:con` (*"clearly for any sufficiently large `γ` and any `(a'_1, ā'_1) ∈ go(ā, γ)` we
have `f(a_1, ā_1) = f(a_1, ā'_1) = f(a'_1, ā'_1)`.  So `f` is locally constant on `B`"*,
`paper.tex:1928`), and it is what makes "locally constant" a continuity notion. -/
theorem goContAt_congr (hbf : BallFacts M) {n m : ℕ} {f g : Tup M n 0 → Tup M m 0}
    {x : Tup M n 0} {r : Fin n → M} (hr : AdmRadius r)
    (h : ∀ y : Tup M n 0, y ∈ goBox x r → f y = g y) (hg : GoContAt g x) : GoContAt f x := by
  have hxr : x ∈ goBox x r := mem_goBox_self hbf x hr
  have hfx : f x = g x := h x hxr
  intro R hR
  obtain ⟨s, hs, hgs⟩ := hg R hR
  obtain ⟨t, ht, htsub⟩ := goBox_inter hbf x hs hr
  refine ⟨t, ht, fun y hy => ?_⟩
  rw [hfx, h y (htsub hy).2]
  exact hgs y (htsub hy).1

/-- A function that is constant on an open polydisc around `x` is continuous at `x`. -/
theorem goContAt_of_locally_const (hbf : BallFacts M) {n m : ℕ} {f : Tup M n 0 → Tup M m 0}
    {x : Tup M n 0} {r : Fin n → M} (hr : AdmRadius r)
    (h : ∀ y : Tup M n 0, y ∈ goBox x r → f y = f x) : GoContAt f x := by
  refine goContAt_congr hbf hr h ?_
  intro R hR
  exact ⟨r, hr, fun y _ => mem_goBox_self hbf (f x) hR⟩

/-- A constant function is continuous at every point. -/
theorem goContAt_const (hbf : BallFacts M) (hex : AdmExists M) {n m : ℕ} (c : Tup M m 0)
    (x : Tup M n 0) : GoContAt (fun _ : Tup M n 0 => c) x := by
  obtain ⟨γ, hγ, hγ0⟩ := hex
  intro R hR
  exact ⟨fun _ => γ, ⟨fun _ => hγ, fun _ => hγ0⟩, fun y _ => mem_goBox_self hbf c hR⟩

/-- A constant function has no discontinuous points. -/
theorem discSet_const (hbf : BallFacts M) {n m : ℕ} (c : Tup M m 0) :
    DiscSet (fun _ : Tup M n 0 => c) = ∅ := by
  ext x
  simp only [DiscSet, Set.mem_ofPred_eq, Set.notMem_empty, iff_false, not_not, GoContAtPaper]
  intro γ hγ hγ0
  exact ⟨γ, hγ, hγ0, fun y _ => mem_goBox_self hbf c ⟨fun _ => hγ, fun _ => hγ0⟩⟩

/-! ## §J. Consistency check: the empty set, and Lemma `fun:almost:cont` for a constant function -/

/-- The empty set is definable. -/
theorem definable_empty (S : SP M) {n m : ℕ} : Definable S (∅ : Set (Tup M n m)) :=
  ⟨⊥, WellSorted.falsum (fSort n m), fun x => by simp⟩

/-- The empty set has `VF`-dimension `0`. -/
theorem hasDim_empty (S : SP M) {n m : ℕ} : HasDim S (∅ : Set (Tup M n m)) 0 := by
  haveI : Nonempty (Tup M 0 0) :=
    ⟨⟨fun i => Sum.casesOn i (fun j => j.elim0) (fun j => j.elim0),
      fun i => Sum.casesOn i (fun j => j.elim0) (fun j => j.elim0)⟩⟩
  refine ⟨0, le_rfl, 0, fun _ => Classical.ofNonempty, ?_, ?_⟩
  · exact ⟨⊤, wellSorted_top S.sortMap (Fin.append (fSort n m) (fSort 0 0)),
      fun x hx => absurd hx (by simp)⟩
  · intro y
    have h : {x : Tup M n m | x ∈ (∅ : Set (Tup M n m)) ∧
        (fun _ => Classical.ofNonempty) x = y} = ∅ := by
      ext x
      simp
    rw [h]
    exact Set.finite_empty

/-- `dim_VF(∅) = 0`. -/
theorem dimVF_empty (S : SP M) {n m : ℕ} : dimVF S (∅ : Set (Tup M n m)) = 0 :=
  (dimVF_eq_zero_iff S ∅).mpr (hasDim_empty S)

/-- **Lemma `fun:almost:loc:con` in the case where `f` is locally constant at every point**: the
witnessing set is `B = ∅`, so the paper's conclusion `FunAlmostLocCon` holds.  Another consistency
check, showing that the statement of the lemma is satisfiable. -/
theorem fun_almost_loc_con_const (S : SP M) {n m : ℕ} (hn : 1 ≤ n) {D : Set (Tup M n m)}
    (h : ∀ x : Tup M n 0, LocallyConstantAt D x) : FunAlmostLocCon S D := by
  refine ⟨∅, definable_empty S, ?_, fun x _ => h x⟩
  rw [dimVF_empty S]
  exact hn

/-- A function that is locally constant (on polydiscs) has no discontinuous points. -/
theorem discSet_eq_empty_of_locally_const (hbf : BallFacts M) {n m : ℕ}
    {f : Tup M n 0 → Tup M m 0}
    (h : ∀ x : Tup M n 0, ∃ r : Fin n → M, AdmRadius r ∧
      ∀ y : Tup M n 0, y ∈ goBox x r → f y = f x) : DiscSet f = ∅ := by
  ext x
  obtain ⟨r, hr, hconst⟩ := h x
  simp only [DiscSet, Set.mem_ofPred_eq, Set.notMem_empty, iff_false, not_not]
  rw [← goContAt_iff_paper hbf]
  exact goContAt_of_locally_const hbf hr hconst

/-! ## Axiom check -/

#print axioms SpecialTransformations.Milestone0.Sec8.mem_discSet_iff
#print axioms SpecialTransformations.Milestone0.Sec8.goContAt_iff_paper
#print axioms SpecialTransformations.Milestone0.Sec8.goContOn_compl_of_discSet_subset
#print axioms SpecialTransformations.Milestone0.Sec8.fun_almost_loc_con_closed
#print axioms SpecialTransformations.Milestone0.Sec8.goContAt_congr
#print axioms SpecialTransformations.Milestone0.Sec8.fun_almost_loc_con_const
#print axioms SpecialTransformations.Milestone0.Sec8.dimVF_inter_eq
#print axioms SpecialTransformations.Milestone0.Sec8.dimVF_discSet_lt
