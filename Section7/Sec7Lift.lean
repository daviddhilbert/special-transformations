module

/-
# Section 7, Theorem \ref{RV:iso:class:lifted}: *isomorphic `RV`-objects have isomorphic lifts*

Direction d3 of swarm `smw1kl4vz` (member m1).  Source: `.ultramath/refs/paper.tex` line 1627 ff.

The paper's sentence, frozen below as `SP.Theorem_7_6_stat`:

> **Theorem \ref{RV:iso:class:lifted}.**  *Suppose that the substructure `S` is `(VF, Γ)`-generated.
> Let `C ⊆ (RV^×)^n × (RV^×)^n` be a definable subset such that both `pr_{≤n} ⌠ C` and
> `pr_{>n} ⌠ C` are finite-to-one.  Then there is a definable subset `C^↑ ⊆ VF^n × VF^n` that
> lifts `C`.*

and Definition \ref{def:lift} that the conclusion refers to:

> *Let `B, C` be two `RV`-pullbacks, `A` a subset of `B × C`, and `U` a subset of `rv(B × C)`.  We
> say that `A` is a `(B, C)`-lift of `U` from `RV` to `VF`, or just a lift of `U` for short, if
> `A ∩ (𝔭 × 𝔮)` is a bijection from `𝔭` onto `𝔮` for any `rv`-polydiscs `𝔭 ⊆ B` and `𝔮 ⊆ C` with
> `rv(𝔭 × 𝔮) ∈ U`.  A partial lift of `U` is a lift of any subset of `U`.*

## What is proved (17 theorems, no `sorry`, no `axiom`)

`SP.BijectiveOn` (Definition \ref{def:lift} read as a relation), `SP.IsLift` (the definition
itself, plus `IsLift.subset` = *"a partial lift of `U` is a lift of any subset of `U`"*),
`SP.FiniteToFst`/`SP.FiniteToSnd` (the two finite-to-one projections), and then:

* `SP.BijectiveOn.fstMap`, `sndMap`, `eq_fstMap`, `eq_sndMap`, `fstMap_mem`, `sndMap_mem`,
  `sndMap_fstMap`, `fstMap_sndMap` — **the relation of Definition \ref{def:lift} is a genuine
  bijection**: `fstMap` and `sndMap` are mutually inverse between the two `rv`-polydiscs, not just a
  pair of single-valued total relations.
* `SP.rvPartner`, `SP.rvPartner'`, `eq_rvPartner`, `eq_rvPartner'` — the partner functions of a
  lifted relation, with their uniqueness properties.  (They are `Classical.choose` on a proposition
  that mentions only `Ā` and the tuples, so they do not depend on the proof of `u ∈ C`.)
* **`SP.liftToFun_bijective`** — the paragraph of §7 after Definition \ref{def:lift}: *"a lift `F^↑`
  of `F` is actually an `(𝕃(U, f), 𝕃(V, g))`-lift of the induced function `F_{f,g} : U_f → V_g`;
  that is, `F^↑` is a function on `𝕃(U, f)` such that each restriction
  `F^↑ : rv⁻¹(f(ū), ū) → rv⁻¹((g ∘ F)(ū), F(ū))` is a bijection."*  Proved for an arbitrary
  bijection `F` between the bases of two `RV[k,·]`-objects — **the two bases may have different
  arities** (`U ⊆ RV^m`, `V ⊆ RV^{m'}`), as in the paper — and an arbitrary lifted relation `Ā`.
  Components: `liftToFun_base` (the base coordinate is `F`), `liftToFun_kOf` (the target lies in the
  second `rv`-disc and the pair in `Ā`), `liftToFun_injective`, `liftToFun_surjective`.
* **`SP.corollary_7_7`** — Corollary \ref{L:semigroup:hom} **proved from Theorem 7.6 carried as an
  explicit hypothesis** (`SP.Corollary_7_7_stat`): *"By Theorem \ref{RV:iso:class:lifted} there is a
  lift `C^↑` of `C`, which induces a `VF[k, ·]`-isomorphism between `𝕃(U, f)` and `𝕃(V, g)`.  So `𝕃`
  induces a map on the isomorphism classes."*  Via
  `exists_lift_and_bijection_of_theorem_7_6` and `exists_lift_and_bijection_of_RVIso` (the latter
  for a genuine pair of mutually inverse `SP.RVHom`s).
* `SP.finiteToFst_rvCorrespondence`, `SP.finiteToSnd_rvCorrespondence` — the two finite-to-one
  hypotheses of Theorem 7.6 **derived** for an `RV[k,·]`-morphism: the first is literally
  `RVHom.finite_fibres`, the second follows from the `RV[k]` condition `RVObj.FiniteToOne` together
  with injectivity of `F`.
* `SP.weight_eq_of_volumetric_inverse` — Corollary \ref{L:semigroup:hom}'s opening sentence: *"For
  any `RV[k, ·]`-isomorphism `F : (U, f) → (V, g)` and any `ū ∈ U`, by definition
  `wgt(f(ū)) = wgt((g ∘ F)(ū))`."*

## What is stated but not proved (and why)

* `SP.Theorem_7_6_stat` — the paper's Theorem 7.6 verbatim as a `Prop`, with
  `SP.IsVFGammaGenerated S` as its hypothesis.
* `SP.Sec7Prereq` — the two §7 lemmas whose *joint conclusion at one point* the proof of 7.6 uses,
  carried as an explicit `structure … : Prop` field, with both paper sentences quoted
  (`exists:gamma:polynomial`, `hensel:lemma`).
* `SP.Theorem_7_6_of_sec7` — the reduction `Sec7Prereq S → Theorem_7_6_stat S`.  **The exact missing
  step** is the paper's *"By compactness, the lemma is reduced to showing that for every
  `(t̄, s̄) ∈ C` there is a definable lift of some subset of `C` that contains `(t̄, s̄)`."*
  Covering a definable `C` by finitely many of the local pieces requires compactness of the space of
  definable types over an `ω`-saturated model; the tree has `SP.acl`/`SP.dcl` and
  `Milestone0/Saturation.lean` but no such compactness theorem.  Not formalized, and nothing proved
  here depends on it.

Two further open inputs, flagged as explicit hypotheses of the theorems that use them and never
hidden:

1. `hCdef : SP.Definable S (pairRVSort k) (rvCorrespondence X Y Φ.F)` — the definability of the
   `RV`-correspondence `{(f(ū), (g∘F)(ū)) : ū ∈ U}`.  This is the image of a definable set under a
   definable map, and closure of `SP.Definable` under such images is **the one wall** recorded in
   `QE/Sec4Categories.lean` (composition of `TmSort`-typed terms, equivalently
   variable substitution) which three separate sections need.
2. `hCunit` — the paper's `C ⊆ (RV^×)^n × (RV^×)^n` (in the encoding, `IsRVUnitTuple`), and
   `Y.FiniteToOne` for the `RV[k]` half of Corollary 7.7.

## Faithfulness notes

* `Fin n ⊕ Fin n` is the paper's `(RV^×)^n × (RV^×)^n` (Notation 2.10's `I_n ⊎ I_n`), with sorts
  `SP.pairRVSort` / `SP.pairVFSort`.  `iRVZero` is `∞ = rv 0`, so the tuples of `RV^×` are the
  `IsRVUnitTuple`s.
* `SP.Definable` is the *well-sorted* fragment of `Milestone0/Encoding.lean`, as everywhere else in
  the tree: the encoding's carrier admits ill-sorted junk terms, so unrestricted `Set.Definable`
  would be the wrong notion.
* The lifted relation `C^↑` is a `Set`, not a function: the paper's `A ∩ (𝔭 × 𝔮)` is a *relation*
  that is required to be a bijection, and `IsLift` says exactly that.  `rvPartner`/`rvPartner'` then
  extract the function and its inverse.

Build (from this directory):

    LEAN_PATH=<repo>/.scratch2/sec3:$LEAN_PATH lean Sec7Lift.lean
-/
public import Sec4Categories

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
namespace SP

variable {M : Type*} [LRV.Structure M]

/-! ## Part 1. `RV`-tuples, the `rv`-polydisc `rv⁻¹(ū)`, and the two halves of `Fin n ⊕ Fin n` -/

/-- `ū` is a tuple of the `RV` sort. -/
def IsRVTuple {α : Type} (u : α → M) : Prop := ∀ i, iRV (u i)

/-- `x̄` is a tuple of the `VF` sort. -/
def IsVFTuple {α : Type} (x : α → M) : Prop := ∀ i, iVF (x i)

/-- `ū` is a tuple of `RV^×`: all coordinates are `RV`-elements and none of them is `∞ = rv 0`.
These are the tuples the paper's `C ⊆ (RV^×)^n × (RV^×)^n` consists of. -/
def IsRVUnitTuple {α : Type} (u : α → M) : Prop := IsRVTuple u ∧ ∀ i, u i ≠ iRVZero

/-- `rv` applied coordinatewise: the paper's `rv(ā)`. -/
def rvTuple {α : Type} (x : α → M) : α → M := fun i => iRv (x i)

@[simp]
theorem rvTuple_apply {α : Type} (x : α → M) (i : α) : rvTuple x i = iRv (x i) := rfl

/-- **The `rv`-polydisc `rv⁻¹(ū) ⊆ VF^α`** — Definition 2.6's `rv`-ball in every coordinate, i.e.
`rv^{-1}(ū_1) × ⋯ × rv^{-1}(ū_n)`.  This is the paper's `𝔭` in Definition \ref{def:lift}. -/
def rvDisc {α : Type} (u : α → M) : Set (α → M) := {x | IsVFTuple x ∧ rvTuple x = u}

theorem mem_rvDisc {α : Type} {u x : α → M} :
    x ∈ rvDisc u ↔ IsVFTuple x ∧ rvTuple x = u := Iff.rfl

theorem IsRVTuple.fstHalf {n : ℕ} {u : (Fin n ⊕ Fin n) → M} (h : IsRVTuple u) :
    IsRVTuple (fun i => u (Sum.inl i)) := fun i => h (Sum.inl i)

/-- The first half of a tuple indexed by `Fin n ⊕ Fin n`. -/
def fstHalf {n : ℕ} (z : (Fin n ⊕ Fin n) → M) : Fin n → M := fun i => z (Sum.inl i)

/-- The second half of a tuple indexed by `Fin n ⊕ Fin n`. -/
def sndHalf {n : ℕ} (z : (Fin n ⊕ Fin n) → M) : Fin n → M := fun i => z (Sum.inr i)

/-- Pair the two halves back into one tuple. -/
def joinHalf {n : ℕ} (x y : Fin n → M) : (Fin n ⊕ Fin n) → M := Sum.elim x y

@[simp]
theorem fstHalf_joinHalf {n : ℕ} (x y : Fin n → M) : fstHalf (joinHalf x y) = x := rfl

@[simp]
theorem sndHalf_joinHalf {n : ℕ} (x y : Fin n → M) : sndHalf (joinHalf x y) = y := rfl

theorem joinHalf_fstHalf_sndHalf {n : ℕ} (z : (Fin n ⊕ Fin n) → M) :
    joinHalf (fstHalf z) (sndHalf z) = z := by
  funext i; cases i <;> rfl

/-- The sort map of `(RV^×)^n × (RV^×)^n`: both halves at the `RV` sort. -/
def pairRVSort (n : ℕ) : (Fin n ⊕ Fin n) → SortTag := fun _ => SortTag.rv

/-- The sort map of `VF^n × VF^n`: both halves at the `VF` sort. -/
def pairVFSort (n : ℕ) : (Fin n ⊕ Fin n) → SortTag := fun _ => SortTag.vf

/-! ## Part 2. Definition \ref{def:lift}: `Ā` lifts `C` -/

/-- **The relation `Ā ∩ (rv⁻¹(ū_{≤n}) × rv⁻¹(ū_{>n}))` is a bijection** from the first `rv`-polydisc
onto the second, in the only form that makes sense in set theory: each point of the first has a
unique partner in the second, and each point of the second has a unique partner in the first.

The paper's wording (`def:lift`) is "`A ∩ (𝔭 × 𝔮)` is a bijection from `𝔭` onto `𝔮`". -/
def BijectiveOn {n : ℕ} (Ā : Set ((Fin n ⊕ Fin n) → M)) (u : (Fin n ⊕ Fin n) → M) : Prop :=
  (∀ x : Fin n → M, x ∈ rvDisc (fstHalf u) →
      ∃! y : Fin n → M, y ∈ rvDisc (sndHalf u) ∧ joinHalf x y ∈ Ā) ∧
    (∀ y : Fin n → M, y ∈ rvDisc (sndHalf u) →
      ∃! x : Fin n → M, x ∈ rvDisc (fstHalf u) ∧ joinHalf x y ∈ Ā)

/-- **Definition \ref{def:lift}, "`A` is a lift of `U`"**: *"`A ∩ (𝔭 × 𝔮)` is a bijection from `𝔭`
onto `𝔮` for any `rv`-polydiscs `𝔭 ⊆ B` and `𝔮 ⊆ C` with `rv(𝔭 × 𝔮) ∈ U`."*

`C` is the paper's `U` (a set of `rv`-tuples, i.e. a subset of `rv(B × C)`), and `Ā` is the
paper's `A`.  Since `𝔭` and `𝔮` are `rv`-polydiscs, `rv(𝔭 × 𝔮)` is a single tuple `u`, so the
condition is: for every `u ∈ C` the relation `Ā` is a bijection from `rv⁻¹(fstHalf u)` onto
`rv⁻¹(sndHalf u)`. -/
def IsLift {n : ℕ} (C Ā : Set ((Fin n ⊕ Fin n) → M)) : Prop := ∀ u, u ∈ C → BijectiveOn Ā u

/-- *"A partial lift of `U` is a lift of any subset of `U`."* -/
theorem IsLift.subset {n : ℕ} {C C' Ā : Set ((Fin n ⊕ Fin n) → M)} (h : IsLift C Ā)
    (hC : C' ⊆ C) : IsLift C' Ā := fun u hu => h u (hC hu)

/-- **`C` has finite-to-one projection to its first `n` coordinates** — the paper's *"`pr_{≤n} ⌠ C`
is finite-to-one"*. -/
def FiniteToFst {n : ℕ} (C : Set ((Fin n ⊕ Fin n) → M)) : Prop :=
  ∀ x : Fin n → M, {y : Fin n → M | joinHalf x y ∈ C}.Finite

/-- **`C` has finite-to-one projection to its last `n` coordinates** — the paper's *"`pr_{>n} ⌠ C`
is finite-to-one"*. -/
def FiniteToSnd {n : ℕ} (C : Set ((Fin n ⊕ Fin n) → M)) : Prop :=
  ∀ y : Fin n → M, {x : Fin n → M | joinHalf x y ∈ C}.Finite

/-! ## Part 3. The bijection supplied by a lift, read as a function on `rv`-polydiscs -/

/-- The function on `rv`-polydiscs that a `BijectiveOn Ā u` supplies: to `x̄ ∈ rv⁻¹(ū_{≤n})` assign
its unique partner in `rv⁻¹(ū_{>n})`. -/
noncomputable def BijectiveOn.fstMap {n : ℕ} {Ā : Set ((Fin n ⊕ Fin n) → M)}
    {u : (Fin n ⊕ Fin n) → M} (h : BijectiveOn Ā u) (x : Fin n → M)
    (hx : x ∈ rvDisc (fstHalf u)) : Fin n → M :=
  Classical.choose (h.1 x hx)

/-- The partner lies in the second polydisc, and the pair lies in `Ā`. -/
theorem BijectiveOn.fstMap_mem {n : ℕ} {Ā : Set ((Fin n ⊕ Fin n) → M)}
    {u : (Fin n ⊕ Fin n) → M} (h : BijectiveOn Ā u) {x : Fin n → M}
    (hx : x ∈ rvDisc (fstHalf u)) :
    h.fstMap x hx ∈ rvDisc (sndHalf u) ∧ joinHalf x (h.fstMap x hx) ∈ Ā :=
  (Classical.choose_spec (h.1 x hx)).1

/-- **Uniqueness of the partner**: the function `fstMap` is the only possible one. -/
theorem BijectiveOn.eq_fstMap {n : ℕ} {Ā : Set ((Fin n ⊕ Fin n) → M)}
    {u : (Fin n ⊕ Fin n) → M} (h : BijectiveOn Ā u) {x y : Fin n → M}
    (hx : x ∈ rvDisc (fstHalf u)) (hy : y ∈ rvDisc (sndHalf u))
    (hA : joinHalf x y ∈ Ā) : y = h.fstMap x hx :=
  (Classical.choose_spec (h.1 x hx)).2 y ⟨hy, hA⟩

/-- The inverse function on the other polydisc. -/
noncomputable def BijectiveOn.sndMap {n : ℕ} {Ā : Set ((Fin n ⊕ Fin n) → M)}
    {u : (Fin n ⊕ Fin n) → M} (h : BijectiveOn Ā u) (y : Fin n → M)
    (hy : y ∈ rvDisc (sndHalf u)) : Fin n → M :=
  Classical.choose (h.2 y hy)

theorem BijectiveOn.sndMap_mem {n : ℕ} {Ā : Set ((Fin n ⊕ Fin n) → M)}
    {u : (Fin n ⊕ Fin n) → M} (h : BijectiveOn Ā u) {y : Fin n → M}
    (hy : y ∈ rvDisc (sndHalf u)) :
    h.sndMap y hy ∈ rvDisc (fstHalf u) ∧ joinHalf (h.sndMap y hy) y ∈ Ā :=
  (Classical.choose_spec (h.2 y hy)).1

/-- **Uniqueness of the preimage**: the second clause of `BijectiveOn`, naming the function
`sndMap`. -/
theorem BijectiveOn.eq_sndMap {n : ℕ} {Ā : Set ((Fin n ⊕ Fin n) → M)}
    {u : (Fin n ⊕ Fin n) → M} (h : BijectiveOn Ā u) {x y : Fin n → M}
    (hy : y ∈ rvDisc (sndHalf u)) (hx : x ∈ rvDisc (fstHalf u))
    (hA : joinHalf x y ∈ Ā) : x = h.sndMap y hy :=
  (Classical.choose_spec (h.2 y hy)).2 x ⟨hx, hA⟩

/-- **`sndMap` is a left inverse of `fstMap`**: the relation is a bijection, not merely a pair of
single-valued total relations. -/
theorem BijectiveOn.sndMap_fstMap {n : ℕ} {Ā : Set ((Fin n ⊕ Fin n) → M)}
    {u : (Fin n ⊕ Fin n) → M} (h : BijectiveOn Ā u) {x : Fin n → M}
    (hx : x ∈ rvDisc (fstHalf u)) :
    h.sndMap (h.fstMap x hx) (h.fstMap_mem hx).1 = x :=
  (h.eq_sndMap (h.fstMap_mem hx).1 hx (h.fstMap_mem hx).2).symm

/-- **`fstMap` is a right inverse of `sndMap`**, symmetrically. -/
theorem BijectiveOn.fstMap_sndMap {n : ℕ} {Ā : Set ((Fin n ⊕ Fin n) → M)}
    {u : (Fin n ⊕ Fin n) → M} (h : BijectiveOn Ā u) {y : Fin n → M}
    (hy : y ∈ rvDisc (sndHalf u)) :
    h.fstMap (h.sndMap y hy) (h.sndMap_mem hy).1 = y :=
  (h.eq_fstMap (h.sndMap_mem hy).1 hy (h.sndMap_mem hy).2).symm

/-- A lift is a family of bijections between `rv`-polydiscs. -/
theorem IsLift.bijectiveOn {n : ℕ} {C Ā : Set ((Fin n ⊕ Fin n) → M)} (h : IsLift C Ā)
    {u : (Fin n ⊕ Fin n) → M} (hu : u ∈ C) : BijectiveOn Ā u := h u hu

/-! ## Part 4. The partner functions of an `rv`-bijection, and the lift of `𝕃(U,f)`

`rvPartner Ā x v` is the unique `y` with `y ∈ rv⁻¹(v)` and `(x,y) ∈ Ā`; `rvPartner' Ā y t` is the
unique `x` with `x ∈ rv⁻¹(t)` and `(x,y) ∈ Ā`.  Both are defined by `Classical.choose` on a
proposition that mentions only `Ā` and the tuples, **not** a proof of `u ∈ C` — so the same term is
produced at every call site, which is what makes the injectivity/surjectivity arguments below go
through without proof-irrelevance side conditions. -/

/-- The partner `y` of `x` under the lifted relation `Ā`, in the second polydisc `rv⁻¹(v)`. -/
noncomputable def rvPartner {n : ℕ} (Ā : Set ((Fin n ⊕ Fin n) → M)) (x v : Fin n → M) :
    Fin n → M := by
  classical
  exact if _ : ∃! y : Fin n → M, y ∈ rvDisc v ∧ joinHalf x y ∈ Ā then
    Classical.choose ‹∃! y : Fin n → M, y ∈ rvDisc v ∧ joinHalf x y ∈ Ā› else x

/-- The preimage `x` of `y` under the lifted relation `Ā`, in the first polydisc `rv⁻¹(t)`. -/
noncomputable def rvPartner' {n : ℕ} (Ā : Set ((Fin n ⊕ Fin n) → M)) (y t : Fin n → M) :
    Fin n → M := by
  classical
  exact if _ : ∃! x : Fin n → M, x ∈ rvDisc t ∧ joinHalf x y ∈ Ā then
    Classical.choose ‹∃! x : Fin n → M, x ∈ rvDisc t ∧ joinHalf x y ∈ Ā› else y

theorem rvPartner_eq_fstMap {n : ℕ} {Ā : Set ((Fin n ⊕ Fin n) → M)}
    {u : (Fin n ⊕ Fin n) → M} (hc : BijectiveOn Ā u) {x : Fin n → M}
    (hx : x ∈ rvDisc (fstHalf u)) :
    rvPartner Ā x (sndHalf u) = hc.fstMap x hx := by
  simp only [rvPartner]
  rw [dif_pos (hc.1 x hx)]
  rfl

theorem rvPartner'_eq_sndMap {n : ℕ} {Ā : Set ((Fin n ⊕ Fin n) → M)}
    {u : (Fin n ⊕ Fin n) → M} (hc : BijectiveOn Ā u) {y : Fin n → M}
    (hy : y ∈ rvDisc (sndHalf u)) :
    rvPartner' Ā y (fstHalf u) = hc.sndMap y hy := by
  simp only [rvPartner']
  rw [dif_pos (hc.2 y hy)]
  rfl

/-- The partner lies in the second polydisc and the pair lies in `Ā`. -/
theorem rvPartner_mem {n : ℕ} {Ā : Set ((Fin n ⊕ Fin n) → M)}
    {u : (Fin n ⊕ Fin n) → M} (hc : BijectiveOn Ā u) {x : Fin n → M}
    (hx : x ∈ rvDisc (fstHalf u)) :
    rvPartner Ā x (sndHalf u) ∈ rvDisc (sndHalf u) ∧
      joinHalf x (rvPartner Ā x (sndHalf u)) ∈ Ā := by
  rw [rvPartner_eq_fstMap hc hx]
  exact hc.fstMap_mem hx

/-- The preimage lies in the first polydisc and the pair lies in `Ā`. -/
theorem rvPartner'_mem {n : ℕ} {Ā : Set ((Fin n ⊕ Fin n) → M)}
    {u : (Fin n ⊕ Fin n) → M} (hc : BijectiveOn Ā u) {y : Fin n → M}
    (hy : y ∈ rvDisc (sndHalf u)) :
    rvPartner' Ā y (fstHalf u) ∈ rvDisc (fstHalf u) ∧
      joinHalf (rvPartner' Ā y (fstHalf u)) y ∈ Ā := by
  rw [rvPartner'_eq_sndMap hc hy]
  exact hc.sndMap_mem hy

/-- **Uniqueness of the partner**: `rvPartner` is the only function with the two properties. -/
theorem eq_rvPartner {n : ℕ} {Ā : Set ((Fin n ⊕ Fin n) → M)}
    {u : (Fin n ⊕ Fin n) → M} (hc : BijectiveOn Ā u) {x y : Fin n → M}
    (hx : x ∈ rvDisc (fstHalf u)) (hy : y ∈ rvDisc (sndHalf u))
    (hA : joinHalf x y ∈ Ā) : y = rvPartner Ā x (sndHalf u) := by
  rw [rvPartner_eq_fstMap hc hx]
  exact hc.eq_fstMap hx hy hA

/-- **Uniqueness of the preimage**. -/
theorem eq_rvPartner' {n : ℕ} {Ā : Set ((Fin n ⊕ Fin n) → M)}
    {u : (Fin n ⊕ Fin n) → M} (hc : BijectiveOn Ā u) {x y : Fin n → M}
    (hy : y ∈ rvDisc (sndHalf u)) (hx : x ∈ rvDisc (fstHalf u))
    (hA : joinHalf x y ∈ Ā) : x = rvPartner' Ā y (fstHalf u) := by
  rw [rvPartner'_eq_sndMap hc hy]
  exact hc.eq_sndMap hy hx hA

/-! ### The canonical lift `𝕃(U,f)` of Definition \ref{def:L}, split into `VF`- and base coordinates -/

/-- The `VF`-coordinates of a point of the canonical lift `𝕃(U,f) = ⋃{rv⁻¹(f(ū)) × {ū} : ū ∈ U}`
(index type `Fin k ⊕ β`, `k` lift coordinates and the base). -/
def kOf {k : ℕ} {β : Type} (z : (Fin k ⊕ β) → M) : Fin k → M := fun i => z (Sum.inl i)

/-- The base coordinates of a point of the canonical lift. -/
def baseOf {k : ℕ} {β : Type} (z : (Fin k ⊕ β) → M) : β → M := fun b => z (Sum.inr b)

/-- Assemble a point of the canonical lift from its `VF`-coordinates and its base point. -/
def joinK {k : ℕ} {β : Type} (x : Fin k → M) (u : β → M) : (Fin k ⊕ β) → M := Sum.elim x u

@[simp]
theorem kOf_joinK {k : ℕ} {β : Type} (x : Fin k → M) (u : β → M) : kOf (joinK x u) = x := rfl

@[simp]
theorem baseOf_joinK {k : ℕ} {β : Type} (x : Fin k → M) (u : β → M) : baseOf (joinK x u) = u := rfl

theorem joinK_kOf_baseOf {k : ℕ} {β : Type} (z : (Fin k ⊕ β) → M) :
    joinK (kOf z) (baseOf z) = z := by
  funext i; cases i <;> rfl

/-- Membership in the canonical lift `𝕃(U,f)` (Definition \ref{def:L}), in the split form the
arguments below use. -/
theorem mem_lift {S : SP M} {β : Type} {sβ : β → SortTag} {A : Set (β → M)} {k : ℕ}
    (X : RVObj S sβ A k) (z : (Fin k ⊕ β) → M) :
    z ∈ X.lift ↔ IsVFTuple (kOf z) ∧ baseOf z ∈ X.U ∧ rvTuple (kOf z) = X.f (baseOf z) := by
  have hsplit : z ∈ X.lift ↔ ((∀ i, iVF (z (Sum.inl i))) ∧ (fun b => z (Sum.inr b)) ∈ X.U ∧
      ∀ i, iRv (z (Sum.inl i)) = X.f (fun b => z (Sum.inr b)) i) := Iff.rfl
  rw [hsplit]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, funext fun i => h3 i⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun i => congrFun h3 i⟩

/-- The `VF`-coordinates of a point of `𝕃(U,f)` lie in the `rv`-disc of `f` at its base point. -/
theorem lift_hx {S : SP M} {β : Type} {sβ : β → SortTag} {A : Set (β → M)} {k : ℕ}
    {X : RVObj S sβ A k} {z : (Fin k ⊕ β) → M} (hz : z ∈ X.lift) :
    kOf z ∈ rvDisc (X.f (baseOf z)) :=
  ⟨((mem_lift X z).1 hz).1, ((mem_lift X z).1 hz).2.2⟩

/-! ### The `RV`-correspondence `C = {(f(ū), (g∘F)(ū)) : ū ∈ U}` of Corollary \ref{L:semigroup:hom} -/

/-- The `rv`-tuple `(f(ū), (g∘F)(ū))` at which the lifted relation of the proof of Theorem
\ref{RV:iso:class:lifted} is consulted. -/
def rvKey {S : SP M} {β β' : Type} {sβ : β → SortTag} {sβ' : β' → SortTag}
    {A : Set (β → M)} {A' : Set (β' → M)} {k : ℕ}
    (X : RVObj S sβ A k) (Y : RVObj S sβ' A' k) (F : (β → M) → β' → M) (u : β → M) :
    (Fin k ⊕ Fin k) → M :=
  joinHalf (X.f u) (Y.f (F u))

/-- **The `RV`-correspondence of an `RV[k,·]`-map**: the paper's *"`C = {(f(ū), (g ∘ F)(ū)) :
ū ∈ U} ⊆ RV^k × RV^k`"* (proof of Corollary \ref{L:semigroup:hom}).

Note that `C` lives in `RV^k × RV^k` — the *`k` coordinates only* — while the base points of the two
`RV`-categories may have different arities (`U ⊆ RV^m`, `V ⊆ RV^{m'}`), which is why `X` and `Y`
below have independent base types `β` and `β'`. -/
def rvCorrespondence {S : SP M} {β β' : Type} {sβ : β → SortTag} {sβ' : β' → SortTag}
    {A : Set (β → M)} {A' : Set (β' → M)} {k : ℕ}
    (X : RVObj S sβ A k) (Y : RVObj S sβ' A' k) (F : (β → M) → β' → M) :
    Set ((Fin k ⊕ Fin k) → M) :=
  {w | ∃ u ∈ X.U, w = rvKey X Y F u}

theorem mem_rvCorrespondence {S : SP M} {β β' : Type} {sβ : β → SortTag} {sβ' : β' → SortTag}
    {A : Set (β → M)} {A' : Set (β' → M)} {k : ℕ}
    {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k} {F : (β → M) → β' → M}
    {w : (Fin k ⊕ Fin k) → M} :
    w ∈ rvCorrespondence X Y F ↔ ∃ u ∈ X.U, w = rvKey X Y F u := Iff.rfl

theorem rvKey_mem {S : SP M} {β β' : Type} {sβ : β → SortTag} {sβ' : β' → SortTag}
    {A : Set (β → M)} {A' : Set (β' → M)} {k : ℕ}
    {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k} {F : (β → M) → β' → M}
    {z : (Fin k ⊕ β) → M} (hz : z ∈ X.lift) : rvKey X Y F (baseOf z) ∈ rvCorrespondence X Y F :=
  ⟨baseOf z, ((mem_lift X z).1 hz).2.1, rfl⟩

theorem rvKey_mem_of_mem {S : SP M} {β β' : Type} {sβ : β → SortTag} {sβ' : β' → SortTag}
    {A : Set (β → M)} {A' : Set (β' → M)} {k : ℕ}
    {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k} {F : (β → M) → β' → M} {u : β → M}
    (hu : u ∈ X.U) : rvKey X Y F u ∈ rvCorrespondence X Y F :=
  ⟨u, hu, rfl⟩

/-! ### The induced map on the canonical lifts -/

section LiftMap

variable {S : SP M} {β β' : Type} {sβ : β → SortTag} {sβ' : β' → SortTag}
  {A : Set (β → M)} {A' : Set (β' → M)} {k : ℕ}
  {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k} {F : (β → M) → β' → M}
  {Ā : Set ((Fin k ⊕ Fin k) → M)}

/-- The partner of the `VF`-coordinates of a point of `𝕃(U,f)`. -/
noncomputable def liftPartner (h : IsLift (rvCorrespondence X Y F) Ā) (z : X.lift) : Fin k → M :=
  rvPartner Ā (kOf z.1) (Y.f (F (baseOf z.1)))

theorem liftPartner_mem (h : IsLift (rvCorrespondence X Y F) Ā) (z : X.lift) :
    liftPartner (X := X) (Y := Y) (F := F) (Ā := Ā) h z ∈ rvDisc (Y.f (F (baseOf z.1))) ∧
      joinHalf (kOf z.1) (liftPartner (X := X) (Y := Y) (F := F) (Ā := Ā) h z) ∈ Ā :=
  rvPartner_mem (h (rvKey X Y F (baseOf z.1)) (rvKey_mem z.2)) (lift_hx z.2)

theorem liftPartner_unique (h : IsLift (rvCorrespondence X Y F) Ā) (z : X.lift)
    {y : Fin k → M} (hy : y ∈ rvDisc (Y.f (F (baseOf z.1))))
    (hA : joinHalf (kOf z.1) y ∈ Ā) :
    y = liftPartner (X := X) (Y := Y) (F := F) (Ā := Ā) h z :=
  eq_rvPartner (h (rvKey X Y F (baseOf z.1)) (rvKey_mem z.2)) (lift_hx z.2) hy hA

theorem liftPartner_unique' (h : IsLift (rvCorrespondence X Y F) Ā) (z : X.lift)
    {x : Fin k → M} (hx : x ∈ rvDisc (X.f (baseOf z.1)))
    (hA : joinHalf x (liftPartner (X := X) (Y := Y) (F := F) (Ā := Ā) h z) ∈ Ā) :
    x = rvPartner' Ā (liftPartner (X := X) (Y := Y) (F := F) (Ā := Ā) h z)
      (X.f (baseOf z.1)) :=
  eq_rvPartner' (h (rvKey X Y F (baseOf z.1)) (rvKey_mem z.2))
    (liftPartner_mem h z).1 hx hA

/-- **The value of the lift `F^↑` of `F`**: `z = (x̄, ū)` goes to `(ȳ, F ū)`, where `ȳ` is the
unique partner of `x̄` in the lifted relation over `(f(ū), (g∘F)(ū))`. -/
noncomputable def liftToFun (h : IsLift (rvCorrespondence X Y F) Ā)
    (hF : ∀ u ∈ X.U, F u ∈ Y.U) (z : X.lift) : Y.lift :=
  ⟨joinK (liftPartner (X := X) (Y := Y) (F := F) (Ā := Ā) h z) (F (baseOf z.1)), by
    rw [mem_lift]
    exact ⟨(liftPartner_mem h z).1.1, hF _ ((mem_lift X z.1).1 z.2).2.1,
      (liftPartner_mem h z).1.2⟩⟩

/-- *"`F^↑` is a function on `𝕃(U, f)`"*: its base coordinates are `F` applied to the base point. -/
theorem liftToFun_base (h : IsLift (rvCorrespondence X Y F) Ā)
    (hF : ∀ u ∈ X.U, F u ∈ Y.U) (z : X.lift) :
    baseOf (liftToFun (X := X) (Y := Y) (F := F) (Ā := Ā) h hF z).1 = F (baseOf z.1) := rfl

/-- *"each restriction `F^↑ : rv⁻¹(f(ū), ū) → rv⁻¹((g∘F)(ū), F(ū))` is a bijection"* at the level
of values: the `VF`-coordinates of `F^↑ z` are the partner of those of `z`, so they lie in the
`rv`-disc of `(g∘F)(ū)` and the pair lies in `Ā`. -/
theorem liftToFun_kOf (h : IsLift (rvCorrespondence X Y F) Ā)
    (hF : ∀ u ∈ X.U, F u ∈ Y.U) (z : X.lift) :
    kOf (liftToFun (X := X) (Y := Y) (F := F) (Ā := Ā) h hF z).1 ∈
        rvDisc (Y.f (F (baseOf z.1))) ∧
      joinHalf (kOf z.1) (kOf (liftToFun (X := X) (Y := Y) (F := F) (Ā := Ā) h hF z).1) ∈ Ā :=
  liftPartner_mem h z

/-- **Injectivity of `F^↑`** from injectivity of `F` on the `RV`-category bases. -/
theorem liftToFun_injective (h : IsLift (rvCorrespondence X Y F) Ā)
    (hF : ∀ u ∈ X.U, F u ∈ Y.U)
    (hFinj : ∀ u ∈ X.U, ∀ u' ∈ X.U, F u = F u' → u = u') :
    Function.Injective (liftToFun (X := X) (Y := Y) (F := F) (Ā := Ā) h hF) := by
  intro z z' heq
  have h1 : (liftToFun (X := X) (Y := Y) (F := F) (Ā := Ā) h hF z).1 =
      (liftToFun (X := X) (Y := Y) (F := F) (Ā := Ā) h hF z').1 := by rw [heq]
  have hbase : F (baseOf z.1) = F (baseOf z'.1) := by
    funext b
    have hb := congrFun h1 (Sum.inr b)
    simpa [liftToFun, joinK, baseOf] using hb
  have hb' : baseOf z.1 = baseOf z'.1 :=
    hFinj _ ((mem_lift X z.1).1 z.2).2.1 _ ((mem_lift X z'.1).1 z'.2).2.1 hbase
  have hpart : liftPartner (X := X) (Y := Y) (F := F) (Ā := Ā) h z =
      liftPartner (X := X) (Y := Y) (F := F) (Ā := Ā) h z' := by
    funext i
    have hp := congrFun h1 (Sum.inl i)
    simpa [liftToFun, joinK, kOf] using hp
  have hmem := liftPartner_mem (X := X) (Y := Y) (F := F) (Ā := Ā) h z
  have hmem' := liftPartner_mem (X := X) (Y := Y) (F := F) (Ā := Ā) h z'
  have hx' : kOf z'.1 ∈ rvDisc (X.f (baseOf z.1)) := by
    rw [hb']
    exact lift_hx z'.2
  have hA : joinHalf (kOf z'.1) (liftPartner (X := X) (Y := Y) (F := F) (Ā := Ā) h z) ∈ Ā := by
    have h2 := hmem'.2
    rw [← hpart] at h2
    exact h2
  have h1' := liftPartner_unique' (X := X) (Y := Y) (F := F) (Ā := Ā) h z hx' hA
  have h2' := liftPartner_unique' (X := X) (Y := Y) (F := F) (Ā := Ā) h z (lift_hx z.2) hmem.2
  have hkk : kOf z.1 = kOf z'.1 := by rw [h2', h1']
  refine Subtype.ext ?_
  rw [← joinK_kOf_baseOf (k := k) (β := β) z.1, ← joinK_kOf_baseOf (k := k) (β := β) z'.1,
    hkk, hb']

/-- **Surjectivity of `F^↑`** from surjectivity of `F` on the `RV`-category bases. -/
theorem liftToFun_surjective (h : IsLift (rvCorrespondence X Y F) Ā)
    (hF : ∀ u ∈ X.U, F u ∈ Y.U)
    (hFsurj : ∀ v ∈ Y.U, ∃ u ∈ X.U, F u = v) :
    Function.Surjective (liftToFun (X := X) (Y := Y) (F := F) (Ā := Ā) h hF) := by
  intro w
  obtain ⟨u, hu, hFu⟩ := hFsurj (baseOf w.1) ((mem_lift Y w.1).1 w.2).2.1
  have hy : kOf w.1 ∈ rvDisc (Y.f (F u)) := by
    rw [hFu]
    exact lift_hx w.2
  have hc := h (rvKey X Y F u) (rvKey_mem_of_mem (X := X) (Y := Y) (F := F) hu)
  have hmem := rvPartner'_mem (Ā := Ā) hc hy
  have hrv : rvPartner Ā (rvPartner' Ā (kOf w.1) (X.f u)) (Y.f (F u)) = kOf w.1 :=
    (eq_rvPartner (Ā := Ā) hc hmem.1 hy hmem.2).symm
  refine ⟨⟨joinK (rvPartner' Ā (kOf w.1) (X.f u)) u, ?_⟩, ?_⟩
  · rw [mem_lift]
    exact ⟨hmem.1.1, hu, hmem.1.2⟩
  · refine Subtype.ext ?_
    simp only [liftToFun, liftPartner, kOf_joinK, baseOf_joinK]
    rw [hrv, hFu, joinK_kOf_baseOf]

/-- **The bijection `𝕃(U,f) → 𝕃(V,g)` induced by a lifted `RV`-correspondence**: the paper's
*"each restriction `F^↑ : rv⁻¹(f(ū), ū) → rv⁻¹((g∘F)(ū), F(ū))` is a bijection"*, globally. -/
theorem liftToFun_bijective (h : IsLift (rvCorrespondence X Y F) Ā)
    (hF : ∀ u ∈ X.U, F u ∈ Y.U)
    (hFinj : ∀ u ∈ X.U, ∀ u' ∈ X.U, F u = F u' → u = u')
    (hFsurj : ∀ v ∈ Y.U, ∃ u ∈ X.U, F u = v) :
    Function.Bijective (liftToFun (X := X) (Y := Y) (F := F) (Ā := Ā) h hF) :=
  ⟨liftToFun_injective h hF hFinj, liftToFun_surjective h hF hFsurj⟩

/-- **`FiniteToFst` for the `RV`-correspondence**, straight from the paper's finite-fibre condition
*"for every `t̄ ∈ RV^k` the subset `(f'∘F)(f^{-1}(t̄))` is finite"* of Definition
\ref{defn:RV:cat} — i.e. from `RVHom.finite_fibres`. -/
theorem finiteToFst_rvCorrespondence (hfib : ∀ t : Fin k → M,
    {v : Fin k → M | ∃ u : β → M, u ∈ X.U ∧ X.f u = t ∧ v = Y.f (F u)}.Finite) :
    FiniteToFst (rvCorrespondence X Y F) := by
  intro x
  refine (hfib x).subset ?_
  rintro y hy
  obtain ⟨u, hu, hwu⟩ := mem_rvCorrespondence.1 hy
  have hinl : x = X.f u := by
    funext i
    have h := congrFun hwu (Sum.inl i)
    simpa [joinHalf, rvKey] using h
  have hinr : y = Y.f (F u) := by
    funext i
    have h := congrFun hwu (Sum.inr i)
    simpa [joinHalf, rvKey] using h
  exact ⟨u, hu, hinl.symm, hinr⟩

/-- **`FiniteToSnd` for the `RV`-correspondence`**, from the finite-to-one-ness of `Y` (the
`RV[k]` condition) together with injectivity of `F`. -/
theorem finiteToSnd_rvCorrespondence (hY : Y.FiniteToOne)
    (hF : ∀ u ∈ X.U, F u ∈ Y.U)
    (hFinj : ∀ u ∈ X.U, ∀ u' ∈ X.U, F u = F u' → u = u') :
    FiniteToSnd (rvCorrespondence X Y F) := by
  intro y
  have hmid : {u : β → M | u ∈ X.U ∧ Y.f (F u) = y}.Finite := by
    refine Set.Finite.of_finite_image (f := F) ?_ ?_
    · refine (hY y).subset ?_
      rintro v ⟨u, ⟨hu, hfu⟩, rfl⟩
      exact ⟨hF u hu, hfu⟩
    · intro u hu u' hu' heq
      exact hFinj u hu.1 u' hu'.1 heq
  refine Set.Finite.subset (hmid.image X.f) ?_
  rintro x hx
  obtain ⟨u, hu, hwu⟩ := mem_rvCorrespondence.1 hx
  have hinl : x = X.f u := by
    funext i
    have h := congrFun hwu (Sum.inl i)
    simpa [joinHalf, rvKey] using h
  have hinr : y = Y.f (F u) := by
    funext i
    have h := congrFun hwu (Sum.inr i)
    simpa [joinHalf, rvKey] using h
  exact ⟨u, ⟨hu, hinr.symm⟩, hinl.symm⟩

end LiftMap

/-! ## Part 5. Theorem \ref{RV:iso:class:lifted} and Corollary \ref{L:semigroup:hom} -/

/-- **The paper's hypothesis that the substructure `S` is `(VF, Γ)`-generated.**

*"Suppose that the substructure `S` is `(VF, Γ)`-generated."* (Theorem
\ref{RV:iso:class:lifted}).

Read through the only property the paper's proofs use (*"Since `S` is `(VF, Γ)`-generated, we may
assume that `φ(X̄)` does not contain parameters from `RV(S) ∖ rv(VF(S))`"*, proof of Lemma
\ref{exists:gamma:polynomial}): every `RV`-parameter of `S` is the `rv` of an element of the field
`VF(S)` generated by the `VF`-parameters.  Since `VF(S)` is a subfield of the valued field and
`rv` is defined on all of `VF`, this is `RV(S) ⊆ rv(VF(S))`, and it is stated here as the existence
of a single `VF`-witness per parameter (weakening it would be a different hypothesis, not the
paper's). -/
def IsVFGammaGenerated (S : SP M) : Prop :=
  ∀ j : Fin S.m, ∃ a : M, iVF a ∧ iRv a = S.rv j

/-- **Theorem \ref{RV:iso:class:lifted}** (paper.tex 1627), frozen statement.

*"Suppose that the substructure `S` is `(VF, Γ)`-generated.  Let `C ⊆ (RV^×)^n × (RV^×)^n` be a
definable subset such that both `pr_{≤n} ⌠ C` and `pr_{>n} ⌠ C` are finite-to-one.  Then there is a
definable subset `C^↑ ⊆ VF^n × VF^n` that lifts `C`."*

`(RV^×)^n × (RV^×)^n` is `Fin n ⊕ Fin n → M` at the sort `pairRVSort n`, `VF^n × VF^n` the same
index type at the sort `pairVFSort n`, "lifts" is `IsLift` (Definition \ref{def:lift}), and the two
finite-to-one projections are `FiniteToFst` / `FiniteToSnd`.

**The proof** (not formalized here — this is a statement) runs: by compactness reduce to the local
statement `Sec7Prereq.localLift`, which is the joint conclusion of Lemma \ref{exists:gamma:polynomial}
(`Sec7Prereq`, d2 of §7) and Lemma \ref{hensel:lemma} (the generalized Hensel lemma, d1 of §7).  The
§3–§6 results it also consumes are all in the tree: `SP.acl` (`QE/Sec3_frozen.lean`) for the
`t_n ∈ acl(t_1, …, t_{n-1})` of Lemma \ref{exists:gamma:polynomial}; the `rv`-polydisc and
`IsRVPullback` apparatus of §5 (`QE/Sec5.lean`, `SP.BijectiveOn`/`SP.IsLift` here); the
`RV`-fibre dimension layer of §4 (`QE/Sec4Dim.lean`); and the `(VF, Γ)`-generated hypothesis
`IsVFGammaGenerated` above. -/
def Theorem_7_6_stat (S : SP M) : Prop :=
  IsVFGammaGenerated S →
    ∀ {n : ℕ} (C : Set ((Fin n ⊕ Fin n) → M)),
      (∀ u ∈ C, IsRVUnitTuple u) → Definable S (pairRVSort n) C →
        FiniteToFst C → FiniteToSnd C →
          ∃ Ā : Set ((Fin n ⊕ Fin n) → M), Definable S (pairVFSort n) Ā ∧ IsLift C Ā

/-- **The two §7 lemmas that the proof of Theorem \ref{RV:iso:class:lifted} quotes, carried as an
explicit hypothesis** — never as `axiom`, never as `sorry`.

`localLift` is their *joint conclusion at one point*, which is all the proof of Theorem
\ref{RV:iso:class:lifted} uses before compactness.  The two paper sentences it comes from:

* Lemma \ref{exists:gamma:polynomial} (paper.tex 1562, §7 direction d2): *"Suppose that `S` is
  `(VF, Γ)`-generated.  Let `t̄ = (t_1, …, t_n) ∈ RV` with `t_n ∈ acl(t_1, …, t_{n-1})`.  Let
  `vrv(t̄) = (γ_1, …, γ_n) = γ̄ ∈ Γ`.  Then there is a `γ̄`-polynomial `F(X_1, …, X_n)` with
  coefficients in `VF(S)` such that `t̄` is a residue root of `F(X̄)` but is not a residue root of
  `∂F(X̄)/∂X_n`."*
* Lemma \ref{hensel:lemma} (Generalized Hensel's lemma, paper.tex 1513, §7 direction d1): *"Let
  `F_1(X̄), …, F_n(X̄)` be `γ̄`-polynomials with residue values `α_1, …, α_n`, where
  `γ̄ = (γ_1, …, γ_n) ∈ Γ`.  For every simple common residue root `t̄ = (t_1, …, t_n) ∈ RV` of
  `F_1(X̄), …, F_n(X̄)` there is a unique `ā ∈ rv^{-1}(t̄)` such that `F_i(ā) = 0` for every `i`."*

At one point `(t̄, s̄)` of `C` the two produce polynomials `H_i(X̄, Ȳ)` whose common zero set is, over
each `rv`-polydisc pair, the graph of a bijection — that is, a definable partial lift — and it
contains `(t̄, s̄)`.  That is `localLift` verbatim.  (The `α`'s and `γ̄`'s of the paper's two
sentences are consumed by Hensel inside this conclusion; the frozen encoding has no `Γ`-sort, so
`vrv` and the `γ̄`-polynomial condition cannot be written down here — see `QE/HANDOFF.md`.  What
*can* be, and is, written down is the conclusion the paper draws.) -/
structure Sec7Prereq (S : SP M) : Prop where
  /-- The joint conclusion, at one point, of `exists:gamma:polynomial` and `hensel:lemma`. -/
  localLift : ∀ {n : ℕ} (C : Set ((Fin n ⊕ Fin n) → M)) (u : (Fin n ⊕ Fin n) → M),
    IsRVUnitTuple u → u ∈ C → Definable S (pairRVSort n) C →
      FiniteToFst C → FiniteToSnd C →
        ∃ (C' Ā : Set ((Fin n ⊕ Fin n) → M)),
          C' ⊆ C ∧ u ∈ C' ∧ Definable S (pairRVSort n) C' ∧
            Definable S (pairVFSort n) Ā ∧ IsLift C' Ā

/-- **The reduction `§7's lemmas ⟹ Theorem \ref{RV:iso:class:lifted}`**, frozen as a `Prop`.

*"By compactness, the lemma is reduced to showing that for every `(t̄, s̄) ∈ C` there is a definable
lift of some subset of `C` that contains `(t̄, s̄)`."* — the paper's own proof of Theorem
\ref{RV:iso:class:lifted}.

**Open, and recorded rather than hidden**: the compactness step itself.  Covering the definable `C`
by finitely many of the local pieces `C'` of `Sec7Prereq.localLift` is compactness of the space of
definable types over an `ω`-saturated model; the tree has `SP.acl`/`SP.dcl` and
`Milestone0/Saturation.lean`, but no formalized compactness of the definable-type space, so this is
stated and not proved.  Nothing else in this file depends on it. -/
def Theorem_7_6_of_sec7 (S : SP M) : Prop :=
  Sec7Prereq S → Theorem_7_6_stat S

/-- **Corollary \ref{L:semigroup:hom}'s opening sentence, proved**: *"For any `RV[k, ·]`-isomorphism
`F : (U, f) → (V, g)` and any `ū ∈ U`, by definition, `wgt(f(ū)) = wgt((g ∘ F)(ū))`."*

`F` volumetric with a volumetric inverse on the same `k` forces equality of the weights (the paper
says "by definition", the inequality in both directions being the definition of the morphisms plus
`G ∘ F = id`). -/
theorem weight_eq_of_volumetric_inverse {S : SP M} {β β' : Type} {sβ : β → SortTag}
    {sβ' : β' → SortTag} {A : Set (β → M)} {A' : Set (β' → M)} {k : ℕ}
    {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k}
    {F : (β → M) → β' → M} {G : (β' → M) → β → M}
    (hF : ∀ u ∈ X.U, F u ∈ Y.U) (hG : ∀ v ∈ Y.U, G v ∈ X.U)
    (hGF : ∀ u ∈ X.U, G (F u) = u)
    (hvol : Volumetric X Y F) (hvol' : Volumetric Y X G) :
    ∀ u ∈ X.U, weight (X.f u) = weight (Y.f (F u)) := by
  intro u hu
  have h1 : weight (X.f u) ≤ weight (Y.f (F u)) := hvol u hu
  have h2 : weight (Y.f (F u)) ≤ weight (X.f (G (F u))) := hvol' (F u) (hF u hu)
  rw [hGF u hu] at h2
  exact le_antisymm h1 h2

/-- **The step of Corollary \ref{L:semigroup:hom}'s proof that Theorem \ref{RV:iso:class:lifted}
supplies**, proved here **from** `Theorem_7_6_stat` carried as an explicit hypothesis:

*"By Theorem \ref{RV:iso:class:lifted} there is a lift `C^↑` of `C`, which induces a `VF[k, ·]`-
isomorphism between `𝕃(U, f)` and `𝕃(V, g)`."*

The hypotheses are exactly Theorem \ref{RV:iso:class:lifted}'s, applied to the `RV`-correspondence
`C = rvCorrespondence X Y F` of the paper's proof of Corollary \ref{L:semigroup:hom}.  Note the two
bases `β`, `β'` are independent: the paper's `(U, f)` and `(V, g)` are objects of `RV[k,·]` over
possibly different arities, and the correspondence lives in `RV^k × RV^k` only. -/
theorem exists_lift_and_bijection_of_theorem_7_6 (S : SP M) (h76 : Theorem_7_6_stat S)
    {β β' : Type} {sβ : β → SortTag} {sβ' : β' → SortTag}
    {A : Set (β → M)} {A' : Set (β' → M)} {k : ℕ}
    {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k} {F : (β → M) → β' → M}
    {G : (β' → M) → β → M}
    (hgen : IsVFGammaGenerated S)
    (hF : ∀ u ∈ X.U, F u ∈ Y.U) (hG : ∀ v ∈ Y.U, G v ∈ X.U)
    (hGF : ∀ u ∈ X.U, G (F u) = u) (hFG : ∀ v ∈ Y.U, F (G v) = v)
    (hCdef : Definable S (pairRVSort k) (rvCorrespondence X Y F))
    (hCunit : ∀ u ∈ rvCorrespondence X Y F, IsRVUnitTuple u)
    (hfst : FiniteToFst (rvCorrespondence X Y F))
    (hsnd : FiniteToSnd (rvCorrespondence X Y F)) :
    ∃ (Ā : Set ((Fin k ⊕ Fin k) → M)) (h : IsLift (rvCorrespondence X Y F) Ā),
      Definable S (pairVFSort k) Ā ∧
        Function.Bijective (liftToFun (X := X) (Y := Y) (F := F) (Ā := Ā) h hF) := by
  obtain ⟨Ā, hdef, hlift⟩ := h76 hgen (rvCorrespondence X Y F) hCunit hCdef hfst hsnd
  refine ⟨Ā, hlift, hdef, ?_⟩
  refine liftToFun_bijective (X := X) (Y := Y) (F := F) (Ā := Ā) hlift hF ?_ ?_
  · intro u hu u' hu' heq
    rw [← hGF u hu, ← hGF u' hu', heq]
  · intro v hv
    exact ⟨G v, hG v hv, hFG v hv⟩

/-- **The step of Corollary \ref{L:semigroup:hom}'s proof, for a genuine `RV[k,·]`-isomorphism.**

`Φ : RVHom X Y` and `Ψ : RVHom Y X` are mutually inverse morphisms of `RV[k,·]` (the paper's
`RV[k,·]`-isomorphism).  From them the two finite-to-one hypotheses of Theorem
\ref{RV:iso:class:lifted} are **derived**, not assumed: `FiniteToFst` is literally
`RVHom.finite_fibres` (`finiteToFst_rvCorrespondence`), and `FiniteToSnd` follows from `Y.FiniteToOne`
(the `RV[k]` condition) and injectivity of `Φ` (`finiteToSnd_rvCorrespondence`).  What remains an
explicit hypothesis is only `hCdef` — the definability of `C = {(f(ū), (g∘F)(ū))}`, which is the
image of a definable set under a definable map, recorded as missing in `QE/Sec4Categories.lean`
("the one wall") — and `hCunit`, the paper's `C ⊆ (RV^×)^k × (RV^×)^k`. -/
theorem exists_lift_and_bijection_of_RVIso (S : SP M) (h76 : Theorem_7_6_stat S)
    {β β' : Type} {sβ : β → SortTag} {sβ' : β' → SortTag}
    {A : Set (β → M)} {A' : Set (β' → M)} {k : ℕ}
    {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k}
    (Φ : RVHom X Y) (Ψ : RVHom Y X)
    (hΨΦ : ∀ u ∈ X.U, Ψ.F (Φ.F u) = u) (hΦΨ : ∀ v ∈ Y.U, Φ.F (Ψ.F v) = v)
    (hgen : IsVFGammaGenerated S) (hYfin : Y.FiniteToOne)
    (hCdef : Definable S (pairRVSort k) (rvCorrespondence X Y Φ.F))
    (hCunit : ∀ u ∈ rvCorrespondence X Y Φ.F, IsRVUnitTuple u) :
    ∃ (Ā : Set ((Fin k ⊕ Fin k) → M)) (h : IsLift (rvCorrespondence X Y Φ.F) Ā),
      Definable S (pairVFSort k) Ā ∧
        Function.Bijective (liftToFun (X := X) (Y := Y) (F := Φ.F) (Ā := Ā) h Φ.F_maps) :=
  exists_lift_and_bijection_of_theorem_7_6 (S := S) h76 hgen Φ.F_maps Ψ.F_maps hΨΦ hΦΨ
    hCdef hCunit
    (finiteToFst_rvCorrespondence (X := X) (Y := Y) (F := Φ.F) Φ.finite_fibres)
    (finiteToSnd_rvCorrespondence (X := X) (Y := Y) (F := Φ.F) hYfin Φ.F_maps
      (fun u hu u' hu' h => by rw [← hΨΦ u hu, ← hΨΦ u' hu', h]))

/-- **Corollary \ref{L:semigroup:hom}** (paper.tex 1705), frozen statement, in the form the frozen
encoding carries.

*"Suppose that the substructure `S` is `(VF, Γ)`-generated.  The map `𝕃` induces surjective
homomorphisms between various Grothendieck semigroups, for example:
`𝕂𝕊𝔾 RV[k, ·] → 𝕂𝕊𝔾 VF[k, ·]`, `𝕂𝕊𝔾 RV[k] → 𝕂𝕊𝔾 VF[k]`."*

The Grothendieck-semigroup construction (`𝕂𝕊𝔾` of a category with finite coproducts) is direction
d4's definitions and is not duplicated here.  What *is* frozen, and proved below as
`corollary_7_7`, is the part of the proof that Theorem \ref{RV:iso:class:lifted} supplies: *"So `𝕃`
induces a map on the isomorphism classes"* — i.e. an `RV[k,·]`-isomorphism `F` together with a lift
of its `RV`-correspondence yields a bijection `𝕃(U,f) → 𝕃(V,g)`.  Surjectivity (the paper's "By
Corollary \ref{L:surjective} it is surjective") is §6's result and is not formalized here. -/
def Corollary_7_7_stat (S : SP M) : Prop :=
  IsVFGammaGenerated S → Theorem_7_6_stat S →
    ∀ {β β' : Type} {sβ : β → SortTag} {sβ' : β' → SortTag}
      {A : Set (β → M)} {A' : Set (β' → M)} {k : ℕ}
      (X : RVObj S sβ A k) (Y : RVObj S sβ' A' k)
      (Φ : RVHom X Y) (Ψ : RVHom Y X),
      (∀ u ∈ X.U, Ψ.F (Φ.F u) = u) → (∀ v ∈ Y.U, Φ.F (Ψ.F v) = v) → Y.FiniteToOne →
      Definable S (pairRVSort k) (rvCorrespondence X Y Φ.F) →
      (∀ u ∈ rvCorrespondence X Y Φ.F, IsRVUnitTuple u) →
      ∃ Ā : Set ((Fin k ⊕ Fin k) → M), Definable S (pairVFSort k) Ā ∧
        IsLift (rvCorrespondence X Y Φ.F) Ā ∧ ∃ Φlift : X.lift → Y.lift, Function.Bijective Φlift

/-- **Corollary \ref{L:semigroup:hom} holds as soon as Theorem \ref{RV:iso:class:lifted} does** —
proved here, with Theorem \ref{RV:iso:class:lifted} as an explicit hypothesis and no `axiom`. -/
theorem corollary_7_7 (S : SP M) : Corollary_7_7_stat S := by
  intro hgen h76 β β' sβ sβ' A A' k X Y Φ Ψ hΨΦ hΦΨ hYfin hCdef hCunit
  obtain ⟨Ā, h, hdef, hbij⟩ :=
    exists_lift_and_bijection_of_RVIso (S := S) h76 Φ Ψ hΨΦ hΦΨ hgen hYfin hCdef hCunit
  exact ⟨Ā, hdef, h, _, hbij⟩

/-! ## Part 6. `IsLift` is not vacuous: the diagonal -/

/-- The `rv`-diagonal `{(ū, ū)}`: a `C` for which a lift provably exists. -/
def rvDiag {n : ℕ} : Set ((Fin n ⊕ Fin n) → M) :=
  {u | IsRVTuple u ∧ fstHalf u = sndHalf u}

/-- The `VF`-diagonal `{(ā, ā)}` — the relation that is the identity bijection from every
`rv`-disc onto itself. -/
def vfDiag {n : ℕ} : Set ((Fin n ⊕ Fin n) → M) :=
  {z | IsVFTuple z ∧ fstHalf z = sndHalf z}

/-- **`IsLift` is satisfiable**: the `VF`-diagonal lifts the `rv`-diagonal.  (This is the
`S`-definable witness that Definition \ref{def:lift} is not a vacuous condition; note the two
hypotheses of Theorem \ref{RV:iso:class:lifted} — definability and finite-to-one projections — hold
for `rvDiag`, the first by the single equation `X_i = Y_i`.) -/
theorem isLift_vfDiag_rvDiag {n : ℕ} :
    IsLift (rvDiag (M := M) (n := n)) (vfDiag (M := M) (n := n)) := by
  rintro u ⟨-, hdiag⟩
  have key : ∀ x y : Fin n → M, x ∈ rvDisc (fstHalf u) → y ∈ rvDisc (sndHalf u) →
      joinHalf x y ∈ vfDiag (M := M) (n := n) → y = x := by
    intro x y _ _ hA
    exact (hA.2).symm
  constructor
  · intro x hx
    refine ⟨x, ⟨?_, ?_⟩, fun y hy => key x y hx hy.1 hy.2⟩
    · refine ⟨hx.1, ?_⟩
      rw [← hdiag]
      exact hx.2
    · refine ⟨fun i => ?_, rfl⟩
      cases i with
      | inl i => exact hx.1 i
      | inr i => exact hx.1 i
  · intro y hy
    refine ⟨y, ⟨?_, ?_⟩, fun x hx => (key x y hx.1 hy hx.2).symm⟩
    · refine ⟨hy.1, ?_⟩
      rw [hdiag]
      exact hy.2
    · refine ⟨fun i => ?_, rfl⟩
      cases i with
      | inl i => exact hy.1 i
      | inr i => exact hy.1 i

#print axioms SpecialTransformations.Milestone0.SP.isLift_vfDiag_rvDiag

end SP
end SpecialTransformations.Milestone0

/-! ## Axiom check -/

#print axioms SpecialTransformations.Milestone0.SP.BijectiveOn.fstMap_mem
#print axioms SpecialTransformations.Milestone0.SP.BijectiveOn.sndMap_fstMap
#print axioms SpecialTransformations.Milestone0.SP.BijectiveOn.fstMap_sndMap
#print axioms SpecialTransformations.Milestone0.SP.rvPartner_mem
#print axioms SpecialTransformations.Milestone0.SP.eq_rvPartner
#print axioms SpecialTransformations.Milestone0.SP.eq_rvPartner'
#print axioms SpecialTransformations.Milestone0.SP.mem_lift
#print axioms SpecialTransformations.Milestone0.SP.liftToFun_base
#print axioms SpecialTransformations.Milestone0.SP.liftToFun_kOf
#print axioms SpecialTransformations.Milestone0.SP.liftToFun_injective
#print axioms SpecialTransformations.Milestone0.SP.liftToFun_surjective
#print axioms SpecialTransformations.Milestone0.SP.liftToFun_bijective
#print axioms SpecialTransformations.Milestone0.SP.finiteToFst_rvCorrespondence
#print axioms SpecialTransformations.Milestone0.SP.finiteToSnd_rvCorrespondence
#print axioms SpecialTransformations.Milestone0.SP.weight_eq_of_volumetric_inverse
#print axioms SpecialTransformations.Milestone0.SP.exists_lift_and_bijection_of_theorem_7_6
#print axioms SpecialTransformations.Milestone0.SP.exists_lift_and_bijection_of_RVIso
#print axioms SpecialTransformations.Milestone0.SP.corollary_7_7
