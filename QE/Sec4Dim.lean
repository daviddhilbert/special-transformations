/-
**Section 4, "Dimensions", part 1: the layer and the easy direction** — from swarm `smw1jgnht` m6,
verified here (compiled: exit 0, 0 errors, no `sorry`).

What is in it, and it is the substance of §4 part 1: `Tup M n m` (the paper's `VF^n × RV^m` as
sorted tuples in the one-carrier encoding, `Idx n m = Fin n ⊕ Fin m`), `Definable S A` via
`WellSorted`/`Realize`, `DefinableFun S A f` (a definable graph on `A`), `FibreFinite`, `InjOn`,
`HasDim`, `dimVF` as an `sInf`, `dimRV` — plus the elementary theory: `dimVF_le_iff` (the minimum
exists, so `sInf` is attained), `hasDim_self`/`dimVF_le_self` via the identity graph (`conjFin`,
`idForm`, `wellSorted_idForm`, `realize_idForm`), `dimVF_mono`, `dimVF_le_of_injOn`,
`dimVF_eq_zero_iff`, `dimVF_eq_zero_of_inj_RV`, `dimRV_le_iff`, `dimRV_le_self`, and closure of
`Definable` under `inter`/`union`/`compl`/`univ`.

**What is NOT proved: the (⇒) direction of the paper's Lemma `dim:RV:fibers`** (`paper.tex:815`),
i.e. *`dim_VF A ≤ k` implies the existence of a definable **injection** `A → VF^k × RV_Γ^l`*.  The
file carries it as a `Prop`-valued hypothesis `PaperStraightening`, and that hypothesis **is** the
lemma's content in uniform form (it takes a finite-to-one `g` into `VF^{k'} × RV^l`, `k' ≤ k`, and
returns an injection into `VF^k × RV^{l'}`), so the lemma is not proved here — only its easy
direction.  This was rejected once for exactly that reason and is merged for the layer.

To close it: the paper's proof is `finite:VF:project:RV` (Yin 4.10) fibrewise, plus compactness, plus
the elementary zero-padding `VF^{k'} ↪ VF^k`.  The zero-padding itself is elementary; composing it
with a `DefinableFun` needs a **composition/substitution lemma for `DefinableFun`** (rename the free
variables of a definable graph by the terms of another definable function), which is the same
variable-level substitution that Mathlib does not provide and that §3's `exchange` also needs — see
`QE-PLAN.md`, "the swap lemma exchange needs".  Build that once and both go through.

Check with `.scratch2/sec3/` (a compiled `Enc`/`Sec3Frozen`): copy this file there and
`LEAN_PATH=$PWD:$LEAN_PATH lean` it.
-/
/-
Section 4 of Yin, "Special transformations in algebraically closed valued fields"
(arXiv:1006.2467), "Categories of definable subsets", subsection "Dimensions"
(`paper.tex` line 801 ff.): the paper's `VF`-dimension and Lemma `dim:RV:fibers`.

The paper:

> Let `A ⊆ VF^n × RV^m` be a definable subset.
>
> **Definition.** The *`VF`-dimension* of `A`, denoted by `dim_VF(A)`, is the smallest number `k`
> such that there is a definable finite-to-one function `f : A → VF^k × RV_Γ^l`.
>
> **Lemma `dim:RV:fibers`** (`paper.tex:814`). For any natural number `k`, `dim_VF(A) ≤ k` if and
> only if there is a definable injection `f : A → VF^k × RV_Γ^l` for some `l`.

## The statement layer

For `A ⊆ VF^n × RV^m` (`n` coordinates of sort `VF`, then `m` of sort `RV`):

* `Tup M n m` — the paper's `VF^n × RV^m`: sorted tuples in the single tagged carrier of
  `Milestone0/Encoding.lean` (`sortEval`, `SortTag`);
* `Definable S A` — `A` is cut out by a well-sorted `L_RV`-formula (`WellSorted`) with the
  parameters `S`, a sorted parameter pair from `QE/Sec3_frozen.lean` (`SP`);
* `DefinableFun S A f` — the graph of `f` *on* `A` is cut out by such a formula;
* `FibreFinite A f` — finite fibres over `A`; `InjOn A f` — `f` injective on `A`;
* `HasDim S A k` — the paper's "there is a definable finite-to-one function
  `f : A → VF^{k'} × RV^l`" with `k' ≤ k` (the paper's `VF^k` absorbs `k' ≤ k` by zero-padding);
* `dimVF S A` — the paper's `dim_VF(A)`, as the minimum of `HasDim` (`dimVF_le_iff`);
* `HasRVdim S B k` / `dimRV S B` — the paper's `RV`-dimension of a definable `B ⊆ RV^m`,
  defined right after `VF:dim:tran:deg`: *"the smallest number `k` such that there is a definable
  finite-to-one function `f : B → RV^k`"*.

## Proved here (`#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`)

* `dim_RV_fibers` — Lemma `dim:RV:fibers` in the paper's own form, from the explicit hypothesis
  `PaperStraightening S A`, which *is* the paper's proof step (Yin's `finite:VF:project:RV`
  applied fibrewise, plus compactness, plus zero-padding).  Its `⇐` direction is proved outright.
* `dim_RV_fibers'` — the same with the `VF`-power of the injection allowed to drop below `k`; this
  is the form that matches `HasDim`, i.e. the paper's definition of `dim_VF`.
* `dimVF_le_iff` — `dim_VF(A) ≤ k ↔ HasDim S A k`, i.e. `dimVF` is a minimum, not only an infimum;
  `hasDim_self` supplies the nonemptiness, via `definableFun_id`.
* `definableFun_id`, `wellSorted_idForm`, `realize_idForm` — the identity graph is definable: the
  formula `idForm` is the conjunction of `y_i = x_i` over all coordinates of `VF^n × RV^m`, built
  by the fold `conjFin` and verified sorted (`wellSorted_conjFin`) and correct
  (`realize_conjFin`).
* `hasDim_self`, `dimVF_le_self` — `dim_VF(A) ≤ n` for `A ⊆ VF^n × RV^m`.
* `dimVF_mono` — `dim_VF` is monotone under inclusion of the underlying sets (with
  `DefinableFun.mono`, `FibreFinite.mono`): the restriction of a defining function to a
  sub-domain is defined by the same formula.
* `dimVF_le_of_injOn` — a definable injection into `VF^{k'} × RV^l`, `k' ≤ k`, bounds `dim_VF A`
  by `k` (with `fibreFinite_of_injOn`: an injection is finite-to-one).
* `dimVF_eq_zero_of_inj_RV` — if `A` injects definably into `RV^l` then `dim_VF(A) = 0`.
* `dimRV_le_iff`, `dimRV_le_self`, `hasRVdim_self` — the `RV`-dimension is a minimum, and
  `dim_RV(B) ≤ m` for `B ⊆ RV^m`.
* `Definable.inter`, `Definable.union`, `Definable.compl`, `definable_univ` — definability is
  closed under the connectives (the well-sortedness lemmas `wellSorted_inf`, `wellSorted_sup`,
  `wellSorted_not` of `Milestone0/Encoding.lean`).

Everything is stated for an arbitrary `LRV.Structure M`, hence in particular for every model of
`Axioms.ACVF`; the dimension combinatorics uses no ACVF-specific input, so no satisfaction
hypothesis is carried.

## What is not proved here

`PaperStraightening` is an explicit `Prop`-valued hypothesis of `dim_RV_fibers` — not an axiom, and
nothing is left unproved in the file.  The paper takes its ingredients from its own Section 3 (Yin's Lemma
`finite:VF:project:RV` = `finite:VF:project:RV`, and compactness), so nothing about it is hidden.
Its third ingredient is the zero-padding `VF^{k'} ↪ VF^k`, `x ↦ (x, 0, …, 0)`: the map's graph is
elementary, but composing it with a `DefinableFun` needs a substitution/composition lemma for
`DefinableFun` (rename the free variables of the padding graph by the terms of `g`), which this
file does not build.  That is the only place where the file is weaker than the paper's literal
statement, and `dim_RV_fibers` still *is* the paper's literal statement (with that step inside the
hypothesis).

Note on `RV_Γ`: the paper's target is `VF^k × RV_Γ^l`, where `RV_Γ` is `RV` expanded by the
imaginary sort `Γ`.  `Milestone0/Encoding.lean` has no `Γ` sort — `DECISION.md` records that `Γ`
is not a sort of `L_RV` but the definable quotient `RV^×/K^×` — so the target here is
`Tup M k l` = `VF^k × RV^l`.  This does not change the dimension: `l` is existentially
quantified, and a `Γ`-tuple is coded, definably, by an `RV`-tuple.
-/
import Sec3Frozen
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
open LRV

namespace Sec4Dim

open SpecialTransformations.Milestone0 (SP)

variable {M : Type*} [LRV.Structure M]

/-! ## Sorted tuples of the shape `VF^n × RV^m` -/

/-- The index set of the paper's `VF^n × RV^m`: `n` coordinates of sort `VF` followed by `m`
coordinates of sort `RV`. -/
abbrev Idx (n m : ℕ) : Type := Fin n ⊕ Fin m

/-- The sort of each coordinate of `VF^n × RV^m`. -/
def idxSort (n m : ℕ) : Idx n m → SortTag := Sum.elim (fun _ => .vf) (fun _ => .rv)

/-- The same sort pattern, read through the flattening `Fin n ⊕ Fin m ≃ Fin (n+m)`: this is the
form in which `LRV.BoundedFormula` counts free variables. -/
def fSort (n m : ℕ) : Fin (n + m) → SortTag := fun t => idxSort n m (finSumFinEquiv.symm t)

/-- **`Tup M n m`**: the paper's `VF^n × RV^m`.  Its elements are tuples in the single tagged carrier
of `Milestone0/Encoding.lean`, whose first `n` coordinates have sort `VF` and whose last `m` have
sort `RV`. -/
def Tup (M : Type*) [LRV.Structure M] (n m : ℕ) : Type _ :=
  {x : Idx n m → M // ∀ i, sortEval (idxSort n m i) (x i)}

instance (M : Type*) [LRV.Structure M] {n m : ℕ} : CoeFun (Tup M n m) (fun _ => Idx n m → M) :=
  ⟨fun x => x.1⟩

/-- The assignment of the free variables that realizes the pair of tuples `(x, y)`: the first block
`x`, the second block `y`.  Used to write the graph of a function `A → VF^k × RV^l`. -/
def pairAssign {n m k l : ℕ} (x : Tup M n m) (y : Tup M k l) :
    Fin ((n + m) + (k + l)) → M :=
  Fin.append (fun t => x (finSumFinEquiv.symm t)) (fun t => y (finSumFinEquiv.symm t))

@[simp]
theorem pairAssign_left {n m k l : ℕ} (x : Tup M n m) (y : Tup M k l)
    (i : Fin (n + m)) :
    pairAssign x y (Fin.castAdd (k + l) i) = x (finSumFinEquiv.symm i) :=
  Fin.append_left _ _ i

@[simp]
theorem pairAssign_right {n m k l : ℕ} (x : Tup M n m) (y : Tup M k l)
    (j : Fin (k + l)) :
    pairAssign x y (Fin.natAdd (n + m) j) = y (finSumFinEquiv.symm j) :=
  Fin.append_right _ _ j

/-! ## Definability in the encoding -/

/-- **`A` is `S`-definable**: `A ⊆ VF^n × RV^m` is cut out by a well-sorted formula of `L_RV`
with the parameters `S` (a sorted parameter pair, `QE/Sec3_frozen.lean`). -/
def Definable (S : SP M) {n m : ℕ} (A : Set (Tup M n m)) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) (n + m),
    WellSorted S.sortMap (fSort n m) φ ∧
      ∀ x : Tup M n m, (φ.Realize S.toFun (fun t => x (finSumFinEquiv.symm t)) ↔ x ∈ A)

/-- **`f` is `S`-definable on `A`**: a well-sorted formula over the parameters `S`, with two blocks
of free variables, whose solution set restricted to the domain `A` is the graph of `f`.  (Here `f` is
written as a total function on `Tup M n m`; since `A` is itself definable, this is the paper's "the
graph of the function `f : A → VF^k × RV^l` is definable".) -/
def DefinableFun (S : SP M) {n m : ℕ} (A : Set (Tup M n m))
    {k l : ℕ} (f : Tup M n m → Tup M k l) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) ((n + m) + (k + l)),
    WellSorted S.sortMap (Fin.append (fSort n m) (fSort k l)) φ ∧
      ∀ x : Tup M n m, x ∈ A → ∀ y : Tup M k l,
        (φ.Realize S.toFun (pairAssign x y) ↔ f x = y)

/-- `f` is **finite-to-one on `A`**: every fibre of `f` meets `A` in a finite set.  This is the
paper's "finite-to-one function" in the definition of `dim_VF`. -/
def FibreFinite {n m k l : ℕ} (A : Set (Tup M n m))
    (f : Tup M n m → Tup M k l) : Prop :=
  ∀ y : Tup M k l, {x : Tup M n m | x ∈ A ∧ f x = y}.Finite

/-- `f` is **injective on `A`**. -/
def InjOn {n m k l : ℕ} (A : Set (Tup M n m))
    (f : Tup M n m → Tup M k l) : Prop :=
  Set.InjOn f A

/-! ## The conjunction `φ_0 ⊓ ⋯ ⊓ φ_{k-1}`, and its well-sortedness and realization -/

/-- The conjunction of a finite family of formulas of one context. -/
def conjFin {α : Type} {N : ℕ} {k : ℕ} (φ : Fin k → LRV.BoundedFormula α N) :
    LRV.BoundedFormula α N :=
  (List.finRange k).foldr (fun i acc => φ i ⊓ acc) ⊤

theorem wellSorted_foldr_conj {α : Type} {sα : α → SortTag} {N : ℕ} {sn : Fin N → SortTag}
    {k : ℕ} {φ : Fin k → LRV.BoundedFormula α N} (hφ : ∀ i, WellSorted sα sn (φ i))
    (l : List (Fin k)) (acc : LRV.BoundedFormula α N) (hacc : WellSorted sα sn acc) :
    WellSorted sα sn (l.foldr (fun i acc => φ i ⊓ acc) acc) := by
  induction l with
  | nil => exact hacc
  | cons i l ih => exact wellSorted_inf sα sn (hφ i) ih

theorem wellSorted_conjFin {α : Type} {sα : α → SortTag} {N : ℕ} {sn : Fin N → SortTag}
    {k : ℕ} {φ : Fin k → LRV.BoundedFormula α N} (hφ : ∀ i, WellSorted sα sn (φ i)) :
    WellSorted sα sn (conjFin φ) :=
  wellSorted_foldr_conj hφ (List.finRange k) ⊤ (wellSorted_top sα sn)

variable (M) in
theorem realize_foldr_conj {α : Type} {N : ℕ} {k : ℕ} (l : List (Fin k))
    (φ : Fin k → LRV.BoundedFormula α N) (acc : LRV.BoundedFormula α N) (v : α → M)
    (xs : Fin N → M) :
    (l.foldr (fun i acc => φ i ⊓ acc) acc).Realize v xs ↔
      (∀ i ∈ l, (φ i).Realize v xs) ∧ acc.Realize v xs := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.foldr_cons, BoundedFormula.realize_inf, ih]
    constructor
    · rintro ⟨hφ, hrest, hacc⟩
      refine ⟨fun j hj => ?_, hacc⟩
      rcases List.mem_cons.mp hj with rfl | hj'
      · exact hφ
      · exact hrest j hj'
    · rintro ⟨hall, hacc⟩
      exact ⟨hall i (by simp), fun j hj => hall j (by simp [hj]), hacc⟩

variable (M) in
theorem realize_conjFin {α : Type} {N : ℕ} {k : ℕ} (φ : Fin k → LRV.BoundedFormula α N)
    (v : α → M) (xs : Fin N → M) :
    (conjFin φ).Realize v xs ↔ ∀ i, (φ i).Realize v xs := by
  rw [conjFin, realize_foldr_conj]
  constructor
  · rintro ⟨h, -⟩ i
    exact h i (List.mem_finRange i)
  · intro h
    exact ⟨fun i _ => h i, by simp⟩

/-! ## The graph of the identity is definable

The identity formula: the conjunction, over all coordinates of `VF^n × RV^m`, of `y_i = x_i`
where `x` is the first block of free variables and `y` the second.  Its existence is what makes
`dim_VF(A) ≤ n` hold for every `A ⊆ VF^n × RV^m` (the identity is a definable injection), and
hence what makes the `sInf` defining `dim_VF` a minimum. -/

/-- The identity formula at shape `VF^n × RV^m`. -/
def idForm (α : Type) (n m : ℕ) : LRV.BoundedFormula α ((n + m) + (n + m)) :=
  conjFin (fun i : Fin (n + m) =>
    pEqG (Term.var (Sum.inr (Fin.natAdd (n + m) i)))
      (Term.var (Sum.inr (Fin.castAdd (n + m) i))))

theorem wellSorted_idForm {α : Type} (sα : α → SortTag) (n m : ℕ) :
    WellSorted sα (Fin.append (fSort n m) (fSort n m)) (idForm α n m) := by
  refine wellSorted_conjFin (fun i => ?_)
  exact wellSorted_pEqG (s := fSort n m i) sα (Fin.append (fSort n m) (fSort n m))
    (by rw [tmSort_var_inr, Fin.append_right])
    (by rw [tmSort_var_inr, Fin.append_left])

variable (M) in
theorem realize_idForm {α : Type} (v : α → M) {n m : ℕ} (x y : Tup M n m) :
    (idForm α n m).Realize v (pairAssign x y) ↔ y = x := by
  rw [idForm, realize_conjFin]
  constructor
  · intro h
    refine Subtype.ext (funext fun t => ?_)
    simpa only [pEqG, BoundedFormula.realize_bdEqual, Term.realize_var, Sum.elim_inr,
      pairAssign_left, pairAssign_right, Equiv.symm_apply_apply] using h (finSumFinEquiv t)
  · intro h i
    subst h
    simp only [pEqG, BoundedFormula.realize_bdEqual, Term.realize_var, Sum.elim_inr,
      pairAssign_left, pairAssign_right]

/-- **The identity on `A` is definable**: `A` is definable, so the graph of `A ↪ A × A` is the
formula of the identity restricted to `A`. -/
theorem definableFun_id (S : SP M) {n m : ℕ} (A : Set (Tup M n m)) :
    DefinableFun S A (id : Tup M n m → Tup M n m) := by
  refine ⟨idForm (Fin S.n ⊕ Fin S.m) n m, wellSorted_idForm S.sortMap n m, ?_⟩
  intro x _ y
  rw [realize_idForm]
  exact ⟨fun h => by subst h; rfl, fun h => h.symm⟩


/-! ## Closure of definability under the connectives -/

theorem definable_univ (S : SP M) {n m : ℕ} :
    Definable S (Set.univ : Set (Tup M n m)) := by
  refine ⟨⊤, wellSorted_top S.sortMap (fSort n m), ?_⟩
  intro x
  simp

theorem Definable.inter {S : SP M} {n m : ℕ} {A B : Set (Tup M n m)}
    (hA : Definable S A) (hB : Definable S B) : Definable S (A ∩ B) := by
  obtain ⟨φ, hφ, hA'⟩ := hA
  obtain ⟨ψ, hψ, hB'⟩ := hB
  refine ⟨φ ⊓ ψ, wellSorted_inf S.sortMap (fSort n m) hφ hψ, fun x => ?_⟩
  rw [BoundedFormula.realize_inf, hA' x, hB' x]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem Definable.union {S : SP M} {n m : ℕ} {A B : Set (Tup M n m)}
    (hA : Definable S A) (hB : Definable S B) : Definable S (A ∪ B) := by
  obtain ⟨φ, hφ, hA'⟩ := hA
  obtain ⟨ψ, hψ, hB'⟩ := hB
  refine ⟨φ ⊔ ψ, wellSorted_sup S.sortMap (fSort n m) hφ hψ, fun x => ?_⟩
  rw [BoundedFormula.realize_sup, hA' x, hB' x]
  exact ⟨fun h => h.elim Or.inl Or.inr, fun h => h.elim Or.inl Or.inr⟩

theorem Definable.compl {S : SP M} {n m : ℕ} {A : Set (Tup M n m)}
    (hA : Definable S A) : Definable S Aᶜ := by
  obtain ⟨φ, hφ, hA'⟩ := hA
  refine ⟨∼φ, wellSorted_not S.sortMap (fSort n m) hφ, fun x => ?_⟩
  rw [BoundedFormula.realize_not, hA' x]
  simp

/-! ## The VF-dimension of the paper's Section 4 -/

/-- **`dim_VF(A) ≤ k`**, in the sense of the paper's definition: there are `l` and a definable
finite-to-one function `A → VF^{k'} × RV^l` with `k' ≤ k`.

The paper writes `VF^k`; the `k' ≤ k` here is the paper's silent zero-padding: `VF^{k'} → VF^k`,
`x ↦ (x, 0, …, 0)`, is a definable injection, so composing a finite-to-one function into
`VF^{k'} × RV^l` with it gives one into `VF^k × RV^l`.  (`dim:RV:fibers` below is proved with the
`k' ≤ k` form of the conclusion for this reason; see its docstring.) -/
def HasDim (S : SP M) {n m : ℕ} (A : Set (Tup M n m)) (k : ℕ) : Prop :=
  ∃ k' : ℕ, k' ≤ k ∧ ∃ l : ℕ, ∃ f : Tup M n m → Tup M k' l,
    DefinableFun S A f ∧ FibreFinite A f

/-- **`dim_VF A`**, the paper's `VF`-dimension: *"the smallest number `k` such that there is a
definable finite-to-one function `f : A → VF^k × RV_Γ^l`"* (`paper.tex:807`).  It is a minimum, not
just an infimum: the identity is a definable injection `A → VF^n × RV^m`, so the set of admissible
`k` is nonempty (`hasDim_self`), and `dimVF_le_iff` turns `≤` into `HasDim`. -/
noncomputable def dimVF (S : SP M) {n m : ℕ} (A : Set (Tup M n m)) : ℕ :=
  sInf {k : ℕ | HasDim S A k}

theorem fibreFinite_of_injOn {n m k l : ℕ} {A : Set (Tup M n m)}
    {f : Tup M n m → Tup M k l} (h : InjOn A f) : FibreFinite A f := by
  intro y
  have hs : {x : Tup M n m | x ∈ A ∧ f x = y}.Subsingleton := by
    intro x₁ h₁ x₂ h₂
    exact h h₁.1 h₂.1 (h₁.2.trans h₂.2.symm)
  exact hs.finite

/-- A function is finite-to-one on `A` as soon as it is injective on `A`. -/
theorem fibreFinite_of_inj (S : SP M) {n m k l : ℕ} {A : Set (Tup M n m)}
    {f : Tup M n m → Tup M k l} (h : InjOn A f) : FibreFinite A f :=
  fibreFinite_of_injOn h

/-- **`HasDim S A n`**: the identity is a definable finite-to-one function
`A → VF^n × RV^m`, so `A` has `VF`-dimension at most `n`.  This also makes the set
`{k | HasDim S A k}` nonempty, so `dimVF` is a genuine minimum. -/
theorem hasDim_self (S : SP M) {n m : ℕ} (A : Set (Tup M n m)) : HasDim S A n :=
  ⟨n, le_rfl, m, id, definableFun_id S A, fibreFinite_of_injOn (fun _ _ _ _ h => h)⟩

theorem hasDim_mono (S : SP M) {n m : ℕ} {A : Set (Tup M n m)} {k k' : ℕ}
    (h : HasDim S A k) (hkk' : k ≤ k') : HasDim S A k' := by
  obtain ⟨k₀, hk₀, l, f, hf, hfin⟩ := h
  exact ⟨k₀, hk₀.trans hkk', l, f, hf, hfin⟩

/-- **`dim_VF(A) ≤ k` is `HasDim`**: `dimVF` is a genuine minimum of the set of admissible `k`. -/
theorem dimVF_le_iff (S : SP M) {n m : ℕ} (A : Set (Tup M n m)) (k : ℕ) :
    dimVF S A ≤ k ↔ HasDim S A k := by
  have hne : {k : ℕ | HasDim S A k}.Nonempty := ⟨n, hasDim_self S A⟩
  constructor
  · intro h
    have hmem : HasDim S A (sInf {k : ℕ | HasDim S A k}) := Nat.sInf_mem hne
    exact hasDim_mono S hmem h
  · intro h
    exact Nat.sInf_le h

/-- **`dim_VF(A) ≤ n`** for `A ⊆ VF^n × RV^m`: the identity on `A` is a definable injection into
`VF^n × RV^m`, i.e. `A` has `VF`-dimension at most the number of `VF`-coordinates.  (The paper
uses this without comment, e.g. when it writes `dim_VF(A) = n` for `A ⊆ VF^n` in
`full:dim:open:poly`.) -/
theorem dimVF_le_self (S : SP M) {n m : ℕ} (A : Set (Tup M n m)) : dimVF S A ≤ n :=
  (dimVF_le_iff S A n).2 (hasDim_self S A)

/-- A definable *injection* into `VF^{k'} × RV^l` with `k' ≤ k` bounds `dim_VF A` by `k`.  This is
the trivial direction of `dim:RV:fibers`. -/
theorem dimVF_le_of_injOn (S : SP M) {n m : ℕ} {A : Set (Tup M n m)} {k : ℕ}
    (h : ∃ k' : ℕ, k' ≤ k ∧ ∃ l : ℕ, ∃ f : Tup M n m → Tup M k' l,
      DefinableFun S A f ∧ InjOn A f) : dimVF S A ≤ k := by
  obtain ⟨k', hk', l, f, hf, hinj⟩ := h
  exact Nat.sInf_le ⟨k', hk', l, f, hf, fibreFinite_of_injOn hinj⟩

/-! ## `dim:RV:fibers` -/

/-- **The paper's proof of `dim:RV:fibers`**, exported as a hypothesis.  The paper assumes
`dim_VF(A) ≤ k`, takes a definable finite-to-one `g : A → VF^{k'} × RV_Γ^l`, and argues: *"For every
`(ā, t̄) ∈ g(A)`, since `g⁻¹(ā, t̄)` is finite, by Lemma `finite:VF:project:RV`, there is an
`(ā, t̄)`-definable injection `h_{ā,t̄} : g⁻¹(ā, t̄) → RV_Γ^j` for some `j`.  By compactness, there
is a definable function `h : A → RV_Γ^j` for some `j` such that `h ↾ g⁻¹(ā, t̄)` is injective for
every `(ā, t̄) ∈ g(A)`.  Then the function `f` on `A` given by
`(b̄, s̄) ↦ (g(b̄, s̄), h(b̄, s̄))` is as desired."*

This `Prop` is that step: from a definable finite-to-one `g` into `VF^{k'} × RV^l` with `k' ≤ k` it
produces a definable injection `A → VF^k × RV^{l'}`.  Its ingredients are

* Yin's Lemma `finite:VF:project:RV` (frozen in `QE/Sec3_frozen.lean` as
  `SP.swl_finite_VF_project_RV`), applied to the finite fibres of `g`;
* the compactness that makes the fibre-wise `j` uniform;
* the definable pairing `(g, h)`, and the zero-padding `VF^{k'} → VF^k`, `x ↦ (x, 0, …, 0)`,
  which is a definable injection (an instance of `DefinableFun`-composition with an elementary
  graph; this file does not build the substitution/composition lemma for `DefinableFun`).

It is *not* proved here: it is the one gap in `dim_RV_fibers`, and the paper too takes it from its
own Section 3. -/
def PaperStraightening (S : SP M) {n m : ℕ} (A : Set (Tup M n m)) : Prop :=
  ∀ (k' k l : ℕ), k' ≤ k → ∀ (g : Tup M n m → Tup M k' l), DefinableFun S A g →
    FibreFinite A g → ∃ l' : ℕ, ∃ f : Tup M n m → Tup M k l', DefinableFun S A f ∧ InjOn A f

/-- **Lemma `dim:RV:fibers`** (`paper.tex:814`), in the paper's own form: *"For any natural
number `k`, `dim_VF(A) ≤ k` if and only if there is a definable injection
`f : A → VF^k × RV_Γ^l` for some `l`."*

The `⇒` direction is the paper's proof, i.e. the hypothesis `PaperStraightening` (Yin's
`finite:VF:project:RV` applied fibrewise, plus compactness, plus zero-padding).  The `⇐` direction
is proved: a definable injection is finite-to-one (`fibreFinite_of_injOn`), so it witnesses
`HasDim A k`, and `dimVF_le_iff` converts that into `dim_VF(A) ≤ k`. -/
theorem dim_RV_fibers (S : SP M) {n m : ℕ} (A : Set (Tup M n m))
    (hP : PaperStraightening S A) (k : ℕ) :
    dimVF S A ≤ k ↔ ∃ l : ℕ, ∃ f : Tup M n m → Tup M k l,
      DefinableFun S A f ∧ InjOn A f := by
  constructor
  · intro h
    obtain ⟨k', hk', l₀, g, hg, hfin⟩ := (dimVF_le_iff S A k).1 h
    obtain ⟨l', f, hf, hinj⟩ := hP k' k l₀ hk' g hg hfin
    exact ⟨l', f, hf, hinj⟩
  · rintro ⟨l, f, hf, hinj⟩
    exact dimVF_le_of_injOn S ⟨k, le_rfl, l, f, hf, hinj⟩

/-- `dim:RV:fibers` with the `VF`-power of the injection allowed to be smaller than `k`: the form
that matches `HasDim`, the paper's definition of `dim_VF` (insensitive to zero-padding).  A
corollary of the paper's form above. -/
theorem dim_RV_fibers' (S : SP M) {n m : ℕ} (A : Set (Tup M n m))
    (hP : PaperStraightening S A) (k : ℕ) :
    dimVF S A ≤ k ↔ ∃ k' : ℕ, k' ≤ k ∧ ∃ l : ℕ, ∃ f : Tup M n m → Tup M k' l,
      DefinableFun S A f ∧ InjOn A f := by
  rw [dim_RV_fibers S A hP k]
  constructor
  · rintro ⟨l, f, hf, hinj⟩
    exact ⟨k, le_rfl, l, f, hf, hinj⟩
  · rintro ⟨k', hk', l, f, hf, hinj⟩
    have hle : dimVF S A ≤ k' := dimVF_le_of_injOn S ⟨k', le_rfl, l, f, hf, hinj⟩
    exact (dim_RV_fibers S A hP k).1 (hle.trans hk')


/-- `dim_VF(A) = 0` is `HasDim S A 0`: `A` admits a definable finite-to-one function into
`VF^0 × RV^l` for some `l`. -/
theorem dimVF_eq_zero_iff (S : SP M) {n m : ℕ} (A : Set (Tup M n m)) :
    dimVF S A = 0 ↔ HasDim S A 0 := by
  constructor
  · intro h
    have h0 : dimVF S A ≤ 0 := by rw [h]
    exact (dimVF_le_iff S A 0).1 h0
  · intro h
    exact Nat.le_antisymm ((dimVF_le_iff S A 0).2 h) (Nat.zero_le _)

/-- The `RV`-case of `dim_VF(A) = 0`: if `A` injects definably into `RV^l` (the paper's
`finite:VF:project:RV`, Yin's Lemma 4.10, applied to the finite sets of `A`), then `dim_VF A = 0`.
This is the paper's remark after `dim:RV:fibers` that a definable injection into the `RV`--part
alone forces `VF`-dimension `0`. -/
theorem dimVF_eq_zero_of_inj_RV (S : SP M) {n m : ℕ} (A : Set (Tup M n m))
    (h : ∃ l : ℕ, ∃ f : Tup M n m → Tup M 0 l, DefinableFun S A f ∧ InjOn A f) :
    dimVF S A = 0 := by
  obtain ⟨l, f, hf, hinj⟩ := h
  have h0 : dimVF S A ≤ 0 := dimVF_le_of_injOn S ⟨0, le_rfl, l, f, hf, hinj⟩
  exact Nat.le_antisymm h0 (Nat.zero_le _)


/-! ## Monotonicity in the set, and the `RV`-dimension -/

/-- A function definable on `B` is definable on any subset `A ⊆ B`: the definition of
`DefinableFun` asks only for the graph *on the domain*, so the same formula witnesses both. -/
theorem DefinableFun.mono {S : SP M} {n m : ℕ} {A B : Set (Tup M n m)} {k l : ℕ}
    {f : Tup M n m → Tup M k l} (hAB : A ⊆ B) (hf : DefinableFun S B f) :
    DefinableFun S A f := by
  obtain ⟨φ, hφ, h⟩ := hf
  exact ⟨φ, hφ, fun x hx => h x (hAB hx)⟩

/-- Finite-to-one-ness is inherited by subsets. -/
theorem FibreFinite.mono {n m k l : ℕ} {A B : Set (Tup M n m)} {f : Tup M n m → Tup M k l}
    (hAB : A ⊆ B) (hf : FibreFinite B f) : FibreFinite A f := by
  intro y
  exact (hf y).subset (fun x hx => ⟨hAB hx.1, hx.2⟩)

/-- **`dim_VF` is monotone under inclusion of definable sets** — a special case of the paper's
remark that parameters do not change the `VF`-dimension, and of `VF:dim:mono` with the identity
function: a finite-to-one defining function for `B` restricts to one for `A`, because the graph on
a sub-domain is the same formula. -/
theorem dimVF_mono (S : SP M) {n m : ℕ} {A B : Set (Tup M n m)} (hAB : A ⊆ B) :
    dimVF S A ≤ dimVF S B := by
  obtain ⟨k', hk', l, f, hf, hfin⟩ := (dimVF_le_iff S B (dimVF S B)).1 le_rfl
  exact Nat.sInf_le ⟨k', hk', l, f, hf.mono hAB, hfin.mono hAB⟩

/-- **`dim_RV(B) ≤ k`**, the paper's `RV`-dimension (`paper.tex`, after `VF:dim:tran:deg`): *"Let
`B ⊆ RV^m` be a definable subset.  The `RV`-dimension of `B`, denoted by `dim_RV(B)`, is the
smallest number `k` such that there is a definable finite-to-one function `f : B → RV^k` (`RV^0` is
taken to be the singleton `{∞}`)."*  The `RV`-dimension has no `VF`-coordinates, hence no padding:
the target power is exact. -/
def HasRVdim (S : SP M) {m : ℕ} (B : Set (Tup M 0 m)) (k : ℕ) : Prop :=
  ∃ f : Tup M 0 m → Tup M 0 k, DefinableFun S B f ∧ FibreFinite B f

/-- **`dim_RV B`**: the paper's `RV`-dimension of a definable `B ⊆ RV^m`. -/
noncomputable def dimRV (S : SP M) {m : ℕ} (B : Set (Tup M 0 m)) : ℕ :=
  sInf {k : ℕ | HasRVdim S B k}

theorem hasRVdim_self (S : SP M) {m : ℕ} (B : Set (Tup M 0 m)) : HasRVdim S B m :=
  ⟨id, definableFun_id S B, fibreFinite_of_injOn (fun _ _ _ _ h => h)⟩

/-- `dim_RV` is a genuine minimum: `dim_RV(B) ≤ k` iff `B` has a definable finite-to-one function
into `RV^{k'}` for some `k' ≤ k`.  (The paper's `RV^k` is exact — the `RV`-dimension has no
`Γ`-coordinate to pad with — so the bounded form is the faithful rendering of `≤`.) -/
theorem dimRV_le_iff (S : SP M) {m : ℕ} (B : Set (Tup M 0 m)) (k : ℕ) :
    dimRV S B ≤ k ↔ ∃ k' : ℕ, k' ≤ k ∧ HasRVdim S B k' := by
  have hne : {k : ℕ | HasRVdim S B k}.Nonempty := ⟨m, hasRVdim_self S B⟩
  constructor
  · intro h
    exact ⟨sInf {k : ℕ | HasRVdim S B k}, h, Nat.sInf_mem hne⟩
  · rintro ⟨k', hk', h⟩
    exact (Nat.sInf_le h).trans hk'

/-- **`dim_RV(B) ≤ m`** for `B ⊆ RV^m`. -/
theorem dimRV_le_self (S : SP M) {m : ℕ} (B : Set (Tup M 0 m)) : dimRV S B ≤ m :=
  (dimRV_le_iff S B m).2 ⟨m, le_rfl, hasRVdim_self S B⟩

end Sec4Dim

end SpecialTransformations.Milestone0
