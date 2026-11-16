module

/-
Section 4 of Yin, *Special transformations in algebraically closed valued fields*
(arXiv:1006.2467), §4.1: the **set-algebra and renaming layer** for `Sec4Dim.Definable`.

The paper works with definable subsets of `VF^n × RV^m` and moves them around silently: it
permutes coordinates, drops or adjoins dummy `RV` coordinates, and takes finite unions and
intersections of definable sets.  This file supplies exactly that, without the general
composition lemma for definable functions:

* `rnVar e φ` — rename the free variables of a formula along `e : Fin N → Fin N'`; it is the
  special case of `QE/SubstVar.lean`'s `BoundedFormula.substVar` in which every variable is
  replaced by a variable (`wellSorted_rnVar`, `realize_rnVar`);
* `Definable.rmap` — `Definable` is invariant under a sort-compatible change of coordinates;
* `blockMap`, `Definable.permBlock` — invariance under a permutation of the `VF` coordinates and
  a permutation of the `RV` coordinates separately;
* `Tup.rvPad`, `Definable.rvPad` — adjoining dummy `RV` coordinates preserves definability;
* `definable_empty`, `Definable.sdiff`, `Definable.biUnion`, `Definable.biInter`,
  `Definable.iUnion_fin`, `Definable.iInter_fin`, `Definable.iUnion'`, `Definable.iInter'` — the
  set algebra of definable subsets over finite index sets;
* `definableSubalgebra (S : SP M) (n m : ℕ) : BooleanSubalgebra (Set (Tup M n m))` with carrier
  `{A | Definable S A}` — **the definable subsets of `VF^n × RV^m` form a Boolean algebra** in
  Mathlib's sense (`⊔` = union, `⊓` = intersection, `ᶜ` = complement, `⊥` = `∅`, `⊤` = `univ`),
  with the coefficient lemmas `definableSubalgebra_{sup,inf,compl,bot,top}_coe`;
* `DefinableFun.comp_precomp`, `FibreFinite.comp_precomp`, `HasDim.comp_precomp`,
  `dimVF_precomp`, `dimVF_blockPerm` — **`dim_VF` is invariant under a permutation of the `VF`
  coordinates and of the `RV` coordinates** (`{y | y ∘ (σ⁻¹,τ⁻¹) ∈ A}` and `A` have the same
  `VF`-dimension), which is the §4.1 payoff of the renaming layer.  `dimVF_blockPerm_one` is the
  identity instance, so the hypotheses are satisfiable.

Deliberately **not** here, and not reachable this way: `dimVF` invariance under adjoining dummy
`RV` coordinates (`A × RV^{m₀}`, i.e. `Tup.rvPad ⁻¹' A`) and union-additivity
`dimVF (A ∪ B) = max (dimVF A) (dimVF B)`.  Both need the *codomain* of a definable function to be
padded/paired with a coordinate projection, i.e. a conjunction of a renamed graph with coordinate
equalities — the composition/pairing lemma for `DefinableFun`, which is a different job.

No `sorry`, no `axiom`, no `native_decide`.
-/
public import SubstVar

@[expose] public section

open FirstOrder FirstOrder.Language
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace SpecialTransformations.Milestone0
open LRV
open Sec4Dim
open Sec4Compose

namespace Sec4Dim

variable {M : Type*} [LRV.Structure M]

/-! ## Renaming the free variables of a formula -/

/-- **Rename the free variables of a formula**: `rnVar e φ` replaces the free variable `x_i` of `φ`
by the free variable `x_{e i}`.  This is `BoundedFormula.substVar` at the substitution
`σ i = x_{e i}`: no term is introduced, which is why it is available without a composition
lemma for definable functions. -/
def rnVar {α : Type} {N N' : ℕ} (e : Fin N → Fin N') (φ : LRV.BoundedFormula α N) :
    LRV.BoundedFormula α N' :=
  Sec4Compose.BoundedFormula.substVar (fun i => Term.var (Sum.inr (e i))) φ

/-- **Well-sortedness is preserved by a change of variables**. -/
theorem wellSorted_rnVar {α : Type} (sα : α → SortTag) {N N' : ℕ} {sN : Fin N → SortTag}
    {sN' : Fin N' → SortTag} (e : Fin N → Fin N') (he : ∀ i, sN' (e i) = sN i)
    {φ : LRV.BoundedFormula α N} (hφ : WellSorted sα sN φ) :
    WellSorted sα sN' (rnVar e φ) := by
  refine Sec4Compose.wellSorted_substVar sα hφ (fun i => ?_)
  show TmSort sα sN' (Term.var (Sum.inr (e i))) = some (sN i)
  rw [tmSort_var_inr, he i]

/-- **The realization of a renamed formula**: it is the realization of `φ` at `i ↦ x_{e i}`. -/
theorem realize_rnVar {α : Type} {N N' : ℕ} (e : Fin N → Fin N')
    (φ : LRV.BoundedFormula α N) (v : α → M) (xs : Fin N' → M) :
    (rnVar e φ).Realize v xs ↔ φ.Realize v (fun i => xs (e i)) := by
  rw [rnVar, Sec4Compose.realize_substVar]
  simp only [Term.realize_var, Sum.elim_inr]

/-! ## Tuples as flat assignments -/

/-- A tuple read as an assignment on the flattened index set `Fin (n + m)`: this is the assignment
that `Definable` uses to realize a formula. -/
def Tup.toFlat {n m : ℕ} (x : Tup M n m) : Fin (n + m) → M :=
  fun t => x (finSumFinEquiv.symm t)

theorem Tup.toFlat_injective {n m : ℕ} :
    Function.Injective (Tup.toFlat (M := M) (n := n) (m := m)) := by
  intro x y h
  refine Subtype.ext (funext fun i => ?_)
  have h' := congrFun h (finSumFinEquiv i)
  simpa [Tup.toFlat] using h'

theorem fSort_finSumFinEquiv {n m : ℕ} (i : Idx n m) :
    fSort n m (finSumFinEquiv i) = idxSort n m i := by
  simp [fSort]

theorem idxSort_inl' {k l : ℕ} (p : Fin k) : idxSort k l (Sum.inl p) = SortTag.vf := rfl

theorem idxSort_inr' {k l : ℕ} (q : Fin l) : idxSort k l (Sum.inr q) = SortTag.rv := rfl

theorem finSumFinEquiv_symm_castAdd' {k l : ℕ} (p : Fin k) :
    (finSumFinEquiv (m := k) (n := l)).symm (Fin.castAdd l p) = Sum.inl p := by
  rw [← finSumFinEquiv_apply_left]
  exact Equiv.symm_apply_apply _ _

theorem finSumFinEquiv_symm_natAdd' {k l : ℕ} (q : Fin l) :
    (finSumFinEquiv (m := k) (n := l)).symm (Fin.natAdd k q) = Sum.inr q := by
  rw [← finSumFinEquiv_apply_right]
  exact Equiv.symm_apply_apply _ _

/-- The first `k` coordinates of `VF^k × RV^l` are of sort `VF`. -/
theorem fSort_castAdd {k l : ℕ} (p : Fin k) : fSort k l (Fin.castAdd l p) = SortTag.vf := by
  show idxSort k l ((finSumFinEquiv (m := k) (n := l)).symm (Fin.castAdd l p)) = SortTag.vf
  rw [finSumFinEquiv_symm_castAdd']
  rfl

/-- The last `l` coordinates of `VF^k × RV^l` are of sort `RV`. -/
theorem fSort_natAdd {k l : ℕ} (q : Fin l) : fSort k l (Fin.natAdd k q) = SortTag.rv := by
  show idxSort k l ((finSumFinEquiv (m := k) (n := l)).symm (Fin.natAdd k q)) = SortTag.rv
  rw [finSumFinEquiv_symm_natAdd']
  rfl

/-- **Pull a tuple back along a map of coordinates**: if `e` sends the `t`-th coordinate of
`VF^n × RV^m` to a coordinate of `VF^{n'} × RV^{m'}` of the same sort, then `precomp e y` is the
tuple whose `t`-th coordinate is the `e t`-th coordinate of `y`. -/
def Tup.precomp {n m n' m' : ℕ} (e : Fin (n + m) → Fin (n' + m'))
    (he : ∀ t, fSort n' m' (e t) = fSort n m t) (y : Tup M n' m') : Tup M n m :=
  ⟨fun i => y (finSumFinEquiv.symm (e (finSumFinEquiv i))), fun i => by
    have h1 : sortEval (fSort n' m' (e (finSumFinEquiv i)))
        (y (finSumFinEquiv.symm (e (finSumFinEquiv i)))) :=
      y.2 (finSumFinEquiv.symm (e (finSumFinEquiv i)))
    rw [he (finSumFinEquiv i)] at h1
    rwa [fSort_finSumFinEquiv] at h1⟩

theorem Tup.toFlat_precomp {n m n' m' : ℕ} (e : Fin (n + m) → Fin (n' + m'))
    (he : ∀ t, fSort n' m' (e t) = fSort n m t) (y : Tup M n' m') :
    Tup.toFlat (Tup.precomp e he y) = fun t => Tup.toFlat y (e t) := by
  funext t
  show y (finSumFinEquiv.symm (e (finSumFinEquiv (finSumFinEquiv.symm t)))) =
    y (finSumFinEquiv.symm (e t))
  rw [Equiv.apply_symm_apply]

theorem Tup.precomp_congr {n m n' m' : ℕ} (e : Fin (n + m) → Fin (n' + m'))
    (he he' : ∀ t, fSort n' m' (e t) = fSort n m t) (y : Tup M n' m') :
    Tup.precomp e he y = Tup.precomp e he' y := by
  refine Tup.toFlat_injective ?_
  simp only [Tup.toFlat_precomp]

/-! ## Definability is invariant under a change of coordinates -/

/-- **The renaming theorem for `Definable`**: a definable subset of `VF^n × RV^m`, pulled back
along a sort-compatible map of coordinates, is definable in `VF^{n'} × RV^{m'}`. -/
theorem Definable.rmap {S : SP M} {n m n' m' : ℕ} {A : Set (Tup M n m)} (hA : Definable S A)
    (e : Fin (n + m) → Fin (n' + m')) (he : ∀ t, fSort n' m' (e t) = fSort n m t) :
    Definable S {y : Tup M n' m' | Tup.precomp e he y ∈ A} := by
  obtain ⟨φ, hφ, hAφ⟩ := hA
  refine ⟨rnVar e φ, wellSorted_rnVar S.sortMap e he hφ, fun y => ?_⟩
  have h1 : (rnVar e φ).Realize S.toFun (Tup.toFlat y) ↔
      φ.Realize S.toFun (Tup.toFlat (Tup.precomp e he y)) := by
    rw [realize_rnVar, Tup.toFlat_precomp]
  exact h1.trans (hAφ (Tup.precomp e he y))

/-! ## The set algebra of definable subsets -/

theorem definable_empty (S : SP M) {n m : ℕ} :
    Definable S (∅ : Set (Tup M n m)) :=
  ⟨⊥, WellSorted.falsum (fSort n m), fun x => by simp⟩

theorem Definable.sdiff {S : SP M} {n m : ℕ} {A B : Set (Tup M n m)}
    (hA : Definable S A) (hB : Definable S B) : Definable S (A \ B) := by
  rw [Set.sdiff_eq]
  exact hA.inter hB.compl

/-- Definability is closed under finite unions. -/
theorem Definable.biUnion {S : SP M} {n m : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → Set (Tup M n m)} (h : ∀ i ∈ s, Definable S (f i)) :
    Definable S (⋃ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using definable_empty S (n := n) (m := m)
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact (h a (Finset.mem_insert_self a s)).union
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Definability is closed under finite intersections. -/
theorem Definable.biInter {S : SP M} {n m : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → Set (Tup M n m)} (h : ∀ i ∈ s, Definable S (f i)) :
    Definable S (⋂ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using definable_univ S (n := n) (m := m)
  | insert a s ha ih =>
    rw [Finset.set_biInter_insert]
    exact (h a (Finset.mem_insert_self a s)).inter
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Definability is closed under a finite union over `Fin k`. -/
theorem Definable.iUnion_fin {S : SP M} {n m : ℕ} {k : ℕ} {f : Fin k → Set (Tup M n m)}
    (h : ∀ i, Definable S (f i)) : Definable S (⋃ i, f i) := by
  have h' := Definable.biUnion (S := S) (f := f) Finset.univ (fun i _ => h i)
  simpa using h'

/-- Definability is closed under a finite intersection over `Fin k`. -/
theorem Definable.iInter_fin {S : SP M} {n m : ℕ} {k : ℕ} {f : Fin k → Set (Tup M n m)}
    (h : ∀ i, Definable S (f i)) : Definable S (⋂ i, f i) := by
  have h' := Definable.biInter (S := S) (f := f) Finset.univ (fun i _ => h i)
  simpa using h'

/-- Definability is closed under a finite union over a finite index type. -/
theorem Definable.iUnion' {S : SP M} {n m : ℕ} {ι : Type*} [Fintype ι]
    {f : ι → Set (Tup M n m)} (h : ∀ i, Definable S (f i)) : Definable S (⋃ i, f i) := by
  have h' := Definable.biUnion (S := S) (f := f) Finset.univ (fun i _ => h i)
  simpa using h'

/-- Definability is closed under a finite intersection over a finite index type. -/
theorem Definable.iInter' {S : SP M} {n m : ℕ} {ι : Type*} [Fintype ι]
    {f : ι → Set (Tup M n m)} (h : ∀ i, Definable S (f i)) : Definable S (⋂ i, f i) := by
  have h' := Definable.biInter (S := S) (f := f) Finset.univ (fun i _ => h i)
  simpa using h'

/-- **The definable subsets of `VF^n × RV^m` form a Boolean subalgebra of `Set (VF^n × RV^m)`**:
they contain `⊥` and are closed under `⊔`, `⊓` and complement.  This bundles `definable_empty`,
`Definable.union`, `Definable.inter`, `Definable.compl` into the structure that Mathlib's
`BooleanAlgebra` API consumes. -/
def definableSubalgebra (S : SP M) (n m : ℕ) : BooleanSubalgebra (Set (Tup M n m)) where
  carrier := {A | Definable S A}
  supClosed' := by
    intro A hA B hB
    exact hA.union hB
  infClosed' := by
    intro A hA B hB
    exact hA.inter hB
  compl_mem' := by
    rintro A hA
    exact hA.compl
  bot_mem' := definable_empty S

theorem mem_definableSubalgebra {S : SP M} {n m : ℕ} {A : Set (Tup M n m)} :
    A ∈ definableSubalgebra S n m ↔ Definable S A := Iff.rfl

/-- The `BooleanAlgebra` structure on definable subsets: `⊔` is union, `⊓` is intersection, `ᶜ` is
complement. -/
theorem definableSubalgebra_coe (S : SP M) (n m : ℕ) :
    (definableSubalgebra S n m : Set (Set (Tup M n m))) = {A | Definable S A} := rfl

@[simp] theorem definableSubalgebra_sup_coe (S : SP M) (n m : ℕ)
    (A B : definableSubalgebra S n m) :
    ((A ⊔ B : definableSubalgebra S n m) : Set (Tup M n m)) =
      (A : Set (Tup M n m)) ∪ (B : Set (Tup M n m)) := rfl

@[simp] theorem definableSubalgebra_inf_coe (S : SP M) (n m : ℕ)
    (A B : definableSubalgebra S n m) :
    ((A ⊓ B : definableSubalgebra S n m) : Set (Tup M n m)) =
      (A : Set (Tup M n m)) ∩ (B : Set (Tup M n m)) := rfl

@[simp] theorem definableSubalgebra_compl_coe (S : SP M) (n m : ℕ)
    (A : definableSubalgebra S n m) :
    ((Aᶜ : definableSubalgebra S n m) : Set (Tup M n m)) = (A : Set (Tup M n m))ᶜ := rfl

@[simp] theorem definableSubalgebra_bot_coe (S : SP M) (n m : ℕ) :
    ((⊥ : definableSubalgebra S n m) : Set (Tup M n m)) = ∅ := rfl

@[simp] theorem definableSubalgebra_top_coe (S : SP M) (n m : ℕ) :
    ((⊤ : definableSubalgebra S n m) : Set (Tup M n m)) = Set.univ := rfl

/-! ## Block maps of coordinates -/

/-- **A map of coordinates acting separately on the two blocks**: `e₁` on the `n` coordinates of
sort `VF` and `e₂` on the `m` coordinates of sort `RV`. -/
def blockMap {n m n' m' : ℕ} (e₁ : Fin n → Fin n') (e₂ : Fin m → Fin m') :
    Fin (n + m) → Fin (n' + m') :=
  fun t => Fin.addCases (fun i => Fin.castAdd m' (e₁ i)) (fun j => Fin.natAdd n' (e₂ j)) t

theorem blockMap_castAdd {n m n' m' : ℕ} (e₁ : Fin n → Fin n') (e₂ : Fin m → Fin m')
    (i : Fin n) : blockMap e₁ e₂ (Fin.castAdd m i) = Fin.castAdd m' (e₁ i) := by
  simp [blockMap]

theorem blockMap_natAdd {n m n' m' : ℕ} (e₁ : Fin n → Fin n') (e₂ : Fin m → Fin m')
    (j : Fin m) : blockMap e₁ e₂ (Fin.natAdd n j) = Fin.natAdd n' (e₂ j) := by
  simp [blockMap]

/-- A block map is sort compatible. -/
theorem fSort_blockMap {n m n' m' : ℕ} (e₁ : Fin n → Fin n') (e₂ : Fin m → Fin m')
    (t : Fin (n + m)) : fSort n' m' (blockMap e₁ e₂ t) = fSort n m t := by
  refine Fin.addCases (m := n) (n := m) ?_ ?_ t
  · intro i
    rw [blockMap_castAdd, fSort_castAdd, fSort_castAdd]
  · intro j
    rw [blockMap_natAdd, fSort_natAdd, fSort_natAdd]

theorem blockMap_comp {n m : ℕ} (e₁' e₁ : Fin n → Fin n) (e₂' e₂ : Fin m → Fin m)
    (h₁ : ∀ i, e₁' (e₁ i) = i) (h₂ : ∀ j, e₂' (e₂ j) = j) (t : Fin (n + m)) :
    blockMap e₁' e₂' (blockMap e₁ e₂ t) = t := by
  refine Fin.addCases (m := n) (n := m) ?_ ?_ t
  · intro i
    rw [blockMap_castAdd, blockMap_castAdd, h₁ i]
  · intro j
    rw [blockMap_natAdd, blockMap_natAdd, h₂ j]

/-! ## Dummy `RV` coordinates -/

/-- **Forgetting dummy `RV` coordinates**: from `VF^n × RV^{m+m₀}` to `VF^n × RV^m`, keeping the
first `m` `RV` coordinates. -/
def Tup.rvPad {n m m₀ : ℕ} (y : Tup M n (m + m₀)) : Tup M n m :=
  Tup.precomp (blockMap (id : Fin n → Fin n) (Fin.castAdd m₀)) (fSort_blockMap _ _) y

theorem Tup.rvPad_inl {n m m₀ : ℕ} (y : Tup M n (m + m₀)) (i : Fin n) :
    Tup.rvPad y (Sum.inl i) = y (Sum.inl i) := by
  show y (finSumFinEquiv.symm (blockMap id (Fin.castAdd m₀) (finSumFinEquiv (Sum.inl i)))) =
    y (Sum.inl i)
  rw [finSumFinEquiv_apply_left, blockMap_castAdd, finSumFinEquiv_symm_castAdd']
  rfl

theorem Tup.rvPad_inr {n m m₀ : ℕ} (y : Tup M n (m + m₀)) (j : Fin m) :
    Tup.rvPad y (Sum.inr j) = y (Sum.inr (Fin.castAdd m₀ j)) := by
  show y (finSumFinEquiv.symm (blockMap id (Fin.castAdd m₀) (finSumFinEquiv (Sum.inr j)))) =
    y (Sum.inr (Fin.castAdd m₀ j))
  rw [finSumFinEquiv_apply_right, blockMap_natAdd, finSumFinEquiv_symm_natAdd']

/-- **Adjoining dummy `RV` coordinates preserves definability.** -/
theorem Definable.rvPad {S : SP M} {n m m₀ : ℕ} {A : Set (Tup M n m)}
    (hA : Definable S A) : Definable S {y : Tup M n (m + m₀) | Tup.rvPad y ∈ A} :=
  hA.rmap (blockMap (id : Fin n → Fin n) (Fin.castAdd m₀)) (fSort_blockMap _ _)

/-! ## Simultaneous permutations of the two blocks -/

/-- The double pull-back along a block map and a left-inverse block map is the identity. -/
theorem Tup.precomp_blockMap_comp {n m : ℕ} (e₁ : Fin n → Fin n) (e₂ : Fin m → Fin m)
    (e₁' : Fin n → Fin n) (e₂' : Fin m → Fin m)
    (h₁ : ∀ i, e₁' (e₁ i) = i) (h₂ : ∀ j, e₂' (e₂ j) = j) (y : Tup M n m) :
    Tup.precomp (blockMap e₁ e₂) (fSort_blockMap _ _)
      (Tup.precomp (blockMap e₁' e₂') (fSort_blockMap _ _) y) = y := by
  refine Tup.toFlat_injective ?_
  simp only [Tup.toFlat_precomp]
  funext t
  rw [show blockMap e₁' e₂' (blockMap e₁ e₂ t) = t from blockMap_comp _ _ _ _ h₁ h₂ t]

/-- **Definability is invariant under a permutation of the `VF` coordinates and a permutation of
the `RV` coordinates.** -/
theorem Definable.permBlock {S : SP M} {n m : ℕ} (e₁ : Fin n ≃ Fin n) (e₂ : Fin m ≃ Fin m)
    {A : Set (Tup M n m)} :
    Definable S A ↔
      Definable S {y : Tup M n m | Tup.precomp (blockMap (⇑e₁) (⇑e₂)) (fSort_blockMap _ _) y ∈ A} := by
  refine ⟨fun h => h.rmap _ (fSort_blockMap _ _), fun h => ?_⟩
  have h' := h.rmap (blockMap (⇑e₁.symm) (⇑e₂.symm)) (fSort_blockMap _ _)
  have key : ∀ y : Tup M n m,
      Tup.precomp (blockMap (⇑e₁) (⇑e₂)) (fSort_blockMap _ _)
        (Tup.precomp (blockMap (⇑e₁.symm) (⇑e₂.symm)) (fSort_blockMap _ _) y) = y :=
    fun y => Tup.precomp_blockMap_comp (e₁ := ⇑e₁) (e₂ := ⇑e₂) (e₁' := ⇑e₁.symm) (e₂' := ⇑e₂.symm)
      (fun i => Equiv.symm_apply_apply e₁ i) (fun j => Equiv.symm_apply_apply e₂ j) y
  have hset : {y : Tup M n m |
      Tup.precomp (blockMap (⇑e₁.symm) (⇑e₂.symm)) (fSort_blockMap _ _) y ∈
        {y : Tup M n m | Tup.precomp (blockMap (⇑e₁) (⇑e₂)) (fSort_blockMap _ _) y ∈ A}} = A := by
    refine Set.ext (fun y => ?_)
    show (Tup.precomp (blockMap (⇑e₁) (⇑e₂)) (fSort_blockMap _ _)
        (Tup.precomp (blockMap (⇑e₁.symm) (⇑e₂.symm)) (fSort_blockMap _ _) y) ∈ A) ↔ y ∈ A
    rw [key y]
  rwa [hset] at h'

/-! ## Transport of definable functions along a change of coordinates -/

/-- The sort pattern of a **two-block** context (domain block, then codomain block) is preserved
by a block map of the two blocks. -/
theorem fSort_append_blockMap {n m n' m' k l k' l' : ℕ}
    (e₁ : Fin (n + m) → Fin (n' + m')) (he₁ : ∀ t, fSort n' m' (e₁ t) = fSort n m t)
    (e₂ : Fin (k + l) → Fin (k' + l')) (he₂ : ∀ t, fSort k' l' (e₂ t) = fSort k l t)
    (t : Fin ((n + m) + (k + l))) :
    Fin.append (fSort n' m') (fSort k' l') (blockMap e₁ e₂ t) =
      Fin.append (fSort n m) (fSort k l) t := by
  refine Fin.addCases (m := n + m) (n := k + l) ?_ ?_ t
  · intro i
    rw [blockMap_castAdd, Fin.append_left, Fin.append_left, he₁ i]
  · intro j
    rw [blockMap_natAdd, Fin.append_right, Fin.append_right, he₂ j]

theorem pairAssign_eq_append {n m k l : ℕ} (x : Tup M n m) (y : Tup M k l) :
    pairAssign x y = Fin.append (Tup.toFlat x) (Tup.toFlat y) := rfl

/-- Realizing the graph context `(n+m)+(k+l)` at a tuple pair, after a block map, is realizing it
at the pair of pulled-back tuples. -/
theorem pairAssign_comp {n m k l : ℕ} {e₁ : Fin (n + m) → Fin (n + m)}
    (he₁ : ∀ t, fSort n m (e₁ t) = fSort n m t)
    {e₂ : Fin (k + l) → Fin (k + l)} (he₂ : ∀ t, fSort k l (e₂ t) = fSort k l t)
    (y : Tup M n m) (y' : Tup M k l) (i : Fin ((n + m) + (k + l))) :
    pairAssign y y' (blockMap e₁ e₂ i) =
      pairAssign (Tup.precomp e₁ he₁ y) (Tup.precomp e₂ he₂ y') i := by
  refine Fin.addCases (m := n + m) (n := k + l) ?_ ?_ i
  · intro i₀
    rw [blockMap_castAdd, pairAssign_left, pairAssign_left]
    exact (congrFun (Tup.toFlat_precomp e₁ he₁ y) i₀).symm
  · intro j₀
    rw [blockMap_natAdd, pairAssign_right, pairAssign_right]
    exact (congrFun (Tup.toFlat_precomp e₂ he₂ y') j₀).symm

theorem Tup.precomp_id {n m : ℕ}
    (he : ∀ t, fSort n m ((id : Fin (n + m) → Fin (n + m)) t) = fSort n m t)
    (y : Tup M n m) : Tup.precomp (id : Fin (n + m) → Fin (n + m)) he y = y := by
  refine Tup.toFlat_injective ?_
  rw [Tup.toFlat_precomp]
  rfl

/-- **A definable function stays definable after pulling its domain back along a change of
coordinates** (codomain unchanged: `y ↦ f (e y)`). -/
theorem DefinableFun.comp_precomp {S : SP M} {n m k l : ℕ}
    {e : Fin (n + m) → Fin (n + m)} (he : ∀ t, fSort n m (e t) = fSort n m t)
    {A : Set (Tup M n m)} {f : Tup M n m → Tup M k l} (hf : DefinableFun S A f) :
    DefinableFun S {y : Tup M n m | Tup.precomp e he y ∈ A}
      (fun y => f (Tup.precomp e he y)) := by
  obtain ⟨φ, hφ, hφA⟩ := hf
  refine ⟨rnVar (blockMap e id) φ,
    wellSorted_rnVar S.sortMap _ (fSort_append_blockMap e he id (fun _ => rfl)) hφ, ?_⟩
  intro y hy y'
  rw [realize_rnVar]
  have hass : (fun i => pairAssign y y' (blockMap e id i)) =
      pairAssign (Tup.precomp e he y) (Tup.precomp id (fun _ => rfl) y') :=
    funext (pairAssign_comp he (fun _ => rfl) y y')
  rw [hass, Tup.precomp_id]
  exact hφA _ hy y'

/-- **Finite-to-one-ness survives pulling the domain back along a change of coordinates**, as long
as the change of coordinates has a left inverse (`hh`). -/
theorem FibreFinite.comp_precomp {n m k l : ℕ}
    {e : Fin (n + m) → Fin (n + m)} (he : ∀ t, fSort n m (e t) = fSort n m t)
    {e' : Fin (n + m) → Fin (n + m)} (he' : ∀ t, fSort n m (e' t) = fSort n m t)
    (hh : ∀ v : Tup M n m, Tup.precomp e he (Tup.precomp e' he' v) = v)
    {A : Set (Tup M n m)} {f : Tup M n m → Tup M k l} (hf : FibreFinite A f) :
    FibreFinite {y : Tup M n m | Tup.precomp e' he' y ∈ A}
      (fun y => f (Tup.precomp e' he' y)) := by
  intro y'
  refine Set.Finite.subset ((hf y').image (Tup.precomp e he)) ?_
  intro y hy
  exact ⟨Tup.precomp e' he' y, hy, hh y⟩

/-- **`dim_VF` bounds are invariant under a change of coordinates of the ambient space** which has
a left inverse: `A` and the preimage of `A` under a coordinate change have the same upper bounds on
`VF`-dimension. -/
theorem HasDim.comp_precomp {S : SP M} {n m : ℕ}
    {e : Fin (n + m) → Fin (n + m)} (he : ∀ t, fSort n m (e t) = fSort n m t)
    {e' : Fin (n + m) → Fin (n + m)} (he' : ∀ t, fSort n m (e' t) = fSort n m t)
    (hh : ∀ v : Tup M n m, Tup.precomp e he (Tup.precomp e' he' v) = v)
    {A : Set (Tup M n m)} {c : ℕ} (hA : HasDim S A c) :
    HasDim S {y : Tup M n m | Tup.precomp e' he' y ∈ A} c := by
  obtain ⟨k', hk', l, f, hf, hff⟩ := hA
  exact ⟨k', hk', l, _, DefinableFun.comp_precomp he' hf,
    FibreFinite.comp_precomp he he' hh hff⟩

/-- **`dim_VF` is invariant under a coordinate permutation of the ambient space**: for `Φ = precomp e`
and `Ψ = precomp e'` mutually inverse maps of `VF^n × RV^m`, the sets `A` and `Ψ ⁻¹' A` have the
same `VF`-dimension. -/
theorem dimVF_precomp {S : SP M} {n m : ℕ}
    {e : Fin (n + m) → Fin (n + m)} (he : ∀ t, fSort n m (e t) = fSort n m t)
    {e' : Fin (n + m) → Fin (n + m)} (he' : ∀ t, fSort n m (e' t) = fSort n m t)
    (hh : ∀ v : Tup M n m, Tup.precomp e he (Tup.precomp e' he' v) = v)
    (hh' : ∀ v : Tup M n m, Tup.precomp e' he' (Tup.precomp e he v) = v)
    {A : Set (Tup M n m)} :
    dimVF S {y : Tup M n m | Tup.precomp e' he' y ∈ A} = dimVF S A := by
  refine le_antisymm ?_ ?_
  · rw [dimVF_le_iff]
    exact HasDim.comp_precomp he he' hh ((dimVF_le_iff S A (dimVF S A)).mp le_rfl)
  · rw [dimVF_le_iff]
    have h := HasDim.comp_precomp (e := e') (he := he') (e' := e) (he' := he) (hh := hh')
      (A := {y : Tup M n m | Tup.precomp e' he' y ∈ A})
      ((dimVF_le_iff S _ (dimVF S _)).mp le_rfl)
    rwa [show {y : Tup M n m | Tup.precomp e he y ∈ {z : Tup M n m |
        Tup.precomp e' he' z ∈ A}} = A from ?_] at h
    refine Set.ext (fun y => ?_)
    show (Tup.precomp e' he' (Tup.precomp e he y) ∈ A) ↔ y ∈ A
    rw [hh' y]

/-- **`dim_VF` is invariant under a permutation of the `VF` coordinates and a permutation of the
`RV` coordinates** — the concrete, non-vacuous instance of `dimVF_precomp`: the set
`{y | y ∘ (σ⁻¹, τ⁻¹) ∈ A}` (the image of `A` under the coordinate permutation `(σ, τ)`) has the
same `VF`-dimension as `A`. -/
theorem dimVF_blockPerm {S : SP M} {n m : ℕ} (σ : Fin n ≃ Fin n) (τ : Fin m ≃ Fin m)
    {A : Set (Tup M n m)} :
    dimVF S {y : Tup M n m |
        Tup.precomp (blockMap (⇑σ.symm) (⇑τ.symm)) (fSort_blockMap _ _) y ∈ A}
      = dimVF S A := by
  refine dimVF_precomp (e := blockMap (⇑σ) (⇑τ)) (he := fSort_blockMap _ _)
    (e' := blockMap (⇑σ.symm) (⇑τ.symm)) (he' := fSort_blockMap _ _) ?_ ?_
  · exact fun v => Tup.precomp_blockMap_comp (e₁ := ⇑σ) (e₂ := ⇑τ) (e₁' := ⇑σ.symm)
      (e₂' := ⇑τ.symm) (fun i => Equiv.symm_apply_apply σ i)
      (fun j => Equiv.symm_apply_apply τ j) v
  · exact fun v => Tup.precomp_blockMap_comp (e₁ := ⇑σ.symm) (e₂ := ⇑τ.symm) (e₁' := ⇑σ)
      (e₂' := ⇑τ) (fun i => Equiv.apply_symm_apply σ i)
      (fun j => Equiv.apply_symm_apply τ j) v

/-- The identity case of `dimVF_blockPerm`: a sanity check that the hypotheses are satisfiable and
that the statement is not vacuous. -/
theorem dimVF_blockPerm_one {S : SP M} {n m : ℕ} {A : Set (Tup M n m)} :
    dimVF S {y : Tup M n m | Tup.precomp (blockMap (id : Fin n → Fin n) (id : Fin m → Fin m))
      (fSort_blockMap _ _) y ∈ A} = dimVF S A :=
  dimVF_blockPerm (Equiv.refl (Fin n)) (Equiv.refl (Fin m))


end Sec4Dim
end SpecialTransformations.Milestone0
