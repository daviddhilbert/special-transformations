module

/-
# Section 7, Corollary `L:semigroup:hom` (`paper.tex` 1705): `𝕃` induces surjective homomorphisms of
Grothendieck semigroups

This file formalizes the statement of Corollary \ref{L:semigroup:hom} of Yin, "Special
transformations in algebraically closed valued fields" (arXiv:1006.2467), §7, together with the parts
of its proof that the tree can carry, on top of the frozen encoding `Milestone0/Encoding.lean` and
§3–§5 as they exist here (`QE/Sec3_frozen.lean`, `QE/Sec4Dim.lean`, `QE/Sec4Categories.lean`).

The paper's corollary (verbatim):

> **Corollary \ref{L:semigroup:hom}.** *Suppose that the substructure `S` is `(VF, Γ)`-generated.  The
> map `𝕃` induces surjective homomorphisms between various Grothendieck semigroups, for example:
> `K₊ RV[k,·] → K₊ VF[k,·]`, `K₊ RV[k] → K₊ VF[k]`.*

with the proof

> *For any `RV[k,·]`-isomorphism `F : (U, f) → (V, g)` and any `ū ∈ U`, by definition,
> `wgt(f(ū)) = wgt((g∘F)(ū))`.  Let `C = {(f(ū), (g∘F)(ū)) : ū ∈ U} ⊆ RV^k × RV^k`.  By
> Theorem \ref{RV:iso:class:lifted} there is a lift `C^↑` of `C`, which induces a `VF[k,·]`-isomorphism
> between `𝕃(U, f)` and `𝕃(V, g)`.  So `𝕃` induces a map on the isomorphism classes, which is clearly
> a semigroup homomorphism.  By Corollary \ref{L:surjective} it is surjective.*

Hence the two ingredients supplied by the *earlier* sections, and carried here as explicit named
hypotheses in `LiftData` (never as `axiom`, never as `sorry`) — per the author's standing instruction
that each section is formalized independently, assuming the previous ones as given:

* `LiftData.iso_lift` — **Theorem \ref{RV:iso:class:lifted}** (`paper.tex` 1627), §7: *"Suppose that
  the substructure `S` is `(VF, Γ)`-generated.  Let `C ⊆ (RV^×)^n × (RV^×)^n` be a definable subset
  such that both `pr_{≤n} ↾ C` and `pr_{>n} ↾ C` are finite-to-one.  Then there is a definable subset
  `C^↑ ⊆ VF^n × VF^n` that lifts `C`."*  In the form used here: isomorphic `RV`-objects have
  isomorphic lifts;
* `LiftData.surj_lift` — **Corollary \ref{L:surjective}** (§6, given as a whole to this file): every
  object of `VF[k,·]` is isomorphic to a lift;
* `LiftData.L_val` — **Definition \ref{def:L}** (`paper.tex` 1057), identifying the object map with
  the canonical lift `𝕃_k(U,f) = ⋃{rv^{-1}(f(ū)) × {ū} : ū ∈ U}`.

What is *proved* here, with no hypothesis beyond the encoding:

* `liftSet` (Definition \ref{def:L} on sorted tuples `VF^k × RV^m`), its destructors, and the fact
  that the canonical lift consists of *sorted* tuples (`lift_subset_sorted`);
* the canonical lift is monotone and depends only on the pair `(U, f)` (`liftSet_mono`,
  `liftSet_congr`), and its fibre over `ū ∈ U` is exactly the `rv`-fibre `rv^{-1}(f(ū))`, i.e.
  `𝕃_k(U,f)` is the union `⋃{rv^{-1}(f(ū)) × {ū} : ū ∈ U}` of Definition \ref{def:L}
  (`rvFibre`, `liftSet_fibre`);
* **the `VF`-part-preserving half of Theorem \ref{RV:iso:class:lifted}**: for an `RV`-isomorphism
  `e : U ≃ V` with `g ∘ e = f`, the paper's `F^↑` — *"a function on `𝕃(U, f)` such that each
  restriction `F^↑ : rv^{-1}(f(ū), ū) → rv^{-1}((g∘F)(ū), F(ū))` is a bijection"* — is a bijection
  `𝕃(U, f) ≃ 𝕃(V, g)` (`liftEquiv`, `liftSet_equiv`); in that case Theorem
  \ref{RV:iso:class:lifted} therefore holds outright (`iso_lift_of_coord`);
* the isomorphism relations on `RV[k,·]` and `VF[k,·]` as `Setoid`s, and **Corollary
  \ref{L:semigroup:hom} itself**: the induced map on isomorphism classes is well defined and
  surjective (`LClass`, `LClass_surjective`), and it induces a surjective homomorphism of the free
  commutative monoids on the classes — the paper's `K₊` (`L_semigroup_hom`) — and of their
  groupifications — the paper's `K₀` (`L_group_hom`);
* the same for the paper's **second arrow**, `K₊RV[k] → K₊VF[k]`: with `RV[k]` the finite-to-one
  subcategory (`SP.RVObj.FiniteToOne`) and `VF[k]` the subcategory of finite `RV`-fibres
  (`RVFibresFinite`), `L_semigroup_hom_fin` and `L_group_hom_fin` state the corollary's *"`K₊RV[k]
  → K₊VF[k]`"* under the corresponding two hypotheses (`LiftDataFin`).

The paper's own hypothesis *"Suppose that the substructure `S` is `(VF, Γ)`-generated"* is not a
separate hypothesis here: it enters only through Lemma \ref{exists:gamma:polynomial} into Theorem
\ref{RV:iso:class:lifted}, i.e. it is inside `LiftData.iso_lift` (and `LiftDataFin.iso_lift`).
`S : SP M` is otherwise arbitrary, as `SP.RVObj`/`Sec4Dim.HasDim` are structural.

Two documented approximations, both recorded because they are where the tree's §4 stops:

1. The *definitional* part of `𝕃` — that `𝕃_k(U,f)` is again an object of `VF[k,·]`, i.e. is
   `S`-definable and of `VF`-dimension `≤ k` — is not proved (definability of the lift needs the
   graph of `f` pulled back along `rv`, and `VF`-dimension `≤ k` of an `RV`-pullback is §5's
   content).  It is carried as the object map `LiftData.L` *together with* the equation `L_val`
   identifying it with the canonical lift set, so the object map is not abstract: it is `liftSet`.
2. The isomorphism relations recorded are the *underlying* ones (a weight-preserving bijection of the
   `RV`-objects; a bijection of the `VF`-objects), not the paper's definable ones: `Definable` is not
   known to be closed under composition in this encoding (the substitution wall, `QE-PLAN.md`), so
   "definable bijection" is not known to be transitive and cannot be used for a `Setoid`.  The
   underlying relation is coarser, so `LiftData.iso_lift` is the paper's Theorem 7.6 for that coarser
   relation (a strengthening of it), while `LiftData.surj_lift` is implied by the paper's Corollary
   `L:surjective`.  `iso_lift_of_coord` below shows the hypothesis is non-vacuous on the coordinate
   isomorphisms: there it holds with no hypothesis.

Build: `LEAN_PATH=<repo>/.scratch2/sec3:$LEAN_PATH lean Sec7Cor77.lean`.
-/
public import Sec4Categories
public import Sec4Dim

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
namespace Sec7

open LRV

variable {M : Type*} [LRV.Structure M]
variable {S : SP M}

/-! ## Part 1. The ambient `RV^m`, and sortedness of definable sets -/

/-- The ambient of an `RV`-object: all sorted `m`-tuples of `RV`-elements, i.e. the paper's `RV^m`
as it occurs in *"An object of the category `RV[k,·]` is a definable pair `(U,f)`, where
`U ⊆ RV^m`"*.  It is itself definable (`SP.definable_sortedTuple`). -/
abbrev RVAmbient (m : ℕ) : Set (Fin m → M) :=
  SP.SortedTuple (fun _ : Fin m => SortTag.rv) M

/-- **The paper's `RV[k,·]`**, at the ambient where it lives: `SP.RVObj` with the base `A` taken to
be the *whole* of `RV^m`, so that the `U` of an object ranges over all definable subsets of `RV^m`,
as in the paper.  (The finite-to-one condition `SP.RVObj.FiniteToOne` distinguishing `RV[k]` from
`RV[k,·]` is not needed for this corollary's argument and is not imposed.) -/
abbrev RVObjK (S : SP M) (m k : ℕ) : Type _ :=
  SP.RVObj S (fun _ : Fin m => SortTag.rv) (RVAmbient (M := M) m) k

/-- **Sortedness of a definable set.**  `SP.Definable` is *"A = {x | (∀ i, sortEval (sα i) (x i)) ∧
φ.Realize …}"*, so a definable set of tuples consists of tuples respecting the declared sorts. -/
theorem sorted_of_mem {α : Type} {sα : α → SortTag} {A : Set (α → M)}
    (hA : SP.Definable S sα A) {x : α → M} (hx : x ∈ A) : ∀ i, sortEval (sα i) (x i) := by
  obtain ⟨φ, -, hEq⟩ := hA
  rw [hEq] at hx
  exact hx.1

/-! ## Part 2. The canonical lift `𝕃_k(U,f)` (Definition \ref{def:L}) -/

/-- The `RV`-part of a tuple of `VF^k × RV^m`: the paper's `ū`. -/
def baseFun {k : ℕ} (z : Fin k ⊕ Fin m → M) : Fin m → M := fun b => z (Sum.inr b)

@[simp] theorem baseFun_apply {k : ℕ} (z : Fin k ⊕ Fin m → M) (b : Fin m) :
    baseFun (m := m) z b = z (Sum.inr b) := rfl

/-- The `VF`-part of a tuple of `VF^k × RV^m`. -/
def vfFun {k : ℕ} (z : Fin k ⊕ Fin m → M) : Fin k → M := fun i => z (Sum.inl i)

@[simp] theorem vfFun_apply {k : ℕ} (z : Fin k ⊕ Fin m → M) (i : Fin k) :
    vfFun (m := m) z i = z (Sum.inl i) := rfl

/-- **The canonical `RV`-lift `𝕃_k(U,f)`** (Definition \ref{def:L}): *"For any `(U,f) ∈ RV[k,·]`,
let `𝕃_k(U,f) = ⋃{rv^{-1}(f(ū)) × {ū} : ū ∈ U}`"* — here as a set of sorted tuples of `VF^k × RV^m`:
the first `k` coordinates are the `VF`-elements lying over `f(ū)`, the last `m` are `ū` itself. -/
def liftSet (X : RVObjK (S := S) m k) : Set (Sec4Dim.Tup M k m) :=
  {x | (x : Fin k ⊕ Fin m → M) ∈ X.lift}

@[simp] theorem mem_liftSet {X : RVObjK (S := S) m k} {x : Sec4Dim.Tup M k m} :
    x ∈ liftSet X ↔ (x : Fin k ⊕ Fin m → M) ∈ X.lift := Iff.rfl

/-- The `VF`-coordinates of a point of `𝕃_k(U,f)` lie in `VF`. -/
theorem lift_vf {X : RVObjK (S := S) m k} {z : Fin k ⊕ Fin m → M} (hz : z ∈ X.lift) :
    ∀ i, iVF (z (Sum.inl i)) := hz.1

/-- The `RV`-part of a point of `𝕃_k(U,f)` lies in `U`. -/
theorem lift_base_mem {X : RVObjK (S := S) m k} {z : Fin k ⊕ Fin m → M} (hz : z ∈ X.lift) :
    baseFun (m := m) z ∈ X.U := hz.2.1

/-- The defining property of the lift: *"`rv^{-1}(f(ū)) × {ū}`"* — the `VF`-coordinates project to
`f(ū)` under `rv`. -/
theorem lift_rv {X : RVObjK (S := S) m k} {z : Fin k ⊕ Fin m → M} (hz : z ∈ X.lift) :
    ∀ i, iRv (z (Sum.inl i)) = X.f (baseFun (m := m) z) i := hz.2.2

/-- **`𝕃(U,f)` consists of sorted tuples**: every point of the canonical lift of an object of
`RV[k,·]` is a tuple of the shape `VF^k × RV^m`.  This is what lets `liftSet` be a set of sorted
tuples at all. -/
theorem lift_subset_sorted (X : RVObjK (S := S) m k) :
    X.lift ⊆ {z : Fin k ⊕ Fin m → M | ∀ j, sortEval (Sec4Dim.idxSort k m j) (z j)} := by
  intro z hz j
  cases j with
  | inl i => exact lift_vf hz i
  | inr b => exact sorted_of_mem X.U_definable (lift_base_mem hz) b

/-- **The lift is monotone in the object**: a subobject (same `f`, smaller `U`) has a smaller lift.
This is the paper's convention *"A subobject of an object `(U, f)` of an `RV`-category is a definable
pair `(A, g)` with `A` a subset of `U` and `g = f ↾ A`"*, transported to `𝕃`. -/
theorem liftSet_mono {X Y : RVObjK (S := S) m k} (hU : X.U ⊆ Y.U)
    (hf : ∀ u ∈ X.U, X.f u = Y.f u) : liftSet X ⊆ liftSet Y := by
  intro x hx
  rw [mem_liftSet] at hx ⊢
  exact ⟨lift_vf hx, hU (lift_base_mem hx),
    fun i => (lift_rv hx i).trans (congrFun (hf _ (lift_base_mem hx)) i)⟩

/-- The lift only depends on the pair `(U, f)`: two objects with the same `U` on which their `f`
agree have the same lift. -/
theorem liftSet_congr {X Y : RVObjK (S := S) m k} (hU : X.U = Y.U)
    (hf : ∀ u ∈ X.U, X.f u = Y.f u) : liftSet X = liftSet Y := by
  refine Set.Subset.antisymm (liftSet_mono hU.subset hf) (liftSet_mono hU.symm.subset ?_)
  intro u hu
  exact (hf u (hU.symm ▸ hu)).symm

/-! ## Part 3. The lift of an `RV`-isomorphism whose base map commutes with `f`

The paper's proof of Theorem \ref{RV:iso:class:lifted} starts from the `RV`-structure: *"For any
`RV[k,·]`-isomorphism `F : (U, f) → (V, g)` … `F^↑` is a function on `𝕃(U, f)` such that each
restriction `F^↑ : rv^{-1}(f(ū), ū) → rv^{-1}((g∘F)(ū), F(ū))` is a bijection"*.  When `g ∘ F = f`
this bijection is immediate: the `VF`-part is carried along unchanged and only the `RV`-part moves.
That is the case proved here, with no hypothesis; the twisting case (`g ∘ F ≠ f`) is exactly the
content of Theorem \ref{RV:iso:class:lifted} and is assumed in `LiftData.iso_lift`.
-/

/-- Replace the `RV`-part of a raw tuple by another `RV`-part, keeping the `VF`-part. -/
def replaceBase {k : ℕ} (a : Fin k → M) (u : Fin m → M) : Fin k ⊕ Fin m → M :=
  Sum.elim a u

@[simp] theorem replaceBase_inl {k : ℕ} (a : Fin k → M) (u : Fin m → M) (i : Fin k) :
    replaceBase (m := m) a u (Sum.inl i) = a i := rfl

@[simp] theorem replaceBase_inr {k : ℕ} (a : Fin k → M) (u : Fin m → M) (b : Fin m) :
    replaceBase (m := m) a u (Sum.inr b) = u b := rfl

@[simp] theorem vfFun_replaceBase {k : ℕ} (a : Fin k → M) (u : Fin m → M) :
    vfFun (m := m) (replaceBase (m := m) a u) = a := rfl

@[simp] theorem baseFun_replaceBase {k : ℕ} (a : Fin k → M) (u : Fin m → M) :
    baseFun (m := m) (replaceBase (m := m) a u) = u := rfl

/-- **The lift of a base bijection commuting with `f`**: for `e : U ≃ V` with `g ∘ e = f`, the map
`(ā, ū) ↦ (ā, e ū)` is a bijection `𝕃(U, f) ≃ 𝕃(V, g)`.  This is the paper's `F^↑` in the case where
the `rv`-fibres on the two sides are the same. -/
noncomputable def liftEquiv (X Y : RVObjK (S := S) m k) (e : X.U ≃ Y.U)
    (he : ∀ u : X.U, Y.f (e u) = X.f u) : X.lift ≃ Y.lift where
  toFun z :=
    ⟨replaceBase (vfFun z.1) ((e ⟨baseFun z.1, lift_base_mem z.2⟩ : Y.U) : Fin m → M), by
      refine ⟨fun i => ?_, ?_, fun i => ?_⟩
      · simpa using lift_vf z.2 i
      · simpa using (e ⟨baseFun z.1, lift_base_mem z.2⟩).2
      · simp only [replaceBase_inl, replaceBase_inr]
        show iRv (z.1 (Sum.inl i)) =
          Y.f ((e ⟨baseFun z.1, lift_base_mem z.2⟩ : Y.U) : Fin m → M) i
        rw [he ⟨baseFun z.1, lift_base_mem z.2⟩]
        exact lift_rv z.2 i⟩
  invFun z :=
    ⟨replaceBase (vfFun z.1) ((e.symm ⟨baseFun z.1, lift_base_mem z.2⟩ : X.U) : Fin m → M), by
      refine ⟨fun i => ?_, ?_, fun i => ?_⟩
      · simpa using lift_vf z.2 i
      · simpa using (e.symm ⟨baseFun z.1, lift_base_mem z.2⟩).2
      · have h := he (e.symm ⟨baseFun z.1, lift_base_mem z.2⟩)
        rw [Equiv.apply_symm_apply] at h
        simp only [replaceBase_inl, replaceBase_inr]
        show iRv (z.1 (Sum.inl i)) =
          X.f ((e.symm ⟨baseFun z.1, lift_base_mem z.2⟩ : X.U) : Fin m → M) i
        rw [← h]
        exact lift_rv z.2 i⟩
  left_inv z := by
    apply Subtype.ext
    funext j
    cases j with
    | inl i => simp
    | inr b =>
        simp only [replaceBase_inr, baseFun_replaceBase]
        rw [Equiv.symm_apply_apply]
        rfl
  right_inv z := by
    apply Subtype.ext
    funext j
    cases j with
    | inl i => simp
    | inr b =>
        simp only [replaceBase_inr, baseFun_replaceBase]
        rw [Equiv.apply_symm_apply]
        rfl

/-- The sorted tuples of the lift, as a subtype of the raw points of the lift: the identity on
values. -/
def liftSetToRaw (X : RVObjK (S := S) m k) : liftSet X ≃ X.lift where
  toFun x := ⟨x.1.1, x.2⟩
  invFun z := ⟨⟨z.1, lift_subset_sorted X z.2⟩, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Theorem \ref{RV:iso:class:lifted}, coordinate case**: an isomorphism of `RV`-objects whose
base map commutes with `f` lifts to a bijection of the canonical lifts, as sets of sorted tuples. -/
theorem liftSet_equiv {X Y : RVObjK (S := S) m k} (e : X.U ≃ Y.U)
    (he : ∀ u : X.U, Y.f (e u) = X.f u) : Nonempty (liftSet X ≃ liftSet Y) :=
  ⟨(liftSetToRaw X).trans ((liftEquiv X Y e he).trans (liftSetToRaw Y).symm)⟩

/-- The `rv`-fibre `rv^{-1}(f(ū))` of an object of `RV[k,·]` at a point `ū` of its domain, as a set of
`VF`-tuples: *"`rv^{-1}(f(ū))`"* in Definition \ref{def:L}. -/
def rvFibre (X : RVObjK (S := S) m k) (u : Fin m → M) : Set (Fin k → M) :=
  {a | (∀ i, iVF (a i)) ∧ ∀ i, iRv (a i) = X.f u i}

/-- **The canonical lift is the union of the `rv`-fibres over `U`** (Definition \ref{def:L}):
*"`𝕃_k(U,f) = ⋃{rv^{-1}(f(ū)) × {ū} : ū ∈ U}`"* — the fibre of `𝕃(U,f)` over a point `ū ∈ U` is
`rv^{-1}(f(ū))`, and the fibre over a point outside `U` is empty. -/
theorem liftSet_fibre {X : RVObjK (S := S) m k} {u : Fin m → M} (hu : u ∈ X.U) :
    Nonempty ({x : Sec4Dim.Tup M k m // x ∈ liftSet X ∧ baseFun (m := m) x.1 = u} ≃ rvFibre X u) := by
  refine ⟨{
    toFun := fun x =>
      ⟨vfFun x.1.1, lift_vf x.2.1, fun i => by
        show iRv (x.1.1 (Sum.inl i)) = X.f u i
        rw [lift_rv x.2.1 i, x.2.2]⟩
    invFun := fun a =>
      ⟨⟨replaceBase a.1 u, by
          intro j
          cases j with
          | inl i => exact a.2.1 i
          | inr b => exact X.U_sub hu b⟩, by
        show replaceBase a.1 u ∈ X.lift
        exact ⟨fun i => by simpa using a.2.1 i, by simpa using hu,
          fun i => by simpa using a.2.2 i⟩, baseFun_replaceBase a.1 u⟩
    left_inv := fun x => by
      apply Subtype.ext
      apply Subtype.ext
      funext j
      cases j with
      | inl i => rfl
      | inr b =>
          show u b = x.1.1 (Sum.inr b)
          exact (congrFun x.2.2 b).symm
    right_inv := fun a => by
      apply Subtype.ext
      funext i
      rfl }⟩

/-! ## Part 4. Isomorphism classes of `RV[k,·]` -/

/-- `X` and `Y` are isomorphic objects of `RV[k,·]`.  The weight condition is the paper's *"For any
`RV[k,·]`-isomorphism `F : (U, f) → (V, g)` and any `ū ∈ U`, by definition,
`wgt(f(ū)) = wgt((g∘F)(ū))`"*, i.e. the volumetric condition of Definition \ref{defn:RV:cat} in both
directions.  (The paper's isomorphism is moreover *definable*; see the header for why only the
underlying bijection is recorded.) -/
def IsoRV (X Y : RVObjK (S := S) m k) : Prop :=
  ∃ e : X.U ≃ Y.U, ∀ u : X.U, SP.weight (Y.f (e u)) = SP.weight (X.f u)

theorem IsoRV.refl (X : RVObjK (S := S) m k) : IsoRV X X :=
  ⟨Equiv.refl _, fun _ => rfl⟩

theorem IsoRV.symm {X Y : RVObjK (S := S) m k} (h : IsoRV X Y) : IsoRV Y X := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun v => ?_⟩
  have h' := he (e.symm v)
  rw [Equiv.apply_symm_apply] at h'
  exact h'.symm

theorem IsoRV.trans {X Y Z : RVObjK (S := S) m k} (h : IsoRV X Y) (h' : IsoRV Y Z) :
    IsoRV X Z := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun u => (he' (e u)).trans (he u)⟩

/-- The isomorphism relation on `RV[k,·]` as a setoid. -/
def setoidRV (S : SP M) (m k : ℕ) : Setoid (RVObjK (S := S) m k) where
  r := IsoRV
  iseqv := ⟨IsoRV.refl, IsoRV.symm, IsoRV.trans⟩

/-- The isomorphism classes of `RV[k,·]` — the generators of the paper's `K₊RV[k,·]`. -/
abbrev RVClass (S : SP M) (m k : ℕ) : Type _ := Quotient (setoidRV (M := M) S m k)

/-! ## Part 5. The objects of `VF[k,·]` and their isomorphism classes -/

/-- **The paper's `VF[k,·]`** (Definition \ref{defn:VF:cat}): *"The objects of the category
`VF[k,·]` are the definable subsets of `VF`-dimension `≤ k`"*.  The ambient is fixed at `VF^k × RV^m`
— the ambient in which the canonical lift `𝕃_k(U,f)` lies — and the dimension bound is §4's
`Sec4Dim.HasDim`. -/
def VFObject (S : SP M) (m k : ℕ) : Type _ :=
  {B : Set (Sec4Dim.Tup M k m) // Sec4Dim.Definable S B ∧ Sec4Dim.HasDim S B k}

/-- Isomorphism in `VF[k,·]`: a bijection of the underlying definable sets.  (The paper's morphisms
are the *definable* functions; see the header for why only the underlying bijection is recorded.) -/
def IsoVF {S : SP M} {m k : ℕ} (B C : VFObject (M := M) S m k) : Prop := Nonempty (B.1 ≃ C.1)

theorem IsoVF.refl {S : SP M} {m k : ℕ} (B : VFObject (M := M) S m k) : IsoVF B B :=
  ⟨Equiv.refl _⟩

theorem IsoVF.symm {S : SP M} {m k : ℕ} {B C : VFObject (M := M) S m k} (h : IsoVF B C) :
    IsoVF C B := by
  obtain ⟨e⟩ := h
  exact ⟨e.symm⟩

theorem IsoVF.trans {S : SP M} {m k : ℕ} {B C D : VFObject (M := M) S m k}
    (h : IsoVF B C) (h' : IsoVF C D) : IsoVF B D := by
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := h'
  exact ⟨e.trans e'⟩

/-- The isomorphism relation on `VF[k,·]` as a setoid. -/
def setoidVF (S : SP M) (m k : ℕ) : Setoid (VFObject (M := M) S m k) where
  r := IsoVF
  iseqv := ⟨IsoVF.refl, IsoVF.symm, IsoVF.trans⟩

/-- The isomorphism classes of `VF[k,·]` — the generators of the paper's `K₊VF[k,·]`. -/
abbrev VFClass (S : SP M) (m k : ℕ) : Type _ := Quotient (setoidVF (M := M) S m k)

/-- `VF[k,·]` is inhabited — the empty definable set is an object of `VF`-dimension `0 ≤ k`.  This
makes the surjectivity hypothesis `LiftData.surj_lift` non-vacuous on its target. -/
def VFObject.empty (S : SP M) (m k : ℕ) : VFObject (M := M) S m k :=
  ⟨∅, ⟨⟨⊥, WellSorted.falsum (Sec4Dim.fSort k m), by intro x; simp⟩,
    k, le_rfl, m, id, Sec4Dim.definableFun_id S ∅, by intro y; simp⟩⟩

/-! ## Part 6. The lift of objects and its behaviour on isomorphism classes -/

/-- The data of Definition \ref{def:L} together with the two results of the earlier sections that
Corollary \ref{L:semigroup:hom} uses.  Per the author's standing instruction each of these is the
paper's own sentence, carried as a hypothesis (no `axiom`, no `sorry`). -/
structure LiftData (S : SP M) (m k : ℕ) where
  /-- **Definition \ref{def:L}**: *"For any `(U,f) ∈ RV[k,·]`, let `𝕃_k(U,f) = ⋃{rv^{-1}(f(ū)) ×
  {ū} : ū ∈ U}`.  The map `𝕃_k : ob RV[k,·] → ob VF[k,·]` is called the `k`th canonical `RV`-lift."*
  (That `𝕃_k(U,f)` is an object of `VF[k,·]` — definable, of `VF`-dimension `≤ k` — is what the
  codomain type records; see the header.) -/
  L : RVObjK (S := S) m k → VFObject (S := S) m k
  /-- `𝕃` is the *canonical* lift: as a set of tuples it is `liftSet`. -/
  L_val : ∀ X, (L X).1 = liftSet X
  /-- **Theorem \ref{RV:iso:class:lifted}** (Theorem 7.6, `paper.tex` 1627; §5 and §6 given):
  *"Suppose that the substructure `S` is `(VF, Γ)`-generated.  Let `C ⊆ (RV^×)^n × (RV^×)^n` be a
  definable subset such that both `pr_{≤n} ↾ C` and `pr_{>n} ↾ C` are finite-to-one.  Then there is a
  definable subset `C^↑ ⊆ VF^n × VF^n` that lifts `C`."*  In the form the corollary uses:
  isomorphic `RV`-objects have isomorphic lifts. -/
  iso_lift : ∀ X Y : RVObjK (S := S) m k, IsoRV X Y → IsoVF (L X) (L Y)
  /-- **Corollary \ref{L:surjective}** (§6, assumed as given): *"The map `𝕃 : ob RV[k,·] → ob
  VF[k,·]` is surjective on the isomorphism classes of `VF[k,·]`."*  This is the paper's *"By
  Corollary \ref{L:surjective} it is surjective."* -/
  surj_lift : ∀ Z : VFObject (S := S) m k, ∃ X : RVObjK (S := S) m k, IsoVF Z (L X)

namespace LiftData

variable (D : LiftData (M := M) S m k)

/-- `LiftData` is consistent: its surjectivity hypothesis, applied to the empty `VF`-object
(`VFObject.empty`), produces an `RV`-object.  So the hypotheses of the corollary are not vacuous on
the `RV` side. -/
theorem nonempty (D : LiftData (M := M) S m k) : Nonempty (RVObjK (S := S) m k) :=
  let ⟨X, _⟩ := D.surj_lift (VFObject.empty S m k)
  ⟨X⟩

/-- **`𝕃` is well defined on isomorphism classes** — the paper's *"So `𝕃` induces a map on the
isomorphism classes"*, with Theorem \ref{RV:iso:class:lifted} supplying the compatibility. -/
def LClass : RVClass (M := M) S m k → VFClass (M := M) S m k :=
  Quotient.map D.L (fun _ _ h => D.iso_lift _ _ h)

theorem LClass_mk (X : RVObjK (S := S) m k) :
    D.LClass (Quotient.mk _ X) = Quotient.mk _ (D.L X) :=
  Quotient.map_mk _ _ X

/-- **The induced map on isomorphism classes is surjective** — the paper's *"By Corollary
\ref{L:surjective} it is surjective."* -/
theorem LClass_surjective : Function.Surjective D.LClass := by
  intro c
  induction c using Quotient.inductionOn with
  | h Z =>
      obtain ⟨X, hX⟩ := D.surj_lift Z
      exact ⟨Quotient.mk _ X, by rw [D.LClass_mk]; exact Quotient.sound (IsoVF.symm hX)⟩

/-- **Theorem \ref{RV:iso:class:lifted} in the coordinate case, as an isomorphism of `VF[k,·]`**:
when the `RV`-isomorphism is given by a base bijection commuting with `f`, the lifts are isomorphic
objects of `VF[k,·]` outright — the hypothesis `iso_lift` is not needed and is not vacuous. -/
theorem iso_lift_of_coord {X Y : RVObjK (S := S) m k} (e : X.U ≃ Y.U)
    (he : ∀ u : X.U, Y.f (e u) = X.f u) : IsoVF (D.L X) (D.L Y) := by
  rw [IsoVF, D.L_val X, D.L_val Y]
  exact liftSet_equiv e he

end LiftData

/-! ## Part 7. Corollary \ref{L:semigroup:hom}: surjective homomorphisms of Grothendieck semigroups -/

/-- A map that is well defined and surjective on isomorphism classes induces a surjection of the
quotient types. -/
theorem quotient_map_surjective {α β : Type*} {rα : Setoid α} {rβ : Setoid β} {g : α → β}
    (hwell : ∀ a a', a ≈ a' → g a ≈ g a') (hsurj : ∀ b, ∃ a, g a ≈ b) :
    Function.Surjective (Quotient.map g hwell) := by
  intro c
  induction c using Quotient.inductionOn with
  | h b =>
      obtain ⟨a, ha⟩ := hsurj b
      exact ⟨Quotient.mk rα a, by rw [Quotient.map_mk]; exact Quotient.sound ha⟩

/-- A surjection of generators of a free commutative monoid induces a surjection of the monoids:
every element is a finite sum of generators. -/
theorem mapDomain_surjective {α β : Type*} {f : α → β} (hf : Function.Surjective f) :
    Function.Surjective (Finsupp.mapDomain (M := ℕ) f) := by
  intro g
  induction g using Finsupp.induction with
  | zero => exact ⟨0, by simp⟩
  | single_add a b g' _ hb ih =>
      obtain ⟨x, hx⟩ := hf a
      obtain ⟨g'', hg''⟩ := ih
      refine ⟨Finsupp.single x b + g'', ?_⟩
      simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single, hg'', hx]

/-- A surjection of generators of a free abelian group induces a surjection of the groups. -/
theorem freeAbelianGroup_map_surjective {α β : Type*} {f : α → β}
    (hf : Function.Surjective f) : Function.Surjective (FreeAbelianGroup.map f) := by
  intro y
  induction y using FreeAbelianGroup.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of a => obtain ⟨x, hx⟩ := hf a; exact ⟨FreeAbelianGroup.of x, by simp [hx]⟩
  | neg a ih => obtain ⟨x, hx⟩ := ih; exact ⟨-x, by simp [hx]⟩
  | add a b iha ihb =>
      obtain ⟨x, hx⟩ := iha
      obtain ⟨y, hy⟩ := ihb
      exact ⟨x + y, by simp [hx, hy]⟩

/-- **Corollary \ref{L:semigroup:hom} as a schema** — *"The map `𝕃` induces surjective homomorphisms
between various Grothendieck semigroups"*: for **any** two categories of definable sets carrying a
lift map `g` that is well defined on isomorphism classes and surjective on them, the induced map of
Grothendieck semigroups `K₊` is a surjective homomorphism.  This is the whole of the corollary's
argument beyond Theorem \ref{RV:iso:class:lifted} and Corollary \ref{L:surjective}: it is why *"the
other cases are handled similarly"*.  `L_semigroup_hom` and `L_semigroup_hom_fin` are its instances
in the §4 categories. -/
theorem grothendieck_semigroup_hom_surjective {α β : Type*} {rα : Setoid α} {rβ : Setoid β}
    {g : α → β} (hwell : ∀ a a', a ≈ a' → g a ≈ g a') (hsurj : ∀ b, ∃ a, g a ≈ b) :
    ∃ φ : (Quotient rα →₀ ℕ) →+ (Quotient rβ →₀ ℕ),
      Function.Surjective φ ∧ ∀ a,
        φ (Finsupp.single (Quotient.mk rα a) 1) = Finsupp.single (Quotient.mk rβ (g a)) 1 :=
  ⟨Finsupp.mapDomain.addMonoidHom (Quotient.map g hwell),
    mapDomain_surjective (quotient_map_surjective hwell hsurj),
    fun a => by
      rw [Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single, Quotient.map_mk]⟩

/-- **Corollary \ref{L:semigroup:hom} as a schema**, groupified (`K₀`). -/
theorem grothendieck_group_hom_surjective {α β : Type*} {rα : Setoid α} {rβ : Setoid β}
    {g : α → β} (hwell : ∀ a a', a ≈ a' → g a ≈ g a') (hsurj : ∀ b, ∃ a, g a ≈ b) :
    ∃ Φ : FreeAbelianGroup (Quotient rα) →+ FreeAbelianGroup (Quotient rβ),
      Function.Surjective Φ ∧ ∀ a,
        Φ (FreeAbelianGroup.of (Quotient.mk rα a)) =
          FreeAbelianGroup.of (Quotient.mk rβ (g a)) :=
  ⟨FreeAbelianGroup.map (Quotient.map g hwell),
    freeAbelianGroup_map_surjective (quotient_map_surjective hwell hsurj),
    fun a => FreeAbelianGroup.map_of_apply _⟩

/-- The paper's `K₊C`, the *Grothendieck semigroup* of a category `C`: *"the semigroup generated by
the isomorphism classes `[A]` of `C`, subject to the relation `[A] + [B] = [A ∪ B] + [A ∩ B]`"*.
Since `C` always has disjoint unions, *"the elements of `K₊C` are precisely the isomorphism classes of
`C`"*, so `K₊C` is the free commutative monoid on the classes — `α →₀ ℕ` for `α` the class type. -/
abbrev GrothendieckSemigroup (α : Type*) : Type _ := α →₀ ℕ

/-- The paper's `K₀C`, the *Grothendieck group* of `C`: *"the formal groupification `(ℤ^{(K₊C)}, ⊕)/C`
of `K₊C`"* — the free abelian group on the classes. -/
abbrev GrothendieckGroup (α : Type*) : Type _ := FreeAbelianGroup α

/-- **Corollary \ref{L:semigroup:hom}**, `K₊` form: *"The map `𝕃` induces surjective homomorphisms
between various Grothendieck semigroups, for example: `K₊RV[k,·] → K₊VF[k,·]`"* — the free
commutative monoid on the isomorphism classes of `RV[k,·]` maps onto that on the isomorphism classes
of `VF[k,·]`, by `[X] ↦ [𝕃X]`, and the map is surjective. -/
theorem L_semigroup_hom (D : LiftData (M := M) S m k) :
    ∃ φ : GrothendieckSemigroup (RVClass (M := M) S m k) →+
        GrothendieckSemigroup (VFClass (M := M) S m k),
      Function.Surjective φ ∧ ∀ X : RVObjK (S := S) m k,
        φ (Finsupp.single (Quotient.mk _ X) 1) = Finsupp.single (Quotient.mk _ (D.L X)) 1 :=
  ⟨Finsupp.mapDomain.addMonoidHom D.LClass, mapDomain_surjective D.LClass_surjective,
    fun X => by
      rw [Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single, D.LClass_mk]⟩

/-- **Corollary \ref{L:semigroup:hom}**, `K₀` form: the same statement after formal groupification,
*"`K₀RV[k,·] → K₀VF[k,·]`"*. -/
theorem L_group_hom (D : LiftData (M := M) S m k) :
    ∃ Φ : GrothendieckGroup (RVClass (M := M) S m k) →+
        GrothendieckGroup (VFClass (M := M) S m k),
      Function.Surjective Φ ∧ ∀ X : RVObjK (S := S) m k,
        Φ (FreeAbelianGroup.of (Quotient.mk _ X)) = FreeAbelianGroup.of (Quotient.mk _ (D.L X)) :=
  ⟨FreeAbelianGroup.map D.LClass, freeAbelianGroup_map_surjective D.LClass_surjective,
    fun X => FreeAbelianGroup.map_of_apply _⟩


/-! ## Part 8. The paper's second arrow: `K₊RV[k] → K₊VF[k]`

Corollary \ref{L:semigroup:hom} displays two maps, *"`K₊ RV[k,·] → K₊ VF[k,·]`, `K₊ RV[k] → K₊ VF[k]`"*,
and closes its proof with *"The other cases are handled similarly."*  This part records the second
arrow: `RV[k]` is Definition \ref{defn:RV:cat}'s finite-to-one subcategory of `RV[k,·]`
(`SP.RVObj.FiniteToOne`), and `VF[k]` is the full subcategory of `VF[k,·]` of the objects *"that have
`RV`-fiber dimension `0` (that is, all the `RV`-fibers are finite)"*.  The same two ingredients are
assumed for it, in the form Corollary \ref{L:surjective} states them: *"The map `𝕃 : ob RV[k] → ob
VF[k]` is surjective on the isomorphism classes of `VF[k]`."* -/

/-- **`B` has finite `RV`-fibres** — the condition defining the full subcategory `VF[k]` of
`VF[k,·]`: *"The category `VF[k]` is the full subcategory of `VF[k,·]` of the definable subsets that
have `RV`-fiber dimension `0` (that is, all the `RV`-fibers are finite)."* -/
def RVFibresFinite {k m : ℕ} (B : Set (Sec4Dim.Tup M k m)) : Prop :=
  ∀ t : Fin m → M,
    {x : Sec4Dim.Tup M k m | x ∈ B ∧ (fun b => (x : Fin k ⊕ Fin m → M) (Sum.inr b)) = t}.Finite

/-- **An object of `VF[k]`**: an object of `VF[k,·]` with finite `RV`-fibres. -/
def VFObjectFin (S : SP M) (m k : ℕ) : Type _ :=
  {B : VFObject (M := M) S m k // RVFibresFinite (M := M) B.1}

/-- **An object of `RV[k]`**: an object of `RV[k,·]` that is finite-to-one over `RV^k` — *"If `F` is
definable, volumetric, and, for every `t̄ ∈ RV^k` the subset `(f'∘F)(f^{-1}(t̄))` is finite, then it
is a morphism in `mor RV[k,·]`"*, and the objects of `RV[k]` are those whose identity has finite
fibres. -/
def RVObjKFin (S : SP M) (m k : ℕ) : Type _ :=
  {X : RVObjK (M := M) S m k // X.FiniteToOne}

/-- Isomorphism of objects of `RV[k]`: the underlying `RV[k,·]`-isomorphism. -/
def IsoRVFin {S : SP M} {m k : ℕ} (X Y : RVObjKFin (M := M) S m k) : Prop := IsoRV X.1 Y.1

theorem IsoRVFin.refl {S : SP M} {m k : ℕ} (X : RVObjKFin (M := M) S m k) : IsoRVFin X X :=
  IsoRV.refl _

theorem IsoRVFin.symm {S : SP M} {m k : ℕ} {X Y : RVObjKFin (M := M) S m k}
    (h : IsoRVFin X Y) : IsoRVFin Y X := IsoRV.symm h

theorem IsoRVFin.trans {S : SP M} {m k : ℕ} {X Y Z : RVObjKFin (M := M) S m k}
    (h : IsoRVFin X Y) (h' : IsoRVFin Y Z) : IsoRVFin X Z := IsoRV.trans h h'

/-- The isomorphism relation on `RV[k]` as a setoid. -/
def setoidRVFin (S : SP M) (m k : ℕ) : Setoid (RVObjKFin (M := M) S m k) where
  r := IsoRVFin
  iseqv := ⟨IsoRVFin.refl, fun h => IsoRVFin.symm h, fun h h' => IsoRVFin.trans h h'⟩

/-- The isomorphism classes of `RV[k]` — the generators of `K₊RV[k]`. -/
abbrev RVClassFin (S : SP M) (m k : ℕ) : Type _ := Quotient (setoidRVFin (M := M) S m k)

/-- Isomorphism of objects of `VF[k]`: a bijection of the underlying sets. -/
def IsoVFFin {S : SP M} {m k : ℕ} (B C : VFObjectFin (M := M) S m k) : Prop :=
  Nonempty (B.1.1 ≃ C.1.1)

theorem IsoVFFin.refl {S : SP M} {m k : ℕ} (B : VFObjectFin (M := M) S m k) : IsoVFFin B B :=
  ⟨Equiv.refl _⟩

theorem IsoVFFin.symm {S : SP M} {m k : ℕ} {B C : VFObjectFin (M := M) S m k}
    (h : IsoVFFin B C) : IsoVFFin C B := by
  obtain ⟨e⟩ := h
  exact ⟨e.symm⟩

theorem IsoVFFin.trans {S : SP M} {m k : ℕ} {B C D : VFObjectFin (M := M) S m k}
    (h : IsoVFFin B C) (h' : IsoVFFin C D) : IsoVFFin B D := by
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := h'
  exact ⟨e.trans e'⟩

/-- The isomorphism relation on `VF[k]` as a setoid. -/
def setoidVFFin (S : SP M) (m k : ℕ) : Setoid (VFObjectFin (M := M) S m k) where
  r := IsoVFFin
  iseqv := ⟨IsoVFFin.refl, fun h => IsoVFFin.symm h, fun h h' => IsoVFFin.trans h h'⟩

/-- The isomorphism classes of `VF[k]` — the generators of `K₊VF[k]`. -/
abbrev VFClassFin (S : SP M) (m k : ℕ) : Type _ := Quotient (setoidVFFin (M := M) S m k)

/-- Corollary \ref{L:semigroup:hom}'s second arrow, on the level of object data: the lift of objects
of `RV[k]` (Definition \ref{def:L} restricted to the finite-to-one subcategory, whose image lies in
`VF[k]`), Theorem \ref{RV:iso:class:lifted} for it, and Corollary \ref{L:surjective}'s second
sentence, *"The map `𝕃 : ob RV[k] → ob VF[k]` is surjective on the isomorphism classes of
`VF[k]`."* -/
structure LiftDataFin (S : SP M) (m k : ℕ) where
  /-- Definition \ref{def:L} restricted to `RV[k]`: its image is in `VF[k]` (the lift of a
  finite-to-one object has finite `RV`-fibres — §5's `RV`-pullback theorem). -/
  L : RVObjKFin (S := S) m k → VFObjectFin (S := S) m k
  /-- `𝕃` is the canonical lift, as a set of tuples. -/
  L_val : ∀ X, (L X).1.1 = liftSet X.1
  /-- **Theorem \ref{RV:iso:class:lifted}**, in the `RV[k]`/`VF[k]` case. -/
  iso_lift : ∀ X Y : RVObjKFin (S := S) m k, IsoRVFin X Y → IsoVFFin (L X) (L Y)
  /-- **Corollary \ref{L:surjective}**, second sentence. -/
  surj_lift : ∀ Z : VFObjectFin (S := S) m k, ∃ X : RVObjKFin (S := S) m k, IsoVFFin Z (L X)

namespace LiftDataFin

variable (D : LiftDataFin (M := M) S m k)

/-- `𝕃` is well defined on isomorphism classes of `RV[k]`. -/
def LClass : RVClassFin (M := M) S m k → VFClassFin (M := M) S m k :=
  Quotient.map D.L (fun _ _ h => D.iso_lift _ _ h)

theorem LClass_mk (X : RVObjKFin (S := S) m k) :
    D.LClass (Quotient.mk _ X) = Quotient.mk _ (D.L X) :=
  Quotient.map_mk _ _ X

/-- The induced map on isomorphism classes of `RV[k]` is surjective. -/
theorem LClass_surjective : Function.Surjective D.LClass := by
  intro c
  induction c using Quotient.inductionOn with
  | h Z =>
      obtain ⟨X, hX⟩ := D.surj_lift Z
      exact ⟨Quotient.mk _ X, by rw [D.LClass_mk]; exact Quotient.sound (IsoVFFin.symm hX)⟩

end LiftDataFin

/-- **Corollary \ref{L:semigroup:hom}**, second arrow, `K₊` form: *"`K₊RV[k] → K₊VF[k]`"* is a
surjective homomorphism — the free commutative monoid on the isomorphism classes of `RV[k]` maps onto
that on the isomorphism classes of `VF[k]`, by `[X] ↦ [𝕃X]`. -/
theorem L_semigroup_hom_fin (D : LiftDataFin (M := M) S m k) :
    ∃ φ : GrothendieckSemigroup (RVClassFin (M := M) S m k) →+
        GrothendieckSemigroup (VFClassFin (M := M) S m k),
      Function.Surjective φ ∧ ∀ X : RVObjKFin (S := S) m k,
        φ (Finsupp.single (Quotient.mk _ X) 1) = Finsupp.single (Quotient.mk _ (D.L X)) 1 :=
  ⟨Finsupp.mapDomain.addMonoidHom D.LClass, mapDomain_surjective D.LClass_surjective,
    fun X => by
      rw [Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single, D.LClass_mk]⟩

/-- **Corollary \ref{L:semigroup:hom}**, second arrow, `K₀` form. -/
theorem L_group_hom_fin (D : LiftDataFin (M := M) S m k) :
    ∃ Φ : GrothendieckGroup (RVClassFin (M := M) S m k) →+
        GrothendieckGroup (VFClassFin (M := M) S m k),
      Function.Surjective Φ ∧ ∀ X : RVObjKFin (S := S) m k,
        Φ (FreeAbelianGroup.of (Quotient.mk _ X)) = FreeAbelianGroup.of (Quotient.mk _ (D.L X)) :=
  ⟨FreeAbelianGroup.map D.LClass, freeAbelianGroup_map_surjective D.LClass_surjective,
    fun X => FreeAbelianGroup.map_of_apply _⟩

end Sec7
end SpecialTransformations.Milestone0
