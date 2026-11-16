module

/-
# §4.2 of Yin, *Special transformations in algebraically closed valued fields*

`paper.tex` lines 967--1127, *"Categories of definable subsets"*: the `RV`-side of the two
categories — Definition \ref{def:L} (the canonical lift), Lemma \ref{RV:morphism:condition} and
Remark \ref{RV:isomorphism:weaker:condition}.

This file builds on the definitions of `QE/Sec4Categories.lean` (`RVObj`, `weight`, `appendInfty`,
`Volumetric`, `RVHom`, `RVObj.lift`, `RVObj.companion`, `RVObj.rvImage`) and of
`QE/Sec3_frozen.lean` (`SP`, `SP.acl`, `SP.paramSet`, `Definable`).

## Proved (no hypotheses beyond the definitions)

* **Definition \ref{def:L}.**  `rvMap` is the paper's `rv` on a tuple of `VF^k × U`-shape;
  `rvImage` is `rvMap '' ·` (`mem_rvImage_iff`, `rvImage_eq_image`); the terms of the paper's union
  are the `rv`-polydiscs `rvPolydisc X u` = `rv^{-1}(f(ū)) × {ū}`, and they are exactly the fibres of
  the lift (`rvPolydisc_eq_lift_fibre`); `rv(𝕃(U,f)) = U_f` as an equality of sets
  (`rvImage_lift_eq_companion`), and the `rv`-image of one polydisc is the companion point
  (`rvMap_image_rvPolydisc`).
* **The induced map `F_{f,f'}`** (paper 1078--1082): `companionMap`, that it maps `U_f` into
  `U'_{f'}` (`companionMap_mem_companion`), that it is the identity for the identity
  (`companionMap_id`) and functorial (`companionMap_comp`), and that its fibre image over `t̄` is
  the paper's `(f'∘F)(f^{-1}(t̄))` (`image_companionFibre`).
* **Both squares of the diagram of Lemma \ref{RV:morphism:condition}.**  `LiftCommutes` is the
  paper's hypothesis (*"`F^↑` … such that the diagram … commutes"*); from the single equation
  `rv ∘ F^↑ = F_{f,f'} ∘ rv` follow the second square `pr_{>k} ∘ F^↑ = F ∘ pr_{>k}`
  (`LiftCommutes.baseOf_eq`) and the `RV`-part `rv(b_i) = f'_i(Fū)` (`LiftCommutes.rvPart_eq`);
  the fibre over `ū` is carried into the fibre over `Fū` (`LiftCommutes.fibre_maps`).  The
  hypothesis is satisfiable: the identity of `𝕃(U,f)` sits over the identity of `(U,f)`
  (`LiftCommutes.id`).
* **`RV[k,·]` is a category once definability is forgotten.**  `RVMap` is Definition
  \ref{defn:RV:cat}'s list of conditions on a morphism minus *"`F` is definable"*: identity
  (`RVMap.id`) and composition (`RVMap.comp`) are proved, together with extensionality
  (`RVMap.ext`) and the category laws (`RVMap.comp_assoc`, `RVMap.id_comp`, `RVMap.comp_id`), so the
  geometric part of §4.2 closes without any model theory.  `RVHom.comp` then isolates the one missing ingredient exactly: the
  definability of the composite's graph, carried as its hypothesis `hdef`.  The same for the
  paper's *"the inclusion map is a morphism"* (`RVMap.restrictIncl`, `RVHom.restrictIncl`).

## Proved modulo named §2--§3 hypotheses

* **Lemma \ref{RV:morphism:condition}, in the paper's own reduced form**
  (`rv_morphism_condition_acl`): volumetric `F` plus a definable `F^↑` whose diagram commutes give
  the paper's *"It is enough to show that … `(f'_i ∘ F)(ū) ∈ acl(f(ū))`"* for every `ū ∈ U`.  The
  hypotheses it consumes from earlier sections are the fields of `RVMorphismInputs`, each the
  paper's own statement with its label: §3 `dcl:to:ac`, §3 Corollary `acl:VF:transfer:acl:RV`, and
  the two §2 facts `f(t̄) ∈ ⟨t̄⟩` and `rv` preserving algebraicity.  `AclOf` is the paper's `acl`
  over an arbitrary parameter set at an arbitrary sort (the tree's `SP.acl` is `VF`-sorted only,
  and `acl_imp_AclOf` embeds it); it is needed because the paper's conclusion here is `RV`-sorted.

## Not claimed, and why

The passage from `(f'_i∘F)(ū) ∈ acl(f(ū))` to the finite-fibre condition of Definition
\ref{defn:RV:cat} is a single line in the paper ("*It is enough*") and needs two things that are not
in the tree: (i) that `(f'∘F)(f^{-1}(t̄))` is **definable** — the projection lemma, i.e. turning
free coordinates into bound variables, the same missing composition/substitution lemma that
`dim:VF:pullback`, `full:dim:open:poly` and §7--§10 need; and (ii) that a definable subset of `RV^k`
all of whose points are algebraic over `t̄` is finite (saturation of the monster).  Without (i) the
set whose finiteness is wanted cannot even be *stated* as a definable set, so asserting
`RVHom.finite_fibres` here would either be a definitional restatement or an unproved claim.  The
lemma is therefore delivered in the paper's reduced form, which is the part the paper actually
argues.

Remark \ref{RV:isomorphism:weaker:condition} (drop volumetric when `F` and `F^↑` are bijections) is
reduced by the paper to Corollary \ref{VF:dim:rv:polydisc} plus invariance of `dim_VF` under
definable bijection; `dim_VF` is a §4.1 object and is not defined in this file, so the remark is not
formalized here (see `LiftCommutes.polydisc_rvImage` for the diagram half of it).

Compiled with `lean M5Sec42.lean` against `.scratch2/sec3`'s oleans: exit 0, no `sorry`, and every
`#print axioms` in the audit at the end is within `{propext, Classical.choice, Quot.sound}`.
-/
public import Sec4Categories

@[expose] public section

open FirstOrder FirstOrder.Language
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false

namespace SpecialTransformations.Milestone0
open LRV

namespace SP

variable {M : Type*} [LRV.Structure M]

/-! ## Part 1. Two projections on a `(Fin k ⊕ β)`-tuple

The paper's Section 4.2 works with `𝕃_k(U,f) ⊆ VF^k × U` and with the companion `U_f ⊆ RV^k × U`
(Definition \ref{def:L} and Definition \ref{defn:RV:cat}); both are sets of tuples indexed by
`Fin k ⊕ β`, the first `k` coordinates being the `VF`- (resp. `RV`-) coordinates and the rest the
point of `U`.  The three maps `vfPart`, `baseOf` and `rvMap` below are the paper's
`pr_{≤k}`, `pr_{>k}` and `rv` on such a tuple. -/

/-- The `VF`/`RV` part of a tuple: the paper's `pr_{≤k}`. -/
def vfPart {k : ℕ} {β : Type} (y : Fin k ⊕ β → M) : Fin k → M := fun i => y (Sum.inl i)

/-- The base part of a tuple: the paper's `pr_{>k}`. -/
def baseOf {k : ℕ} {β : Type} (y : Fin k ⊕ β → M) : β → M := fun b => y (Sum.inr b)

/-- The tuple `(a, u)` assembled from its parts. -/
def mkTuple {k : ℕ} {β : Type} (a : Fin k → M) (u : β → M) : Fin k ⊕ β → M := Sum.elim a u

@[simp] theorem vfPart_mkTuple {k : ℕ} {β : Type} (a : Fin k → M) (u : β → M) :
    vfPart (mkTuple a u) = a := rfl

@[simp] theorem baseOf_mkTuple {k : ℕ} {β : Type} (a : Fin k → M) (u : β → M) :
    baseOf (mkTuple a u) = u := rfl

theorem mkTuple_vfPart_baseOf {k : ℕ} {β : Type} (y : Fin k ⊕ β → M) :
    mkTuple (vfPart y) (baseOf y) = y := by
  funext i; cases i <;> rfl

/-- First component of a tuple split as `α ⊕ γ`, with the split spelled out (the tree's `baseProj`
leaves it implicit, which is ambiguous when the same space is split in two different ways). -/
def fstProj {α γ : Type} (z : (α ⊕ γ) → M) : α → M := fun a => z (Sum.inl a)

/-- Second component of a tuple split as `α ⊕ γ`. -/
def sndProj {α γ : Type} (z : (α ⊕ γ) → M) : γ → M := fun c => z (Sum.inr c)

/-- Assemble a tuple from two parts of arbitrary index types. -/
def mkPair {α γ : Type} (a : α → M) (c : γ → M) : (α ⊕ γ) → M := Sum.elim a c

@[simp] theorem fstProj_mkPair {α γ : Type} (a : α → M) (c : γ → M) :
    fstProj (mkPair a c) = a := rfl

@[simp] theorem sndProj_mkPair {α γ : Type} (a : α → M) (c : γ → M) :
    sndProj (mkPair a c) = c := rfl

@[simp] theorem mkPair_fstProj_sndProj {α γ : Type} (z : (α ⊕ γ) → M) :
    mkPair (fstProj z) (sndProj z) = z := by
  funext i; cases i <;> rfl

theorem mkTuple_eq_mkPair {k : ℕ} {β : Type} (a : Fin k → M) (u : β → M) :
    mkTuple a u = mkPair a u := rfl

/-- `rv` coordinatewise on the `k` `VF`-coordinates, the identity on the base coordinates.  This is
the `rv` of the paper's first square of Lemma \ref{RV:morphism:condition}: `rv : 𝕃(U,f) → U_f`. -/
def rvMap {k : ℕ} {β : Type} (y : Fin k ⊕ β → M) : Fin k ⊕ β → M :=
  Sum.elim (fun i => iRv (y (Sum.inl i))) (fun b => y (Sum.inr b))

@[simp] theorem rvMap_inl {k : ℕ} {β : Type} (y : Fin k ⊕ β → M) (i : Fin k) :
    rvMap y (Sum.inl i) = iRv (y (Sum.inl i)) := rfl

@[simp] theorem rvMap_inr {k : ℕ} {β : Type} (y : Fin k ⊕ β → M) (b : β) :
    rvMap y (Sum.inr b) = y (Sum.inr b) := rfl

@[simp] theorem vfPart_rvMap {k : ℕ} {β : Type} (y : Fin k ⊕ β → M) :
    vfPart (rvMap y) = fun i => iRv (vfPart y i) := rfl

@[simp] theorem baseOf_rvMap {k : ℕ} {β : Type} (y : Fin k ⊕ β → M) :
    baseOf (rvMap y) = baseOf y := rfl

/-! ## Part 2. `rvImage` is the image of `rvMap` (Definition \ref{def:L}) -/

/-- The `rv`-image of a set of tuples is the image of the set under `rvMap`. -/
theorem mem_rvImage_iff {k : ℕ} {β : Type} {Y : Set (Fin k ⊕ β → M)}
    {y : Fin k ⊕ β → M} :
    y ∈ RVObj.rvImage Y ↔ ∃ z ∈ Y, y = rvMap z := by
  constructor
  · rintro ⟨z, hz, hinl, hinr⟩
    refine ⟨z, hz, ?_⟩
    funext i
    cases i with
    | inl i => exact hinl i
    | inr b => exact hinr b
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, fun i => rfl, fun b => rfl⟩

theorem rvImage_eq_image {k : ℕ} {β : Type} (Y : Set (Fin k ⊕ β → M)) :
    RVObj.rvImage Y = rvMap '' Y := by
  ext y
  rw [mem_rvImage_iff]
  simp only [Set.mem_image, eq_comm]

/-! ## Part 3. The companion map `F_{f,f'}` induced by a function `F : U → U'`

`paper.tex` 1078--1082: *"For any two objects `(U,f), (U',f') ∈ RV[k,·]` and any definable function
`F : U → U'` there is a naturally induced function `F_{f,f'} : U_f → U'_{f'}` given by
`(f(ū), ū) ↦ ((f'∘F)(ū), F(ū))`."* -/

section CompanionMap

variable {S : SP M} {β β' : Type} {sβ : β → SortTag} {sβ' : β' → SortTag}
  {A : Set (β → M)} {A' : Set (β' → M)} {k : ℕ}

/-- The paper's `F_{f,f'} : U_f → U'_{f'}`: on a companion point `(f(ū), ū)` it is
`((f'∘F)(ū), F(ū))`.  It is written here as a map on all tuples, so that its two squares with
`rv` and `pr_{>k}` are equations of functions. -/
def companionMap (X : RVObj S sβ A k) (Y : RVObj S sβ' A' k)
    (F : (β → M) → β' → M) (y : Fin k ⊕ β → M) : Fin k ⊕ β' → M :=
  mkTuple (Y.f (F (baseOf y))) (F (baseOf y))

@[simp] theorem vfPart_companionMap (X : RVObj S sβ A k) (Y : RVObj S sβ' A' k)
    (F : (β → M) → β' → M) (y : Fin k ⊕ β → M) :
    vfPart (companionMap X Y F y) = Y.f (F (baseOf y)) := rfl

/-- **The second square of the diagram of Lemma \ref{RV:morphism:condition}**:
`pr_{>k} ∘ F_{f,f'} = F ∘ pr_{>k}`. -/
@[simp] theorem baseOf_companionMap (X : RVObj S sβ A k) (Y : RVObj S sβ' A' k)
    (F : (β → M) → β' → M) (y : Fin k ⊕ β → M) :
    baseOf (companionMap X Y F y) = F (baseOf y) := rfl

/-- On the companion `U_f` the induced map is literally `(f(ū), ū) ↦ ((f'∘F)(ū), F(ū))`. -/
theorem companionMap_companion (X : RVObj S sβ A k) (Y : RVObj S sβ' A' k)
    (F : (β → M) → β' → M) (u : β → M) :
    companionMap X Y F (mkTuple (X.f u) u) = mkTuple (Y.f (F u)) (F u) := rfl

/-- **`F_{f,f'}` maps the companion `U_f` into the companion `U'_{f'}`.**  This needs the
hypothesis that `F` maps `U` into `U'`, which is the first field of `RVHom`. -/
theorem companionMap_mem_companion (X : RVObj S sβ A k) (Y : RVObj S sβ' A' k)
    (F : (β → M) → β' → M) (hF : ∀ u ∈ X.U, F u ∈ Y.U) :
    ∀ y ∈ X.companion, companionMap X Y F y ∈ Y.companion := by
  intro y hy
  obtain ⟨u, hu, rfl⟩ := (RVObj.mem_companion X y).1 hy
  exact (RVObj.mem_companion Y _).2 ⟨F u, hF u hu, rfl⟩

/-- `F_{f,f'}` is determined by the second square: two maps `F`, `F₁` with the same base part give
the same companion map.  (Used to compare the paper's induced map with a candidate `F^↑`.) -/
theorem companionMap_congr (X : RVObj S sβ A k) (Y : RVObj S sβ' A' k)
    {F F₁ : (β → M) → β' → M} (h : ∀ u ∈ X.U, F u = F₁ u) :
    ∀ y ∈ X.companion, companionMap X Y F y = companionMap X Y F₁ y := by
  intro y hy
  obtain ⟨u, hu, rfl⟩ := (RVObj.mem_companion X y).1 hy
  exact congrArg (fun w => mkTuple (Y.f w) w) (h u hu)

/-- `F_{f,f'}` for the identity of `(U,f)` is the identity on `U_f`. -/
theorem companionMap_id (X : RVObj S sβ A k) :
    ∀ y ∈ X.companion, companionMap X X (fun u b => u b) y = y := by
  intro y hy
  obtain ⟨u, hu, rfl⟩ := (RVObj.mem_companion X y).1 hy
  rfl

/-- `F_{f,f'}` is functorial: the companion of a composite is the composite of the companions. -/
theorem companionMap_comp {β'' : Type} {sβ'' : β'' → SortTag} {A'' : Set (β'' → M)}
    (X : RVObj S sβ A k) (Y : RVObj S sβ' A' k) (Z : RVObj S sβ'' A'' k)
    (F : (β → M) → β' → M) (G : (β' → M) → β'' → M) (y : Fin k ⊕ β → M) :
    companionMap Y Z G (companionMap X Y F y)
      = companionMap X Z (fun u => G (F u)) y := rfl

/-! ### The fibres of `F_{f,f'}`

The paper's morphism condition for an object of `RV[k,·]` is that `f'∘F` be finite-to-one over
`RV^k`.  On the companion, `F_{f,f'}` is a *function*, so its own fibres are singletons; what the
paper measures is the fibre of `pr_{≤k} ∘ F_{f,f'}`, i.e. the fibre of the companion map restricted
to the companion points lying over a fixed `t̄ ∈ RV^k`.  These are the next two lemmas. -/

/-- The fibre of `pr_{≤k}` over `t̄` in the companion `U_f`, transported to `β → M`. -/
def companionFibre (X : RVObj S sβ A k) (t : Fin k → M) : Set (β → M) :=
  {u | u ∈ X.U ∧ X.f u = t}

/-- **The image of the companion fibre over `t̄` under `F_{f,f'}` is the paper's
`(f'∘F)(f^{-1}(t̄))`.**  Definition \ref{defn:RV:cat}: *"for every `t̄ ∈ RV^k` the subset
`(f'∘F)(f^{-1}(t̄))` is finite"*. -/
theorem image_companionFibre (X : RVObj S sβ A k) (Y : RVObj S sβ' A' k)
    (F : (β → M) → β' → M) (t : Fin k → M) :
    Y.f '' (F '' companionFibre X t) =
      (fun u => Y.f (F u)) '' companionFibre X t := by
  ext v
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨F u, ⟨u, hu, rfl⟩, rfl⟩

end CompanionMap



/-! ## Part 4. The canonical lift `𝕃_k(U,f)` and its fibres (Definition \ref{def:L})

*"For any `(U,f) ∈ RV[k,·]`, let `𝕃_k(U,f) = ⋃{rv^{-1}(f(ū)) × {ū} : ū ∈ U}`."*  The terms of that
union are `rv`-polydiscs; Corollary \ref{VF:dim:rv:polydisc} computes their `VF`-dimension as
`wgt(f(ū))`, which is why they matter. -/

section Lift

variable {S : SP M} {β : Type} {sβ : β → SortTag} {A : Set (β → M)} {k : ℕ}

namespace RVObj

variable (X : RVObj S sβ A k)

/-- Membership in the lift, in the coordinates the proofs use. -/
theorem mem_lift_iff {z : Fin k ⊕ β → M} :
    z ∈ X.lift ↔ (∀ i, iVF (z (Sum.inl i))) ∧ baseOf z ∈ X.U ∧
      ∀ i, iRv (z (Sum.inl i)) = X.f (baseOf z) i := Iff.rfl

theorem lift_mem_of {a : Fin k → M} {u : β → M}
    (hVF : ∀ i, iVF (a i)) (hU : u ∈ X.U) (hrv : ∀ i, iRv (a i) = X.f u i) :
    mkTuple a u ∈ X.lift := ⟨hVF, hU, hrv⟩

/-- The paper's `rv`-polydisc `rv^{-1}(f(ū)) × {ū}`: the fibre of `𝕃_k(U,f)` over the base point
`ū`.  Corollary \ref{VF:dim:rv:polydisc} is the statement `dim_VF ≥ wgt(f(ū))` for this set. -/
def rvPolydisc (u : β → M) : Set (Fin k ⊕ β → M) :=
  {z | (∀ i, iVF (z (Sum.inl i))) ∧ baseOf z = u ∧
    ∀ i, iRv (z (Sum.inl i)) = X.f (baseOf z) i}

theorem mem_rvPolydisc_iff {u : β → M} {z : Fin k ⊕ β → M} :
    z ∈ X.rvPolydisc u ↔ (∀ i, iVF (z (Sum.inl i))) ∧ baseOf z = u ∧
      ∀ i, iRv (z (Sum.inl i)) = X.f (baseOf z) i := Iff.rfl

/-- The fibre of `𝕃_k(U,f)` over `ū ∈ U` is the `rv`-polydisc at `ū`. -/
theorem rvPolydisc_eq_lift_fibre {u : β → M} (hu : u ∈ X.U) :
    X.rvPolydisc u = {z | z ∈ X.lift ∧ baseOf z = u} := by
  ext z
  simp only [Set.mem_ofPred_eq, mem_rvPolydisc_iff, mem_lift_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, by rw [h2]; exact hu, h3⟩, h2⟩
  · rintro ⟨⟨h1, hU, hrv⟩, h2⟩
    exact ⟨h1, h2, hrv⟩

/-- The `rv`-image of an `rv`-polydisc at `ū` is the single companion point `(f(ū), ū)`.  The
reverse inclusion is where `rv` being onto the `RV` sort is used, exactly as in
`RVObj.companion_subset_rvImage_lift`. -/
theorem rvMap_image_rvPolydisc {u : β → M} (hu : u ∈ X.U)
    (hsurj : ∀ t : M, iRV t → ∃ x : M, iVF x ∧ iRv x = t) :
    rvMap '' X.rvPolydisc u = {mkTuple (X.f u) u} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_rvPolydisc_iff] at hz
    obtain ⟨h1, h2, h3⟩ := hz
    rw [h2] at h3
    have hzy : rvMap z = mkTuple (X.f u) u := by
      funext i
      cases i with
      | inl i => rw [rvMap_inl]; exact h3 i
      | inr b => rw [rvMap_inr]; exact congrFun h2 b
    rw [hzy]
    exact Set.mem_singleton _
  · rintro hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    choose a ha hrv using fun i => hsurj (X.f u i) (X.f_sorted u hu i)
    refine ⟨mkTuple a u, ?_, ?_⟩
    · rw [mem_rvPolydisc_iff]
      exact ⟨fun i => ha i, rfl, fun i => hrv i⟩
    · funext i
      cases i with
      | inl i => rw [rvMap_inl]; exact hrv i
      | inr b => rw [rvMap_inr]; rfl

end RVObj

/-- **`rv(𝕃(U,f)) = U_f`** (the paper's *"Also note that `rv(𝕃(U, f)) = U_f`"*), as an equality of
sets of tuples. -/
theorem rvImage_lift_eq_companion (X : RVObj S sβ A k)
    (hsurj : ∀ t : M, iRV t → ∃ x : M, iVF x ∧ iRv x = t) :
    RVObj.rvImage X.lift = X.companion :=
  Set.Subset.antisymm (RVObj.rvImage_lift_subset X) (RVObj.companion_subset_rvImage_lift X hsurj)

end Lift

/-! ## Part 5. The two squares of Lemma \ref{RV:morphism:condition}

The paper's diagram is

```
𝕃(U,f) --F↑--> 𝕃(U',f')
  |rv               |rv
  v                 v
  U_f --F_{f,f'}--> U'_{f'}
```

with the lower arrow the induced map of Part 3, and a second square with `pr_{>k}`.  Its
commutation is `rv ∘ F↑ = F_{f,f'} ∘ rv`; the lemmas below show that this equation, together with
`F↑` mapping the lift into the lift, forces the base part of `F↑` to be `F` and its `RV` part to be
`f' ∘ F` — which is exactly how the paper's proof reads the diagram. -/

section FirstSquare

variable {S : SP M} {β β' : Type} {sβ : β → SortTag} {sβ' : β' → SortTag}
  {A : Set (β → M)} {A' : Set (β' → M)} {k : ℕ}

/-- **The diagram hypothesis of Lemma \ref{RV:morphism:condition}**: `F↑` carries `𝕃(U,f)` into
`𝕃(U',f')` and makes the upper square commute, `rv ∘ F↑ = F_{f,f'} ∘ rv`. -/
structure LiftCommutes (X : RVObj S sβ A k) (Y : RVObj S sβ' A' k)
    (F : (β → M) → β' → M) (FUp : (Fin k ⊕ β → M) → Fin k ⊕ β' → M) : Prop where
  /-- `F↑` maps `𝕃(U,f)` into `𝕃(U',f')` -/
  maps : ∀ z ∈ X.lift, FUp z ∈ Y.lift
  /-- the upper square commutes: `rv ∘ F↑ = F_{f,f'} ∘ rv` -/
  comm : ∀ z ∈ X.lift, rvMap (FUp z) = companionMap X Y F (rvMap z)

/-- The diagram hypothesis is non-vacuous: the identity of `𝕃(U,f)` sits over the identity
morphism of `(U,f)`. -/
theorem LiftCommutes.id (X : RVObj S sβ A k) :
    LiftCommutes X X (fun u => u) (fun z => z) where
  maps := fun _ hz => hz
  comm := by
    intro z hz
    rw [RVObj.mem_lift_iff] at hz
    obtain ⟨h1, hU, hrv⟩ := hz
    have hz' : rvMap z = mkTuple (X.f (baseOf z)) (baseOf z) := by
      funext i
      cases i with
      | inl i => rw [rvMap_inl]; exact hrv i
      | inr b => rfl
    rw [hz']
    rfl

/-- **The base part of `F↑` is `F`** — the paper's second square, derived from the first. -/
theorem LiftCommutes.baseOf_eq {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k}
    {F : (β → M) → β' → M} {FUp : (Fin k ⊕ β → M) → Fin k ⊕ β' → M}
    (h : LiftCommutes X Y F FUp) {z : Fin k ⊕ β → M} (hz : z ∈ X.lift) :
    baseOf (FUp z) = F (baseOf z) := by
  have hc := congrArg baseOf (h.comm z hz)
  rw [baseOf_rvMap, baseOf_companionMap, baseOf_rvMap] at hc
  exact hc

/-- **The `RV`-part of `F↑` is `f' ∘ F`**: the paper's `(pr_i ∘ F_{f,f'})(f(ū),ū) = rv(b_i)`,
read as the statement that `rv` of the `i`-th coordinate of `F↑(ā,ū)` is `f'_i(F(ū))`. -/
theorem LiftCommutes.rvPart_eq {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k}
    {F : (β → M) → β' → M} {FUp : (Fin k ⊕ β → M) → Fin k ⊕ β' → M}
    (h : LiftCommutes X Y F FUp) {z : Fin k ⊕ β → M} (hz : z ∈ X.lift) (i : Fin k) :
    iRv (FUp z (Sum.inl i)) = Y.f (F (baseOf z)) i := by
  have hc := congrFun (congrArg vfPart (h.comm z hz)) i
  rw [vfPart_rvMap, vfPart_companionMap, baseOf_rvMap] at hc
  exact hc

/-- The lift's fibre over `ū ∈ U` is carried into the lift's fibre over `F(ū)`. -/
theorem LiftCommutes.fibre_maps {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k}
    {F : (β → M) → β' → M} {FUp : (Fin k ⊕ β → M) → Fin k ⊕ β' → M}
    (h : LiftCommutes X Y F FUp) {u : β → M} (hu : u ∈ X.U) :
    FUp '' X.rvPolydisc u ⊆ Y.rvPolydisc (F u) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [RVObj.mem_rvPolydisc_iff] at hz
  obtain ⟨h1, h2, h3⟩ := hz
  have hzlift : z ∈ X.lift := by
    rw [RVObj.mem_lift_iff]; exact ⟨h1, by rw [h2]; exact hu, h3⟩
  rw [RVObj.mem_rvPolydisc_iff]
  refine ⟨fun i => (h.maps z hzlift).1 i, ?_, fun i => ?_⟩
  · rw [h.baseOf_eq hzlift, h2]
  · rw [h.rvPart_eq hzlift i, h.baseOf_eq hzlift]

/-- On the fibre over `ū` the hypothesis `rv ∘ F↑ = F_{f,f'} ∘ rv` says that the two `rv`-polydiscs
have the same `rv`-image, namely the companion point `(f'(Fū), Fū)`.  This is the shape in which
Remark \ref{RV:isomorphism:weaker:condition} uses the diagram. -/
theorem LiftCommutes.polydisc_rvImage {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k}
    {F : (β → M) → β' → M} {FUp : (Fin k ⊕ β → M) → Fin k ⊕ β' → M}
    (h : LiftCommutes X Y F FUp) {u : β → M} (hu : u ∈ X.U)
    (hsurj : ∀ t : M, iRV t → ∃ x : M, iVF x ∧ iRv x = t) :
    rvMap '' (FUp '' X.rvPolydisc u) = {mkTuple (Y.f (F u)) (F u)} := by
  rw [Set.image_image]
  have hcomp : (fun z => rvMap (FUp z)) '' X.rvPolydisc u
      = companionMap X Y F '' (rvMap '' X.rvPolydisc u) := by
    rw [Set.image_image]
    refine Set.image_congr ?_
    intro z hz
    rw [RVObj.mem_rvPolydisc_iff] at hz
    obtain ⟨h1, h2, h3⟩ := hz
    have hzlift : z ∈ X.lift := by
      rw [RVObj.mem_lift_iff]; exact ⟨h1, by rw [h2]; exact hu, h3⟩
    exact h.comm z hzlift
  rw [hcomp, RVObj.rvMap_image_rvPolydisc X hu hsurj, Set.image_singleton]
  rfl

end FirstSquare

/-! ## Part 6. `RV[k,·]` as a category

Definition \ref{defn:RV:cat} asks a morphism to be definable, volumetric and finite-to-one over
`RV^k`.  The three conditions are closed under composition *without* any use of definability, and
composition of `RVHom` differs from that only in the definability of the composite graph.  So the
argument below splits `RVHom` into its syntactic and its geometric parts and proves the geometric
part; the syntactic part is `RVHom.comp`'s explicit hypothesis `hdef`, which is exactly the
composition lemma for definable functions. -/

section RVCategory

variable {S : SP M} {β β' β'' β''' : Type} {sβ : β → SortTag} {sβ' : β' → SortTag}
  {sβ'' : β'' → SortTag} {sβ''' : β''' → SortTag} {A : Set (β → M)} {A' : Set (β' → M)}
  {A'' : Set (β'' → M)} {A''' : Set (β''' → M)} {k : ℕ}

/-- **The geometric part of a morphism of `RV[k,·]`.**  The conditions of Definition
\ref{defn:RV:cat} other than definability: *"If `F` is definable, volumetric, and, for every
`t̄ ∈ RV^k` the subset `(f'∘F)(f^{-1}(t̄))` is finite, then it is a morphism in `mor RV[k,·]`."* -/
structure RVMap (X : RVObj S sβ A k) (Y : RVObj S sβ' A' k) where
  /-- the paper's `F : U → U'` -/
  F : (β → M) → β' → M
  /-- `F` maps `U` into `U'` -/
  maps : ∀ u ∈ X.U, F u ∈ Y.U
  /-- `F` is volumetric -/
  volumetric : Volumetric X Y F
  /-- `(f'∘F)(f^{-1}(t̄))` is finite for every `t̄` -/
  finite_fibres : ∀ t : Fin k → M,
    {v : Fin k → M | ∃ u : β → M, u ∈ X.U ∧ X.f u = t ∧ v = Y.f (F u)}.Finite

/-- Every `RVHom` is an `RVMap`: definability is an extra condition, not an alternative one. -/
def RVHom.toRVMap {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k} (h : RVHom X Y) : RVMap X Y :=
  { F := h.F, maps := h.F_maps, volumetric := h.volumetric, finite_fibres := h.finite_fibres }

/-- The finite-fibre condition, read on the companion: it is the fibre of `pr_{≤k} ∘ F_{f,f'}`. -/
theorem RVMap.finite_fibres_iff {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k}
    (F : (β → M) → β' → M) :
    (∀ t : Fin k → M,
        {v : Fin k → M | ∃ u : β → M, u ∈ X.U ∧ X.f u = t ∧ v = Y.f (F u)}.Finite) ↔
      (∀ t : Fin k → M, (Y.f '' (F '' companionFibre X t)).Finite) := by
  have hset : ∀ t : Fin k → M,
      {v : Fin k → M | ∃ u : β → M, u ∈ X.U ∧ X.f u = t ∧ v = Y.f (F u)}
        = (fun u => Y.f (F u)) '' companionFibre X t := by
    intro t
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_image, companionFibre]
    constructor
    · rintro ⟨u, hu, hfu, rfl⟩; exact ⟨u, ⟨hu, hfu⟩, rfl⟩
    · rintro ⟨u, ⟨hu, hfu⟩, rfl⟩; exact ⟨u, hu, hfu, rfl⟩
  refine forall_congr' (fun t => ?_)
  rw [image_companionFibre, hset]

/-- **The identity is a morphism.** -/
def RVMap.id (X : RVObj S sβ A k) : RVMap X X where
  F := fun u => u
  maps := fun _ hu => hu
  volumetric := Volumetric.refl X
  finite_fibres := by
    intro t
    refine (Set.finite_singleton t).subset ?_
    rintro v ⟨u, hu, hfu, rfl⟩
    exact hfu

/-- **Morphisms compose**: the paper's three conditions are closed under composition.  Volumetric
is `Volumetric.trans`; the fibre condition is that the finite fibre of `f'∘F` over `t̄` is mapped
into the fibres of `f''∘G`, each of which is finite. -/
def RVMap.comp {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k} {Z : RVObj S sβ'' A'' k}
    (g : RVMap Y Z) (f : RVMap X Y) : RVMap X Z where
  F := fun u => g.F (f.F u)
  maps := fun u hu => g.maps (f.F u) (f.maps u hu)
  volumetric := Volumetric.trans f.maps f.volumetric g.volumetric
  finite_fibres := by
    intro t
    refine (Set.Finite.biUnion (f.finite_fibres t) (fun w _ => g.finite_fibres w)).subset ?_
    rintro v ⟨u, hu, hfu, rfl⟩
    exact Set.mem_iUnion₂.2 ⟨Y.f (f.F u), ⟨u, hu, hfu, rfl⟩, f.F u, f.maps u hu, rfl, rfl⟩

/-- **Composition of morphisms in `mor RV[k,·]`.**  Every condition of Definition
\ref{defn:RV:cat} is discharged by `RVMap.comp` except definability of the composite's graph, which
is carried as `hdef`.  For `F = g.F ∘ f.F` the graph is
`{(ū,ū'') : ū ∈ U, ū'' = (g.F∘f.F)(ū)}`; that it is definable — substituting `f`'s defining
formula into `g`'s — is the missing composition lemma for definable functions, the same one that
`dim:VF:pullback`, `full:dim:open:poly` and §7--§10 need.  This theorem locates the gap exactly:
nothing else about `RV[k,·]` is missing. -/
def RVHom.comp {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k} {Z : RVObj S sβ'' A'' k}
    (g : RVHom Y Z) (f : RVHom X Y)
    (hdef : Definable S (Sum.elim sβ sβ'')
      {z : (β ⊕ β'') → M | baseProj z ∈ X.U ∧ secondPart z = g.F (f.F (baseProj z))}) :
    RVHom X Z :=
  { F := fun u => g.F (f.F u)
    F_maps := (RVMap.comp g.toRVMap f.toRVMap).maps
    F_definable := hdef
    volumetric := (RVMap.comp g.toRVMap f.toRVMap).volumetric
    finite_fibres := (RVMap.comp g.toRVMap f.toRVMap).finite_fibres }

/-- Two `RVMap`s with the same underlying function are equal (the remaining fields are `Prop`s). -/
theorem RVMap.ext {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k} {f g : RVMap X Y}
    (h : f.F = g.F) : f = g := by
  cases f; cases g
  cases h
  rfl

/-- `RV[k,·]` with definability forgotten satisfies the category laws. -/
theorem RVMap.comp_assoc {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k}
    {Z : RVObj S sβ'' A'' k} {W : RVObj S sβ''' A''' k}
    (h : RVMap Z W) (g : RVMap Y Z) (f : RVMap X Y) :
    h.comp (g.comp f) = (h.comp g).comp f :=
  RVMap.ext rfl

theorem RVMap.id_comp {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k} (f : RVMap X Y) :
    (RVMap.id Y).comp f = f :=
  RVMap.ext rfl

theorem RVMap.comp_id {X : RVObj S sβ A k} {Y : RVObj S sβ' A' k} (f : RVMap X Y) :
    f.comp (RVMap.id X) = f :=
  RVMap.ext rfl

/-! ### Subobjects

The paper: *"A subobject of an object `(U, f)` of an `RV`-category is a definable pair `(A, g)` with
`A` a subset of `U` and `g = f ↾ A`.  Note that the inclusion map is a morphism in both cases."* -/

/-- **The inclusion of a subobject is a morphism in `RV[k,·]`**, geometrically: it is volumetric
(the weights are equal) and its fibres are singletons. -/
def RVMap.restrictIncl (X : RVObj S sβ A k) (B : Set (β → M)) (hB : Definable S sβ B)
    (hBU : B ⊆ X.U) : RVMap (X.restrict B hB hBU) X where
  F := fun u => u
  maps := fun u hu => hBU hu
  volumetric := fun _ _ => le_rfl
  finite_fibres := by
    intro t
    refine (Set.finite_singleton t).subset ?_
    rintro v ⟨u, hu, hfu, rfl⟩
    exact hfu

/-- The inclusion of a subobject as a morphism of `RV[k,·]`, with the definability of the graph —
the diagonal `{z : (β ⊕ β) → M | pr_{≤k} z = pr_{>k} z}`, i.e. a renaming of coordinates — carried
as `hdef`. -/
def RVHom.restrictIncl (X : RVObj S sβ A k) (B : Set (β → M)) (hB : Definable S sβ B)
    (hBU : B ⊆ X.U)
    (hdef : Definable S (Sum.elim sβ sβ)
      {z : (β ⊕ β) → M | baseProj z ∈ B ∧ secondPart z = baseProj z}) :
    RVHom (X.restrict B hB hBU) X :=
  { F := fun u => u
    F_maps := fun u hu => hBU hu
    F_definable := hdef
    volumetric := fun _ _ => le_rfl
    finite_fibres := (RVMap.restrictIncl X B hB hBU).finite_fibres }

end RVCategory

/-! ## Part 7. Lemma \ref{RV:morphism:condition}: the paper's reduction to algebraic closure

The paper's Lemma: *"Suppose that `F` is volumetric and there is a definable function
`F^↑ : 𝕃(U, f) → 𝕃(U', f')` such that the diagram commutes.  Then `F` is a morphism in
`RV[k,·]`."*  Its proof: *"It is enough to show that, for every `ū ∈ U` and every `i ≤ k`,
`(f'_i ∘ F)(ū) ∈ acl(f(ū))`."*

That reduction is what is formalized here.  The two steps it takes from §2--§3 are carried as
explicit named hypotheses of `RVMorphismInputs` below, each with the paper's sentence and label;
the rest — that `F^↑` defined on the lift forces its base part to be `F` and its `RV` part to be
`f' ∘ F`, and that the parameter sets work out — is proved here (`LiftCommutes.baseOf_eq`,
`LiftCommutes.rvPart_eq`, `rv_morphism_condition_acl`).

**What is *not* claimed.**  The passage from `(f'_i∘F)(ū) ∈ acl(f(ū))` to the finite-fibre
condition of `Definition \ref{defn:RV:cat}` is passed over in one line in the paper and needs two
things that are not available at this point of the tree: (i) that
`(f'∘F)(f^{-1}(t̄))` is a *definable* set — the projection lemma, i.e. assigning the value
coordinates to bound variables, the same missing piece as the composition lemma; and (ii) that a
definable subset of `RV^k` all of whose points are algebraic over `t̄` is finite, which is the
saturation of the monster model.  With (i) absent we cannot even state the set whose finiteness is
required without it being a definitional restatement, so the lemma is delivered in the paper's own
reduced form and `finite_fibres` is not asserted. -/

section MorphismCondition

variable {S : SP M} {β β' : Type} {sβ : β → SortTag} {sβ' : β' → SortTag}
  {A : Set (β → M)} {A' : Set (β' → M)} {k : ℕ}

/-- **`x` is algebraic over the parameter set `P`, at the sort `s`**: some well-sorted formula with
parameters drawn from `P` has finitely many solutions at sort `s` and is satisfied by `x`.  This is
the paper's `x ∈ acl(ā, t̄)`; `SP.acl` is the case `P = SP.paramSet S`, `s = .vf` (see
`acl_imp_AclOf`).  The parameter tuple is existentially quantified, which is what lets the same
notion be used at the several parameter shapes the paper mixes (`ā`, `t̄`, `ā,ū`). -/
def AclOf (P : Set M) (s : SortTag) (x : M) : Prop :=
  ∃ (ρ : Type) (sρ : ρ → SortTag) (f : ρ → M),
    (∀ i, f i ∈ P) ∧
      ∃ φ : LRV.BoundedFormula ρ 1,
        WellSorted sρ (fun _ => s) φ ∧
          ({y | sortEval s y ∧ φ.Realize f ![y]} : Set M).Finite ∧
            sortEval s x ∧ φ.Realize f ![x]

/-- Algebraic closure grows with the parameter set. -/
theorem AclOf.mono {P P' : Set M} (h : P ⊆ P') {s : SortTag} {x : M} (hx : AclOf P s x) :
    AclOf P' s x := by
  obtain ⟨ρ, sρ, f, hf, φ, hφ, hfin, hse, hrel⟩ := hx
  exact ⟨ρ, sρ, f, fun i => h (hf i), φ, hφ, hfin, hse, hrel⟩

/-- `SP.acl` is this notion at `P = SP.paramSet S` and `s = .vf`. -/
theorem acl_imp_AclOf (S : SP M) {x : M} (h : acl S x) : AclOf (paramSet S) .vf x := by
  obtain ⟨φ, hφ, hfin, hse, hrel⟩ := h
  refine ⟨Fin S.n ⊕ Fin S.m, S.sortMap, S.toFun, ?_, φ, hφ, hfin, hse, hrel⟩
  rintro (i | j)
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨j, rfl⟩

/-- The range of an assembled tuple is the union of the ranges of its parts. -/
theorem range_mkTuple {k : ℕ} {β : Type} (a : Fin k → M) (u : β → M) :
    Set.range (mkTuple a u) = Set.range a ∪ Set.range u := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | inl i => exact Or.inl ⟨i, rfl⟩
    | inr b => exact Or.inr ⟨b, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr b, rfl⟩

/-- The inputs that the proof of Lemma \ref{RV:morphism:condition} takes from §2 and §3.  None of
the fields mentions `F`, `F^↑`, `U`, `U'` or the conclusion; each is the paper's own statement, with
its label. -/
structure RVMorphismInputs where
  /-- §3, Lemma \ref{dcl:to:ac}: *"For any `ā`, `b ∈ VF` and `t̄ ∈ RV`, if `b ∈ acl(ā, t̄)` then
  `b ∈ VF(S)(ā)^{alg}`."*  With "algebraic over the field `VF(S)(ā)`" giving a finite solution set
  over `ā` alone, this is: `RV`-sorted parameters can be dropped from the algebraic closure of a
  `VF`-element. -/
  dcl_to_ac : ∀ (P Q : Set M), (∀ x ∈ Q, iRV x) → ∀ b : M, iVF b →
    AclOf (P ∪ Q) .vf b → AclOf P .vf b
  /-- §3, Corollary \ref{acl:VF:transfer:acl:RV}: *"For any `t̄ ∈ RV`, any `t̄`-definable subset
  `A ⊆ rv^{-1}(t̄)`, and any element `x`, if `x ∈ acl(ā)` for every `ā ∈ A` then `x ∈ acl(t̄)`."*
  Stated for the whole `rv`-fibre `A = rv^{-1}(t̄)` in the `VF` sort, which is the case the §4.2
  proof uses and which is `t̄`-definable by its defining formula, so that no definability side
  condition on `A` is needed. -/
  acl_transfer : ∀ (P : Set M) (k : ℕ) (t : Fin k → M), (∀ i, iRV (t i)) → ∀ (s : SortTag) (x : M),
    (∀ a : Fin k → M, (∀ i, iVF (a i)) → (∀ i, iRv (a i) = t i) →
      AclOf (P ∪ Set.range a) s x) →
    AclOf (P ∪ Set.range t) s x
  /-- §2, the step the paper writes as `f(t̄) ∈ ⟨t̄⟩` in the proof of Corollary
  \ref{function:rv:to:vf:finite:image} (*"Since for any `t̄ ∈ A` we have `f(t̄) ∈ ⟨t̄⟩`"*): the
  value of a definable function is algebraic over the parameters together with the arguments. -/
  value_acl : ∀ (P : Set M) {σ : Type} (sσ : σ → SortTag) (G : (σ → M) → M) (T : Set (σ → M)),
    Definable S (Sum.elim sσ (fun _ : Fin 1 => SortTag.vf))
      {z : (σ ⊕ Fin 1) → M | fstProj z ∈ T ∧ sndProj z = fun _ => G (fstProj z)} →
    ∀ (x : σ → M), x ∈ T → AclOf (P ∪ Set.range x) .vf (G x)
  /-- `rv` preserves algebraicity: the paper's inference from `b_i ∈ acl(ā)` to
  `rv(b_i) ∈ acl(ā)`, i.e. the case `G = rv` of the previous field. -/
  rv_acl : ∀ (P : Set M) (x : M), AclOf P .vf x → AclOf P .rv (iRv x)

/-- **Lemma \ref{RV:morphism:condition}, in the paper's own reduced form**: `F` volumetric and a
definable `F^↑` with `F^↑(𝕃(U,f)) ⊆ 𝕃(U',f')` and `rv ∘ F^↑ = F_{f,f'} ∘ rv` give
`(f'_i ∘ F)(ū) ∈ acl(f(ū))` for every `ū ∈ U`.  The base sorts are required `RV`-sorted, which is
the paper's *"`U ⊆ RV^m`"* in Definition \ref{defn:RV:cat}. -/
theorem rv_morphism_condition_acl (inputs : RVMorphismInputs (M := M) (S := S))
    (X : RVObj S sβ A k) (Y : RVObj S sβ' A' k) (F : (β → M) → β' → M)
    (FUp : (Fin k ⊕ β → M) → Fin k ⊕ β' → M)
    (hsβ : ∀ b, sβ b = SortTag.rv) (hsβ' : ∀ b, sβ' b = SortTag.rv)
    (hVol : Volumetric X Y F) -- kept for fidelity: the paper's hypothesis, not used by the reduction
    (hUpDef : ∀ i : Fin k,
      Definable S (Sum.elim (Sum.elim (fun _ : Fin k => SortTag.vf) sβ) (fun _ : Fin 1 => SortTag.vf))
        {z : ((Fin k ⊕ β) ⊕ Fin 1) → M | fstProj z ∈ X.lift ∧
          sndProj z = fun _ => FUp (fstProj z) (Sum.inl i)})
    (hComm : LiftCommutes X Y F FUp)
    (u : β → M) (hu : u ∈ X.U) (i : Fin k) :
    AclOf (paramSet S ∪ Set.range (X.f u)) .rv (Y.f (F u) i) := by
  -- `U` lies in the `RV`-sorted tuples, so every coordinate of `u` is an `RV`-element
  have hU_rv : ∀ x ∈ Set.range u, iRV x := by
    rintro x ⟨b, rfl⟩
    have hs := (Definable.subset_sortedTuple S X.U_definable) hu
    have hb := hs b
    rw [hsβ b] at hb
    exact hb
  -- the paper's acl transfer, applied to the fibre `rv^{-1}(f(ū))` of `VF`-tuples
  refine inputs.acl_transfer (paramSet S) k (X.f u) (fun i => X.f_sorted u hu i) .rv (Y.f (F u) i) ?_
  intro a haVF harv
  -- `z = (ā, ū)` is a point of the lift
  have hzlift : mkTuple a u ∈ X.lift :=
    RVObj.lift_mem_of (X := X) (a := a) (u := u) haVF hu harv
  -- §2: the value of the definable `F^↑` is algebraic over the arguments
  have h1 : AclOf (paramSet S ∪ Set.range (mkTuple a u)) .vf (FUp (mkTuple a u) (Sum.inl i)) :=
    inputs.value_acl (paramSet S) (Sum.elim (fun _ : Fin k => SortTag.vf) sβ)
      (fun z => FUp z (Sum.inl i)) X.lift (hUpDef i) (mkTuple a u) hzlift
  -- §3 `dcl:to:ac`: drop the `RV`-sorted parameters `ū`
  have hset : paramSet S ∪ Set.range (mkTuple a u)
      = (paramSet S ∪ Set.range a) ∪ Set.range u := by
    rw [range_mkTuple, Set.union_assoc]
  have h2 : AclOf ((paramSet S ∪ Set.range a) ∪ Set.range u) .vf
      (FUp (mkTuple a u) (Sum.inl i)) := by
    rw [← hset]; exact h1
  have h3 : AclOf (paramSet S ∪ Set.range a) .vf (FUp (mkTuple a u) (Sum.inl i)) :=
    inputs.dcl_to_ac (paramSet S ∪ Set.range a) (Set.range u) hU_rv _
      ((hComm.maps _ hzlift).1 i) h2
  -- `rv` preserves algebraicity, and the diagram says `rv` of that value is `f'_i(Fū)`
  have h4 : AclOf (paramSet S ∪ Set.range a) .rv (Y.f (F (baseOf (mkTuple a u))) i) := by
    have := inputs.rv_acl _ _ h3
    rwa [hComm.rvPart_eq hzlift i] at this
  rw [baseOf_mkTuple] at h4
  exact h4

end MorphismCondition

end SP
end SpecialTransformations.Milestone0

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.SP.LiftCommutes.baseOf_eq
#print axioms SpecialTransformations.Milestone0.SP.LiftCommutes.rvPart_eq
#print axioms SpecialTransformations.Milestone0.SP.RVObj.rvMap_image_rvPolydisc
#print axioms SpecialTransformations.Milestone0.SP.rvImage_lift_eq_companion
#print axioms SpecialTransformations.Milestone0.SP.RVMap.id
#print axioms SpecialTransformations.Milestone0.SP.RVMap.comp
#print axioms SpecialTransformations.Milestone0.SP.RVMap.finite_fibres_iff
#print axioms SpecialTransformations.Milestone0.SP.RVHom.comp
#print axioms SpecialTransformations.Milestone0.SP.RVMap.restrictIncl
#print axioms SpecialTransformations.Milestone0.SP.AclOf.mono
#print axioms SpecialTransformations.Milestone0.SP.acl_imp_AclOf
#print axioms SpecialTransformations.Milestone0.SP.range_mkTuple
#print axioms SpecialTransformations.Milestone0.SP.rv_morphism_condition_acl
#print axioms SpecialTransformations.Milestone0.SP.RVMap.ext
#print axioms SpecialTransformations.Milestone0.SP.RVMap.comp_assoc
#print axioms SpecialTransformations.Milestone0.SP.RVMap.id_comp
#print axioms SpecialTransformations.Milestone0.SP.RVMap.comp_id
#print axioms SpecialTransformations.Milestone0.SP.LiftCommutes.id
