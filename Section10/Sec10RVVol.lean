module

/-
**Section 10, "Categories with volume forms"** — the `RV`-side: Definition \ref{defn:RV:cat:vol}
(`paper.tex` line 2245), the lift `𝕃(U,ω)` (`paper.tex` line 2262), Theorem \ref{L:measure:surjective}
(10.4, `paper.tex` line 2264) and Theorem \ref{L:measure:class:lift} (10.5, `paper.tex` line 2275).

The paper's own sentences, which the definitions below freeze (quoted from `paper.tex`):

* Definition \ref{defn:RV:cat:vol}: *"First set `mRV[0] = RV[0]`. Suppose `k > 0`. An object of the
  category `mRV[k]` is a definable triple `(U, f, ω)`, where `(U, f) ∈ RV[k]` and `ω : U → RV^×` is a
  function, which is understood as a volume form on `(U, f)`. A morphism between two objects
  `(U,f,ω)`, `(U',f',ω')` is an essential isomorphism `F : (U, f) → (U', f')` such that
  (1) `ω(ū) = ω'(F(ū)) · jcb_RV F(f(ū), ū)` for every `ū ∈ dom(F)` outside of a definable subset of
  `dom(F)` of dimension `< k`, (2) `vrv(ω(ū)) = (vrv ∘ ω' ∘ F)(ū) + jcb_Γ F(f(ū), ū)` for every
  `ū ∈ dom(F)`. It is easily seen from the definitions of `jcb_RV` and `jcb_Γ` that every morphism
  here is actually an isomorphism."*
* The lift: *"For any `(U,ω) ∈ mRV[k]`, let `L ω` be the function on `L U` naturally induced by `ω`.
  The lift of `(U,ω)` is the object `L(U,ω) = (L U, L ω) ∈ mVF[k]`."*
* Theorem \ref{L:measure:surjective} (10.4): *"Every object `(A,ω)` in `mVF[k]` is isomorphic to
  another object `L(U,π)` in `mVF[k]`, where `(U,π) ∈ mRV[k]`; similarly for other pairs of
  corresponding categories."*
* Theorem \ref{L:measure:class:lift} (10.5): *"Let `F : (U,ω) → (U',ω')` be a `mRV[k]`-isomorphism.
  Then there exists a measuring-preserving lift `F^↑ : L(U,ω) → L(U',ω')` of `F`."*

## What is proved, what is a hypothesis, and why

`lean Sec10RVVol.lean` exits `0` with no `sorry`, no `axiom`, no `native_decide`; the `#print axioms`
audit is in `axcheck.lean`.

Proved here: the objects of `mRV[k,·]` and their unit parts (`RVVolObj`, `RVVolObj.unitPart`); the
exceptional-set dimension `RVdimLt` via §4's `dimRV`, with `RVdimLt ∅ ↔ 0 < k`; the morphisms
(`RVVolHom`) with the paper's conditions (1) and (2) as fields; the identity morphism and composition
of morphisms (the elementary closure lemmas); that **every morphism is an isomorphism**
(`RVVolHom.inverse`, `RVVolHom.isIso` — the paper's *"It is easily seen from the definitions of
`jcb_RV` and `jcb_Γ` that every morphism here is actually an isomorphism"*), with the inverse's
reciprocal Jacobians and its definability as named hypotheses; the `RV_1[k]` condition
(`RVVolObj.IsOne`); the lift
`𝕃(U,ω) = (𝕃U, 𝕃ω)` (`RVVolObj.lift`, on §4's `RVObj.lift`); the `mVF[k]`-measure-preserving
condition (`VFMeasurePreservingOff`); and Theorems 10.4 and 10.5 derived from explicitly named
hypotheses that are the paper's cited inputs.

Carried as explicit hypotheses, with the paper's label in the docstring of the binder:

* `VolLaws` — the group laws of `RV^×`, that `vrv` is a homomorphism onto `Γ`, and the abelian group
  laws of `Γ` (`paper.tex`, Definitions 2.1–2.2).  Consequences of the frozen `ACVF` axiom set, not
  re-derived here; every law used is a field, so the reader can check exactly how much is assumed.
* `jcb_RV`, `jcb_Γ` — the two Jacobians of §9 (`paper.tex` lines 2093, 2104).  §9 is a **separate
  section of this run** and `SpecialTransformations/Differentiation.lean` is a skeleton, so the
  Jacobians enter as *data attached to a morphism*, with the paper's own compatibilities as fields:
  `jcb_RV` is `RV^×`-valued (`jcbRV_ne`) and *"Obviously this always exists and
  `vrv(jcb_RV F(f(ū),ū)) = jcb_Γ F(f(ū),ū)`"* is `jcb_vrv` (`paper.tex` line 2108).  The
  identification with the §9 construction is **not** assumed anywhere.
* the chain rule for both Jacobians, `paper.tex` line 2111: *"Note that the chain rule clearly holds
  for both `jcb_RV` and `jcb_Γ` whenever the things involved are defined."*  It enters `RVVolHom.comp`
  through the *definition* of the composite's Jacobian (product in `RV^×`, sum in `Γ`), so it is not a
  separate hypothesis.
* `hreduce` in `L_measure_surjective` — Corollary \ref{all:subsets:rvproduct}, Corollary
  \ref{diff:almost:every} and Lemma \ref{special:tran:vol:pre} of §5/§7/§9 (`paper.tex` lines
  2266–2267).  **This hypothesis carries the whole mathematical content of 10.4**; see its docstring.
* `hlift` in `L_measure_class_lift` — Theorem \ref{iso:lifted:vol} (`paper.tex` line 2126), with
  Theorem \ref{RV:iso:class:lifted} of §7 behind it.

**The `VF`-side category is not built here.**  §10's `VF`-categories with volume forms (Definition
\ref{defn:mVF:cat:vol}) are a *different direction* of this run; this file only needs the *shape* of
the lift `𝕃(U,f) ⊆ VF^k × U`, which is §4's `RVObj.lift` (Definition \ref{def:L}) together with the
projection `𝕃ω(x) = ω(base x)`.  `VFVolData` below is that shape and nothing more: it deliberately
does not claim to be the paper's `mVF[k,·]` (no definability fields), and `VFMeasurePreservingOff`
records exactly the one equation Definition \ref{defn:mVF:cat:vol} puts on a `VF`-morphism, which is
what Theorem 10.5 asserts about `F^↑`.

**Deviations from the paper's wording, documented at the definition that carries them:**

1. The exceptional set of Definition \ref{defn:RV:cat:vol}(1) is carried on the **codomain** of a
   morphism (`RVVolHom.holes ⊆ Fin m' → M`, `vol` holds off the image).  The paper states it on
   `dom(F)`; moving it across the essential isomorphism is the definable-image step that
   `QE/Sec4Categories.lean` records as missing from the tree (`QE-PLAN.md`, "the one wall, three
   times").  The dimension bound itself *is* formalized (`RVdimLt`, via §4's `dimRV`), not assumed.
2. `RV_0[k]` (the full subcategory with `ω = 0`) is not formalized: Definition \ref{defn:RV:cat:vol}
   requires `ω : U → RV^×`, while `0 = iRVZero = rv(0)` is the absorbing element, not in `RV^×`.
   `RVVolObj.IsOne` is `RV_1[k]`; see its docstring.
3. **`mgRV[k]` (the `Γ`-volume forms) is not formalized.**  Definition \ref{defn:RV:cat:vol} also
   defines the category of triples `(U,f,ω)` with `ω : U → Γ` a definable function, whose morphisms
   satisfy `ω(ū) = ω'(F ū) + jcb_Γ F(ū)` instead of a product.  The obstacle is in the frozen
   encoding, not in the mathematics: `SP.Definable` (`QE/Sec4Categories.lean`) is definability by a
   well-sorted formula of `L_RV`, whose `SortTag` has just the two constructors `vf` and `rv` — `Γ` is
   not a sort of `L_RV` but a definable quotient of `RV` (and a sort only of the `Γ`-expansion
   `LRVΓ`, `Milestone0/Encoding.lean` Part 4, whose `WellSorted` is not built anywhere in the tree).
   So "`ω : U → Γ` is definable" cannot be stated with the available `Definable`, and it is exactly
   the `Γ`-valued counterpart of the map whose graph `ω_definable` records here.  The `Γ`-half of the
   §10 morphism conditions *is* formalized, as `RVVolHom.volΓ` and the `Γ`-laws of `VolLaws`.
4. Objects are indexed by `m` with base `Fin m → M` of sort `RV`, which is the paper's `U ⊆ RV^m`;
   the paper's `mRV[k]` (no `·`) is the full subcategory of finite-to-one objects
   (`RVVolObj.FiniteToOne`), recorded as a predicate rather than a separate structure.
5. In 10.5 the measure-preserving equation is asserted on the **unit part** of the lift
   (`RVVolObj.liftUnit`) — the paper's own reduction, *"since the parts `f(U) ∖ A` and `g(V) ∖ B` will
   not concern us, we may assume `f^{-1}(A) = U`"* (`paper.tex` line 2079).
-/
public import Sec4Categories
public import Sec4Dim

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
open LRV

namespace SP

open Sec4Dim

variable {M : Type*} [LRV.Structure M]

/-! ## Part 0. The background laws

The paper's Definitions 2.1–2.2 give `RV` as a structure whose unit part `RV^×` is a commutative
group, and `Γ = RV^×/K^×` with the quotient map `vrv`.  The frozen encoding
(`Milestone0/Encoding.lean`) has the function symbols (`Fn.rvMul`, `Fn.rvOne`, `Fn.rvZero`) and, in
its `Γ`-expansion `LRVΓ` (Part 4), the value-group symbols `Gamma.FnΓ.vrv/add/neg/zero`
(`Gamma.gVrv`, `Gamma.gAdd`, …).  The *laws* follow from `ACVF` and are not re-derived here. -/

/-- **The background laws used by the `RV`-categories with volume forms.**  `vrv`, `gAdd`, `gZero`,
`gNeg` are the interpretation of the `Γ`-expansion's symbols `Gamma.FnΓ.vrv` (the quotient map
`vrv : RV → Γ ∪ {∞}` of Definition 2.2 item (5)), `Gamma.FnΓ.add`, `Gamma.FnΓ.zero`,
`Gamma.FnΓ.neg`; they are carried as data rather than through an `LRVΓ` structure instance, so that
this file's statements are statements about `LRV`-models with a value-group structure on the same
carrier.

The multiplication fields are the paper's *"`RV = RV^× ∪ {0}` and `RV^×` is a commutative group with
respect to `×`, with identity `1`"* (Definition 2.2, item (4)); the `vrv` fields are item (5), `vrv`
being a homomorphism on `RV^×`. -/
structure VolLaws (M : Type*) [LRV.Structure M] where
  /-- the quotient map `vrv : RV → Γ ∪ {∞}` (Definition 2.2 item (5)) -/
  vrv : M → M
  /-- `+` of the value group `Γ` -/
  gAdd : M → M → M
  /-- `0` of the value group `Γ` -/
  gZero : M
  /-- `-` of the value group `Γ` -/
  gNeg : M → M
  /-- `1 ∈ RV` is `RV`-sorted -/
  one_sorted : iRV (M := M) iRVOne
  /-- `1 ≠ 0 = ∞` in `RV` -/
  one_ne_zero : (iRVOne : M) ≠ (iRVZero : M)
  /-- `1` is a right identity of `RV^×` -/
  mul_one : ∀ t : M, iRV t → t ≠ iRVZero → iRVMul t iRVOne = t
  /-- `1` is a left identity of `RV^×` -/
  one_mul : ∀ t : M, iRV t → t ≠ iRVZero → iRVMul iRVOne t = t
  /-- `×` is associative on `RV^×` -/
  mul_assoc : ∀ s t u : M, iRV s → iRV t → iRV u → s ≠ iRVZero → t ≠ iRVZero → u ≠ iRVZero →
    iRVMul (iRVMul s t) u = iRVMul s (iRVMul t u)
  /-- `×` is commutative on `RV^×` -/
  mul_comm : ∀ s t : M, iRV s → iRV t → iRVMul s t = iRVMul t s
  /-- the `RV` sort is closed under `×` -/
  mul_sorted : ∀ s t : M, iRV s → iRV t → iRV (iRVMul s t)
  /-- `RV^×` is closed under `×` -/
  mul_ne_zero : ∀ s t : M, iRV s → iRV t → s ≠ iRVZero → t ≠ iRVZero → iRVMul s t ≠ iRVZero
  /-- `RV^×` is a group: cancellation -/
  mul_left_cancel : ∀ s t u : M, iRV s → iRV t → iRV u → iRVMul u s = iRVMul u t → s = t
  /-- `vrv(1) = 0` -/
  vrv_one : vrv iRVOne = gZero
  /-- `vrv` is a homomorphism on `RV^×` -/
  vrv_mul : ∀ s t : M, iRV s → iRV t → vrv (iRVMul s t) = gAdd (vrv s) (vrv t)
  /-- `+` of `Γ` is associative -/
  add_assoc : ∀ a b c : M, gAdd (gAdd a b) c = gAdd a (gAdd b c)
  /-- `+` of `Γ` is commutative -/
  add_comm : ∀ a b : M, gAdd a b = gAdd b a
  /-- `0` is neutral for `+` -/
  add_zero : ∀ a : M, gAdd a gZero = a
  /-- `gNeg` is a negative -/
  add_left_neg : ∀ a : M, gAdd a (gNeg a) = gZero

/-! ## Part 1. Objects of the paper's `mRV[k,·]`

*"An object of the category `RV[k,·]` is a definable pair `(U,f)`, where `U ⊆ RV^m` for some `m` and
`f : U → RV^k` is a function"* (`QE/Sec4Categories.lean`, `RVObj`; the base is `Fin m → M` with
every coordinate of sort `RV`). -/

/-- **An object of the paper's `mRV[k,·]`** (Definition \ref{defn:RV:cat:vol}): *"An object of the
category `mRV[k]` is a definable triple `(U, f, ω)`, where `(U, f) ∈ RV[k]` and `ω : U → RV^×` is a
function, which is understood as a volume form on `(U, f)`."*

`toRV` is §4's `(U,f)`; `ω` is the volume form with its three defining properties: `RV`-valued
(`ω_sorted`), `RV^×`-valued (`ω_ne_zero`, since `RV^× = RV ∖ {0 = ∞}` in the encoding) and definable
(`ω_definable`).  The paper's `k > 0` is not a field of the structure: it is needed only to *satisfy*
the dimension bound of a morphism's exceptional set (`RVdimLt` fails at `k = 0` on `∅`), so it is a
hypothesis of the lemmas that produce such a bound. -/
structure RVVolObj (S : SP M) (m k : ℕ) where
  /-- the paper's `(U, f) ∈ RV[k,·]` -/
  toRV : RVObj S (fun _ => SortTag.rv) (Set.univ : Set (Fin m → M)) k
  /-- the paper's `ω : U → RV^×` -/
  ω : (Fin m → M) → M
  /-- `ω` takes values in the `RV` sort -/
  ω_sorted : ∀ u ∈ toRV.U, iRV (ω u)
  /-- `ω` takes values in `RV^× = RV ∖ {0}` -/
  ω_ne_zero : ∀ u ∈ toRV.U, ω u ≠ iRVZero
  /-- `ω` is a *definable* function: its graph over the base is definable -/
  ω_definable : Definable S (rvSort (fun _ : Fin m => SortTag.rv) (Fin 1))
    {z : (Fin m ⊕ Fin 1) → M | baseProj z ∈ toRV.U ∧ secondPart z 0 = ω (baseProj z)}

namespace RVVolObj

variable {S : SP M} {m k : ℕ}

/-- **The unit part of the domain**, `f^{-1}(A)` for `A = f(U) ∩ (RV^×)^k` (`paper.tex` line 2076):
the points at which the `RV`-tuple `f(ū)` is unit-valued.  The paper's *essential isomorphism*
(Definition \ref{defn:essential:iso}) is an isomorphism between these parts. -/
def unitPart (X : RVVolObj S m k) : Set (Fin m → M) :=
  {u | u ∈ X.toRV.U ∧ ∀ i, X.toRV.f u i ≠ iRVZero}

@[simp]
theorem mem_unitPart {X : RVVolObj S m k} {u : Fin m → M} :
    u ∈ X.unitPart ↔ u ∈ X.toRV.U ∧ ∀ i, X.toRV.f u i ≠ iRVZero := Iff.rfl

/-- The `RV`-base of a point of the lift `𝕃U`: its `Fin m`-block. -/
def base {k : ℕ} (x : (Fin k ⊕ Fin m) → M) : Fin m → M := fun i => x (Sum.inr i)

/-- **`(U,f) ∈ RV[k]`**: *"The category `RV[k]` is the full subcategory of `RV[k,·]` of the pairs
`(U,f)` such that `f : U → RV^k` is finite-to-one."*  (`RVObj.FiniteToOne`.) -/
def FiniteToOne (X : RVVolObj S m k) : Prop := X.toRV.FiniteToOne

/-- **`RV_1[k]`** (Definition \ref{defn:RV:cat:vol}): *"The categories `mgRV[k]`, `RV_1[k]`,
`RV_0[k]` are similar to the corresponding `VF`-categories"*, where *"the category `VF_1[k,·]` is the
full subcategory of `mVF[k,·]` such that `(A,ω) ∈ VF_1[k,·]` if and only if `ω = 1`"*.

`RV_0[k]` (the same with `ω = 0`) is **not** stated here: `0 = iRVZero = rv(0)` is the absorbing
element and is not in `RV^×`, so with the definition's `ω : U → RV^×` an object with `ω = 0` must
have `U = ∅`; see the header, deviation 2. -/
def IsOne (X : RVVolObj S m k) : Prop := ∀ u : Fin m → M, X.ω u = iRVOne

end RVVolObj

/-! ## Part 2. The exceptional set of Definition \ref{defn:RV:cat:vol}(1): `dim < k`

*"… for every `ū ∈ dom(F)` outside of a definable subset of `dom(F)` of dimension `< k`"*.  On the
`RV`-side the domain is a subset of `RV^m`, where the paper's `VF`-dimension is the `RV`-dimension of
§4 (`paper.tex`, after Lemma \ref{VF:dim:tran:deg}): *"the `RV`-dimension of `B` … is the smallest
number `k` such that there is a definable finite-to-one function `f : B → RV^k`"*.  `Sec4Dim.dimRV`
is that dimension; `RVdimLt` transports it from §4's `Tup M 0 m` presentation (`Idx 0 m`-indexed
tuples) to the `Fin m → M` presentation of this file's objects. -/

/-- **`dim(B) < k`**, the paper's *"a definable subset of `dom(F)` of dimension `< k`"*
(`paper.tex` line 2248), with §4's `dimRV` (`QE/Sec4Dim.lean`) as the dimension. -/
noncomputable def RVdimLt (S : SP M) (m k : ℕ) (B : Set (Fin m → M)) : Prop :=
  dimRV S {x : Tup M 0 m | (fun i => x (Sum.inr i)) ∈ B} < k

/-- **The empty exceptional set is admissible when `k > 0`** — the paper's *"Suppose `k > 0`"*
(Definition \ref{defn:RV:cat:vol}).  This is what makes the identity morphism, and the subcategory
`RV_1[k]`, non-vacuous: `RVdimLt S m k ∅` holds iff `k > 0`.

The `RV`-dimension of `∅` is `0`: the empty set carries a definable finite-to-one map into `RV^0`. -/
theorem rvDimLt_empty {S : SP M} {m k : ℕ} (hk : 0 < k) :
    RVdimLt S m k (∅ : Set (Fin m → M)) := by
  have hempty : {x : Tup M 0 m | (fun i => x (Sum.inr i)) ∈ (∅ : Set (Fin m → M))} = ∅ := by
    ext x
    simp
  have h0 : HasRVdim S (∅ : Set (Tup M 0 m)) 0 := by
    refine ⟨fun _ => ⟨fun i => Sum.elim (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0) i,
      fun i => Sum.elim (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0) i⟩, ?_, ?_⟩
    · exact ⟨⊥, WellSorted.falsum _, fun x hx => absurd hx (by simp)⟩
    · intro y
      refine Set.Finite.subset (Set.finite_empty (α := Tup M 0 m)) ?_
      intro x hx
      exact absurd hx.1 (by simp)
  have hle : dimRV S (∅ : Set (Tup M 0 m)) ≤ 0 := (dimRV_le_iff S ∅ 0).2 ⟨0, le_rfl, h0⟩
  have hz : dimRV S (∅ : Set (Tup M 0 m)) = 0 := le_antisymm hle (Nat.zero_le _)
  show dimRV S {x : Tup M 0 m | (fun i => x (Sum.inr i)) ∈ (∅ : Set (Fin m → M))} < k
  rw [hempty, hz]
  exact hk

/-! ## Part 3. Morphisms of the paper's `mRV[k,·]` (Definition \ref{defn:RV:cat:vol})

*"A morphism between two objects `(U,f,ω)`, `(U',f',ω')` is an essential isomorphism
`F : (U, f) → (U', f')` such that
 (1) `ω(ū) = ω'(F(ū)) · jcb_RV F(f(ū), ū)` for every `ū ∈ dom(F)` outside of a definable subset of
     `dom(F)` of dimension `< k`,
 (2) `vrv(ω(ū)) = (vrv ∘ ω' ∘ F)(ū) + jcb_Γ F(f(ū), ū)` for every `ū ∈ dom(F)`."*

An *essential isomorphism* is *"an isomorphism between `(f^{-1}(A), f ↾ f^{-1}(A))` and
`(g^{-1}(B), g ↾ g^{-1}(B))`"*, `A = f(U) ∩ (RV^×)^n`, `B = g(V) ∩ (RV^×)^n` — i.e. a bijection
between the **unit parts**. -/
structure RVVolHom {S : SP M} (L : VolLaws M) {k : ℕ} {m m' : ℕ}
    (X : RVVolObj S m k) (Y : RVVolObj S m' k) where
  /-- the paper's `F : U → U'`, the underlying function of the essential isomorphism -/
  F : (Fin m → M) → Fin m' → M
  /-- the essential isomorphism maps the unit part of `X` into the unit part of `Y` -/
  F_maps : ∀ u ∈ X.unitPart, F u ∈ Y.unitPart
  /-- `F` is definable — *"a definable essential bijection"* -/
  F_definable : Definable S (Sum.elim (fun _ : Fin m => SortTag.rv) (fun _ : Fin m' => SortTag.rv))
    {z : (Fin m ⊕ Fin m') → M | baseProj z ∈ X.unitPart ∧ secondPart z = F (baseProj z)}
  /-- the essential isomorphism is injective on the unit part -/
  F_inj : Set.InjOn F X.unitPart
  /-- the essential isomorphism is onto the unit part -/
  F_surj : ∀ v ∈ Y.unitPart, ∃ u ∈ X.unitPart, F u = v
  /-- the paper's `jcb_RV F(f(ū),ū)`: *"a `ū`-definable element in `RV^×`"* (`paper.tex` line 2093),
  carried as data — see the header -/
  jcbRV : (Fin m → M) → M
  /-- the paper's `jcb_Γ F(f(ū),ū) = Σ(vrv ∘ g ∘ F)(ū) − Σ(vrv ∘ f)(ū)` (`paper.tex` line 2104) -/
  jcbΓ : (Fin m → M) → M
  /-- `jcb_RV` is `RV`-valued -/
  jcbRV_sorted : ∀ u ∈ X.unitPart, iRV (jcbRV u)
  /-- `jcb_RV` is `RV^×`-valued -/
  jcbRV_ne : ∀ u ∈ X.unitPart, jcbRV u ≠ iRVZero
  /-- the two Jacobians agree after `vrv`: *"Obviously this always exists and
  `vrv(jcb_RV F(f(ū),ū)) = jcb_Γ F(f(ū),ū)`"* (`paper.tex` line 2108) -/
  jcb_vrv : ∀ u ∈ X.unitPart, L.vrv (jcbRV u) = jcbΓ u
  /-- the exceptional set of condition (1); carried on the codomain, see the header, deviation 1 -/
  holes : Set (Fin m' → M)
  /-- *"a definable subset"* -/
  holes_definable : Definable S (fun _ : Fin m' => SortTag.rv) holes
  /-- *"of dimension `< k`"* -/
  holes_small : RVdimLt S m' k holes
  /-- **condition (1)**: *"ω(ū) = ω'(F(ū)) · jcb_RV F(f(ū), ū) for every ū ∈ dom(F) outside of a
  definable subset of dom(F) of dimension < k"* -/
  vol : ∀ u ∈ X.unitPart, F u ∉ holes → X.ω u = iRVMul (Y.ω (F u)) (jcbRV u)
  /-- **condition (2)**: *"vrv(ω(ū)) = (vrv ∘ ω' ∘ F)(ū) + jcb_Γ F(f(ū), ū) for every
  ū ∈ dom(F)"* — for **every** `ū`, with no exceptional set -/
  volΓ : ∀ u ∈ X.unitPart,
    L.vrv (X.ω u) = L.gAdd (L.vrv (Y.ω (F u))) (jcbΓ u)

namespace RVVolHom

variable {S : SP M} {L : VolLaws M} {m m' m'' k : ℕ}
  {X : RVVolObj S m k} {Y : RVVolObj S m' k} {Z : RVVolObj S m'' k}

/-! ### The elementary closure lemmas -/

/-- **The identity is a morphism.**  Remark \ref{mor:equi}: *"since the Jacobian of the identity map
is equal to `1` almost everywhere, by Lemma \ref{jcb:chain}, every morphism is actually an
isomorphism"*.  Here `jcb_RV = 1`, `jcb_Γ = 0`, and conditions (1), (2) become `ω = ω · 1` and
`vrv ω = vrv ω + 0`, which are the `RV^×`-unit and `Γ`-neutral laws.

The definability of the identity's graph is the paper's *"definable"*; it is a hypothesis here because
the tree has no `Definable`-identity lemma for a general index type — the substitution wall recorded
in `QE-PLAN.md`.  The `0 < k` is the paper's *"Suppose `k > 0`"*. -/
def id (X : RVVolObj S m k) (L : VolLaws M) (hk : 0 < k)
    (hid : Definable S (Sum.elim (fun _ : Fin m => SortTag.rv) (fun _ : Fin m => SortTag.rv))
      {z : (Fin m ⊕ Fin m) → M | baseProj z ∈ X.unitPart ∧ secondPart z = baseProj z}) :
    RVVolHom L X X where
  F := fun u => u
  F_maps := fun _ hu => hu
  F_definable := hid
  F_inj := fun _ _ _ _ h => h
  F_surj := fun v hv => ⟨v, hv, rfl⟩
  jcbRV := fun _ => iRVOne
  jcbΓ := fun _ => L.gZero
  jcbRV_sorted := fun _ _ => L.one_sorted
  jcbRV_ne := fun _ _ => L.one_ne_zero
  jcb_vrv := fun _ _ => L.vrv_one
  holes := ∅
  holes_definable := definable_empty S _
  holes_small := rvDimLt_empty hk
  vol := fun u hu _ => (L.mul_one (X.ω u) (X.ω_sorted u hu.1) (X.ω_ne_zero u hu.1)).symm
  volΓ := fun u _ => (L.add_zero (L.vrv (X.ω u))).symm

/-- **Composition of morphisms.**  The paper's chain rule for the Jacobians (`paper.tex` line 2111,
*"Note that the chain rule clearly holds for both `jcb_RV` and `jcb_Γ` whenever the things involved
are defined"*): the composite's `jcb_RV` is `(jcb_RV G ∘ F) · jcb_RV F` and its `jcb_Γ` is
`(jcb_Γ G ∘ F) + jcb_Γ F`.  Conditions (1) and (2) for the composite are then instances of
associativity in `RV^×` and in `Γ`, applied to the two component equations.

Because the exceptional set of condition (1) is carried on the codomain (header, deviation 1), the
composite's exceptional set has to be *supplied*: it must contain the points whose image under `F`
lies in either component's exceptional set, and moving those sets to the domain of the composite is
again the definable-image step the tree does not have.  Hence `holes`, its definability, its dimension
bound, and the covering hypothesis `hcover` are explicit arguments; so is the definability of the
composite's graph. -/
def comp (h : RVVolHom L X Y) (g : RVVolHom L Y Z)
    (holes : Set (Fin m'' → M))
    (holes_definable : Definable S (fun _ : Fin m'' => SortTag.rv) holes)
    (holes_small : RVdimLt S m'' k holes)
    (hcover : ∀ u ∈ X.unitPart, g.F (h.F u) ∉ holes →
      g.F (h.F u) ∉ g.holes ∧ h.F u ∉ h.holes)
    (Fdef : Definable S (Sum.elim (fun _ : Fin m => SortTag.rv) (fun _ : Fin m'' => SortTag.rv))
      {z : (Fin m ⊕ Fin m'') → M |
        baseProj z ∈ X.unitPart ∧ secondPart z = g.F (h.F (baseProj z))}) :
    RVVolHom L X Z where
  F := fun u => g.F (h.F u)
  F_maps := fun u hu => g.F_maps _ (h.F_maps u hu)
  F_definable := Fdef
  F_inj := fun u hu u' hu' heq =>
    h.F_inj hu hu' (g.F_inj (h.F_maps u hu) (h.F_maps u' hu') heq)
  F_surj := by
    rintro w hw
    obtain ⟨v, hv, rfl⟩ := g.F_surj w hw
    obtain ⟨u, hu, rfl⟩ := h.F_surj v hv
    exact ⟨u, hu, rfl⟩
  jcbRV := fun u => iRVMul (g.jcbRV (h.F u)) (h.jcbRV u)
  jcbΓ := fun u => L.gAdd (g.jcbΓ (h.F u)) (h.jcbΓ u)
  jcbRV_sorted := fun u hu => by
    have hFu : h.F u ∈ Y.unitPart := h.F_maps u hu
    exact L.mul_sorted _ _ (g.jcbRV_sorted _ hFu) (h.jcbRV_sorted u hu)
  jcbRV_ne := fun u hu => by
    have hFu : h.F u ∈ Y.unitPart := h.F_maps u hu
    exact L.mul_ne_zero _ _ (g.jcbRV_sorted _ hFu) (h.jcbRV_sorted u hu)
      (g.jcbRV_ne _ hFu) (h.jcbRV_ne u hu)
  jcb_vrv := fun u hu => by
    have hFu : h.F u ∈ Y.unitPart := h.F_maps u hu
    rw [L.vrv_mul _ _ (g.jcbRV_sorted _ hFu) (h.jcbRV_sorted u hu),
      g.jcb_vrv _ hFu, h.jcb_vrv u hu]
  holes := holes
  holes_definable := holes_definable
  holes_small := holes_small
  vol := fun u hu hnot => by
    obtain ⟨h1, h2⟩ := hcover u hu hnot
    have hFu : h.F u ∈ Y.unitPart := h.F_maps u hu
    have hZF : g.F (h.F u) ∈ Z.unitPart := g.F_maps _ hFu
    rw [h.vol u hu h2, g.vol (h.F u) hFu h1]
    exact L.mul_assoc _ _ _ (Z.ω_sorted _ hZF.1) (g.jcbRV_sorted _ hFu) (h.jcbRV_sorted u hu)
      (Z.ω_ne_zero _ hZF.1) (g.jcbRV_ne _ hFu) (h.jcbRV_ne u hu)
  volΓ := fun u hu => by
    have hFu : h.F u ∈ Y.unitPart := h.F_maps u hu
    rw [h.volΓ u hu, g.volΓ (h.F u) hFu, L.add_assoc]


/-! ### The inverse of a morphism: *"every morphism here is actually an isomorphism"*

Definition \ref{defn:RV:cat:vol}: *"It is easily seen from the definitions of `jcb_RV` and `jcb_Γ`
that every morphism here is actually an isomorphism."*  (The `VF`-side counterpart is Remark
\ref{mor:equi}.)  The inverse's Jacobians are the reciprocal Jacobians of `F` — the paper's chain
rule for the Jacobians (`paper.tex` line 2111) applied to `F ∘ F^{-1} = id` and to the identity's
Jacobians `1` and `0` — and the inverse of a definable bijection is definable; both are carried as
hypotheses here, because the tree has neither the chain rule of §9 nor the definable-inverse lemma.

The inverse also shows where the *codomain* convention of `RVVolHom.holes` bites: the inverse's
exceptional set must contain the preimage under `F` of the exceptional set of `F`, and moving that
preimage across is the definable-image step the tree does not have.  `hcover` records the implication
that the proof actually needs. -/

variable {S : SP M} {L : VolLaws M} {m m' k : ℕ} {X : RVVolObj S m k} {Y : RVVolObj S m' k}

/-- The inverse of an essential bijection, as a choice function on the unit part. -/
noncomputable def invFun (F : RVVolHom L X Y) (dflt : Fin m → M) : (Fin m' → M) → Fin m → M := by
  classical
  exact fun v => if hv : v ∈ Y.unitPart then Classical.choose (F.F_surj v hv) else dflt

theorem invFun_maps (F : RVVolHom L X Y) (dflt : Fin m → M) {v : Fin m' → M}
    (hv : v ∈ Y.unitPart) : F.invFun dflt v ∈ X.unitPart := by
  rw [invFun, dif_pos hv]
  exact (Classical.choose_spec (F.F_surj v hv)).1

theorem F_invFun (F : RVVolHom L X Y) (dflt : Fin m → M) {v : Fin m' → M}
    (hv : v ∈ Y.unitPart) : F.F (F.invFun dflt v) = v := by
  rw [invFun, dif_pos hv]
  exact (Classical.choose_spec (F.F_surj v hv)).2

theorem invFun_F (F : RVVolHom L X Y) (dflt : Fin m → M) {u : Fin m → M}
    (hu : u ∈ X.unitPart) : F.invFun dflt (F.F u) = u := by
  have hFu : F.F u ∈ Y.unitPart := F.F_maps u hu
  rw [invFun, dif_pos hFu]
  have hspec := Classical.choose_spec (F.F_surj (F.F u) hFu)
  exact F.F_inj hspec.1 hu hspec.2

/-- **Every morphism of `mRV[k,·]` is an isomorphism** (Definition \ref{defn:RV:cat:vol}):
*"It is easily seen from the definitions of `jcb_RV` and `jcb_Γ` that every morphism here is actually
an isomorphism."*

The inverse `F^{-1}` is `invFun` (a choice function on the unit part, which is where the essential
isomorphism lives), its Jacobians are the reciprocal Jacobians `jcbRV'`, `jcbΓ'`, and its exceptional
set `holes` contains the preimage of `F`'s (`hcover`).  Condition (1) for the inverse is then
`ω(v) = ω'(F^{-1}v) · jcb_RV' v`, obtained from condition (1) for `F` by associativity in `RV^×` and
`jcb_RV F · jcb_RV' = 1`; condition (2) is `Γ`-associativity together with
`jcb_Γ F + jcb_Γ' = 0`, i.e. `vrv(jcb_RV') = -vrv(jcb_RV)` — the `Γ`-half of the chain rule. -/
noncomputable def inverse (F : RVVolHom L X Y) (dflt : Fin m → M)
    (hdef : Definable S (Sum.elim (fun _ : Fin m' => SortTag.rv) (fun _ : Fin m => SortTag.rv))
      {z : (Fin m' ⊕ Fin m) → M | baseProj z ∈ Y.unitPart ∧ secondPart z = F.invFun dflt (baseProj z)})
    (jcbRV' : (Fin m' → M) → M) (jcbΓ' : (Fin m' → M) → M)
    (hRV'_sorted : ∀ v ∈ Y.unitPart, iRV (jcbRV' v))
    (hRV'_ne : ∀ v ∈ Y.unitPart, jcbRV' v ≠ iRVZero)
    (h'_vrv : ∀ v ∈ Y.unitPart, L.vrv (jcbRV' v) = jcbΓ' v)
    (hprod : ∀ v ∈ Y.unitPart, iRVMul (F.jcbRV (F.invFun dflt v)) (jcbRV' v) = iRVOne)
    (hneg : ∀ v ∈ Y.unitPart, L.gAdd (F.jcbΓ (F.invFun dflt v)) (jcbΓ' v) = L.gZero)
    (holes : Set (Fin m → M)) (holes_definable : Definable S (fun _ : Fin m => SortTag.rv) holes)
    (holes_small : RVdimLt S m k holes)
    (hcover : ∀ v ∈ Y.unitPart, F.invFun dflt v ∉ holes → v ∉ F.holes) :
    RVVolHom L Y X where
  F := F.invFun dflt
  F_maps := fun v hv => F.invFun_maps dflt hv
  F_definable := hdef
  F_inj := by
    intro v hv v' hv' heq
    rw [← F.F_invFun dflt hv, ← F.F_invFun dflt hv', heq]
  F_surj := fun u hu => ⟨F.F u, F.F_maps u hu, F.invFun_F dflt hu⟩
  jcbRV := jcbRV'
  jcbΓ := jcbΓ'
  jcbRV_sorted := hRV'_sorted
  jcbRV_ne := hRV'_ne
  jcb_vrv := h'_vrv
  holes := holes
  holes_definable := holes_definable
  holes_small := holes_small
  vol := fun v hv hnot => by
    have hv' : F.invFun dflt v ∈ X.unitPart := F.invFun_maps dflt hv
    have hFv : F.F (F.invFun dflt v) = v := F.F_invFun dflt hv
    have h1 : X.ω (F.invFun dflt v) =
        iRVMul (Y.ω v) (F.jcbRV (F.invFun dflt v)) := by
      rw [F.vol (F.invFun dflt v) hv' (by rw [hFv]; exact hcover v hv hnot), hFv]
    have hassoc : iRVMul (iRVMul (Y.ω v) (F.jcbRV (F.invFun dflt v))) (jcbRV' v) =
        iRVMul (Y.ω v) (iRVMul (F.jcbRV (F.invFun dflt v)) (jcbRV' v)) :=
      L.mul_assoc (Y.ω v) (F.jcbRV (F.invFun dflt v)) (jcbRV' v)
        (Y.ω_sorted v hv.1) (F.jcbRV_sorted (F.invFun dflt v) hv')
        (hRV'_sorted v hv) (Y.ω_ne_zero v hv.1) (F.jcbRV_ne (F.invFun dflt v) hv')
        (hRV'_ne v hv)
    have hprod' : iRVMul (F.jcbRV (F.invFun dflt v)) (jcbRV' v) = iRVOne := hprod v hv
    rw [h1, hassoc, hprod',
      L.mul_one (Y.ω v) (Y.ω_sorted v hv.1) (Y.ω_ne_zero v hv.1)]
  volΓ := fun v hv => by
    have hv' : F.invFun dflt v ∈ X.unitPart := F.invFun_maps dflt hv
    have hFv : F.F (F.invFun dflt v) = v := F.F_invFun dflt hv
    have h1 : L.vrv (X.ω (F.invFun dflt v)) =
        L.gAdd (L.vrv (Y.ω v)) (F.jcbΓ (F.invFun dflt v)) := by
      rw [F.volΓ (F.invFun dflt v) hv', hFv]
    rw [h1, L.add_assoc, hneg v hv, L.add_zero]

/-- **Every morphism is an isomorphism**, as an existential: a two-sided inverse morphism. -/
theorem isIso (F : RVVolHom L X Y) (dflt : Fin m → M)
    (hdef : Definable S (Sum.elim (fun _ : Fin m' => SortTag.rv) (fun _ : Fin m => SortTag.rv))
      {z : (Fin m' ⊕ Fin m) → M | baseProj z ∈ Y.unitPart ∧ secondPart z = F.invFun dflt (baseProj z)})
    (jcbRV' : (Fin m' → M) → M) (jcbΓ' : (Fin m' → M) → M)
    (hRV'_sorted : ∀ v ∈ Y.unitPart, iRV (jcbRV' v))
    (hRV'_ne : ∀ v ∈ Y.unitPart, jcbRV' v ≠ iRVZero)
    (h'_vrv : ∀ v ∈ Y.unitPart, L.vrv (jcbRV' v) = jcbΓ' v)
    (hprod : ∀ v ∈ Y.unitPart, iRVMul (F.jcbRV (F.invFun dflt v)) (jcbRV' v) = iRVOne)
    (hneg : ∀ v ∈ Y.unitPart, L.gAdd (F.jcbΓ (F.invFun dflt v)) (jcbΓ' v) = L.gZero)
    (holes : Set (Fin m → M)) (holes_definable : Definable S (fun _ : Fin m => SortTag.rv) holes)
    (holes_small : RVdimLt S m k holes)
    (hcover : ∀ v ∈ Y.unitPart, F.invFun dflt v ∉ holes → v ∉ F.holes) :
    ∃ F' : RVVolHom L Y X, (∀ v ∈ Y.unitPart, F.F (F'.F v) = v) ∧
      (∀ u ∈ X.unitPart, F'.F (F.F u) = u) :=
  ⟨F.inverse dflt hdef jcbRV' jcbΓ' hRV'_sorted hRV'_ne h'_vrv hprod hneg holes holes_definable
      holes_small hcover,
    fun v hv => F.F_invFun dflt hv, fun u hu => F.invFun_F dflt hu⟩

end RVVolHom

/-! ## Part 4. The lift `𝕃(U,ω)`

*"For any `(U,ω) ∈ mRV[k]`, let `L ω` be the function on `L U` naturally induced by `ω`.  The lift of
`(U,ω)` is the object `L(U,ω) = (L U, L ω) ∈ mVF[k]`."*

`RVObj.lift` (§4, Definition \ref{def:L}) is `𝕃_k(U,f) = ⋃{rv^{-1}(f(ū)) × {ū} : ū ∈ U}`, a subset
of `VF^k × (base)` indexed by `Fin k ⊕ Fin m`, the `k` `VF`-coordinates first.  `L ω` is `ω` read on
the base coordinate: `𝕃ω(a,ū) = ω(ū)`. -/

/-- The **shape** of the paper's lift `𝕃(U,ω) = (𝕃U, 𝕃ω)`: the underlying set `𝕃_k(U,f)` of §4 together
with the volume form `𝕃ω`, which is constant on `rv`-fibres by construction (it only sees the base).

This is deliberately *not* the paper's `mVF[k,·]`: the `VF`-side category, with its own definability
fields and its Jacobian condition `ω(x̄) = ω'(F(x̄)) · rv(jcb_VF F(x̄))`, is Definition
\ref{defn:mVF:cat:vol} and a different direction of this run.  Here it serves the two purposes §10
puts it to: the statement of Theorem 10.4 (`(A,ω)` is isomorphic to a lift) and of Theorem 10.5
(`F^↑ : 𝕃(U,ω) → 𝕃(U',ω')` is measure-preserving), through `VFMeasurePreservingOff`. -/
structure VFVolData (S : SP M) (k m : ℕ) where
  /-- the underlying set, `𝕃_k(U,f) ⊆ VF^k × (RV-base)` -/
  total : Set ((Fin k ⊕ Fin m) → M)
  /-- the paper's `𝕃ω` -/
  ω : ((Fin k ⊕ Fin m) → M) → M
  /-- `𝕃ω` is `RV`-valued -/
  ω_sorted : ∀ x ∈ total, iRV (ω x)
  /-- `𝕃ω` is `RV^×`-valued: it takes the values of `ω` -/
  ω_ne_zero : ∀ x ∈ total, ω x ≠ iRVZero

namespace RVVolObj

variable {S : SP M} {m k : ℕ}

/-- **`𝕃(U,ω) = (𝕃U, 𝕃ω)`**: *"The lift of `(U,ω)` is the object `L(U,ω) = (L U, L ω)`"*
(`paper.tex` line 2262).  `𝕃ω` is *"the function on `L U` naturally induced by `ω`"*: on
`𝕃U = ⋃{rv^{-1}(f(ū)) × {ū}}` the only available datum is the base point `ū`, so `𝕃ω(a,ū) = ω(ū)`.

(Whether `𝕃U` and the graph of `𝕃ω` are definable — they are, by §3's quantifier elimination — is a
separate question this shape does not record; see the `VFVolData` docstring.) -/
def lift (X : RVVolObj S m k) : VFVolData S k m where
  total := X.toRV.lift
  ω := fun x => X.ω (base x)
  ω_sorted := by
    rintro x ⟨-, hU, -⟩
    exact X.ω_sorted _ hU
  ω_ne_zero := by
    rintro x ⟨-, hU, -⟩
    exact X.ω_ne_zero _ hU

@[simp]
theorem lift_total (X : RVVolObj S m k) : X.lift.total = X.toRV.lift := rfl

@[simp]
theorem lift_ω (X : RVVolObj S m k) (x : (Fin k ⊕ Fin m) → M) :
    X.lift.ω x = X.ω (base x) := rfl

/-- **The unit part of the lift.**  *"since the parts `f(U) ∖ A` and `g(V) ∖ B` will not concern us,
we may assume `f^{-1}(A) = U` and `g^{-1}(B) = V`"* (`paper.tex` line 2079): the measure-preserving
equation of 10.5 is asserted on the part of `𝕃U` lying over the unit part of the base — this is the
paper's own reduction, and it is what makes the `ω`-equation of condition (1) applicable at every
point. -/
def liftUnit (X : RVVolObj S m k) : Set ((Fin k ⊕ Fin m) → M) :=
  {x | x ∈ X.toRV.lift ∧ base x ∈ X.unitPart}

theorem mem_liftUnit {X : RVVolObj S m k} {x : (Fin k ⊕ Fin m) → M} :
    x ∈ X.liftUnit ↔ x ∈ X.toRV.lift ∧ base x ∈ X.unitPart := Iff.rfl

end RVVolObj

/-- **The `mVF[k]`-condition of Definition \ref{defn:mVF:cat:vol}**, off an exceptional set: *"A
morphism between two objects `(A, ω)`, `(A', ω')` is a definable essential bijection `F : A → A'` …
such that for every `x̄ ∈ dom(F)`, `ω(x̄) = ω'(F(x̄)) · rv(jcb_VF F(x̄))`"*.

Only this equation is recorded, and only off `holes`: the `VF`-side category is a different direction
of this run, and here the equation is exactly what Theorem 10.5 asserts about `F^↑`. -/
def VFMeasurePreservingOff {S : SP M} {k m m' : ℕ} (A : Set ((Fin k ⊕ Fin m) → M))
    (ω : ((Fin k ⊕ Fin m) → M) → M) (holes : Set ((Fin k ⊕ Fin m) → M))
    (Y : VFVolData S k m') (F : ((Fin k ⊕ Fin m) → M) → (Fin k ⊕ Fin m') → M)
    (jcbVF : ((Fin k ⊕ Fin m) → M) → M) : Prop :=
  ∀ x ∈ A, x ∉ holes → ω x = iRVMul (Y.ω (F x)) (iRv (jcbVF x))

/-! ## Part 5. Theorem \ref{L:measure:surjective} (10.4)

*"Every object `(A, ω)` in `mVF[k]` is isomorphic to another object `L(U,π)` in `mVF[k]`, where
`(U, π) ∈ mRV[k]`; similarly for other pairs of corresponding categories."*

Proof (`paper.tex` lines 2266–2269): *"By Corollary \ref{all:subsets:rvproduct} there is a special
bijection `T : A_ω → A_1` with `A_1` an `RV`-pullback such that `(rv(A_1), pr_{≤k}) ∈ RV[k]`.  Let
`ω_1 = ω ∘ T^{-1}`.  So `ω_1` is constant on every `rv`-polydisc.  By Corollary
\ref{diff:almost:every} and Lemma \ref{special:tran:vol:pre}, `(A, ω)` and `(A_1, ω_1)` are
isomorphic.  Let `π : rv(A_1) → RV` be the function naturally induced by `ω_1`.  Then
`(rv(A_1), pr_{≤k}, π)` is as required."*

The computational half — the part of this proof that is §10's own and not a citation — is the lemma
`measure_preserving_of_jcb_one` below: with `ω(x) = 𝕃π(T x)` (which is what `ω_1 = ω ∘ T^{-1}`
constant on `rv`-polydiscs says) and `rv(jcb T) = 1` (which is Lemma \ref{special:tran:vol:pre}),
condition (1) of the `mVF`-morphism becomes `ω(x) = 𝕃π(T x) · 1`, the `RV^×`-unit law. -/

/-- **The step `(A,ω) ≅ (A_1,ω_1)` of the proof of 10.4**: a bijection `T` onto the lift of an
`RV`-object which pulls the volume form back (`ω x = 𝕃π(T x)`) and has Jacobian `1`
(`rv(jcb T) = 1`, Lemma \ref{special:tran:vol:pre}) is `mVF`-measure-preserving. -/
theorem measure_preserving_of_jcb_one {L : VolLaws M} {S : SP M} {k m m' : ℕ}
    (A : Set ((Fin k ⊕ Fin m) → M)) (ω : ((Fin k ⊕ Fin m) → M) → M)
    (Y : RVVolObj S m' k) (T : ((Fin k ⊕ Fin m) → M) → (Fin k ⊕ Fin m') → M)
    (jcbT : ((Fin k ⊕ Fin m) → M) → M)
    (hT : ∀ x ∈ A, T x ∈ Y.lift.total)
    (hjcb : ∀ x ∈ A, iRv (jcbT x) = iRVOne)
    (hω : ∀ x ∈ A, ω x = Y.lift.ω (T x)) :
    VFMeasurePreservingOff A ω ∅ Y.lift T jcbT := by
  intro x hx _
  have hYω : iRV (Y.lift.ω (T x)) := Y.lift.ω_sorted _ (hT x hx)
  have hYne : Y.lift.ω (T x) ≠ iRVZero := Y.lift.ω_ne_zero _ (hT x hx)
  rw [hjcb x hx, hω x hx]
  exact (L.mul_one (Y.lift.ω (T x)) hYω hYne).symm

/-- **Theorem \ref{L:measure:surjective} (10.4)**, in the family form `mVF[k,·] → mRV[k,·]` (the
paper's `mVF[k]` is the case `m = 0` up to the empty block `Fin 0`).

**What is assumed, exactly.**  `hreduce` is Corollary \ref{all:subsets:rvproduct} together with
Corollary \ref{diff:almost:every} and Lemma \ref{special:tran:vol:pre} of §5/§7/§9, in the form the
paper's proof uses them: there are `(U,π) ∈ mRV[k]` (i.e. an `RVVolObj Y`) and a definable bijection
`T` from `A` onto `𝕃(U,π)` that (i) transports the volume form back, `ω x = 𝕃π(T x)` — the paper's
`ω_1 = ω ∘ T^{-1}`, constant on `rv`-polydiscs, hence induced by a function of the `rv`-coordinate —
and (ii) has Jacobian `1`, `rv(jcb T) = 1`.

**Explicitly noted:** this hypothesis carries essentially the *whole* mathematical content of the
theorem (it already exhibits the target lift and the bijection onto it); what is *proved* from it is
the measure-preserving equation, i.e. that `T` is an `mVF[k]`-morphism — the paper's *"By Corollary
\ref{diff:almost:every} and Lemma \ref{special:tran:vol:pre}, `(A, ω)` and `(A_1, ω_1)` are
isomorphic"*.  The remaining input, that every `mVF[k]`-morphism is an isomorphism (Remark
\ref{mor:equi}), needs the inverse's Jacobian to be the reciprocal, i.e. `jcb:chain` — a §9 result of
another direction of this run — and is *not* claimed here. -/
theorem L_measure_surjective (L : VolLaws M) {S : SP M} {k m : ℕ}
    (A : Set ((Fin k ⊕ Fin m) → M)) (ω : ((Fin k ⊕ Fin m) → M) → M)
    (hreduce : ∃ (m' : ℕ) (Y : RVVolObj S m' k) (T : ((Fin k ⊕ Fin m) → M) → (Fin k ⊕ Fin m') → M)
      (jcbT : ((Fin k ⊕ Fin m) → M) → M),
      (∀ x ∈ A, T x ∈ Y.lift.total) ∧
      (∀ x ∈ A, iRv (jcbT x) = iRVOne) ∧
      (∀ x ∈ A, ω x = Y.lift.ω (T x))) :
    ∃ (m' : ℕ) (Y : RVVolObj S m' k) (T : ((Fin k ⊕ Fin m) → M) → (Fin k ⊕ Fin m') → M)
      (jcbT : ((Fin k ⊕ Fin m) → M) → M),
      (∀ x ∈ A, T x ∈ Y.lift.total) ∧ VFMeasurePreservingOff A ω ∅ Y.lift T jcbT := by
  obtain ⟨m', Y, T, jcbT, hT, hjcb, hω⟩ := hreduce
  exact ⟨m', Y, T, jcbT, hT, measure_preserving_of_jcb_one (L := L) A ω Y T jcbT hT hjcb hω⟩

/-! ## Part 6. Theorem \ref{L:measure:class:lift} (10.5)

*"Let `F : (U, ω) → (U', ω')` be a `mRV[k]`-isomorphism.  Then there exists a measuring-preserving
lift `F^↑ : L(U, ω) → L(U', ω')` of `F`."*

Proof (`paper.tex` lines 2276–2281): *"Let `ω* : dom(F) → RV` be the function given by
`ū ↦ ω(ū)/ω'(F(ū))`.  By Theorem \ref{iso:lifted:vol}, there is a lift `F^↑ : L U → L U'` such that
`rv(jcb_VF F^↑(ā, ū)) = ω*(ū)` for almost all `(ā, ū) ∈ L U`, that is, `F^↑` is a `mVF[k]`-isomorphism
between `L(U, ω)` and `L(U', ω')`."*

Here `ω* = jcb_RV F`: condition (1) of the `mRV`-morphism is exactly
`ω(ū) = ω'(F ū) · jcb_RV F(ū)`, and `vrv(jcb_RV) = jcb_Γ` (`jcb_vrv`) is what makes `ω*` satisfy the
second hypothesis of Theorem \ref{iso:lifted:vol}.  So the hypothesis `hlift` below is that theorem
*for the particular `ω* = jcb_RV F`*, and the conclusion — the measure-preserving equation for `F^↑` —
is derived from it together with condition (1). -/

/-- **Theorem \ref{L:measure:class:lift} (10.5).**

**What is assumed, exactly.**  `hlift` is Theorem \ref{iso:lifted:vol} (`paper.tex` line 2126, with
Theorem \ref{RV:iso:class:lifted} of §7 behind it), instantiated at the function
`ω* = jcb_RV F` of the paper's proof: it produces a lift `F^↑` of `F` (a map `𝕃U → 𝕃U'` whose
`rv`-component is `F`) together with its `VF`-Jacobian `jcb_VF F^↑`, satisfying
`rv(jcb_VF F^↑(ā,ū)) = ω*(ū)`.

**What is proved.**  The conclusion is the measure-preserving equation of Definition
\ref{defn:mVF:cat:vol} — `𝕃ω(x̄) = 𝕃ω'(F^↑ x̄) · rv(jcb_VF F^↑(x̄))` — for that `F^↑`, off the points
whose base lies in the `mRV`-morphism's exceptional set `F.holes`.  Substituting
`rv(jcb_VF F^↑) = jcb_RV F` into condition (1) of `F`, `ω(ū) = ω'(F ū) · jcb_RV F(ū)`, gives it
verbatim; equivalently, the paper's `ω* = ω/ω'` is `jcb_RV F`.  The `mVF`-essential-bijectivity half
of "`F^↑` is a `mVF[k]`-isomorphism" is part of `hlift`, not claimed here. -/
theorem L_measure_class_lift {L : VolLaws M} {S : SP M} {k m m' : ℕ}
    (X : RVVolObj S m k) (Y : RVVolObj S m' k) (F : RVVolHom L X Y)
    (hlift : ∃ (Fup : ((Fin k ⊕ Fin m) → M) → (Fin k ⊕ Fin m') → M)
      (jcbVF : ((Fin k ⊕ Fin m) → M) → M),
      (∀ x ∈ X.toRV.lift, Fup x ∈ Y.toRV.lift) ∧
      (∀ x ∈ X.toRV.lift, RVVolObj.base (m := m') (Fup x) = F.F (RVVolObj.base (m := m) x)) ∧
      (∀ x ∈ X.toRV.lift, F.F (fun i => x (Sum.inr i)) ∉ F.holes →
        iRv (jcbVF x) = F.jcbRV (fun i => x (Sum.inr i)))) :
    ∃ (Fup : ((Fin k ⊕ Fin m) → M) → (Fin k ⊕ Fin m') → M)
      (jcbVF : ((Fin k ⊕ Fin m) → M) → M),
      (∀ x ∈ X.toRV.lift, Fup x ∈ Y.toRV.lift) ∧
      (∀ x ∈ X.toRV.lift, RVVolObj.base (m := m') (Fup x) = F.F (RVVolObj.base (m := m) x)) ∧
      VFMeasurePreservingOff X.liftUnit X.lift.ω
        {x : (Fin k ⊕ Fin m) → M | F.F (fun i => x (Sum.inr i)) ∈ F.holes}
        Y.lift Fup jcbVF := by
  obtain ⟨Fup, jcbVF, hmaps, hbase, hjcb⟩ := hlift
  refine ⟨Fup, jcbVF, hmaps, hbase, ?_⟩
  intro x hx hnot
  obtain ⟨-, hbaseUnit⟩ := RVVolObj.mem_liftUnit.1 hx
  have hb : F.F (fun i => x (Sum.inr i)) ∉ F.holes := hnot
  have hvol := F.vol _ hbaseUnit hb
  have hb2 : RVVolObj.base (m := m') (Fup x) = F.F (RVVolObj.base (m := m) x) := hbase x hx.1
  have hj := hjcb x hx.1 hb
  rw [RVVolObj.lift_ω, RVVolObj.lift_ω (X := Y), hb2, hvol, hj]
  rfl

end SP

end SpecialTransformations.Milestone0
