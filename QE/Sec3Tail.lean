/-
**The rest of Section 3's conclusion** — `fun:bounded:cons` (`paper.tex:764`), `fun:quo:rep`
(`paper.tex:777`) and `fun:quo:rep:mult` (`paper.tex:797`) — stated, and the parts that are provable
proved.

The three items are statements about *definable set-valued functions into `𝓟(RV^m)`*, the object
that `fun:into:power` (`Sec3FunIntoPower.lean`) introduced.  None of them was formalized anywhere in
the tree.  What this file does:

**§1, the objects.**  `IsSetValuedFun S m f` — the paper's "definable function
`f : VF^× -> 𝓟(RV^m)`": the graph of `f`, as a set of `(1 + m)`-tuples (one `VF`-coordinate, then
`m` `RV`-coordinates), is definable over `S` by a formula of `L_RV`, and the values are `RV`-tuples.
`imageSet` is `⋃ f(VF^×)`; `omega δ` is the paper's `ω(0,δ)`; `VrvBounded` is
"`vrv(⋃ f(VF^×))` is bounded from both above and below", stated in the preorder `<=` of `RV`
(`Rel.rvLe`), which is the order that `vrv` quotients onto `Γ` — `L_RV` has no sort for `Γ`
(see the docstring of `VrvBounded`).

**§2, `fun:bounded:cons`.**  The frozen statement `FunBoundedCons` with the paper's sentence in its
docstring, plus the two things provable without the paper's normal-form computation:
`funBoundedCons_of_const` (the conclusion holds whenever `f` is constant) and `funBoundedCons_mono`
(the conclusion is monotone in `δ`, so "for any sufficiently large `δ`" is "for some `δ`").

**§3, `fun:quo:rep`.**  `IsAddSubgroupVF G`, the relation `IsAddCosetSetoid G s` ("`s` is the coset
relation of `G`", `s x y <-> y - x ∈ G`), and the paper's two conclusions as frozen Props
`FunQuoRepOne`, `FunQuoRepOneFinite`, `FunQuoRepTwo`.  Proved:

* `funQuoRepOne_iff_finite` — **the two forms of part (1) agree**: "there are cosets `D_1, ..., D_n`
  such that `f ↾ (VF ∖ ⋃_i D_i)` is a function from `(VF ∖ ⋃_i D_i)/G` into `𝓟(RV^m)`" and "`f`
  fails to be constant on only finitely many cosets" — the second is the form §7 uses
  (`paper.tex:1887`: "By Lemma `fun:quo:rep`, `f` fails to be constant on only finitely many cosets
  of `ω(0,γ)`").
* `funQuoRepOne_descends` — part (1) is exactly the condition of `fun:into:power` applied to the
  graph of `f ↾ (VF ∖ ⋃D_i)`: the graph of the restricted `f` *is* a function
  `(VF ∖ ⋃D_i)/G -> 𝓟(RV^m)` in the sense of `paper.tex:755`.
* `funQuoRepTwo_noDef` — **the attainment half of part (2) is free**: for *any* set-valued function
  and *any* coset relation there is a `G`-invariant `f↓` that attains `f` on every coset, with no
  definability at all.  Hence the entire content of part (2) is the **definability** of `f↓`.
* `funQuoRepTwo_of_coset_const` — if `f` is constant on every coset then part (2) holds outright
  (`f↓ := f`); so only the *finite* exceptional family of part (1) needs the paper's
  centres/effectiveness argument.
* `AddSubgroupVFIsBall` — the paper's parenthetical in `fun:quo:rep` ("hence `G` is either an open
  ball around `0` or a closed ball around `0`"), frozen: it rests on C-minimality.
* `funQuoRepOne_of_coset_const` — (1) with empty exception set, so the frozen form of (1) is not
  vacuous.
* `funQuoRepTwo_of_one_and_choice` — **the paper's "This establishes (2)"**: (2) from (1) plus a
  *centre function* on the exceptional cosets (`qe.tex:1132`; a function, not a set).
* `FunQuoRepOneHolds`, `FunQuoRepTwoHolds` — (1) and (2) packaged with the paper's hypotheses on `G`
  and `f`.

**§4, `fun:quo:rep:mult`.**  The multiplicative analogue: `IsMulSubgroupVF`, `IsMulCosetSetoid`
(`s x y <-> ∃ g ∈ G, y = g * x`, the relation "`y/x ∈ G`" written without an inverse symbol — `L_RV`
has none), the paper's trichotomy for definable multiplicative subgroups (frozen:
`MulSubgroupVFTrichotomy`), parts (1) and (2) as frozen Props, and the same two proved reductions
(`funQuoRepMultOne_of_coset_const`, `funQuoRepMultTwo_noDef`, `funQuoRepMultTwo_of_coset_const`,
`funQuoRepMultTwo_of_one_and_choice`).  Both conclusions mention the subgroup only through its coset
relation `s`, so the additive and multiplicative forms are the *same* statement; what differs is the
hypotheses on `s`.

No `sorry`, no `axiom`, no `decide`/`native_decide`.  The frozen statements are `def`s of type
`Prop`, not theorems, so that a later section can take them as named hypotheses in the project's
standing style — nothing here is proved by assumption.

Check with (`.scratch2/sec3/` holds the compiled `Enc`, `Sec3Frozen`, `Sec3Infra`,
`Sec3FunIntoPower`):

    cp .ultramath/smw1qqehg/m2/Sec3Tail.lean .scratch2/sec3/
    cd .scratch2/sec3 && LEAN_PATH=$PWD:$LEAN_PATH lean Sec3Tail.lean
-/
import Sec3FunIntoPower

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0

namespace Sec3Tail

open FunIntoPower

/-! ## 1. The objects -/

variable {M : Type*} [LRV.Structure M]

/-- The interpretation of the constant `0` of the `VF` sort. -/
def vfZero : M := Structure.funMap (L := LRV) Fn.vfZero fun i => i.elim0

/-- The interpretation of the constant `1` of the `VF` sort. -/
def vfOne : M := Structure.funMap (L := LRV) Fn.vfOne fun i => i.elim0

/-- The interpretation of `+` of the `VF` sort. -/
def vfAdd (x y : M) : M := Structure.funMap (L := LRV) Fn.vfAdd ![x, y]

/-- The interpretation of `-` of the `VF` sort. -/
def vfNeg (x : M) : M := Structure.funMap (L := LRV) Fn.vfNeg ![x]

/-- The interpretation of `times` of the `VF` sort. -/
def vfMul (x y : M) : M := Structure.funMap (L := LRV) Fn.vfMul ![x, y]

/-- `x - y` in the ring of the `VF` sort. -/
def vfSub (x y : M) : M := vfAdd x (vfNeg y)

/-- **The paper's preorder `<=` on `RV`** (`Rel.rvLe`), semantically.  This is the order whose
quotient by `vrv` is the order of `Γ`: `iLeRV u v` is "`v u <= v v`", and `vrv (rv x) = vv x`. -/
def iLeRV (x y : M) : Prop := Structure.RelMap (L := LRV) Rel.rvLe ![x, y]

/-- The `VF`-sort as a type. -/
def VFp (M : Type*) [LRV.Structure M] : Type _ := {x : M // iVF x}

instance : Coe (VFp M) M := ⟨Subtype.val⟩

/-- The open ball of radius `δ` around `c`: `{x : v (x - c) > δ}`. -/
def openBall (c δ : M) : Set M := {x | iVF x ∧ ¬ iLeRV (iRv (vfSub x c)) δ}

/-- The closed ball of radius `δ` around `c`: `{x : v (x - c) >= δ}`. -/
def closedBall (c δ : M) : Set M := {x | iVF x ∧ iLeRV δ (iRv (vfSub x c))}

/-- **The paper's `ω(0, δ)`**: the open ball of radius `δ` around `0`. -/
def omega (δ : M) : Set M := openBall (vfZero (M := M)) δ

/-- The paper's `ω(0, δ) ∖ {0}`. -/
def puncturedOmega (δ : M) : Set M := {x | iVF x ∧ x ≠ vfZero (M := M) ∧ ¬ iLeRV (iRv x) δ}

/-- **The units `𝔒 ∖ 𝔐`**: the `VF`-elements whose `rv`-image is a unit of `RV`, i.e. whose value is
`0` (the paper's `𝔒 = {x : vv x >= 0}`, `𝔐 = {x : vv x > 0}`). -/
def unitsVF : Set M := {x | iVF x ∧ Structure.RelMap (L := LRV) Rel.memUnits ![iRv x]}

/-- The tuple shape of the graph of a set-valued function: one `VF`-coordinate, then `m`
`RV`-coordinates. -/
abbrev GraphIdx (m : ℕ) := Sum (Fin 1) (Fin m)

/-- The graph of `f : VF -> 𝓟(RV^m)` as a set of tuples. -/
def graphSet (m : ℕ) (f : M → Set (Fin m → M)) : Set (GraphIdx m → M) :=
  {w | iVF (w (Sum.inl 0)) ∧ (fun i => w (Sum.inr i)) ∈ f (w (Sum.inl 0))}

/-- **A definable set-valued function `f : VF -> 𝓟(RV^m)`** — the paper's "definable function
`f : VF^× -> 𝓟(RV^m)`", with the domain restriction to nonzero elements carried by the hypotheses of
the individual statements, and with definability of the graph required as in the source
(`fun:into:power`'s "We are of course only interested in definable objects").

Definability is Mathlib's `Set.Definable` in the language `L_RV`, the notion the tree's other
verified §3 file uses (`QE/InfRVDefGam.lean`).  `SP.DefinableAt` of `QE/Sec3Infra.lean` is its
well-sorted refinement; the unrestricted notion admits ill-sorted terms (the caveat recorded in
`Milestone0/Encoding.lean` above `HasQE`), so these frozen hypotheses are slightly *stronger* than
the paper's.  That is harmless for a frozen target and deliberately visible here: a proof of the
statements below for the well-sorted notion would only need `DefinableAt`. -/
def IsSetValuedFun (S : Set M) (m : ℕ) (f : M → Set (Fin m → M)) : Prop :=
  Set.Definable S LRV (graphSet m f) ∧ ∀ a (Y : Fin m → M), Y ∈ f a → ∀ i, iRV (Y i)

/-- The graph of a function on the `VF`-sort `g : VF -> 𝓟(RV^m)`, as a set of tuples.  (The
`∃ h` binder is immaterial: proof irrelevance makes the value unique.) -/
def graphSetSub (m : ℕ) (g : VFp M → Set (Fin m → M)) : Set (GraphIdx m → M) :=
  {w | ∃ h : iVF (w (Sum.inl 0)), (fun i => w (Sum.inr i)) ∈ g ⟨w (Sum.inl 0), h⟩}

/-- Definability of a set-valued function on the `VF`-sort. -/
def IsSetValuedFunSub (S : Set M) (m : ℕ) (g : VFp M → Set (Fin m → M)) : Prop :=
  Set.Definable S LRV (graphSetSub m g) ∧ ∀ a (Y : Fin m → M), Y ∈ g a → ∀ i, iRV (Y i)

/-- **`⋃ f(VF^×)`**: the union of the values of `f` at the nonzero `VF`-elements. -/
def imageSet (m : ℕ) (f : M → Set (Fin m → M)) : Set (Fin m → M) :=
  {Y | ∃ a : M, iVF a ∧ a ≠ vfZero (M := M) ∧ Y ∈ f a}

/-- **"`vrv(⋃ f(VF^×))` is bounded from both above and below"**, the hypothesis of
`fun:bounded:cons`.  `L_RV` has no sort for `Γ` (`Milestone0/Encoding.lean`'s `LRVΓ` adds one and
`Gamma.iVrv` reads it, but it needs `LRVΓ.Structure M`), so the hypothesis is written where the
paper's `Γ`-order lives inside `L_RV`: in the preorder `<=` of the `RV` sort, of which `vrv` is the
quotient map onto `Γ` (`v <= w` iff `vrv v <= vrv w`).  For a subset of the `RV` sort the two
boundedness conditions are the same. -/
def VrvBounded (m : ℕ) (f : M → Set (Fin m → M)) : Prop :=
  ∃ t₁ t₂ : M, ∀ Y ∈ imageSet m f, ∀ i : Fin m, iLeRV t₁ (Y i) ∧ iLeRV (Y i) t₂

/-! ## 2. `fun:bounded:cons` -/

/-- **`fun:bounded:cons`** (`paper.tex:764`), frozen.  The paper's sentence, verbatim:

> Let `f : VF^× -> 𝓟(RV^m)` be a definable function such that the subset `vrv(⋃ f(VF^×))` is bounded
> from both above and below.  Then for any sufficiently large `δ ∈ Γ` the restriction
> `f ↾ ω(0,δ) ∖ {0}` is constant.

`δ` ranges over `RV`-elements (the paper's `Γ` is a subset of `RV`); "sufficiently large" is
`∃ δ` rather than `∀ δ` because `funBoundedCons_mono` shows the admissible `δ` form an upper set. -/
def FunBoundedCons (S : Set M) (m : ℕ) (f : M → Set (Fin m → M)) : Prop :=
  IsSetValuedFun S m f → VrvBounded m f →
    ∃ δ : M, ∀ a a' : M, a ∈ puncturedOmega δ → a' ∈ puncturedOmega δ → f a = f a'

/-- The conclusion of `fun:bounded:cons` holds whenever `f` is constant on the nonzero
`VF`-elements: the boundedness hypothesis plays no role, and every `δ` works. -/
theorem funBoundedCons_of_const {m : ℕ} {f : M → Set (Fin m → M)}
    (h : ∃ c : Set (Fin m → M), ∀ a : M, iVF a → a ≠ vfZero (M := M) → f a = c) :
    ∃ δ : M, ∀ a a' : M, a ∈ puncturedOmega δ → a' ∈ puncturedOmega δ → f a = f a' := by
  obtain ⟨c, hc⟩ := h
  exact ⟨vfZero, fun a a' ha ha' => by rw [hc a ha.1 ha.2.1, hc a' ha'.1 ha'.2.1]⟩

/-- The conclusion of `fun:bounded:cons` is monotone in `δ`: a punctured ball contained in another
gives a weaker conclusion.  Hence "for any sufficiently large `δ`" is the same as "for some `δ`",
and a proof for one `δ` gives every `δ` whose punctured ball is contained in it. -/
theorem funBoundedCons_mono {m : ℕ} {f : M → Set (Fin m → M)} {δ δ' : M}
    (hsub : ∀ x : M, x ∈ puncturedOmega δ → x ∈ puncturedOmega δ')
    (h : ∀ a a' : M, a ∈ puncturedOmega δ' → a' ∈ puncturedOmega δ' → f a = f a') :
    ∀ a a' : M, a ∈ puncturedOmega δ → a' ∈ puncturedOmega δ → f a = f a' :=
  fun a a' ha ha' => h a a' (hsub a ha) (hsub a' ha')

/-! ## 3. `fun:quo:rep` (additive case) -/

/-- **`G` is an additive subgroup of the additive group of `VF`.**  The group laws are *part of this
definition* rather than derived from `Axioms.ACVF`: deriving them needs an additive-group instance on
the `VF`-sort, which the tree has only for a Mathlib-`Valuation` field (`QE/VFField.lean`,
`QE/VFValued.lean`) and not for the one-sorted `L_RV` encoding.  Stating them is not an extra
hypothesis over the paper — the paper's "additive subgroup" *means* these laws. -/
structure IsAddSubgroupVF (G : Set M) : Prop where
  /-- `G` consists of `VF`-elements. -/
  subset_vf : ∀ x ∈ G, iVF x
  /-- `0 ∈ G`. -/
  zero_mem : vfZero (M := M) ∈ G
  /-- `G` is closed under addition. -/
  add_mem : ∀ x ∈ G, ∀ y ∈ G, vfAdd x y ∈ G
  /-- `G` is closed under negation. -/
  neg_mem : ∀ x ∈ G, vfNeg x ∈ G

/-- **`s` is the coset relation of `G`**: two `VF`-elements are `s`-related exactly when their
difference lies in `G`, i.e. exactly when they lie in the same `G`-coset.  The `Setoid` is data
because `L_RV` does not provide the ring laws on the `VF`-sort that would make `y - x ∈ G` an
equivalence relation; `IsAddSubgroupVF` records what the paper's "`G` is a subgroup" means, and this
names the relation on top of it. -/
def IsAddCosetSetoid (G : Set M) (s : Setoid (VFp M)) : Prop :=
  ∀ x y : VFp M, s.r x y ↔ vfSub (y : M) (x : M) ∈ G

/-- **`fun:quo:rep` (1)** (`paper.tex:777`), frozen:

> There are `G`-cosets `D_1, ..., D_n` such that `f ↾ (VF ∖ ⋃_i D_i)` is a function from
> `(VF ∖ ⋃_i D_i)/G` into `𝓟(RV^m)`.

The cosets are a `Finset` of the quotient `VF/G`; `f` is a function on the quotient off the union of
those classes exactly when it takes equal values on `s`-related points outside them.
`funQuoRepOne_iff_finite` shows this is the same as "`f` fails to be constant on only finitely many
cosets". -/
def FunQuoRepOne (m : ℕ) (s : Setoid (VFp M)) (f : M → Set (Fin m → M)) : Prop :=
  ∃ E : Finset (Quotient s), ∀ x y : VFp M,
    Quotient.mk s x ∉ E → Quotient.mk s y ∉ E → s.r x y → f (x : M) = f (y : M)

/-- Part (1) in the form §7 quotes it (`paper.tex:1887`: "By Lemma `fun:quo:rep`, `f` fails to be
constant on only finitely many cosets of `ω(0,γ)`"): the set of cosets on which `f` is *not*
constant is finite. -/
def FunQuoRepOneFinite (m : ℕ) (s : Setoid (VFp M)) (f : M → Set (Fin m → M)) : Prop :=
  {q : Quotient s | ∃ x y : VFp M,
    Quotient.mk s x = q ∧ Quotient.mk s y = q ∧ f (x : M) ≠ f (y : M)}.Finite

/-- **The two forms of part (1) agree.** -/
theorem funQuoRepOne_iff_finite {m : ℕ} {s : Setoid (VFp M)} {f : M → Set (Fin m → M)} :
    FunQuoRepOne m s f ↔ FunQuoRepOneFinite m s f := by
  classical
  constructor
  · rintro ⟨E, hE⟩
    refine Set.Finite.subset (E.finite_toSet) ?_
    rintro q ⟨x, y, hx, hy, hne⟩
    by_contra hq
    refine hne (hE x y ?_ ?_ ?_)
    · rw [hx]; simpa using hq
    · rw [hy]; simpa using hq
    · rw [← Quotient.eq, hx, hy]
  · intro hfin
    refine ⟨hfin.toFinset, fun x y hx hy hxy => ?_⟩
    by_contra hne
    refine hx ?_
    exact (Set.Finite.mem_toFinset hfin).mpr
      ⟨x, y, rfl, (Quotient.sound hxy).symm, hne⟩

/-- **The paper's `E_t̄`** in the proof of `fun:quo:rep` (`paper.tex:783`):

> For any `D ∈ VF/G` and any `t̄ ∈ RV^m` let `U_t̄(D) = {d ∈ D : t̄ ∈ f(d)}`.  Let
> `E_t̄ = {D ∈ VF/G : U_t̄(D) ≠ ∅ and U_t̄(D) ≠ D}`.

`Eset m s f Y` is `E_Y`: the cosets on which `Y` is attained by `f` and also missed by `f`. -/
def Eset (m : ℕ) (s : Setoid (VFp M)) (f : M → Set (Fin m → M)) (Y : Fin m → M) :
    Set (Quotient s) :=
  {q | (∃ d : VFp M, Quotient.mk s d = q ∧ Y ∈ f (d : M)) ∧
       (∃ d : VFp M, Quotient.mk s d = q ∧ Y ∉ f (d : M))}

theorem mem_Eset {m : ℕ} {s : Setoid (VFp M)} {f : M → Set (Fin m → M)} {Y : Fin m → M}
    {q : Quotient s} :
    q ∈ Eset m s f Y ↔
      (∃ d : VFp M, Quotient.mk s d = q ∧ Y ∈ f (d : M)) ∧
        (∃ d : VFp M, Quotient.mk s d = q ∧ Y ∉ f (d : M)) :=
  Iff.rfl

/-- **The paper's first observation in the proof of `fun:quo:rep`**: *"If `D ∉ E_t̄` for any `t̄` then
`f ↾ D` is constant."*  In the form used below: the set of cosets on which `f` is not constant is
exactly `⋃_{t̄} E_t̄`.  (`nonConstancy` of a class means that two of its points get different values,
which by extensionality is the same as some `t̄` being attained at one and missed at the other.) -/
theorem nonConstancy_eq_iUnion_Eset {m : ℕ} (s : Setoid (VFp M)) (f : M → Set (Fin m → M)) :
    {q : Quotient s | ∃ x y : VFp M,
      Quotient.mk s x = q ∧ Quotient.mk s y = q ∧ f (x : M) ≠ f (y : M)}
      = ⋃ Y : Fin m → M, Eset m s f Y := by
  ext q
  constructor
  · rintro ⟨x, y, hx, hy, hne⟩
    have hsym : (∃ Y : Fin m → M, Y ∈ f (x : M) ∧ Y ∉ f (y : M))
        ∨ (∃ Y : Fin m → M, Y ∈ f (y : M) ∧ Y ∉ f (x : M)) := by
      by_contra h
      push Not at h
      refine hne (Set.ext fun Y => ⟨fun h1 => ?_, fun h2 => ?_⟩)
      · by_contra h2
        exact h2 (h.1 Y h1)
      · by_contra h1
        exact h1 (h.2 Y h2)
    rw [Set.mem_iUnion]
    rcases hsym with ⟨Y, h1, h2⟩ | ⟨Y, h1, h2⟩
    · exact ⟨Y, ⟨x, hx, h1⟩, y, hy, h2⟩
    · exact ⟨Y, ⟨y, hy, h1⟩, x, hx, h2⟩
  · intro hq
    rw [Set.mem_iUnion] at hq
    obtain ⟨Y, ⟨x, hx, h1⟩, y, hy, h2⟩ := hq
    exact ⟨x, y, hx, hy, fun h => h2 (h ▸ h1)⟩

/-- **`fun:quo:rep` (1) is exactly the finiteness the paper proves**: `f` fails to be constant on only
finitely many cosets iff `⋃_{t̄} E_t̄` is finite.  This isolates the paper's model-theoretic input —
C-minimality twice, effectiveness and `function:rv:to:vf:finite:image`, which produce the finiteness
of this union (`paper.tex:786-795`) — from the set-theoretic part of the argument (proved here). -/
theorem funQuoRepOneFinite_iff_iUnion_Eset_finite {m : ℕ} {s : Setoid (VFp M)}
    {f : M → Set (Fin m → M)} :
    FunQuoRepOneFinite m s f ↔ (⋃ Y : Fin m → M, Eset m s f Y).Finite := by
  rw [FunQuoRepOneFinite, nonConstancy_eq_iUnion_Eset]

/-- The shape in which the paper's model theory is consumed: finiteness of `⋃_{t̄} E_t̄` gives part
(1). -/
theorem funQuoRepOne_of_iUnion_Eset_finite {m : ℕ} {s : Setoid (VFp M)}
    {f : M → Set (Fin m → M)} (h : (⋃ Y : Fin m → M, Eset m s f Y).Finite) :
    FunQuoRepOne m s f :=
  (funQuoRepOne_iff_finite).mpr ((funQuoRepOneFinite_iff_iUnion_Eset_finite).mpr h)

/-- The graph of `f` restricted to the points outside the cosets in `E`: the relation whose
`fun:into:power` treatment is part (1). -/
def graphExcept (m : ℕ) (s : Setoid (VFp M)) (E : Finset (Quotient s))
    (f : M → Set (Fin m → M)) : Set (VFp M × (Fin m → M)) :=
  {p | Quotient.mk s p.1 ∉ E ∧ p.2 ∈ f (p.1 : M)}

theorem fib_graphExcept_of_mem {m : ℕ} (s : Setoid (VFp M)) (E : Finset (Quotient s))
    (f : M → Set (Fin m → M)) (x : VFp M) (hx : Quotient.mk s x ∈ E) :
    fib (graphExcept m s E f) x = ∅ := by
  ext Y
  simp [fib, graphExcept, hx]

theorem fib_graphExcept_of_notMem {m : ℕ} (s : Setoid (VFp M)) (E : Finset (Quotient s))
    (f : M → Set (Fin m → M)) (x : VFp M) (hx : Quotient.mk s x ∉ E) :
    fib (graphExcept m s E f) x = f (x : M) := by
  ext Y
  simp [fib, graphExcept, hx]

/-- **Part (1) is the condition of `fun:into:power`**: off the finitely many exceptional cosets, the
graph of `f` descends to a function on the quotient `VF/G` into `𝓟(RV^m)` — i.e. it satisfies the
condition of `paper.tex:755` (with the trivial equivalence relation on the values, `RV^m`). -/
theorem funQuoRepOne_descends {m : ℕ} {s : Setoid (VFp M)} {f : M → Set (Fin m → M)}
    (h : FunQuoRepOne m s f) :
    ∃ E : Finset (Quotient s),
      Descends s (discreteSetoid (Fin m → M)) (graphExcept m s E f) := by
  classical
  obtain ⟨E, hE⟩ := h
  refine ⟨E, (descends_discrete s (graphExcept m s E f)).mpr ?_⟩
  intro x y hxy
  by_cases hx : Quotient.mk s x ∈ E
  · have hy : Quotient.mk s y ∈ E := by rw [← Quotient.sound hxy]; exact hx
    rw [fib_graphExcept_of_mem s E f x hx, fib_graphExcept_of_mem s E f y hy]
  · have hy : Quotient.mk s y ∉ E := by
      intro hy; exact hx (by rw [Quotient.sound hxy]; exact hy)
    rw [fib_graphExcept_of_notMem s E f x hx, fib_graphExcept_of_notMem s E f y hy]
    exact hE x y hx hy hxy

/-- **`fun:quo:rep` (2)** (`paper.tex:777`), frozen:

> If either `G` is a closed ball or `S` is `(VF, Γ)`-generated then there is a definable function
> `f↓ : VF/G -> 𝓟(RV^m)` such that for any `G`-coset `D` there is a `d ∈ D` such that
> `f(d) = f↓(D)`.

`f_down` is a function on the `VF`-sort which is `s`-invariant (that is what a function on `VF/G`
is), and "definable" is `IsSetValuedFunSub S m f_down`.  The paper's two alternatives in the
hypothesis (`G` a closed ball, or `S` `(VF,Γ)`-generated) are the standing hypotheses under which
this is asserted; `funQuoRepTwo_noDef` shows the attainment clause costs nothing and
`funQuoRepTwo_of_coset_const` shows the case of no exceptional cosets is free, so what is left is
the definability of `f_down` on the finite exceptional family of part (1) — the paper's
effectiveness/centres step. -/
def FunQuoRepTwo (S : Set M) (m : ℕ) (s : Setoid (VFp M)) (f : M → Set (Fin m → M)) : Prop :=
  ∃ f_down : VFp M → Set (Fin m → M), IsSetValuedFunSub S m f_down ∧
    (∀ x y : VFp M, s.r x y → f_down x = f_down y) ∧
      ∀ x : VFp M, ∃ d : VFp M, s.r d x ∧ f (d : M) = f_down x

/-- **The attainment clause of part (2) is free.**  For *every* set-valued function `f` and *every*
coset relation `s` there is an `s`-invariant `f_down` attaining `f` on every coset — no
definability, no hypothesis.  Consequently `FunQuoRepTwo` differs from this only by the definability
of `f_down`: the mathematical content of part (2) is *definability*, not attainment. -/
theorem funQuoRepTwo_noDef (m : ℕ) (s : Setoid (VFp M)) (f : M → Set (Fin m → M)) :
    ∃ f_down : VFp M → Set (Fin m → M),
      (∀ x y : VFp M, s.r x y → f_down x = f_down y) ∧
        ∀ x : VFp M, ∃ d : VFp M, s.r d x ∧ f (d : M) = f_down x := by
  classical
  refine ⟨fun x => f ((Quotient.out (s := s) (Quotient.mk s x) : VFp M) : M), ?_, ?_⟩
  · intro x y hxy
    have hq : Quotient.mk s x = Quotient.mk s y := Quotient.sound hxy
    have hout : (Quotient.out (s := s) (Quotient.mk s x) : VFp M)
        = Quotient.out (s := s) (Quotient.mk s y) := by rw [hq]
    show f ((Quotient.out (s := s) (Quotient.mk s x) : VFp M) : M)
        = f ((Quotient.out (s := s) (Quotient.mk s y) : VFp M) : M)
    rw [hout]
  · intro x
    exact ⟨(Quotient.out (s := s) (Quotient.mk s x) : VFp M),
      Quotient.exact (Quotient.out_eq _), rfl⟩

/-- **Part (2) when `f` is already constant on every coset**: then `f_down := f` works, so the case
of part (2) that needs the paper's effectiveness argument is exactly the finite exceptional family of
part (1). -/
theorem funQuoRepTwo_of_coset_const {S : Set M} {m : ℕ} {s : Setoid (VFp M)}
    {f : M → Set (Fin m → M)} (hdef : IsSetValuedFun S m f)
    (hconst : ∀ x y : VFp M, s.r x y → f (x : M) = f (y : M)) :
    FunQuoRepTwo S m s f := by
  classical
  refine ⟨fun x => f (x : M), ⟨?_, ?_⟩, hconst, fun x => ⟨x, s.refl x, rfl⟩⟩
  · have hset : graphSetSub m (fun x : VFp M => f (x : M)) = graphSet m f := by
      ext w
      constructor
      · rintro ⟨h, hw⟩
        exact ⟨h, hw⟩
      · rintro ⟨h, hw⟩
        exact ⟨h, hw⟩
    rw [hset]
    exact hdef.1
  · intro a Y hY i
    exact hdef.2 (a : M) Y hY i

/-- Part (1) in the case of no exceptional cosets: if `f` is constant on every coset then it is a
function on the whole quotient, so the `Finset` of exceptions can be taken empty.  (Sanity check
that the frozen statement of part (1) is not vacuous.) -/
theorem funQuoRepOne_of_coset_const {m : ℕ} {s : Setoid (VFp M)} {f : M → Set (Fin m → M)}
    (hconst : ∀ x y : VFp M, s.r x y → f (x : M) = f (y : M)) : FunQuoRepOne m s f :=
  ⟨∅, fun x y _ _ hxy => hconst x y hxy⟩

/-- **`fun:quo:rep` (2)** packaged with the paper's hypotheses: `G` a definable additive subgroup,
`s` its coset relation, `f` a definable set-valued function.  (The paper's second alternative in the
hypothesis — "or `S` is `(VF,Γ)`-generated" — needs the `Γ`-sort of `L_RV^Γ` and is recorded in the
docstring of `FunQuoRepTwo` rather than formalized.) -/
def FunQuoRepTwoHolds (S : Set M) (m : ℕ) (G : Set M) (s : Setoid (VFp M))
    (f : M → Set (Fin m → M)) : Prop :=
  IsAddSubgroupVF G → IsAddCosetSetoid G s → Set.Definable₁ S LRV G → IsSetValuedFun S m f →
    FunQuoRepTwo S m s f

/-- **The step "This establishes (2)" of `fun:quo:rep`.**  Part (2) follows from part (1) once one
has, on the finite exceptional family, an `S`-definable `G`-invariant `g` attaining `f` there (the
paper obtains it from effectiveness/centres: "By Lemma `effectiveness` or Lemma
`algebraic:balls:definable:centers`, `⋃_t̄ E_t̄` has definable centers.  This establishes (2)").

The input `g` with `hatt` is exactly a **centre function** in the sense of the companion paper's
Definition at `qe.tex:1132` — "If there is a definable function `f : 𝓑 → VF` such that `f(𝔟_i) ∈ 𝔟_i`
for every `𝔟_i` then we say that `𝓑` has *centers*" — applied to the finite family of exceptional
cosets: a definable, `G`-invariant choice of a value of `f` on each of them.  (Note that this is a
*function*, not a set; the frozen `SP.IsSetOfCenters` of `QE/Sec3_sat.lean` is the set-valued
notion, which is refutable — see `.ultramath/smw1kv9xm/m3/CentersNote.lean`.)  The paper obtains it
from `effectiveness` (`qe.tex:1139`, algebraic sets of *closed* balls) when `G` is a closed ball, and
from `algebraic:balls:definable:centers` (`qe.tex:1170`, which needs `S` `(VF,Γ)`-generated)
otherwise — exactly the two alternatives in the hypothesis of `fun:quo:rep` (2).

`U` is the union of the exceptional cosets; it is required to be `S`-definable and a union of
cosets, and `g` supplies the attained values on it.  The `f↓` built is `g` on `U` and `f` off `U`:
`f` is constant on cosets off `U` by part (1) and `g` is invariant everywhere, so the piecewise
function is invariant, and its graph is `(graph g ∩ U) ∪ (graph f ∩ Uᶜ)`, which is definable. -/
theorem funQuoRepTwo_of_one_and_choice {S : Set M} {m : ℕ} {s : Setoid (VFp M)}
    {f : M → Set (Fin m → M)} (hfdef : IsSetValuedFun S m f)
    (g : VFp M → Set (Fin m → M)) (hgdef : IsSetValuedFunSub S m g)
    (hginv : ∀ x y : VFp M, s.r x y → g x = g y)
    (U : Set M) (hUdef : Set.Definable₁ S LRV U)
    (hUsat : ∀ x y : VFp M, s.r x y → ((x : M) ∈ U ↔ (y : M) ∈ U))
    (hconstoff : ∀ x y : VFp M, (x : M) ∉ U → (y : M) ∉ U → s.r x y → f (x : M) = f (y : M))
    (hatt : ∀ x : VFp M, (x : M) ∈ U → ∃ d : VFp M, s.r d x ∧ f (d : M) = g x) :
    FunQuoRepTwo S m s f := by
  classical
  have hW : Set.Definable S LRV {w : GraphIdx m → M | w (Sum.inl 0) ∈ U} :=
    Set.Definable.preimage_comp (fun _ : Fin 1 => (Sum.inl 0 : GraphIdx m)) hUdef
  refine ⟨fun y : VFp M => if (y : M) ∈ U then g y else f (y : M), ⟨?_, ?_⟩, ?_, ?_⟩
  · have hgraph : graphSetSub m (fun y : VFp M => if (y : M) ∈ U then g y else f (y : M))
        = (graphSetSub m g ∩ {w : GraphIdx m → M | w (Sum.inl 0) ∈ U}) ∪
          (graphSet m f ∩ {w : GraphIdx m → M | w (Sum.inl 0) ∈ U}ᶜ) := by
      ext w
      by_cases hw : w (Sum.inl 0) ∈ U <;> by_cases hv : iVF (w (Sum.inl 0)) <;>
        simp [graphSetSub, graphSet, hw, hv]
    rw [hgraph]
    exact (hgdef.1.inter hW).union (hfdef.1.inter hW.compl)
  · intro a Y hY i
    by_cases ha : (a : M) ∈ U
    · simp only [ha, if_true] at hY
      exact hgdef.2 a Y hY i
    · simp only [ha, if_false] at hY
      exact hfdef.2 (a : M) Y hY i
  · intro x y hxy
    by_cases hx : (x : M) ∈ U
    · have hy : (y : M) ∈ U := (hUsat x y hxy).mp hx
      simp only [hx, hy, if_true]
      exact hginv x y hxy
    · have hy : (y : M) ∉ U := fun h => hx ((hUsat x y hxy).mpr h)
      simp only [hx, hy, if_false]
      exact hconstoff x y hx hy hxy
  · intro x
    by_cases hx : (x : M) ∈ U
    · obtain ⟨d, hd, hfd⟩ := hatt x hx
      exact ⟨d, hd, by simp only [hx, if_true]; exact hfd⟩
    · exact ⟨x, s.refl x, by simp only [hx, if_false]⟩

/-- **The paper's parenthetical in `fun:quo:rep`**: "`G` is a definable additive subgroup of `VF`
(hence `G` is either an open ball around `0` or a closed ball around `0`)".  Frozen: the "hence"
rests on C-minimality. -/
def AddSubgroupVFIsBall (G : Set M) : Prop :=
  ∃ δ : M, G = openBall (vfZero (M := M)) δ ∨ G = closedBall (vfZero (M := M)) δ

/-- **`fun:quo:rep`, part (1)**, packaged with the paper's hypotheses: `G` a definable additive
subgroup and `f` a definable set-valued function. -/
def FunQuoRepOneHolds (S : Set M) (m : ℕ) (G : Set M) (s : Setoid (VFp M))
    (f : M → Set (Fin m → M)) : Prop :=
  IsAddSubgroupVF G → IsAddCosetSetoid G s → Set.Definable₁ S LRV G → IsSetValuedFun S m f →
    FunQuoRepOne m s f

/-! ## 4. `fun:quo:rep:mult` (multiplicative case) -/

/-- **`G` is a multiplicative subgroup of `VF^×`**, with the group laws taken as part of the
definition, as in `IsAddSubgroupVF`.  (`L_RV` has no inverse symbol on the `VF` sort, so "`y/x ∈ G`"
is written existentially in `IsMulCosetSetoid` below.) -/
structure IsMulSubgroupVF (G : Set M) : Prop where
  /-- `G` consists of `VF`-elements. -/
  subset_vf : ∀ x ∈ G, iVF x
  /-- `1 ∈ G`. -/
  one_mem : vfOne (M := M) ∈ G
  /-- `G` is closed under multiplication. -/
  mul_mem : ∀ x ∈ G, ∀ y ∈ G, vfMul x y ∈ G
  /-- `G` contains the inverse of each of its elements, in the form `∃ g ∈ G, g x = 1`. -/
  inv_mem : ∀ x ∈ G, ∃ g ∈ G, vfMul g x = vfOne (M := M)

/-- **`s` is the coset relation of the multiplicative subgroup `G`**: `x` and `y` are related when
`y = g * x` for some `g ∈ G`, i.e. when `y/x ∈ G`.  (The division is implicit: `L_RV` has no `x⁻¹`
on the `VF` sort.) -/
def IsMulCosetSetoid (G : Set M) (s : Setoid (VFp M)) : Prop :=
  ∀ x y : VFp M, s.r x y ↔ ∃ g : M, g ∈ G ∧ vfMul g (x : M) = (y : M)

/-- **`fun:quo:rep:mult` (1)** (`paper.tex:797`), frozen: the conclusion of `fun:quo:rep` (1) for a
*multiplicative* subgroup `G` of `VF^×`.  The paper's remark says the proof of `fun:quo:rep` works
verbatim for this `G`, and that is visible in the statements: both conclusions mention the subgroup
only through its coset relation `s`, so the additive and multiplicative forms are the *same*
statement — what differs is the pair of hypotheses on `s` (`IsAddCosetSetoid` versus
`IsMulCosetSetoid`). -/
def FunQuoRepMultOne (m : ℕ) (s : Setoid (VFp M)) (f : M → Set (Fin m → M)) : Prop :=
  FunQuoRepOne m s f

/-- **`fun:quo:rep:mult` (2)**, frozen: the conclusion of `fun:quo:rep` (2) for a multiplicative
subgroup `G`.  For `G = 𝔒 ∖ 𝔐` the paper modifies the construction so that `𝔟_D` is a finite union
of `rv`-balls containing `h(D)` rather than a closed ball; that is the only change, so the statement
has the same shape as the additive one. -/
def FunQuoRepMultTwo (S : Set M) (m : ℕ) (s : Setoid (VFp M))
    (f : M → Set (Fin m → M)) : Prop :=
  FunQuoRepTwo S m s f

/-- **The paper's trichotomy for a definable multiplicative subgroup of `VF^×`**
(`paper.tex:797-798`): "Then `G` is an open ball around `1` or a closed ball around `1` or
`𝔒 ∖ 𝔐`."  Frozen: it rests on C-minimality. -/
def MulSubgroupVFTrichotomy (G : Set M) : Prop :=
  (∃ δ : M, G = openBall (vfOne (M := M)) δ) ∨
    (∃ δ : M, G = closedBall (vfOne (M := M)) δ) ∨ G = unitsVF

/-- **The `fun:quo:rep:mult` attainment clause is free**, exactly as for the additive case: every
set-valued function has an `s`-invariant `f_down` attaining it on every coset. -/
theorem funQuoRepMultTwo_noDef (m : ℕ) (s : Setoid (VFp M)) (f : M → Set (Fin m → M)) :
    ∃ f_down : VFp M → Set (Fin m → M),
      (∀ x y : VFp M, s.r x y → f_down x = f_down y) ∧
        ∀ x : VFp M, ∃ d : VFp M, s.r d x ∧ f (d : M) = f_down x :=
  funQuoRepTwo_noDef m s f

/-- Part (1) for a multiplicative subgroup in the case of no exceptional cosets. -/
theorem funQuoRepMultOne_of_coset_const {m : ℕ} {s : Setoid (VFp M)} {f : M → Set (Fin m → M)}
    (hconst : ∀ x y : VFp M, s.r x y → f (x : M) = f (y : M)) : FunQuoRepMultOne m s f :=
  funQuoRepOne_of_coset_const hconst

/-- **The multiplicative analogue of the "This establishes (2)" step**: for part (2) of
`fun:quo:rep:mult` the same reduction applies verbatim, since the statement has the same shape
(the paper's only change is in the construction of `𝔟_D`, which enters through the choice `g` on the
exceptional cosets, i.e. through the hypothesis `hatt`). -/
theorem funQuoRepMultTwo_of_one_and_choice {S : Set M} {m : ℕ} {s : Setoid (VFp M)}
    {f : M → Set (Fin m → M)} (hfdef : IsSetValuedFun S m f)
    (g : VFp M → Set (Fin m → M)) (hgdef : IsSetValuedFunSub S m g)
    (hginv : ∀ x y : VFp M, s.r x y → g x = g y)
    (U : Set M) (hUdef : Set.Definable₁ S LRV U)
    (hUsat : ∀ x y : VFp M, s.r x y → ((x : M) ∈ U ↔ (y : M) ∈ U))
    (hconstoff : ∀ x y : VFp M, (x : M) ∉ U → (y : M) ∉ U → s.r x y → f (x : M) = f (y : M))
    (hatt : ∀ x : VFp M, (x : M) ∈ U → ∃ d : VFp M, s.r d x ∧ f (d : M) = g x) :
    FunQuoRepMultTwo S m s f :=
  funQuoRepTwo_of_one_and_choice hfdef g hgdef hginv U hUdef hUsat hconstoff hatt

/-- **The multiplicative analogue of `funQuoRepTwo_of_coset_const`**: if `f` is constant on every
coset of a multiplicative subgroup then `FunQuoRepMultTwo` holds outright. -/
theorem funQuoRepMultTwo_of_coset_const {S : Set M} {m : ℕ} {s : Setoid (VFp M)}
    {f : M → Set (Fin m → M)} (hdef : IsSetValuedFun S m f)
    (hconst : ∀ x y : VFp M, s.r x y → f (x : M) = f (y : M)) : FunQuoRepMultTwo S m s f :=
  funQuoRepTwo_of_coset_const hdef hconst

end Sec3Tail

end SpecialTransformations.Milestone0
