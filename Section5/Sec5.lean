module

/-
# Section 5: `RV`-pullbacks and special bijections (standalone)

The paper's Section 5, in the shape swarm `smw18ygko` m1 left it and verified here (compiled:
exit 0, 0 errors, **no `sorry`**, 55 theorems): `Pt`, `key`, `SamePD`, `polydisc`, `rvHull`,
`IsRVPullback`, degenerate pullbacks, `Csharp`, `rvHullSharp`, the focus map, `eta`,
`SpecialBijection` (with `image`, `invMap`, `lh`, `refl`, `comp`), `IsDeformedRVPullback`,
`eta_wellPosed` derived from its hypotheses, `etaInv ∘ eta = id`, and the paper's unique contraction
`exists_unique_contractionVF`.

**Why it lives here and not in `SpecialTransformations/SpecialBijection.lean`:** it is a standalone
snapshot with its own copy of `RV`, as `AGENTS.md` §4 prescribes for every `.lean` file here, and that
copy clashes with `SpecialTransformations/Basic.lean`'s `RV` when both are in one `lake build`
(`environment already contains 'SpecialTransformations.RV'`).  Unifying the two copies is part of
Milestone 1–2 work, not of merging this file.

What is *not* here: the paper's numbered statements 5.2, 5.4, 5.5 are frozen as `def … : Prop` (the
apparatus is formalized, the theorems are not).  Recorded dead end, which is why the paper deforms
rather than maps directly: `T(A)` need not be an `RV`-pullback after one centripetal step (witness
ℚ_p, λ = 1: `1+p`, `1+p²` share an `rv`-polydisc, `p`, `p²` do not).

Build: `LEAN_PATH=$PWD:$LEAN_PATH lean QE/Sec5.lean` from the repository root.  See
`MILESTONES.md` (Milestone 3).
-/
public import Mathlib

@[expose] public section

open Valuation

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace SpecialTransformations

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-! ### The `RV` sort and its valuation (paper: Definition 2.1, Definition 2.2) -/

/-- `RV× = Kˣ / (1 + M)`, the multiplicative RV sort. -/
abbrev RVUnit (v : Valuation K Γ₀) : Type _ := Kˣ ⧸ v.valuationSubring.principalUnitGroup

/-- The RV sort with the point at infinity: `RV = RV× ∪ {∞}`.  `none` is `∞`. -/
abbrev RV (v : Valuation K Γ₀) : Type _ := Option (RVUnit v)

/-- The quotient map `rv : K → RV`, with `rv 0 = ∞`. -/
noncomputable def rv (v : Valuation K Γ₀) (x : K) : RV v := by
  classical
  exact if h : x = 0 then none else some (QuotientGroup.mk (Units.mk0 x h))

@[simp] theorem rv_zero (v : Valuation K Γ₀) : rv v 0 = none := by
  classical simp [rv]

theorem rv_of_ne (v : Valuation K Γ₀) {x : K} (h : x ≠ 0) :
    rv v x = some (QuotientGroup.mk (Units.mk0 x h)) := by
  classical simp [rv, h]

theorem rv_eq_none_iff (v : Valuation K Γ₀) {a : K} : rv v a = none ↔ a = 0 := by
  classical
  by_cases h : a = 0
  · simp [rv, h]
  · simp [rv, h]

/-! ### The valuation on `RV` (the paper's `vrv`) -/

/-- The valuation, viewed as a monoid homomorphism on the units of `K`. -/
noncomputable def vUnits (v : Valuation K Γ₀) : Kˣ →* Γ₀ˣ where
  toFun u := Units.mk0 (v (u : K)) (by
    rw [Valuation.ne_zero_iff]
    exact Units.ne_zero u)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [Valuation.map_mul]

@[simp] theorem vUnits_apply (v : Valuation K Γ₀) (u : Kˣ) :
    ((vUnits v u : Γ₀ˣ) : Γ₀) = v (u : K) := rfl

theorem vUnits_ker (v : Valuation K Γ₀) :
    v.valuationSubring.principalUnitGroup ≤ (vUnits v).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, Units.ext_iff, vUnits_apply]
  exact (Valuation.mem_unitGroup_iff K v x).1 (v.valuationSubring.principal_units_le_units hx)

/-- The map `RV^× → Γ` induced by the valuation (the paper's `vrv` on the group part
of the `RV`-sort).  Well defined because `v` is trivial on `1 + M`. -/
noncomputable def vrvUnit (v : Valuation K Γ₀) : RVUnit v →* Γ₀ˣ :=
  QuotientGroup.lift _ (vUnits v) (vUnits_ker v)

@[simp] theorem vrvUnit_mk (v : Valuation K Γ₀) (u : Kˣ) :
    vrvUnit v (QuotientGroup.mk' _ u) = vUnits v u := rfl

/-- The paper's `vrv : RV → Γ ∪ {∞}`: the map induced by the valuation on `RV^×`,
extended by `vrv ∞ = 0`. -/
noncomputable def vrv (v : Valuation K Γ₀) : RV v → Γ₀
  | none => 0
  | some q => (vrvUnit v q : Γ₀)

@[simp] theorem vrv_none (v : Valuation K Γ₀) : vrv v (none : RV v) = 0 := rfl

@[simp] theorem vrv_some (v : Valuation K Γ₀) (q : RVUnit v) :
    vrv v (some q) = (vrvUnit v q : Γ₀) := rfl

theorem vrv_mk (v : Valuation K Γ₀) (u : Kˣ) :
    vrv v (some (QuotientGroup.mk' _ u)) = v (u : K) := rfl

/-- `vv = vrv ∘ rv` (axiom 6 of Definition 2.2). -/
theorem vrv_rv (v : Valuation K Γ₀) (x : K) : vrv v (rv v x) = v x := by
  by_cases h : x = 0
  · subst h; simp [rv_zero]
  · rw [rv_of_ne v h]
    change vrv v (some (QuotientGroup.mk' v.valuationSubring.principalUnitGroup
      (Units.mk0 x h))) = v x
    rw [vrv_mk]
    rfl

/-! ### `rv`-balls (paper: Definition 2.6) -/

/-- The `rv`-ball `rv⁻¹(t)`. -/
noncomputable def rvBall (v : Valuation K Γ₀) (t : RV v) : Set K := {a | rv v a = t}

@[simp] theorem mem_rvBall (v : Valuation K Γ₀) {a : K} {t : RV v} :
    a ∈ rvBall v t ↔ rv v a = t := Iff.rfl

/-- The open ball `{b | v (b - a) < γ}`.  (Mathlib's order: smaller value = deeper.) -/
def openBall (v : Valuation K Γ₀) (a : K) (γ : Γ₀) : Set K := {b | v (b - a) < γ}

@[simp] theorem mem_openBall (v : Valuation K Γ₀) {a b : K} {γ : Γ₀} :
    b ∈ openBall v a γ ↔ v (b - a) < γ := Iff.rfl

/-- `v a` is invertible for `a ≠ 0`. -/
theorem pos_map_of_ne_zero (v : Valuation K Γ₀) {a : K} (ha : a ≠ 0) : 0 < v a := by
  have h0 : v a ≠ 0 := fun h => ha ((v.zero_iff).mp h)
  exact lt_of_le_of_ne' zero_le h0

/-- Multiplying by `(v a)⁻¹` does not change the ordering against `1`. -/
theorem mul_inv_lt_one_iff (v : Valuation K Γ₀) {a : K} (ha : a ≠ 0) (x : Γ₀) :
    x * (v a)⁻¹ < 1 ↔ x < v a := by
  have hv : 0 < v a := pos_map_of_ne_zero v ha
  constructor
  · intro h
    have h2 := mul_lt_mul_of_pos_right h hv
    have h3 : (x * (v a)⁻¹) * v a = x := by
      rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hv), mul_one]
    simpa [h3] using h2
  · intro h
    have h2 := mul_lt_mul_of_pos_right h (inv_pos.mpr hv)
    simpa [mul_inv_cancel₀ (ne_of_gt hv)] using h2

theorem mem_principalUnitGroup_iff_v (v : Valuation K Γ₀) (x : Kˣ) :
    x ∈ v.valuationSubring.principalUnitGroup ↔ v ((x : K) - 1) < 1 := by
  rw [ValuationSubring.mem_principalUnitGroup_iff]
  have h := Valuation.isEquiv_valuation_valuationSubring (v := v)
  have hle : v.valuationSubring.valuation ((x : K) - 1) ≤
      v.valuationSubring.valuation (1 : K) ↔ v ((x : K) - 1) ≤ v (1 : K) :=
    (h.le_iff_le (x := (x : K) - 1) (y := (1 : K))).symm
  rw [Valuation.map_one, Valuation.map_one] at hle
  have heq : v.valuationSubring.valuation ((x : K) - 1) = 1 ↔ v ((x : K) - 1) = 1 :=
    (h.eq_one_iff_eq_one (x := (x : K) - 1)).symm
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, hle]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hv => h2 (heq.mpr hv)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun ha => h2 (heq.mp ha)⟩

/-- **The bridge** (paper: Definition 2.6): the `rv`-fibres of `RV = Kˣ/(1+M)` are the
open balls `{b | v (b - a) < v a}`, i.e. `rv a = rv b ↔ v (a - b) < v a`. -/
theorem rv_eq_iff (v : Valuation K Γ₀) {a b : K} (ha : a ≠ 0) :
    rv v a = rv v b ↔ v (a - b) < v a := by
  classical
  rcases eq_or_ne b 0 with hb | hb
  · subst hb
    rw [rv_zero, rv_eq_none_iff, sub_zero]
    exact ⟨fun h => absurd h ha, fun h => absurd h (lt_irrefl _)⟩
  · have hrv_a : rv v a = some (QuotientGroup.mk (Units.mk0 a ha)) := by simp [rv, ha]
    have hrv_b : rv v b = some (QuotientGroup.mk (Units.mk0 b hb)) := by simp [rv, hb]
    rw [hrv_a, hrv_b, Option.some_inj, QuotientGroup.eq, mem_principalUnitGroup_iff_v]
    have hval : ((((Units.mk0 a ha)⁻¹ * Units.mk0 b hb : Kˣ) : K)) = a⁻¹ * b := by simp
    have hval2 : a⁻¹ * b - 1 = (b - a) / a := by
      rw [div_eq_mul_inv, sub_mul, mul_inv_cancel₀ ha, mul_comm b, sub_eq_add_neg]
    rw [hval, hval2, div_eq_mul_inv, v.map_mul, v.map_inv, mul_inv_lt_one_iff v ha,
      v.map_sub_swap b a]

/-- The `rv`-ball of `rv b` is the open ball of radius `v b` around `b`. -/
theorem rvBall_eq_openBall (v : Valuation K Γ₀) {b : K} (hb : b ≠ 0) :
    rvBall v (rv v b) = openBall v b (v b) := by
  ext a
  rw [mem_rvBall, mem_openBall, eq_comm, rv_eq_iff v hb, v.map_sub_swap b a]

/-! ### The ambient space, `rv`-polydiscs, `RV`-hulls, `RV`-pullbacks

Paper, Section 5 preamble (`paper.tex` :1251):

> For any subset `U`, recall from [*QE and minimality conditions in ACVF*,
> Definition 4.21] that the *`RV`-hull* of `U` is the union of the `rv`-polydiscs
> that have a nonempty intersection with `U`.  If `U` is equal to its `RV`-hull
> then `U` is an *`RV`-pullback*.  An `RV`-pullback is *degenerate* if it contains
> a degenerate `rv`-polydisc and is *strictly degenerate* if it only contains
> degenerate `rv`-polydiscs.

with (Definition 2.6) "a subset `𝕡 ⊆ VFⁿ × RVᵐ` is an *(open, closed, `rv`-)
polydisc* if it is of the form `(∏ᵢ 𝕓ᵢ) × {t̄}`, where each `𝕓ᵢ` is an (open,
closed, `rv`-) ball", "an `rv`-polydisc `rv⁻¹(t₁,…,tₙ) × {s̄}` is *degenerate* if
`tᵢ = ∞` for some `i`", and (Definition 4.21) `RVH(U) = ⋃{rv⁻¹(t̄) × {s̄} :
(t̄, s̄) ∈ rv(U)}`.

Our ambient space is the one of Definition 5.1, `A ⊆ VF × VFⁿ × RV × RVᵐ`; the
coordinate `x₁` is the "targeted `VF`-coordinate", `t₁` is the `RV`-coordinate that
`can` attaches to it.  The `RV`-key of a point is `(rv x₁, rv ā₁, t₁, t̄₁)`, and
this is a faithful `rv`-polydisc index: `key p = key q` iff `p` and `q` lie in a
common `rv`-polydisc. -/

section Geo

variable (v : Valuation K Γ₀)

/-- A point of the ambient space `VF × VFⁿ × RV × RVᵐ` of Definition 5.1:
the targeted `VF`-coordinate `x₁`, the remaining `VF`-coordinates `ā₁`, the
`RV`-coordinate `t₁` attached to `x₁` by the canonical bijection, and the
remaining `RV`-coordinates `t̄₁`. -/
structure Pt (n m : ℕ) where
  /-- the targeted `VF`-coordinate -/
  x₁ : K
  /-- the other `VF`-coordinates -/
  a : Fin n → K
  /-- the `RV`-coordinate attached to `x₁` by `can` -/
  t₁ : RV v
  /-- the other `RV`-coordinates -/
  t : Fin m → RV v

instance {n m : ℕ} : Nonempty (Pt v n m) :=
  ⟨⟨0, fun _ => 0, none, fun _ => none⟩⟩

/-- `rv` applied to a tuple of field elements (the paper writes `rv(ā)`). -/
noncomputable def rvVec {n : ℕ} (x : Fin n → K) : Fin n → RV v := fun i => rv v (x i)

/-- The `RV`-key of a point: the `RV`-coordinates of all `VF`-coordinates together
with the `RV`-coordinates of the point.  These are exactly the parameters of the
`rv`-polydisc through the point. -/
abbrev Key (n m : ℕ) : Type _ := RV v × (Fin n → RV v) × RV v × (Fin m → RV v)

/-- The `RV`-key of a point; see `Key`. -/
noncomputable def key {n m : ℕ} (p : Pt v n m) : Key v n m :=
  (rv v p.x₁, rvVec v p.a, p.t₁, p.t)

/-- `p` and `q` lie in one `rv`-polydisc, i.e. have the same `RV`-key. -/
noncomputable def SamePD {n m : ℕ} (p q : Pt v n m) : Prop := key v p = key v q

theorem key_eq_iff {n m : ℕ} {p q : Pt v n m} :
    key v p = key v q ↔
      (rv v p.x₁ = rv v q.x₁ ∧ (∀ i, rv v (p.a i) = rv v (q.a i)) ∧
        p.t₁ = q.t₁ ∧ p.t = q.t) := by
  simp only [key, rvVec, Prod.mk.injEq, funext_iff]

theorem samePD_iff {n m : ℕ} {p q : Pt v n m} :
    SamePD v p q ↔
      (rv v p.x₁ = rv v q.x₁ ∧ (∀ i, rv v (p.a i) = rv v (q.a i)) ∧
        p.t₁ = q.t₁ ∧ p.t = q.t) := key_eq_iff v

theorem samePD_refl {n m : ℕ} (p : Pt v n m) : SamePD v p p := rfl

theorem samePD_symm {n m : ℕ} {p q : Pt v n m} (h : SamePD v p q) : SamePD v q p := h.symm

theorem samePD_trans {n m : ℕ} {p q r : Pt v n m} (h₁ : SamePD v p q) (h₂ : SamePD v q r) :
    SamePD v p r := h₁.trans h₂

/-- The `rv`-polydisc through `p`, i.e. `rv⁻¹(t̄) × {s̄}` for `(t̄,s̄) = rv(p)`
(Definition 2.6 / Definition 4.21). -/
noncomputable def polydisc {n m : ℕ} (p : Pt v n m) : Set (Pt v n m) := {q | SamePD v p q}

@[simp] theorem mem_polydisc {n m : ℕ} {p q : Pt v n m} :
    q ∈ polydisc v p ↔ SamePD v p q := Iff.rfl

/-- The `RV`-hull of `A`: the union of the `rv`-polydiscs meeting `A`
(Definition 4.21 of *QE and minimality conditions in ACVF*; paper Section 5). -/
noncomputable def rvHull {n m : ℕ} (A : Set (Pt v n m)) : Set (Pt v n m) :=
  {q | ∃ p ∈ A, SamePD v p q}

theorem mem_rvHull {n m : ℕ} {A : Set (Pt v n m)} {q : Pt v n m} :
    q ∈ rvHull v A ↔ ∃ p ∈ A, SamePD v p q := Iff.rfl

theorem subset_rvHull {n m : ℕ} (A : Set (Pt v n m)) : A ⊆ rvHull v A :=
  fun p hp => ⟨p, hp, samePD_refl v p⟩

theorem rvHull_mono {n m : ℕ} {A B : Set (Pt v n m)} (h : A ⊆ B) : rvHull v A ⊆ rvHull v B :=
  fun _ ⟨p, hp, hpq⟩ => ⟨p, h hp, hpq⟩

/-- The `RV`-hull is idempotent: it is exactly the union of the `rv`-polydiscs it meets. -/
theorem rvHull_idem {n m : ℕ} (A : Set (Pt v n m)) : rvHull v (rvHull v A) = rvHull v A := by
  refine Set.Subset.antisymm ?_ (subset_rvHull v _)
  rintro q ⟨p, ⟨p', hp', hpp'⟩, hqp⟩
  exact ⟨p', hp', hpp'.trans hqp⟩

/-- `U` is an `RV`-pullback if it is a union of `rv`-polydiscs, `U = RVH(U)`. -/
noncomputable def IsRVPullback {n m : ℕ} (U : Set (Pt v n m)) : Prop := rvHull v U = U

theorem isRVPullback_iff {n m : ℕ} {U : Set (Pt v n m)} :
    IsRVPullback v U ↔ ∀ p ∈ U, polydisc v p ⊆ U := by
  constructor
  · intro h p hp q hq
    rw [← h]
    exact ⟨p, hp, hq⟩
  · intro h
    refine Set.Subset.antisymm ?_ (subset_rvHull v U)
    rintro q ⟨p, hp, hqp⟩
    exact h p hp hqp

theorem polydisc_subset_of_isRVPullback {n m : ℕ} {U : Set (Pt v n m)}
    (h : IsRVPullback v U) {p : Pt v n m} (hp : p ∈ U) : polydisc v p ⊆ U :=
  (isRVPullback_iff v).1 h p hp

/-- An `rv`-polydisc is degenerate if one of its `rv`-radii is `∞`, i.e. if one of
its `VF`-coordinates is forced to be `0` (Definition 2.6: `tᵢ = ∞`). -/
noncomputable def IsDegeneratePD {n m : ℕ} (p : Pt v n m) : Prop :=
  rv v p.x₁ = none ∨ ∃ i : Fin n, rv v (p.a i) = none

theorem isDegeneratePD_iff {n m : ℕ} (p : Pt v n m) :
    IsDegeneratePD v p ↔ (p.x₁ = 0 ∨ ∃ i : Fin n, p.a i = 0) := by
  simp only [IsDegeneratePD, rv_eq_none_iff]

/-- An `RV`-pullback is degenerate if it contains a degenerate `rv`-polydisc. -/
noncomputable def IsDegenerate {n m : ℕ} (U : Set (Pt v n m)) : Prop :=
  ∃ p ∈ U, IsDegeneratePD v p

/-- An `RV`-pullback is strictly degenerate if it only contains degenerate
`rv`-polydiscs. -/
noncomputable def IsStrictlyDegenerate {n m : ℕ} (U : Set (Pt v n m)) : Prop :=
  ∀ p ∈ U, IsDegeneratePD v p

end Geo

variable (v : Valuation K Γ₀)

/-- `RVH` commutes with binary unions. -/
theorem rvHull_union {n m : ℕ} (A B : Set (Pt v n m)) :
    rvHull v (A ∪ B) = rvHull v A ∪ rvHull v B := by
  ext q
  constructor
  · rintro ⟨p, hp | hp, hpq⟩
    · exact Or.inl ⟨p, hp, hpq⟩
    · exact Or.inr ⟨p, hp, hpq⟩
  · rintro (⟨p, hp, hpq⟩ | ⟨p, hp, hpq⟩)
    · exact ⟨p, Or.inl hp, hpq⟩
    · exact ⟨p, Or.inr hp, hpq⟩

@[simp] theorem rvHull_empty {n m : ℕ} : rvHull v (∅ : Set (Pt v n m)) = ∅ := by
  ext q; simp [mem_rvHull]

/-- An `rv`-polydisc is an `RV`-pullback. -/
theorem isRVPullback_polydisc {n m : ℕ} (p : Pt v n m) :
    IsRVPullback v (polydisc v p) := by
  refine Set.Subset.antisymm ?_ (subset_rvHull v _)
  rintro q ⟨p', hp', hqp⟩
  exact hp'.trans hqp

/-- `RV`-pullbacks are closed under binary unions. -/
theorem isRVPullback_union {n m : ℕ} {A B : Set (Pt v n m)}
    (hA : IsRVPullback v A) (hB : IsRVPullback v B) : IsRVPullback v (A ∪ B) := by
  rw [IsRVPullback, rvHull_union, hA, hB]

/-- A union of `rv`-polydiscs is an `RV`-pullback, and conversely. -/
theorem isRVPullback_iUnion_polydisc {n m : ℕ} {ι : Type*} (f : ι → Pt v n m) :
    IsRVPullback v (⋃ i : ι, polydisc v (f i)) := by
  refine Set.Subset.antisymm ?_ (subset_rvHull v _)
  rintro q ⟨p, hp, hqp⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp
  exact Set.mem_iUnion.2 ⟨i, hi.trans hqp⟩

/-! ### Definition 5.1: the centripetal transformation

Paper, Definition 5.1 (`defn:special:bijection`), verbatim:

> Let `A ⊆ VF × VFⁿ × RVᵐ`.  Let `C ⊆ RVH(A)` be an `RV`-pullback and
> `λ : pr_{>1}(C ∩ A) → VF` a function such that every `(λ(ā₁, t̄), ā₁, t̄)` is in `C`.
> Let
>   `C♯ = ⋃_{(ā₁,t₁,t̄₁) ∈ pr_{>1}C} ( (⋃{rv⁻¹(t) : vrv(t) > vrv(t₁)}) × {(ā₁,t₁,t̄₁)} )`,
>   `RVH(A)♯ = C♯ ⊎ (RVH(A) ∖ C)`.
> The *centripetal transformation `η : A → RVH(A)♯` with respect to `λ`* is defined by
> `η(a₁, ā₁, t̄) = (a₁ - λ(ā₁,t̄), ā₁, t̄)` on `C ∩ A`, and `η = id` on `A ∖ C`.
> Note that `η` is injective.  The inverse of `η` is naturally called the *centrifugal
> transformation with respect to `λ`*.  The function `λ` is called a *focus map of `X`*.
> The `RV`-pullback `C` is called the *locus* of `λ`.  A *special bijection `T`* is an
> alternating composition of centripetal transformations and the canonical bijection.
> The *length* of a special bijection `T`, denoted by `lh T`, is the number of
> centripetal transformations in `T`.  The image `T(A)` is sometimes denoted by `A♯`.

`λ` is a function of the whole projection `pr_{>1}` in this file (the paper defines it on
`pr_{>1}(C ∩ A)`); the lemmas below only ever evaluate `λ` at `proj` of a point of `C`, so
nothing is lost.  The paper's condition on `λ` -- `(λ(ā₁,t̄), ā₁, t̄) ∈ C` -- is the
predicate `IsFocusMap` below, and the further condition that the focus point lies in the
`rv`-ball `t₁` (implicit in the paper, needed for `η` to land in `C♯`) is
`IsFocusMap.ball`. -/

section Def51

variable (v : Valuation K Γ₀)

/-- `pr_{>1}`: forget the targeted `VF`-coordinate `x₁`; keeps `ā₁` and all the
`RV`-coordinates. -/
def proj {n m : ℕ} (p : Pt v n m) : (Fin n → K) × RV v × (Fin m → RV v) :=
  (p.a, p.t₁, p.t)

@[simp] theorem proj_mk {n m : ℕ} (x : K) (a : Fin n → K) (t₁ : RV v) (t : Fin m → RV v) :
    proj v (⟨x, a, t₁, t⟩ : Pt v n m) = (a, t₁, t) := rfl

/-- `C♯` (Definition 5.1): over each projection `(ā₁,t₁,t̄₁) ∈ pr_{>1}C` the `VF`-fibre is
replaced by `⋃{rv⁻¹(t) : vrv(t) > vrv(t₁)}`, the set of `x` with `vv x > vv t₁`.  In
Mathlib's (reversed) order this is `{x | v x < vrv t₁}`. -/
noncomputable def Csharp {n m : ℕ} (C : Set (Pt v n m)) : Set (Pt v n m) :=
  {q | ∃ p ∈ C, proj v q = proj v p ∧ v q.x₁ < vrv v p.t₁}

theorem mem_Csharp_iff {n m : ℕ} {C : Set (Pt v n m)} {q : Pt v n m} :
    q ∈ Csharp v C ↔ ∃ p ∈ C, proj v q = proj v p ∧ v q.x₁ < vrv v p.t₁ := Iff.rfl

/-- The paper's formula for `C♯`, with the union `⋃{rv⁻¹(t) : vrv(t) > vrv(t₁)}` made
explicit: a point of the fibre lies in the `rv`-ball of some `rv`-class `t` strictly
smaller than `t₁`. -/
theorem mem_Csharp_iff' {n m : ℕ} {C : Set (Pt v n m)} {q : Pt v n m} :
    q ∈ Csharp v C ↔ ∃ p ∈ C, proj v q = proj v p ∧
      ∃ t : RV v, rv v q.x₁ = t ∧ vrv v t < vrv v p.t₁ := by
  constructor
  · rintro ⟨p, hp, hproj, hlt⟩
    exact ⟨p, hp, hproj, rv v q.x₁, rfl, by rwa [vrv_rv]⟩
  · rintro ⟨p, hp, hproj, t, ht, hlt⟩
    refine ⟨p, hp, hproj, ?_⟩
    calc v q.x₁ = vrv v (rv v q.x₁) := (vrv_rv v _).symm
      _ = vrv v t := by rw [ht]
      _ < vrv v p.t₁ := hlt

/-- `C♯` is monotone in the locus. -/
theorem Csharp_mono {n m : ℕ} {C C' : Set (Pt v n m)} (h : C ⊆ C') :
    Csharp v C ⊆ Csharp v C' :=
  fun _ ⟨p, hp, hproj, hlt⟩ => ⟨p, h hp, hproj, hlt⟩

/-- `RVH(A)♯ = C♯ ⊎ (RVH(A) ∖ C)` (Definition 5.1). -/
noncomputable def rvHullSharp {n m : ℕ} (A C : Set (Pt v n m)) : Set (Pt v n m) :=
  Csharp v C ∪ (rvHull v A \ C)

/-- The centripetal transformation `η` with respect to the focus map `λ` (Definition 5.1).
It shears the targeted coordinate, `x₁ ↦ x₁ - λ(ā₁,t₁,t̄₁)` on the locus `C`, and is the
identity off `C`; the two clauses of the paper's definition are `eta_of_mem` and
`eta_of_not_mem`. -/
noncomputable def eta {n m : ℕ} (C : Set (Pt v n m))
    (lam : (Fin n → K) × RV v × (Fin m → RV v) → K) (q : Pt v n m) : Pt v n m := by
  classical
  exact if q ∈ C then ⟨q.x₁ - lam (proj v q), q.a, q.t₁, q.t⟩ else q

theorem eta_of_mem {n m : ℕ} {C : Set (Pt v n m)}
    {lam : (Fin n → K) × RV v × (Fin m → RV v) → K} {q : Pt v n m} (h : q ∈ C) :
    eta v C lam q = ⟨q.x₁ - lam (proj v q), q.a, q.t₁, q.t⟩ := by
  classical
  rw [eta]
  exact if_pos h

theorem eta_of_not_mem {n m : ℕ} {C : Set (Pt v n m)}
    {lam : (Fin n → K) × RV v × (Fin m → RV v) → K} {q : Pt v n m} (h : q ∉ C) :
    eta v C lam q = q := by
  classical
  rw [eta]
  exact if_neg h

/-- `η` does not move the projection: it only shears the targeted coordinate. -/
theorem proj_eta {n m : ℕ} (C : Set (Pt v n m))
    (lam : (Fin n → K) × RV v × (Fin m → RV v) → K) (q : Pt v n m) :
    proj v (eta v C lam q) = proj v q := by
  by_cases h : q ∈ C
  · rw [eta_of_mem v h]; rfl
  · rw [eta_of_not_mem v h]

/-- `λ : pr_{>1}(C ∩ A) → VF` is a *focus map with locus `C`* (Definition 5.1) if every
`(λ(ā₁,t̄), ā₁, t̄)` lies in `C`.  The extra field `ball` records the condition that the
focus point lies in the `rv`-ball of `t₁`; the paper leaves it implicit, and it is what
makes `η` land in `C♯` (see `IsFocusMap.eta_mapsTo_Csharp`). -/
structure IsFocusMap {n m : ℕ} (C : Set (Pt v n m))
    (lam : (Fin n → K) × RV v × (Fin m → RV v) → K) : Prop where
  /-- `(λ(ā₁,t̄), ā₁, t̄) ∈ C` for every `(ā₁,t₁,t̄₁) = pr_{>1}(p)`, `p ∈ C`. -/
  mem : ∀ p ∈ C, (⟨lam (proj v p), p.a, p.t₁, p.t⟩ : Pt v n m) ∈ C
  /-- the focus point lies in the `rv`-class `t₁` of the targeted coordinate -/
  ball : ∀ p ∈ C, rv v (lam (proj v p)) = p.t₁

/-! #### `η` is injective (the paper: "Note that `η` is injective") -/

/-- `η` is injective on its locus `C`: on `C` it is a shear in the targeted coordinate. -/
theorem eta_injOn_locus {n m : ℕ} (C : Set (Pt v n m))
    (lam : (Fin n → K) × RV v × (Fin m → RV v) → K) : Set.InjOn (eta v C lam) C := by
  intro x hx y hy hxy
  have hproj : proj v x = proj v y := by
    rw [← proj_eta v C lam x, ← proj_eta v C lam y, hxy]
  have hx' := eta_of_mem v (C := C) (lam := lam) hx
  have hy' := eta_of_mem v (C := C) (lam := lam) hy
  have hsub : lam (proj v x) = lam (proj v y) := by rw [hproj]
  rw [hx', hy', hsub] at hxy
  simp only [Pt.mk.injEq] at hxy
  obtain ⟨e1, e2, e3, e4⟩ := hxy
  have e1' : x.x₁ = y.x₁ := by
    have hh := congrArg (fun z => z + lam (proj v y)) e1
    simpa [sub_add_cancel] using hh
  cases x
  cases y
  simp_all

/-- `η` is injective on any set on which the shear does not collide with the identity
part: this is the hypothesis the paper omits ("Note that `η` is injective").  It holds
e.g. when `A ⊆ C` (`eta_injOn_of_subset`); in the paper's applications it is discharged
by choosing `λ` so that the sheared image misses the holes `A ∖ C`. -/
theorem eta_injOn_of_disjoint {n m : ℕ} {A C : Set (Pt v n m)}
    {lam : (Fin n → K) × RV v × (Fin m → RV v) → K}
    (hdisj : ∀ q ∈ A, q ∈ C → eta v C lam q ∉ A \ C) : Set.InjOn (eta v C lam) A := by
  intro x hx y hy hxy
  by_cases hxC : x ∈ C
  · by_cases hyC : y ∈ C
    · exact eta_injOn_locus v C lam hxC hyC hxy
    · exfalso
      have hy' : y ∈ A \ C := ⟨hy, hyC⟩
      rw [← eta_of_not_mem v (C := C) (lam := lam) hyC] at hy'
      rw [← hxy] at hy'
      exact hdisj x hx hxC hy'
  · by_cases hyC : y ∈ C
    · exfalso
      have hx' : x ∈ A \ C := ⟨hx, hxC⟩
      have hx'' : eta v C lam x ∈ A \ C := by
        rw [eta_of_not_mem v (C := C) (lam := lam) hxC]
        exact hx'
      rw [hxy] at hx''
      exact hdisj y hy hyC hx''
    · rw [eta_of_not_mem v hxC, eta_of_not_mem v hyC] at hxy
      exact hxy

/-- `η` is injective when its locus contains `A`. -/
theorem eta_injOn_of_subset {n m : ℕ} {A C : Set (Pt v n m)} (hAC : A ⊆ C)
    (lam : (Fin n → K) × RV v × (Fin m → RV v) → K) : Set.InjOn (eta v C lam) A := by
  intro x hx y hy hxy
  exact eta_injOn_locus v C lam (hAC hx) (hAC hy) hxy

/-! #### `η` lands in `RVH(A)♯` -/

/-- The heart of Definition 5.1: with `A` in canonical form (`t₁ = rv x₁`), a
non-degenerate targeted coordinate, and a focus map whose focus point lies in the
`rv`-class `t₁`, the centripetal transformation lands in `C♯`.  The geometric input is
`rv_eq_iff`: two points of one `rv`-ball are at distance strictly less than its radius. -/
theorem IsFocusMap.eta_mapsTo_Csharp {n m : ℕ} {A C : Set (Pt v n m)}
    {lam : (Fin n → K) × RV v × (Fin m → RV v) → K} (hfm : IsFocusMap v C lam)
    (hcan : ∀ q ∈ A, rv v q.x₁ = q.t₁) (hnz : ∀ q ∈ A, q.x₁ ≠ 0)
    {q : Pt v n m} (hA : q ∈ A) (hC : q ∈ C) : eta v C lam q ∈ Csharp v C := by
  refine ⟨q, hC, proj_eta v C lam q, ?_⟩
  rw [eta_of_mem v hC]
  have hq1 : rv v q.x₁ = q.t₁ := hcan q hA
  have hl : rv v (lam (proj v q)) = q.t₁ := hfm.ball q hC
  have hne : q.x₁ ≠ 0 := hnz q hA
  have hrv : rv v q.x₁ = rv v (lam (proj v q)) := by rw [hq1, hl]
  have hlt : v (q.x₁ - lam (proj v q)) < v q.x₁ := (rv_eq_iff v hne).1 hrv
  rwa [← hq1, vrv_rv]

/-- `η` maps `A` into `RVH(A)♯ = C♯ ∪ (RVH(A) ∖ C)` (Definition 5.1). -/
theorem IsFocusMap.eta_mapsTo_rvHullSharp {n m : ℕ} {A C : Set (Pt v n m)}
    {lam : (Fin n → K) × RV v × (Fin m → RV v) → K} (hfm : IsFocusMap v C lam)
    (hcan : ∀ q ∈ A, rv v q.x₁ = q.t₁) (hnz : ∀ q ∈ A, q.x₁ ≠ 0)
    {q : Pt v n m} (hA : q ∈ A) : eta v C lam q ∈ rvHullSharp v A C := by
  by_cases hC : q ∈ C
  · exact Or.inl (hfm.eta_mapsTo_Csharp v hcan hnz hA hC)
  · refine Or.inr ⟨?_, ?_⟩
    · rw [eta_of_not_mem v hC]
      exact subset_rvHull v A hA
    · rw [eta_of_not_mem v hC]
      exact hC

/-! #### Sanity checks: the empty locus

With `C = ∅` there is no shear, `λ` is a focus map vacuously, and the construction
degenerates to the identity -- so Definition 5.1 is never vacuously unusable. -/

@[simp] theorem Csharp_empty {n m : ℕ} : Csharp v (∅ : Set (Pt v n m)) = ∅ := by
  ext q; simp [Csharp]

@[simp] theorem rvHullSharp_empty {n m : ℕ} (A : Set (Pt v n m)) :
    rvHullSharp v A ∅ = rvHull v A := by
  simp [rvHullSharp]

@[simp] theorem eta_empty {n m : ℕ}
    (lam : (Fin n → K) × RV v × (Fin m → RV v) → K) :
    eta v (∅ : Set (Pt v n m)) lam = id := by
  funext q
  exact eta_of_not_mem v (by simp)

theorem isFocusMap_empty {n m : ℕ}
    (lam : (Fin n → K) × RV v × (Fin m → RV v) → K) :
    IsFocusMap v (∅ : Set (Pt v n m)) lam where
  mem := by simp
  ball := by simp

/-! #### Consequences of the canonical form and of `C ⊆ RVH(A)`

The paper writes `η` only for `A` replaced by `can(A)` (Convention 4.20/5.0), i.e. `t₁` is
the `rv`-class of `x₁`; and it requires `C ⊆ RVH(A)`.  Under these two hypotheses the
`ball` field of `IsFocusMap` is *automatic*: a point of `C` lies in `RVH(A)`, hence in the
`rv`-polydisc of a point of `A`, hence is itself in canonical form. -/

/-- Points of one `rv`-polydisc are closer to each other than the radius: if `p` and `q`
lie in one `rv`-ball in the targeted coordinate then `v (p.x₁ - q.x₁) < v p.x₁`. -/
theorem v_sub_lt_of_samePD {n m : ℕ} {p q : Pt v n m} (hp : p.x₁ ≠ 0) (h : SamePD v p q) :
    v (p.x₁ - q.x₁) < v p.x₁ := by
  have hrv : rv v p.x₁ = rv v q.x₁ := ((samePD_iff v).1 h).1
  exact (rv_eq_iff v hp).1 hrv

/-- If `A` is in canonical form then every set contained in `RVH(A)` is in canonical form:
`t₁ = rv x₁` propagates through `rv`-polydiscs. -/
theorem can_of_subset_rvHull {n m : ℕ} {A C : Set (Pt v n m)}
    (hcan : ∀ q ∈ A, rv v q.x₁ = q.t₁) (hC : C ⊆ rvHull v A) :
    ∀ q ∈ C, rv v q.x₁ = q.t₁ := by
  intro q hq
  obtain ⟨p, hp, hpq⟩ := hC hq
  obtain ⟨h1, -, h3, -⟩ := (samePD_iff v).1 hpq
  rw [← h1, hcan p hp, h3]

/-- The paper's conditions on a focus map (`(λ(ā₁,t̄),ā₁,t̄) ∈ C`) together with
`C ⊆ RVH(A)` and the canonical form of `A` give a `IsFocusMap`: the `ball` field follows. -/
theorem isFocusMap_of_mem {n m : ℕ} {A C : Set (Pt v n m)}
    {lam : (Fin n → K) × RV v × (Fin m → RV v) → K}
    (hcan : ∀ q ∈ A, rv v q.x₁ = q.t₁) (hC : C ⊆ rvHull v A)
    (hmem : ∀ p ∈ C, (⟨lam (proj v p), p.a, p.t₁, p.t⟩ : Pt v n m) ∈ C) :
    IsFocusMap v C lam where
  mem := hmem
  ball := by
    intro p hp
    have := can_of_subset_rvHull v hcan hC _ (hmem p hp)
    simpa using this

/-- **`η` is injective** (the paper: "Note that `η` is injective"), under the paper's own
hypotheses: `A` in canonical form, a nondegenerate targeted coordinate, and a focus map.
This is `eta_injOn_of_disjoint` with the disjointness discharged: if the sheared image of
`x ∈ A ∩ C` were again in `A` then (being in canonical form) `rv (x₁ - λ) = t₁ = rv x₁`,
which together with `rv λ = t₁` gives both `v λ < v x₁` and `v λ = v x₁`. -/
theorem eta_injOn {n m : ℕ} {A C : Set (Pt v n m)}
    {lam : (Fin n → K) × RV v × (Fin m → RV v) → K} (hfm : IsFocusMap v C lam)
    (hcan : ∀ q ∈ A, rv v q.x₁ = q.t₁) (hnz : ∀ q ∈ A, q.x₁ ≠ 0) :
    Set.InjOn (eta v C lam) A := by
  refine eta_injOn_of_disjoint v ?_
  intro x hx hxC hxA
  have hcanx : rv v x.x₁ = x.t₁ := hcan x hx
  have hcanE : rv v (eta v C lam x).x₁ = (eta v C lam x).t₁ := hcan _ hxA.1
  rw [eta_of_mem v hxC] at hcanE
  have hb : rv v (lam (proj v x)) = x.t₁ := hfm.ball x hxC
  have h1 : rv v (x.x₁ - lam (proj v x)) = rv v x.x₁ := by rw [hcanE, hcanx]
  have h2 : v (lam (proj v x)) < v x.x₁ := by
    have hh := (rv_eq_iff v (hnz x hx)).1 h1.symm
    have heq : x.x₁ - (x.x₁ - lam (proj v x)) = lam (proj v x) := by ring
    rwa [heq] at hh
  have h3 : v (lam (proj v x)) = v x.x₁ := by
    have hb' : v (lam (proj v x)) = vrv v x.t₁ := by rw [← hb, vrv_rv]
    rw [hb', ← hcanx, vrv_rv]
  exact absurd h3 (ne_of_lt h2)

/-- **Definition 5.1 is well posed**: under the paper's hypotheses -- `A` in canonical form
(`can` applied), a nondegenerate targeted coordinate, `C ⊆ RVH(A)`, and a focus map with
locus `C` -- the centripetal transformation is injective on `A` and maps `A` into
`RVH(A)♯ = C♯ ∪ (RVH(A) ∖ C)`.  (The `RV`-pullback condition on `C` is used by the paper to
*find* `λ`: the focus point must lie in the same `rv`-polydisc as the point it is subtracted
from, which `isFocusMap_of_mem` extracts from `C ⊆ RVH(A)`.) -/
theorem eta_wellPosed {n m : ℕ} {A C : Set (Pt v n m)}
    {lam : (Fin n → K) × RV v × (Fin m → RV v) → K}
    (hcan : ∀ q ∈ A, rv v q.x₁ = q.t₁) (hnz : ∀ q ∈ A, q.x₁ ≠ 0)
    (hC : C ⊆ rvHull v A)
    (hmem : ∀ p ∈ C, (⟨lam (proj v p), p.a, p.t₁, p.t⟩ : Pt v n m) ∈ C) :
    Set.InjOn (eta v C lam) A ∧ ∀ q ∈ A, eta v C lam q ∈ rvHullSharp v A C := by
  have hfm : IsFocusMap v C lam := isFocusMap_of_mem v hcan hC hmem
  exact ⟨eta_injOn v hfm hcan hnz, fun q hq => hfm.eta_mapsTo_rvHullSharp v hcan hnz hq⟩

/-! #### The centrifugal transformation -/

/-- The *centrifugal transformation with respect to `λ`*: the inverse of the centripetal
transformation on its image (Definition 5.1).  It shears back, `x₁ ↦ x₁ + λ(ā₁,t₁,t̄₁)`,
over the projection of the locus. -/
noncomputable def etaInv {n m : ℕ} (C : Set (Pt v n m))
    (lam : (Fin n → K) × RV v × (Fin m → RV v) → K) (q : Pt v n m) : Pt v n m := by
  classical
  exact if proj v q ∈ proj v '' C then ⟨q.x₁ + lam (proj v q), q.a, q.t₁, q.t⟩ else q

theorem proj_etaInv {n m : ℕ} (C : Set (Pt v n m))
    (lam : (Fin n → K) × RV v × (Fin m → RV v) → K) (q : Pt v n m) :
    proj v (etaInv v C lam q) = proj v q := by
  classical
  by_cases h : proj v q ∈ proj v '' C
  · rw [etaInv, if_pos h]; rfl
  · rw [etaInv, if_neg h]

/-- The centrifugal transformation inverts the centripetal one on the locus. -/
theorem etaInv_eta_of_mem {n m : ℕ} (C : Set (Pt v n m))
    (lam : (Fin n → K) × RV v × (Fin m → RV v) → K) {q : Pt v n m} (h : q ∈ C) :
    etaInv v C lam (eta v C lam q) = q := by
  classical
  have hp : proj v (eta v C lam q) = proj v q := proj_eta v C lam q
  have hmem : proj v (eta v C lam q) ∈ proj v '' C := by
    rw [hp]; exact ⟨q, h, rfl⟩
  rw [etaInv, if_pos hmem, eta_of_mem v h]
  obtain ⟨qx, qa, qt₁, qt⟩ := q
  simp

/-- The centripetal transformation inverts the centrifugal one on the image of the locus. -/
theorem eta_etaInv_of_mem {n m : ℕ} (C : Set (Pt v n m))
    (lam : (Fin n → K) × RV v × (Fin m → RV v) → K) {q : Pt v n m} (h : q ∈ C) :
    eta v C lam (etaInv v C lam (eta v C lam q)) = eta v C lam q := by
  rw [etaInv_eta_of_mem v C lam h]

end Def51


/-! ### Special bijections (Definition 5.1, second half)

> A *special bijection `T`* is an alternating composition of centripetal transformations
> and the canonical bijection.  The *length* of a special bijection `T`, denoted by `lh T`,
> is the number of centripetal transformations in `T`.  The image `T(A)` is sometimes
> denoted by `A♯`.

A "step" is therefore either a centripetal transformation `η` (with its locus and focus
map) or the canonical bijection `can`.  Since `Pt` already carries the `RV`-coordinate `t₁`
next to `x₁`, the canonical bijection does not move the ambient space in this encoding, so
it is recorded as the identity map; what `can` does is to *enforce* `t₁ = rv x₁`, which is
the predicate `Can` below (and is a hypothesis where the paper applies `can`). -/

section SpecialBij

variable (v : Valuation K Γ₀)

/-- A step of a special bijection: a centripetal transformation (Definition 5.1), or the
canonical bijection `can`. -/
inductive Step (n m : ℕ) where
  /-- a centripetal transformation with its locus and (total) focus map -/
  | cent (C : Set (Pt v n m))
      (lam : (Fin n → K) × RV v × (Fin m → RV v) → K) (hfm : IsFocusMap v C lam)
  /-- the canonical bijection `can` (the identity in this encoding, see the section note) -/
  | canon

/-- The underlying map of a step. -/
noncomputable def Step.toFun {n m : ℕ} : Step v n m → Pt v n m → Pt v n m
  | .cent C lam _ => eta v C lam
  | .canon => id

/-- Whether a step is a centripetal transformation. -/
def Step.isCent {n m : ℕ} : Step v n m → Bool
  | .cent _ _ _ => true
  | .canon => false

/-- The contribution of a step to the length: `1` for a centripetal transformation, `0`
for the canonical bijection. -/
def Step.len {n m : ℕ} : Step v n m → ℕ
  | .cent _ _ _ => 1
  | .canon => 0

/-- The composite of a list of steps (applied left to right). -/
noncomputable def compose {n m : ℕ} : List (Step v n m) → Pt v n m → Pt v n m
  | [] => id
  | s :: l => compose l ∘ Step.toFun v s

@[simp] theorem compose_nil {n m : ℕ} : compose v ([] : List (Step v n m)) = id := rfl

theorem compose_cons {n m : ℕ} (s : Step v n m) (l : List (Step v n m)) :
    compose v (s :: l) = compose v l ∘ Step.toFun v s := rfl

theorem compose_append {n m : ℕ} (l₁ l₂ : List (Step v n m)) :
    compose v (l₁ ++ l₂) = compose v l₂ ∘ compose v l₁ := by
  induction l₁ with
  | nil => rfl
  | cons s l ih =>
    rw [List.cons_append, compose_cons, ih, compose_cons]
    rfl

/-- `lh T`, the length of a special bijection: the number of centripetal transformations. -/
def length {n m : ℕ} (l : List (Step v n m)) : ℕ := (l.map (Step.len v)).sum

@[simp] theorem length_nil {n m : ℕ} : length v ([] : List (Step v n m)) = 0 := rfl

@[simp] theorem length_append {n m : ℕ} (l₁ l₂ : List (Step v n m)) :
    length v (l₁ ++ l₂) = length v l₁ + length v l₂ := by
  simp [length, List.map_append, List.sum_append]

/-- `T` is an *alternating* composition: consecutive centripetal transformations are
separated by the canonical bijection. -/
def IsAlternating {n m : ℕ} : List (Step v n m) → Prop
  | [] => True
  | _ :: [] => True
  | s :: t :: rest => (Step.isCent v s = true → Step.isCent v t = false) ∧ IsAlternating (t :: rest)

/-- A special bijection `T` on `A`: an alternating composition of centripetal
transformations and canonical bijections (Definition 5.1), injective on `A` -- in the paper
this is automatic from "`η` is injective", see `eta_injOn_of_disjoint`.  The inverse on
the image `T(A)` is `invMap`. -/
structure SpecialBijection {n m : ℕ} (A : Set (Pt v n m)) where
  /-- the list of steps -/
  steps : List (Step v n m)
  /-- the steps alternate -/
  alternating : IsAlternating v steps
  /-- the composite is injective on `A` -/
  inj : Set.InjOn (compose v steps) A

/-- The image `T(A)` of a special bijection (the paper's `A♯`). -/
noncomputable def SpecialBijection.image {n m : ℕ} {A : Set (Pt v n m)}
    (T : SpecialBijection v A) : Set (Pt v n m) := compose v T.steps '' A

/-- The inverse of a special bijection on its image. -/
noncomputable def SpecialBijection.invMap {n m : ℕ} {A : Set (Pt v n m)}
    (T : SpecialBijection v A) : Pt v n m → Pt v n m :=
  Function.invFunOn (compose v T.steps) A

/-- The inverse of a special bijection on its image is a left inverse. -/
theorem SpecialBijection.invMap_apply {n m : ℕ} {A : Set (Pt v n m)}
    (T : SpecialBijection v A) {q : Pt v n m} (hq : q ∈ A) :
    SpecialBijection.invMap v T (compose v T.steps q) = q :=
  Set.InjOn.leftInvOn_invFunOn T.inj hq

/-- `lh T`: the length of a special bijection. -/
def SpecialBijection.lh {n m : ℕ} {A : Set (Pt v n m)} (T : SpecialBijection v A) : ℕ :=
  length v T.steps

/-- The trivial special bijection (the empty composition): length `0`. -/
def SpecialBijection.refl {n m : ℕ} (A : Set (Pt v n m)) : SpecialBijection v A where
  steps := []
  alternating := trivial
  inj := by intro x _ y _ h; exact h

@[simp] theorem SpecialBijection.lh_refl {n m : ℕ} (A : Set (Pt v n m)) :
    (SpecialBijection.refl v A).lh = 0 := rfl

/-- Composition of special bijections; the lengths add. -/
noncomputable def SpecialBijection.comp {n m : ℕ} {A : Set (Pt v n m)}
    (T : SpecialBijection v A) (U : SpecialBijection v (T.image v))
    (halt : IsAlternating v (T.steps ++ U.steps)) :
    SpecialBijection v A where
  steps := T.steps ++ U.steps
  alternating := halt
  inj := by
    intro x hx y hy hxy
    have hx' : compose v T.steps x ∈ SpecialBijection.image v T := ⟨x, hx, rfl⟩
    have hy' : compose v T.steps y ∈ SpecialBijection.image v T := ⟨y, hy, rfl⟩
    have h1 : compose v U.steps (compose v T.steps x) = compose v U.steps (compose v T.steps y) := by
      simpa only [compose_append, Function.comp_apply] using hxy
    exact T.inj hx hy (U.inj hx' hy' h1)

@[simp] theorem SpecialBijection.lh_comp {n m : ℕ} {A : Set (Pt v n m)}
    (T : SpecialBijection v A) (U : SpecialBijection v (T.image v))
    (halt : IsAlternating v (T.steps ++ U.steps)) :
    (T.comp v U halt).lh = T.lh + U.lh := by
  simp [SpecialBijection.lh, SpecialBijection.comp, length_append]

end SpecialBij


/-! ### Deformed `RV`-pullbacks

Paper, after Definition 5.1: "Recall that a subset `A` is called a *deformed `RV`-pullback*
if there is a special bijection `T` such that `T(A)` is an `RV`-pullback." -/

section Deformed

variable (v : Valuation K Γ₀)

/-- A set is a *deformed `RV`-pullback* if some special bijection carries it to an
`RV`-pullback (paper, after Definition 5.1). -/
noncomputable def IsDeformedRVPullback {n m : ℕ} (A : Set (Pt v n m)) : Prop :=
  ∃ T : SpecialBijection v A, IsRVPullback v (SpecialBijection.image v T)

end Deformed

/-! ### Contractible functions and the contraction `f↓`

Paper, between Lemma 5.2 and Theorem 5.4, verbatim:

> Let `f : A → B` be a function.  We say that `f` is *contractible* if for every
> `rv`-polydisc `𝕡 ⊆ RVH(A)` the subset `f(𝕡 ∩ A)` is contained in one `rv`-polydisc.
> Clearly, if `f : A → B` is a (definable) contractible function then there is a unique
> (definable) function `f↓ : rv(A) → rv(B)` such that the diagram commutes.

The `rv`-polydiscs are the fibres of `key`, so contractibility says that `f` is constant
on `rv`-classes, and `f↓` is the induced map of `rv`-keys.  Both existence and uniqueness
are proved below (`exists_unique_contraction`, `exists_unique_contractionVF`). -/

section Contraction

variable (v : Valuation K Γ₀)

/-- `f : A → VF` is *contractible*: it maps every `rv`-polydisc into a single `rv`-ball,
i.e. it is constant on `rv`-classes. -/
def ContractibleVF {n m : ℕ} (A : Set (Pt v n m)) (f : Pt v n m → K) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, SamePD v p q → rv v (f p) = rv v (f q)

/-- `f : A → B` (both subsets of the ambient spaces) is *contractible*: it maps every
`rv`-polydisc into a single `rv`-polydisc. -/
def Contractible {n m n' m' : ℕ} (A : Set (Pt v n m)) (f : Pt v n m → Pt v n' m') : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, SamePD v p q → SamePD v (f p) (f q)

/-- The contraction `f↓` of a contractible `VF`-valued function, as a function of the
`rv`-key: the `rv`-class of `f` at any point of `A` with that key. -/
noncomputable def contractionVF {n m : ℕ} (A : Set (Pt v n m)) (f : Pt v n m → K) :
    ↥(key v '' A) → RV v :=
  fun k => rv v (f (Classical.choose k.2))

/-- The defining property of the contraction: the triangle commutes. -/
theorem contractionVF_spec {n m : ℕ} (A : Set (Pt v n m)) (f : Pt v n m → K)
    (hf : ContractibleVF v A f) :
    ∀ (p : Pt v n m) (hp : p ∈ A),
      contractionVF v A f ⟨key v p, ⟨p, hp, rfl⟩⟩ = rv v (f p) := by
  intro p hp
  have hspec := Classical.choose_spec (⟨p, hp, rfl⟩ : key v p ∈ key v '' A)
  exact hf _ hspec.1 p hp hspec.2

/-- The contraction is unique: any function of the `rv`-key with the same property agrees. -/
theorem contractionVF_unique {n m : ℕ} (A : Set (Pt v n m)) (f : Pt v n m → K)
    (hf : ContractibleVF v A f) {g : ↥(key v '' A) → RV v}
    (hg : ∀ (p : Pt v n m) (hp : p ∈ A), g ⟨key v p, ⟨p, hp, rfl⟩⟩ = rv v (f p)) :
    g = contractionVF v A f := by
  funext k
  obtain ⟨p, hp, hpk⟩ := k.2
  have h1 : g k = g ⟨key v p, ⟨p, hp, rfl⟩⟩ := by
    congr 1
    exact Subtype.ext hpk.symm
  rw [h1, hg p hp]
  show rv v (f p) = rv v (f (Classical.choose k.2))
  have hspec := Classical.choose_spec k.2
  exact hf p hp _ hspec.1
    (by show key v p = key v (Classical.choose k.2); rw [hpk, hspec.2])

/-- The contraction `f↓ : rv(A) → rv(B)` exists and is unique. -/
theorem exists_unique_contractionVF {n m : ℕ} (A : Set (Pt v n m)) (f : Pt v n m → K)
    (hf : ContractibleVF v A f) :
    ∃! g : ↥(key v '' A) → RV v,
      ∀ (p : Pt v n m) (hp : p ∈ A), g ⟨key v p, ⟨p, hp, rfl⟩⟩ = rv v (f p) :=
  ⟨contractionVF v A f, contractionVF_spec v A f hf,
    fun _ hy => contractionVF_unique v A f hf hy⟩

/-- The contraction of a contractible function between ambient spaces. -/
noncomputable def contraction {n m n' m' : ℕ} (A : Set (Pt v n m))
    (f : Pt v n m → Pt v n' m') : ↥(key v '' A) → Key v n' m' :=
  fun k => key v (f (Classical.choose k.2))

theorem contraction_spec {n m n' m' : ℕ} (A : Set (Pt v n m))
    (f : Pt v n m → Pt v n' m') (hf : Contractible v A f) :
    ∀ (p : Pt v n m) (hp : p ∈ A),
      contraction v A f ⟨key v p, ⟨p, hp, rfl⟩⟩ = key v (f p) := by
  intro p hp
  have hspec := Classical.choose_spec (⟨p, hp, rfl⟩ : key v p ∈ key v '' A)
  exact hf _ hspec.1 p hp hspec.2

theorem contraction_unique {n m n' m' : ℕ} (A : Set (Pt v n m))
    (f : Pt v n m → Pt v n' m') (hf : Contractible v A f) {g : ↥(key v '' A) → Key v n' m'}
    (hg : ∀ (p : Pt v n m) (hp : p ∈ A), g ⟨key v p, ⟨p, hp, rfl⟩⟩ = key v (f p)) :
    g = contraction v A f := by
  funext k
  obtain ⟨p, hp, hpk⟩ := k.2
  have h1 : g k = g ⟨key v p, ⟨p, hp, rfl⟩⟩ := by
    congr 1
    exact Subtype.ext hpk.symm
  rw [h1, hg p hp]
  show key v (f p) = key v (f (Classical.choose k.2))
  have hspec := Classical.choose_spec k.2
  exact hf p hp _ hspec.1
    (by show key v p = key v (Classical.choose k.2); rw [hpk, hspec.2])

theorem exists_unique_contraction {n m n' m' : ℕ} (A : Set (Pt v n m))
    (f : Pt v n m → Pt v n' m') (hf : Contractible v A f) :
    ∃! g : ↥(key v '' A) → Key v n' m',
      ∀ (p : Pt v n m) (hp : p ∈ A), g ⟨key v p, ⟨p, hp, rfl⟩⟩ = key v (f p) :=
  ⟨contraction v A f, contraction_spec v A f hf, fun _ hy => contraction_unique v A f hf hy⟩

end Contraction

/-! ### The frozen statements of Section 5

The three items below are the paper's statements, with the paper's quantifiers, recorded as
*definitions of a `Prop`*: they are frozen statements awaiting a proof, not proved theorems
(nothing in this file uses `sorry` or `axiom`).  A later session proves `Statement_5_2`,
`Statement_5_4`, `Statement_5_5`; the definitions of Definition 5.1 and the lemmas above are
the vocabulary those proofs will need.

What the statements consume from the rest of the paper (this is the "which facts about
`ACVF`/`L_RV` does Section 5 consume" inventory):

* `Definable` is `∅`-definability in the theory `ACVF_S(0,0)` in a sufficiently saturated
  model (paper, Convention 2.5).  It is an abstract predicate here; instantiating it needs
  `Milestone0/Encoding.lean` (`ACVF`, `ACVF_S(0,0)`, the model `(C v) ⊨ ACVF`).
* *Compactness* of `ACVF_S(0,0)` (used throughout the proofs: "by compactness, we may
  concentrate on one `rv`-polydisc", and to glue definable data).
* Theorem 2.8, C-minimality of `ACVF` (`Milestone0/Encoding.lean`,
  `theorem_2_8_c_minimal`) -- consumed by Lemma 5.2, whose proof the paper delegates to
  [QE, Lemma 4.26], and by the "ball:proper:sub:center" steps.
* Lemma 3.8 (`average:0:rv:not:constant`, [QE, Lemma 4.9]) -- consumed by the base case of
  the induction in Theorem 5.4 to make the number of roots in an `rv`-polydisc drop.
* Lemma 3.1 (`dcl:to:ac`) and Corollary 3.2 (`acl:VF:transfer:acl:RV`) -- consumed by the
  proof of Lemma 5.3/`RV:morphism:condition` type arguments (not frozen here) and by the
  reduction in 5.4.
* Theorem 5.4 -- consumed by Theorem 5.5's proof (one line: apply 5.4 to the occurring
  polynomials of the formula defining `rv ∘ f`).
* Lemma 4.4 (`dim:RV:fibers`) and Lemma 4.13 (`RV:fiber:dim:same`) -- consumed by
  Corollary 5.6/5.7, which are *not* frozen here (they need the `VF`/`RV`-categories and
  the lifting map `𝕃` of §4, i.e. another direction's work).
-/

section Frozen

variable (v : Valuation K Γ₀)

/- Abstract definability predicate (paper, Convention 2.5): a *hypothesis* of the frozen
statements, never a definition -- this file does not model the language `L_RV`. -/

variable (Definable : ∀ {n m : ℕ}, Set (Pt v n m) → Prop)

/-- The `rv`-polydisc `rv⁻¹(ū) × {s̄}`: the set of points with a given `RV`-key (the
domain `rv⁻¹(ū)` of the special bijection `τ` in Theorems 5.4 and 5.5). -/
noncomputable def rvPolydisc {n m : ℕ} (u : Key v n m) : Set (Pt v n m) := {p | key v p = u}

/-- The `VF`-coordinates of a point, as one tuple `(x₁, ā₁) ∈ VF^{n+1}`. -/
noncomputable def vfTuple {n m : ℕ} (p : Pt v n m) : Fin (n + 1) → K := Fin.cons p.x₁ p.a

/-- Evaluation of a polynomial with coefficients in `VF(S)` at the `VF`-coordinates of a
point.  (The paper writes `F(X₁,…,Xₙ)`; here `n+1` is the number of `VF`-coordinates of
the ambient space, i.e. the paper's `n`.) -/
noncomputable def evalPoly {n m : ℕ} (S : Subfield K) (F : MvPolynomial (Fin (n + 1)) ↥S)
    (p : Pt v n m) : K :=
  MvPolynomial.eval₂ (Subfield.subtype S) (vfTuple v p) F

/-- **Lemma 5.2** (`simplex:with:hole:rvproduct`), frozen.  Paper, verbatim:

> Every definable subset `A ⊆ VF × RVᵐ` is a deformed `RV`-pullback.

(In our coordinates `A ⊆ Pt v 0 m`, i.e. `VF × VF⁰ × RV × RVᵐ`; the `RV`-coordinate `t₁`
next to `x₁` is the one `can` attaches, cf. the `Can` predicate.) -/
def Statement_5_2 {m : ℕ} (A : Set (Pt v 0 m)) (hA : Definable A) : Prop :=
  IsDeformedRVPullback v A

/-- **Theorem 5.4** (`special:bi:polynomial:constant:disc`), frozen.  Paper, verbatim:

> Let `F(X̄) = F(X₁,…,Xₙ)` be a polynomial with coefficients in `VF(S)`, `ū ∈ RVⁿ` a
> definable tuple, `τ : rv⁻¹(ū) → A` a special bijection, and `f = F ∘ τ⁻¹`.  Then there is
> a special bijection `T` on `A` such that `f ∘ T⁻¹` is contractible.

The two extra hypotheses `hA` and `hτ` record that `A` is definable and that `τ` maps the
polydisc `rv⁻¹(ū)` onto `A` (the paper writes `τ : rv⁻¹(ū) → A` meaning a bijection onto
`A`; in the paper's proof `τ` is a special bijection *from* the polydisc onto `A`). -/
def Statement_5_4 {n m : ℕ} (S : Subfield K) (F : MvPolynomial (Fin (n + 1)) ↥S)
    (u : Key v n m) (A : Set (Pt v n m)) (τ : SpecialBijection v (rvPolydisc v u))
    (hA : Definable A) (hτ : SpecialBijection.image v τ = A) : Prop :=
  ∃ T : SpecialBijection v A,
    ContractibleVF v A
      (fun x => evalPoly v S F (SpecialBijection.invMap v τ (SpecialBijection.invMap v T x)))

/-- **Theorem 5.5** (`special:bi:polynomial:constant`), frozen.  Paper, verbatim:

> Let `F(X̄) = F(X₁,…,Xₙ)` be a polynomial with coefficients in `VF(S)`, `B ⊆ VFⁿ` a
> definable subset, `τ : B → A` a special bijection, and `f = F ∘ τ⁻¹`.  Then there is a
> special bijection `T` on `A` such that `T(A)` is an `RV`-pullback and `f ∘ T⁻¹` is
> contractible. -/
def Statement_5_5 {n m : ℕ} (S : Subfield K) (F : MvPolynomial (Fin (n + 1)) ↥S)
    (B A : Set (Pt v n m)) (τ : SpecialBijection v B)
    (hB : Definable B) (hA : Definable A) (hτ : SpecialBijection.image v τ = A) : Prop :=
  ∃ T : SpecialBijection v A,
    IsRVPullback v (SpecialBijection.image v T) ∧
      ContractibleVF v A
        (fun x => evalPoly v S F (SpecialBijection.invMap v τ (SpecialBijection.invMap v T x)))

end Frozen

end SpecialTransformations
