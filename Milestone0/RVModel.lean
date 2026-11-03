import Mathlib

/-!
# Semantics of the `RV`-sort of Yin's `L_RV` on a Mathlib valued field

Reference: Yimu Yin, *Special transformations in algebraically closed valued fields*,
APAL 2010, arXiv:1006.2467, Section 2 (Definition 2.1, Definition 2.2, axioms 2, 4, 5, 6).

This file is deliberately *syntax free*: it builds the **intended structure** of the
two-sorted language `L_RV` on a valued field `(K, v)` and proves that it has the
properties the axioms of `ACVF` demand.  Any candidate encoding of `L_RV`
(Mathlib's one-sorted `FirstOrder.Language`, the many-sorted framework, or an in-repo
layer) must interpret the symbols in exactly these functions and relations, so the
lemmas here are a faithfulness test for such an encoding and supply the reference model
for `ACVF` and `ACVF_S(0,0)`.

## The sorts

* `VF` is `K`.
* The `RV`-sort is `RV0 v = Option (RV v)` with `RV v = Option (RVUnit v)` and
  `RVUnit v = Kˣ ⧸ (1 + M)`:
  * `RV0 v`'s `none` is the paper's `0` (the *residue field's* zero),
  * `RV v`'s `none` is the paper's `∞` (the value of `rv 0`),
  * `some (some q)`, `q : Kˣ ⧸ (1+M)`, are the elements of `RV^×`.
  `0` and `∞` are distinct, which is why the nested `Option` of the repo's
  `RV0 = Option (RV v)` is the correct carrier.
* `Γ` is *not* a sort of `L_RV`: it is the quotient `RV / K^×` (axioms 4, 5), realised
  here by `vrv : RV v → Γ₀` into Mathlib's value monoid `Γ₀ = WithZero Γ`.  Its kernel
  is exactly the predicate `K^×` and its range is the range of `v`.

## What is proved

* `rv_mul` : `rv` is multiplicative, `rv 0 = ∞`, `rv` is onto `RV ∖ {∞}` (axiom 6);
* `vrv_rv` : `vv = vrv ∘ rv` (axiom 6), `vrv_mul`, `vrv_range` (`vrv` is onto `Γ`);
* `vrv_kernel` : `vrv t = 1` iff `t` is the image of a unit of the valuation ring, so
  the predicate `K^×` is canonically the residue field's units `k^×`;
* `le_iff`, `le_infty`, `le_class_of_one_iff` : `≤` is a preorder with `∞` on top and
  `K^×` as the class of `1` (axiom 4);
* `valuationSubring_eq`, `maximalIdeal_eq` : the definitions `𝒪 = rv⁻¹(RV^{≥1})` and
  `𝔪 = rv⁻¹(RV^{>1})` of axiom 6 hold;
* `rv_eq_one_iff` : `rv x = 1 ↔ x ∈ 1 + M` (fibres of `rv`);
* `rvUnit_divisible` : `RV^×` is divisible when `K` is algebraically closed (axiom 2).

No `sorry` in this file.
-/

open Valuation

namespace SpecialTransformations

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

section Basics

variable (v : Valuation K Γ₀)

/-- `RV× = Kˣ / (1 + M)`, the multiplicative RV sort. -/
abbrev RVUnit : Type _ := Kˣ ⧸ v.valuationSubring.principalUnitGroup

/-- The RV sort with the point at infinity: `RV = RV× ∪ {∞}`.  `none` is `∞`. -/
abbrev RV : Type _ := Option (RVUnit v)

/-- `RV0 = RV ∪ {0}`.  The outer `none` is the added `0` (zero of the residue field). -/
abbrev RV0 : Type _ := Option (RV v)

/-- The quotient map `rv : K → RV`, with `rv 0 = ∞`. -/
noncomputable def rv (x : K) : RV v := by
  classical
  exact if h : x = 0 then none else some (QuotientGroup.mk' _ (Units.mk0 x h))

/-- The paper's `∞`, i.e. `rv 0`. -/
abbrev rvInfty : RV v := none

/-- The paper's `1`, i.e. `rv 1`, the identity of `RV^×`. -/
noncomputable abbrev rvOne : RV v := rv v 1

variable {v}

@[simp] theorem rv_zero : rv v 0 = (none : RV v) := by
  rw [rv]; exact dif_pos rfl

theorem rv_of_ne {x : K} (h : x ≠ 0) :
    rv v x = some (QuotientGroup.mk' _ (Units.mk0 x h)) := by
  rw [rv]; exact dif_neg h

theorem rv_eq_none_iff {x : K} : rv v x = none ↔ x = 0 := by
  unfold rv
  split_ifs with h
  · simp [h]
  · simp [h]

/-- `rv` is onto `RV ∖ {∞}`: the paper's "`rv : VF^× → RV^×` is surjective". -/
theorem rv_surjective {t : RV v} (h : t ≠ none) : ∃ x : K, x ≠ 0 ∧ rv v x = t := by
  cases t with
  | none => exact absurd rfl h
  | some q =>
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (v.valuationSubring.principalUnitGroup) q
    refine ⟨(u : K), Units.ne_zero u, ?_⟩
    rw [rv_of_ne (Units.ne_zero u)]
    congr 2
    exact Units.ext rfl

/-- Multiplication of the `RV`-sort: the group law on `RV^×`, with `∞` absorbing
(axiom 2 of Definition 2.2: `t × ∞ = ∞`).  On `RV` (i.e. away from the residue-field
zero) this is determined by the axioms. -/
def rvMul : RV v → RV v → RV v
  | none, _ => none
  | some _, none => none
  | some a, some b => some (a * b)

@[simp] theorem rvMul_infty (t : RV v) : rvMul t none = none := by cases t <;> rfl

@[simp] theorem rvMul_infty' (t : RV v) : rvMul none t = none := by cases t <;> rfl

@[simp] theorem rvMul_some_some (a b : RVUnit v) : rvMul (some a) (some b) = some (a * b) :=
  rfl

/-- The paper's `1` in the `RV`-sort is the identity of `RV^× = Kˣ/(1+M)`. -/
theorem rvOne_eq : rvOne v = some (1 : RVUnit v) := by
  rw [rvOne, rv_of_ne one_ne_zero]
  congr 1
  rw [show Units.mk0 (1 : K) one_ne_zero = (1 : Kˣ) from Units.ext rfl, map_one]

theorem rvMul_comm (t s : RV v) : rvMul t s = rvMul s t := by
  cases t with
  | none => cases s <;> simp
  | some a =>
    cases s with
    | none => simp
    | some b =>
      induction a using Quotient.inductionOn with
      | _ x =>
        induction b using Quotient.inductionOn with
        | _ y =>
          simp only [rvMul_some_some, ← QuotientGroup.mk_mul, mul_comm]

theorem rvMul_assoc (t s r : RV v) : rvMul (rvMul t s) r = rvMul t (rvMul s r) := by
  cases t with
  | none => simp
  | some a =>
    cases s with
    | none => simp
    | some b =>
      cases r with
      | none => simp
      | some c =>
        induction a using Quotient.inductionOn with
        | _ x =>
          induction b using Quotient.inductionOn with
          | _ y =>
            induction c using Quotient.inductionOn with
            | _ z =>
              simp only [rvMul_some_some, ← QuotientGroup.mk_mul, mul_assoc]

/-- `1` is the identity of `RV^×` and `∞ × 1 = ∞`. -/
theorem rvMul_one (t : RV v) : rvMul t (rvOne v) = t := by
  cases t with
  | none => simp
  | some a =>
    rw [rvOne_eq, rvMul_some_some]
    exact congrArg some (mul_one a)

/-- `rv` is multiplicative (axiom 6 of Definition 2.2). -/
theorem rv_mul (x y : K) : rv v (x * y) = rvMul (rv v x) (rv v y) := by
  by_cases hx : x = 0
  · subst hx; simp [rv_zero]
  by_cases hy : y = 0
  · subst hy; simp [rv_zero]
  rw [rv_of_ne hx, rv_of_ne hy, rv_of_ne (mul_ne_zero hx hy), rvMul_some_some,
    show Units.mk0 (x * y) (mul_ne_zero hx hy) = Units.mk0 x hx * Units.mk0 y hy from
      Units.ext rfl,
    map_mul]

/-- The fibre of `rv` over `1` is `1 + M`, i.e. the principal units. -/
theorem rv_eq_one_iff (u : Kˣ) :
    rv v (u : K) = rvOne v ↔ u ∈ v.valuationSubring.principalUnitGroup := by
  rw [rv_of_ne (Units.ne_zero u), rvOne, rv_of_ne one_ne_zero,
    show Units.mk0 ((u : K)) (Units.ne_zero u) = u from Units.ext rfl,
    show Units.mk0 (1 : K) one_ne_zero = (1 : Kˣ) from Units.ext rfl,
    map_one, Option.some_inj, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

end Basics

section Vrv

variable (v : Valuation K Γ₀)

/-- The valuation, viewed as a monoid homomorphism on the units of `K`. -/
noncomputable def vUnits : Kˣ →* Γ₀ˣ where
  toFun u := Units.mk0 (v (u : K)) (by
    rw [Valuation.ne_zero_iff]
    exact Units.ne_zero u)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [Valuation.map_mul]

@[simp] theorem vUnits_apply (u : Kˣ) : ((vUnits v u : Γ₀ˣ) : Γ₀) = v (u : K) := rfl

theorem vUnits_ker : v.valuationSubring.principalUnitGroup ≤ (vUnits v).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, Units.ext_iff, vUnits_apply]
  exact (Valuation.mem_unitGroup_iff K v x).1 (v.valuationSubring.principal_units_le_units hx)

/-- The map `RV^× → Γ` induced by the valuation, i.e. the paper's `vrv` restricted to
the group part of the `RV`-sort.  Well defined because `v` is trivial on `1 + M`. -/
noncomputable def vrvUnit : RVUnit v →* Γ₀ˣ :=
  QuotientGroup.lift _ (vUnits v) (vUnits_ker v)

@[simp] theorem vrvUnit_mk (u : Kˣ) :
    vrvUnit v (QuotientGroup.mk' _ u) = vUnits v u := rfl

/-- The paper's `vrv : RV → Γ ∪ {∞}`: the map induced by the valuation on `RV^×`,
extended by `vrv ∞ = 0`.  (Mathlib's `Γ₀ = WithZero Γ` is ordered so that `0` is the
bottom; the paper's order on `Γ ∪ {∞}` is the reverse, cf. `le_iff`.) -/
noncomputable def vrv : RV v → Γ₀
  | none => 0
  | some q => (vrvUnit v q : Γ₀)

@[simp] theorem vrv_none : vrv v (none : RV v) = 0 := rfl

@[simp] theorem vrv_some (q : RVUnit v) : vrv v (some q) = (vrvUnit v q : Γ₀) := rfl

theorem vrv_mk (u : Kˣ) : vrv v (some (QuotientGroup.mk' _ u)) = v (u : K) := rfl

/-- `vv = vrv ∘ rv` (axiom 6): the projection commutes with the valuation. -/
theorem vrv_rv (x : K) : vrv v (rv v x) = v x := by
  by_cases h : x = 0
  · subst h; simp [rv_zero]
  · rw [rv_of_ne h, vrv_mk]
    rfl

/-- `vrv` is multiplicative. -/
theorem vrv_mul (t s : RV v) : vrv v (rvMul t s) = vrv v t * vrv v s := by
  cases t with
  | none => simp
  | some a =>
    cases s with
    | none => simp
    | some b => simp

/-- `vrv` and `v` have the same range: `vrv` maps `RV` *onto* the value group. -/
theorem vrv_range (γ : Γ₀) :
    (∃ t : RV v, vrv v t = γ) ↔ (∃ x : K, v x = γ) := by
  constructor
  · rintro ⟨t, rfl⟩
    cases t with
    | none => exact ⟨0, by simp⟩
    | some q =>
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (v.valuationSubring.principalUnitGroup) q
      exact ⟨(u : K), by rw [← vrv_mk]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨rv v x, vrv_rv v x⟩

/-- The kernel of `vrv` is the predicate `K^×` of Definition 2.1: the equivalence class
of `1`, i.e. the image of the units of the valuation ring
(`(𝒪 ∖ 𝔪)/(1+𝔪) ≅ k^×`). -/
theorem vrv_kernel (t : RV v) :
    vrv v t = 1 ↔ ∃ u : v.valuationSubring.unitGroup,
      some (QuotientGroup.mk' _ (u : Kˣ)) = t := by
  constructor
  · intro ht
    cases t with
    | none => simp at ht
    | some q =>
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (v.valuationSubring.principalUnitGroup) q
      refine ⟨⟨u, ?_⟩, rfl⟩
      have h := ht
      rw [vrv_mk] at h
      exact (Valuation.mem_unitGroup_iff K v u).2 h
  · rintro ⟨u, rfl⟩
    rw [vrv_mk]
    exact (Valuation.mem_unitGroup_iff K v (u : Kˣ)).1 u.2

end Vrv

section Order

variable (v : Valuation K Γ₀)

/-- The paper's preorder on `RV`: `t ≤ s` iff `vrv t ≥ vrv s` in the value monoid
ordered so that `𝒪 = {x : v x ≤ 1}`.  Then `∞` is the top element and the
equivalence class of `1` is `K^×` (axiom 4 of Definition 2.2). -/
def rvLe (t s : RV v) : Prop := vrv v s ≤ vrv v t

instance : Preorder (RV v) where
  le := rvLe v
  lt t s := rvLe v t s ∧ ¬ rvLe v s t
  le_refl := fun _ => le_rfl
  le_trans _ _ _ h₁ h₂ := le_trans h₂ h₁
  lt_iff_le_not_ge _ _ := Iff.rfl

theorem le_iff {t s : RV v} : t ≤ s ↔ vrv v s ≤ vrv v t := Iff.rfl

theorem lt_iff {t s : RV v} : t < s ↔ vrv v s < vrv v t := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge]
  exact Iff.rfl

/-- `∞` is the top element. -/
theorem le_infty (t : RV v) : t ≤ (none : RV v) := by
  rw [le_iff]; simp

/-- The equivalence class of `1` is `K^×` (axiom 4). -/
theorem le_class_of_one_iff {t : RV v} : (rvOne v ≤ t ∧ t ≤ rvOne v) ↔ vrv v t = 1 := by
  rw [le_iff, le_iff, show vrv v (rvOne v) = 1 from by rw [rvOne, vrv_rv, Valuation.map_one]]
  exact ⟨fun ⟨h1, h2⟩ => le_antisymm h1 h2, fun h => ⟨le_of_eq h, le_of_eq h.symm⟩⟩

/-- Axiom 6, first half: `𝒪 = rv⁻¹(RV^{≥1})` where `RV^{≥1} = {x : 1 ≤ x}`. -/
theorem valuationSubring_eq (x : K) :
    x ∈ v.valuationSubring ↔ rvOne v ≤ rv v x := by
  rw [le_iff, vrv_rv, rvOne, vrv_rv, Valuation.map_one, Valuation.mem_valuationSubring_iff]

/-- Axiom 6, second half: `𝔪 = rv⁻¹(RV^{>1})` where `RV^{>1} = {x : 1 < x}`. -/
theorem maximalIdeal_eq (x : K) : v x < 1 ↔ rvOne v < rv v x := by
  rw [lt_iff, vrv_rv, rvOne, vrv_rv, Valuation.map_one]

/-- `RV^×` is divisible when `K` is algebraically closed (axiom 2 of Definition 2.2). -/
theorem rvUnit_divisible [IsAlgClosed K] (n : ℕ) (hn : n ≠ 0) (t : RVUnit v) :
    ∃ s : RVUnit v, s ^ n = t := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (v.valuationSubring.principalUnitGroup) t
  have hu : (u : K) ≠ 0 := Units.ne_zero u
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (u : K) (n := n) (Nat.pos_of_ne_zero hn)
  have hw0 : w ≠ 0 := by rintro rfl; rw [zero_pow hn] at hw; exact hu hw.symm
  have hpow : (Units.mk0 w hw0 : Kˣ) ^ n = u := by
    ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, hw]
  refine ⟨QuotientGroup.mk' _ (Units.mk0 w hw0), ?_⟩
  rw [← map_pow, hpow]

end Order



/-! ### The theory `ACVF` instantiated at the intended model

The definitions of `LRVSig` and of the RV-layer `RVGroupAxioms` of Definition 2.2 are
repeated here (each file of this submission is self-contained); `LRVSorts.lean` has the
full theory `IsACVF` and the target statements.  Below, `intendedSig v` is the `L_RV`
structure of a valued field and `rvGroupAxioms_intended` proves the axioms of
`RVGroupAxioms` for it.  This is the check that catches mis-statements: e.g. `rv_surj` has
to be guarded by `IsRVUnit`, because the carrier `RV0 v` contains the residue-field zero,
which is not in the image of `rv`.
-/

section Theory

variable (v : Valuation K Γ₀)

/-- The symbols of `L_RV` on two carriers (Definition 2.1); same as in `LRVSorts.lean`. -/
structure LRVSig (VF : Type*) where
  RV : Type*
  vfZero : VF
  vfOne : VF
  vfAdd : VF → VF → VF
  vfNeg : VF → VF
  vfMul : VF → VF → VF
  rvOne : RV
  rvMul : RV → RV → RV
  rvZero : RV
  Kx : Set RV
  rvAddK : RV → RV → RV
  rvNegK : RV → RV
  rvLe : RV → RV → Prop
  rvMap : VF → RV

namespace LRVSig

variable {VF : Type*} (M : LRVSig VF)

/-- `K = K^× ∪ {0}`, the residue field inside the `RV`-sort. -/
def Kset : Set M.RV := M.Kx ∪ {M.rvZero}

/-- `RV^× = RV ∖ {0}`: the absorbing element `rv 0` is the only non-group element. -/
def IsRVUnit (t : M.RV) : Prop := t ≠ M.rvZero

/-- Powers in the `RV`-sort. -/
def rvPow : M.RV → ℕ → M.RV
  | _, 0 => M.rvOne
  | t, (n + 1) => M.rvMul (rvPow t n) t

end LRVSig

/-- The RV-layer of the axioms of `ACVF` (Definition 2.2 (2), the order axioms of (4), and
the `rv`-part of (6)); same as in `LRVSorts.lean`. -/
structure RVGroupAxioms {VF : Type*} [Field VF] (M : LRVSig VF) : Prop where
  rvOne_unit : M.IsRVUnit M.rvOne
  rv_mul_comm : ∀ {t s : M.RV}, M.IsRVUnit t → M.IsRVUnit s → M.rvMul t s = M.rvMul s t
  rv_mul_assoc : ∀ {t s r : M.RV}, M.IsRVUnit t → M.IsRVUnit s → M.IsRVUnit r →
    M.rvMul (M.rvMul t s) r = M.rvMul t (M.rvMul s r)
  rv_mul_one : ∀ {t : M.RV}, M.IsRVUnit t → M.rvMul t M.rvOne = t
  rv_mul_inv : ∀ {t : M.RV}, M.IsRVUnit t → ∃ s : M.RV, M.IsRVUnit s ∧ M.rvMul t s = M.rvOne
  rv_divisible : ∀ (n : ℕ), n ≠ 0 → ∀ {t : M.RV}, M.IsRVUnit t →
    ∃ s : M.RV, M.IsRVUnit s ∧ M.rvPow s n = t
  /-- `t × 0 = 0` for `t ∈ K = K^× ∪ {0}`, split into the two cases. -/
  rv_mul_zero_Kx : ∀ {t : M.RV}, t ∈ M.Kx → M.rvMul t M.rvZero = M.rvZero
  rv_mul_zero_zero : M.rvMul M.rvZero M.rvZero = M.rvZero
  /-- `t × 0 = 0` for all `t` (the paper's `t × ∞ = ∞`; `∞ = rv 0 = 0`). -/
  rv_mul_infty : ∀ t : M.RV, M.rvMul t M.rvZero = M.rvZero
  le_refl : ∀ t : M.RV, M.rvLe t t
  le_trans : ∀ {t s r : M.RV}, M.rvLe t s → M.rvLe s r → M.rvLe t r
  le_total : ∀ t s : M.RV, M.rvLe t s ∨ M.rvLe s t
  le_infty : ∀ t : M.RV, M.rvLe t M.rvZero
  rv_zero : M.rvMap 0 = M.rvZero
  rv_mul : ∀ x y : VF, M.rvMap (x * y) = M.rvMul (M.rvMap x) (M.rvMap y)
  /-- `rv` is surjective onto everything but `rv 0` (Definition 2.2(6)). -/
  rv_surj : ∀ {t : M.RV}, M.IsRVUnit t → ∃ x : VF, x ≠ 0 ∧ M.rvMap x = t

/-- An admissible reading of the paper's multiplication on `RV_0 = RV ∪ {0}`: the group law
on `RV^×`, `∞` absorbing, `0` absorbing on `K`.  (The axioms do not determine `t × 0` for
`t ∈ RV^× ∖ K^×`, so this is one faithful choice.) -/
def rv0Mul : RV0 v → RV0 v → RV0 v
  | some none, _ => some none
  | _, some none => some none
  | none, _ => none
  | some (some _), none => none
  | some (some a), some (some b) => some (some (a * b))

/-- The paper's `≤` on the whole sort `RV_0`: the residue-field zero is the bottom, `∞` the
top, and on `RV` it is the order induced by `vrv` (`le_iff`). -/
def le0 : RV0 v → RV0 v → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => rvLe v a b

/-- `K^×` as a subset of the whole sort `RV_0`: the class of `1`, i.e. the residue field's
units (axiom 4). -/
def Kx0 : Set (RV0 v) := {t | ∃ q : RVUnit v, t = some (some q) ∧ vrv v (some q) = 1}

/-- The intended `L_RV`-structure of a valued field `(K, v)`.  `rvAddK`/`rvNegK` are
junk-valued totalisations of the paper's partial `+`/`-` on `K ⊂ RV`; the field structure
on `K` (the residue field) is not constructed in this file, so the axioms of `ACVF` that
mention them are not claimed here. -/
noncomputable def intendedSig : LRVSig K where
  RV := RV v
  vfZero := 0
  vfOne := 1
  vfAdd := fun x y => x + y
  vfNeg := fun x => -x
  vfMul := fun x y => x * y
  rvOne := rvOne v
  rvMul := rvMul
  rvZero := none
  Kx := {t | ∃ q : RVUnit v, t = some q ∧ vrv v (some q) = 1}
  rvAddK := fun _ _ => none
  rvNegK := fun _ => none
  rvLe := fun t s => vrv v s ≤ vrv v t
  rvMap := rv v

@[simp] theorem rv0Mul_infty (t : RV0 v) : rv0Mul v t (some none) = some none := by
  match t with
  | none => rfl
  | some t => cases t <;> rfl

theorem rv0Mul_some_rv (x y : K) :
    rv0Mul v (some (rv v x)) (some (rv v y)) = some (rv v (x * y)) := by
  rw [rv_mul x y]
  match hx : rv v x, hy : rv v y with
  | none, _ => rfl
  | some _, none => rfl
  | some a, some b => rfl

/-- `b : RV` is not `∞`. -/
theorem rv_shape {b : RV v} (hb : b ≠ none) : ∃ c : RVUnit v, b = some c := by
  match b, hb with
  | none, h => exact absurd rfl h
  | some c, _ => exact ⟨c, rfl⟩

/-- `t : RV_0` has the shape of a group element. -/
theorem rv0_shape {t : RV v} (ht : (intendedSig (v := v)).IsRVUnit t) :
    ∃ q : RVUnit v, t = some q :=
  rv_shape (v := v) ht

/-- The group law of `RV^×` at the level of `RVUnit`. -/
theorem rvUnit_mul_comm (a b : RVUnit v) : a * b = b * a := mul_comm a b

theorem rvUnit_mul_assoc (a b c : RVUnit v) : a * b * c = a * (b * c) := mul_assoc a b c

theorem rvUnit_mul_one (a : RVUnit v) : a * 1 = a := mul_one a

theorem rvUnit_inv (a : RVUnit v) : ∃ c : RVUnit v, a * c = 1 := ⟨a⁻¹, mul_inv_cancel a⟩

theorem rv0Mul_some_some (a b : RVUnit v) :
    rv0Mul v (some (some a)) (some (some b)) = some (some (a * b)) := rfl

theorem le0_refl (t : RV0 v) : le0 v t t := by
  match t with
  | none => trivial
  | some none => exact le_infty v none
  | some (some q) => exact le_rfl

theorem le0_total (t s : RV0 v) : le0 v t s ∨ le0 v s t := by
  match t, s with
  | none, _ => exact Or.inl trivial
  | some _, none => exact Or.inr trivial
  | some a, some b =>
    rcases le_total (vrv v a) (vrv v b) with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem le0_trans {t s r : RV0 v} (h1 : le0 v t s) (h2 : le0 v s r) : le0 v t r := by
  match t, s, r with
  | none, _, _ => trivial
  | some _, none, _ => exact absurd h1 (by simp [le0])
  | some _, some _, none => exact absurd h2 (by simp [le0])
  | some a, some b, some c =>
    exact le_trans (show vrv v c ≤ vrv v b from h2) (show vrv v b ≤ vrv v a from h1)

theorem le0_infty (t : RV0 v) : le0 v t (some none) := by
  match t with
  | none => trivial
  | some none => exact le_infty v none
  | some (some q) => exact le_infty v (some q)

theorem rvPow_intended (q : RVUnit v) : ∀ n : ℕ,
    LRVSig.rvPow (intendedSig (v := v)) (some q) n = some (q ^ n)
  | 0 => by
    rw [show LRVSig.rvPow (intendedSig (v := v)) (some q) 0 = rvOne v from rfl,
      rvOne_eq, pow_zero]
  | n + 1 => by
    rw [show LRVSig.rvPow (intendedSig (v := v)) (some q) (n + 1)
          = rvMul (LRVSig.rvPow (intendedSig (v := v)) (some q) n) (some q) from rfl,
      rvPow_intended q n, pow_succ]
    rfl

/-- **The theory's own axiom layer holds at the intended structure**: `RVGroupAxioms`
(Definition 2.2 (2), the order axioms of (4) and the `rv`-part of (6)) is proved for
`intendedSig v`.  `rv_surj` is asserted only for `t ∈ RV^×`: the residue zero is outside
the image of `rv`, so the unguarded form would be false on this carrier. -/
theorem rvGroupAxioms_intended [IsAlgClosed K] :
    RVGroupAxioms (intendedSig (v := v)) where
  rvOne_unit := by
    show rvOne v ≠ (none : RV v)
    rw [rvOne_eq]; simp
  rv_mul_comm := by
    intro t s ht hs
    obtain ⟨a, rfl⟩ := rv0_shape v ht
    obtain ⟨b, rfl⟩ := rv0_shape v hs
    show rvMul (some a) (some b) = rvMul (some b) (some a)
    rw [rvMul_some_some, rvMul_some_some, rvUnit_mul_comm]
  rv_mul_assoc := by
    intro t s r ht hs hr
    obtain ⟨a, rfl⟩ := rv0_shape v ht
    obtain ⟨b, rfl⟩ := rv0_shape v hs
    obtain ⟨c, rfl⟩ := rv0_shape v hr
    show rvMul (rvMul (some a) (some b)) (some c) = rvMul (some a) (rvMul (some b) (some c))
    simp only [rvMul_some_some, rvUnit_mul_assoc]
  rv_mul_one := by
    intro t ht
    obtain ⟨a, rfl⟩ := rv0_shape v ht
    show rvMul (some a) (rvOne v) = some a
    rw [rvOne_eq, rvMul_some_some, rvUnit_mul_one]
  rv_mul_inv := by
    intro t ht
    obtain ⟨a, rfl⟩ := rv0_shape v ht
    obtain ⟨c, hc⟩ := rvUnit_inv v a
    refine ⟨some c, ?_, ?_⟩
    · show (some c : RV v) ≠ none
      simp
    · show rvMul (some a) (some c) = rvOne v
      rw [rvMul_some_some, rvOne_eq, hc]
  rv_divisible := by
    intro n hn t ht
    obtain ⟨q, rfl⟩ := rv0_shape v ht
    obtain ⟨s, hs⟩ := rvUnit_divisible v n hn q
    refine ⟨some s, ?_, ?_⟩
    · show (some s : RV v) ≠ none
      simp
    · show LRVSig.rvPow (intendedSig (v := v)) (some s) n = some q
      rw [rvPow_intended, hs]
  rv_mul_zero_Kx := by
    intro t ht
    obtain ⟨q, rfl, -⟩ := ht
    rfl
  rv_mul_zero_zero := rfl
  rv_mul_infty := fun t => rvMul_infty t
  le_refl := fun t => le_rfl
  le_trans := fun h1 h2 => le_trans h2 h1
  le_total := fun t s => le_total (vrv v s) (vrv v t)
  le_infty := fun t => le_infty v t
  rv_zero := rv_zero
  rv_mul := fun x y => rv_mul x y
  rv_surj := by
    intro t ht
    exact rv_surjective (v := v) (t := t) ht

end Theory

end SpecialTransformations
