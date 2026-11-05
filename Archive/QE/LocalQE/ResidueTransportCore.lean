import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
Minimal support for ResidueTranscendentalTransport.
Extracted from QE/UnitTranscend.lean (namespace M7 through ResidueTranscendental)
and QE/RV_henselian.lean (namespace RVCalc through rv_mul), at fa3867c.
Definitions and proofs are verbatim; only imports, the unused Polynomial open,
and closing namespace/section commands differ.  Production sources are untouched.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace M7



variable {L : Type*} [Field L] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-! ## 1. Residues of integral elements -/

/-- The residue of an element `x` of the valuation ring of `v`. -/
noncomputable def vres (v : Valuation L Γ) (x : L) (hx : v x ≤ 1) :
    IsLocalRing.ResidueField v.valuationSubring :=
  IsLocalRing.residue v.valuationSubring
    ⟨x, (Valuation.mem_valuationSubring_iff v x).mpr hx⟩

/-- `vres` does not depend on the integrality proof. -/
lemma vres_proof_irrel (v : Valuation L Γ) (x : L) (h₁ h₂ : v x ≤ 1) :
    vres v x h₁ = vres v x h₂ :=
  rfl

/-- A residue vanishes exactly on the maximal ideal, i.e. on elements of value `< 1`. -/
lemma vres_eq_zero_iff (v : Valuation L Γ) (x : L) (hx : v x ≤ 1) :
    vres v x hx = 0 ↔ v x < 1 := by
  simp only [vres]
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]

/-- Residues are multiplicative. -/
lemma vres_mul (v : Valuation L Γ) {x y : L} (hx : v x ≤ 1) (hy : v y ≤ 1)
    (hxy : v (x * y) ≤ 1) :
    vres v (x * y) hxy = vres v x hx * vres v y hy := by
  have key : (⟨x * y, (Valuation.mem_valuationSubring_iff v (x * y)).mpr hxy⟩ :
        v.valuationSubring)
      = ⟨x, (Valuation.mem_valuationSubring_iff v x).mpr hx⟩ *
        ⟨y, (Valuation.mem_valuationSubring_iff v y).mpr hy⟩ := Subtype.ext rfl
  simp only [vres]
  rw [key, map_mul]

/-- Residues of finite sums of integral elements. -/
lemma vres_sum {ι : Type*} [Fintype ι] (v : Valuation L Γ) {f : ι → L}
    (hf : ∀ i, v (f i) ≤ 1) (h : v (∑ i, f i) ≤ 1) :
    vres v (∑ i, f i) h = ∑ i, vres v (f i) (hf i) := by
  have key : (⟨∑ i, f i, (Valuation.mem_valuationSubring_iff v (∑ i, f i)).mpr h⟩ :
        v.valuationSubring)
      = ∑ i, (⟨f i, (Valuation.mem_valuationSubring_iff v (f i)).mpr (hf i)⟩ :
          v.valuationSubring) := by
    refine Subtype.ext ?_
    simp
  have hh := congrArg (IsLocalRing.residue v.valuationSubring) key
  simpa only [map_sum, vres] using hh

/-- Ultrametric bound for a sum of integral elements. -/
lemma val_sum_le_one {ι : Type*} (v : Valuation L Γ) (s : Finset ι) {f : ι → L}
    (hf : ∀ i ∈ s, v (f i) ≤ 1) : v (∑ i ∈ s, f i) ≤ 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine le_trans (v.map_add _ _) (max_le (hf a (Finset.mem_insert_self a s)) ?_)
      exact ih fun i hi => hf i (Finset.mem_insert_of_mem hi)

lemma val_sum_le_one' {ι : Type*} [Fintype ι] (v : Valuation L Γ) {f : ι → L}
    (hf : ∀ i, v (f i) ≤ 1) : v (∑ i, f i) ≤ 1 :=
  val_sum_le_one v Finset.univ fun i _ => hf i

/-- `v (x ^ n) ≤ 1` for integral `x`. -/
lemma val_pow_le_one (v : Valuation L Γ) {x : L} (hx : v x ≤ 1) (n : ℕ) :
    v (x ^ n) ≤ 1 := by
  rw [map_pow]
  exact pow_le_one₀ zero_le hx

/-- Residues of powers. -/
lemma vres_one (v : Valuation L Γ) (h : v (1 : L) ≤ 1) : vres v 1 h = 1 := by
  have key : (⟨1, (Valuation.mem_valuationSubring_iff v (1:L)).mpr h⟩ : v.valuationSubring)
      = 1 := Subtype.ext rfl
  simp only [vres]
  rw [key, map_one]

lemma vres_pow (v : Valuation L Γ) {x : L} (hx : v x ≤ 1) (n : ℕ)
    (h : v (x ^ n) ≤ 1) : vres v (x ^ n) h = vres v x hx ^ n := by
  have key : (⟨x ^ n, (Valuation.mem_valuationSubring_iff v (x ^ n)).mpr h⟩ : v.valuationSubring)
      = ⟨x, (Valuation.mem_valuationSubring_iff v x).mpr hx⟩ ^ n := Subtype.ext (by simp)
  simp only [vres]
  rw [key, map_pow]

/-! ## 2. The min formula: no cancellation for a unit with transcendental residue

All families below are indexed by `Fin n`, matching the paper's expansions
`b = Σ_{0 ≤ i ≤ m} bᵢ eⁱ` (`Fin (m+1)`). -/

/-- **The elementary core of Lemma 3.6's value computation.**

`e` is a unit (`v e = 1`) and `rv(e)` is transcendental over the base residue field — the latter is
hypothesis `hT`, in the form the reduction uses: a vanishing residue polynomial in the residue of
`e` has all its coefficient residues zero.

Then an expansion whose coefficients are integral and at least one of which has value exactly `1`
has value exactly `1`: there is no cancellation across the terms.  This is the statement the paper
obtains from the dimension inequality (via `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`, `qe.tex:741-747`). -/
theorem val_sum_eq_one {n : ℕ} (v : Valuation L Γ) {e : L} (he : v e = 1)
    {c : Fin n → L} {m : Fin n → ℕ} (hle : ∀ i, v (c i) ≤ 1) (hsome : ∃ i, v (c i) = 1)
    (hT : (∑ i, vres v (c i) (hle i) * (vres v e (le_of_eq he)) ^ (m i)) = 0 →
      ∀ i, vres v (c i) (hle i) = 0) :
    v (∑ i, c i * e ^ m i) = 1 := by
  classical
  have hterm : ∀ i, v (c i * e ^ m i) ≤ 1 := fun i => by
    have h1 : v (c i * e ^ m i) = v (c i) := by
      simp only [map_mul, map_pow, he, mul_one, one_pow]
    rw [h1]; exact hle i
  have hsum : v (∑ i, c i * e ^ m i) ≤ 1 := val_sum_le_one' v hterm
  refine le_antisymm hsum ?_
  by_contra hcon
  push Not at hcon
  have hz : vres v (∑ i, c i * e ^ m i) hsum = 0 := (vres_eq_zero_iff v _ hsum).mpr hcon
  have hsplit : vres v (∑ i, c i * e ^ m i) hsum
      = ∑ i, vres v (c i) (hle i) * (vres v e (le_of_eq he)) ^ (m i) := by
    rw [vres_sum v hterm hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [vres_mul (v := v) (x := c i) (y := e ^ m i) (hle i)
      (val_pow_le_one v (le_of_eq he) (m i)) (hterm i)]
    rw [vres_pow v (le_of_eq he) (m i) (val_pow_le_one v (le_of_eq he) (m i))]
  rw [hsplit] at hz
  obtain ⟨i₀, hi₀⟩ := hsome
  have hzero := hT hz i₀
  rw [vres_eq_zero_iff] at hzero
  rw [hi₀] at hzero
  exact lt_irrefl 1 hzero

/-! ## 3. Value normalization for expansions and their quotients -/

/-- The hypothesis of §2 in base-relative form: `rv(e)` is transcendental over the image of the
base field `K` in the residue field, stated as "no residue polynomial with coefficients the
residues of integral base elements vanishes at `rv(e)`". -/
def ResidueTranscendental (v : Valuation L Γ) (K : Subfield L) {e : L} (he : v e = 1) : Prop :=
  ∀ (n : ℕ) (d : Fin n → K) (m : Fin n → ℕ), Function.Injective m →
    (hd : ∀ i, v (d i : L) ≤ 1) →
    (∑ i, vres v (d i : L) (hd i) * (vres v e (le_of_eq he)) ^ (m i)) = 0 →
      ∀ i, vres v (d i : L) (hd i) = 0


end M7

namespace RVCalc

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

section LeadingTerm

variable (v : Valuation K Γ₀)

/-- `1 + 𝔪`, the group of principal units of the valuation ring of `v`. -/
def principalUnits : Subgroup Kˣ where
  carrier := {u | v ((u : K) - 1) < 1}
  mul_mem' := by
    intro a b ha hb
    have hb1 : v ((b : K)) = 1 := by
      have h : (b : K) = (b - 1) + 1 := by ring
      rw [h, Valuation.map_add_eq_of_lt_right v (by simpa using hb), Valuation.map_one]
    have hkey : ((a : K) * (b : K) - 1) = ((a : K) - 1) * (b : K) + ((b : K) - 1) := by
      ring
    show v (((a : K) * (b : K)) - 1) < 1
    rw [hkey]
    refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ hb)
    rw [map_mul, hb1, mul_one]
    exact ha
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    have ha1 : v ((a : K)) = 1 := by
      have h : (a : K) = (a - 1) + 1 := by ring
      rw [h, Valuation.map_add_eq_of_lt_right v (by simpa using ha), Valuation.map_one]
    have hsub : (((a⁻¹ : Kˣ) : K)) - 1 = -((a : K) - 1) / (a : K) := by
      simp only [Units.val_inv_eq_inv_val]
      field_simp
      ring
    show v ((((a⁻¹ : Kˣ) : K)) - 1) < 1
    rw [hsub, Valuation.map_div v, Valuation.map_neg v, ha1, div_one]
    exact ha

@[simp] theorem mem_principalUnits {u : Kˣ} :
    u ∈ principalUnits v ↔ v ((u : K) - 1) < 1 := Iff.rfl

/-- `RV× = Kˣ/(1+𝔪)`, the multiplicative part of the `RV` sort. -/
abbrev RVUnit : Type _ := Kˣ ⧸ principalUnits v

/-- The `RV` sort `RV× ∪ {∞}`; `none` is `∞ = rv 0`. -/
abbrev RV : Type _ := Option (RVUnit v)

/-- The quotient map `rv : K → RV`, with `rv 0 = ∞`. -/
noncomputable def rv (x : K) : RV v := by
  classical
  exact if h : x = 0 then none else some (QuotientGroup.mk' (principalUnits v) (Units.mk0 x h))

variable {v}

@[simp] theorem rv_zero : rv v 0 = none := by
  rw [rv]; exact dif_pos rfl

theorem rv_of_ne {x : K} (h : x ≠ 0) :
    rv v x = some (QuotientGroup.mk' (principalUnits v) (Units.mk0 x h)) := by
  rw [rv]; exact dif_neg h

theorem rv_eq_none_iff {x : K} : rv v x = none ↔ x = 0 := by
  rw [rv]
  split_ifs with h
  · simp [h]
  · simp [h]

theorem rv_ne_none {x : K} (h : x ≠ 0) : rv v x ≠ none := fun hc => h (rv_eq_none_iff.1 hc)


/-- `rv` is surjective onto `RV×`: every leading term has a field representative. -/
theorem rv_surjective (v : Valuation K Γ₀) (t : RVUnit v) :
    ∃ x : K, x ≠ 0 ∧ rv v x = some t := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (principalUnits v) t
  refine ⟨(u : K), Units.ne_zero u, ?_⟩
  rw [rv_of_ne (v := v) (Units.ne_zero u),
    show Units.mk0 (u : K) (Units.ne_zero u) = u from Units.ext rfl]


/-- `rv` is a group homomorphism on units: `rv (x⁻¹) = (rv x)⁻¹`. -/
theorem rv_inv {x : K} (hx : x ≠ 0) :
    rv v x⁻¹ = some (QuotientGroup.mk' (principalUnits v) (Units.mk0 x hx))⁻¹ := by
  have hunit : Units.mk0 x⁻¹ (inv_ne_zero hx) = (Units.mk0 x hx)⁻¹ := by
    ext
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0]
  rw [rv_of_ne (inv_ne_zero hx), hunit, map_inv]

/-- Multiplication of the `RV` sort, with `∞` absorbing. -/
def rvMul (v : Valuation K Γ₀) : RV v → RV v → RV v
  | none, _ => none
  | some _, none => none
  | some a, some b => some (a * b)

@[simp] theorem rvMul_none_left (t : RV v) : rvMul v none t = none := by cases t <;> rfl

@[simp] theorem rvMul_none_right (t : RV v) : rvMul v t none = none := by cases t <;> rfl

@[simp] theorem rvMul_some (a b : RVUnit v) : rvMul v (some a) (some b) = some (a * b) := rfl

/-- `rv` is multiplicative. -/
theorem rv_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    rv v (x * y) = rvMul v (rv v x) (rv v y) := by
  rw [rv_of_ne (mul_ne_zero hx hy), rv_of_ne hx, rv_of_ne hy, rvMul_some, ← map_mul]
  congr 2
  ext
  rfl


end LeadingTerm
end RVCalc

