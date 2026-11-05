/-
# M7 / d6: Lemma 3.6's `Γ`-step needs no dimension inequality

Yin, *Special transformations in ACVF*, Lemma 3.6 (`lift:transcendental`, `qe.tex:732`) proves
Claim (⋆) for `e ∈ U(M)` with `rv(e)` transcendental over `K(Ŝ)`, and its proof routes the value
computation through the **dimension inequality** of valuation theory (Engler–Prestel Thm 3.4.3):

  rational rank of `Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` is 0, `Γ(Ŝ)` divisible  ⇒  `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`.

This file proves that the quotation is **not needed** for that lemma.  Under the paper's own
hypotheses the value computation is elementary: `e` is a *unit* (`v e = 1`), so every term of an
expansion `Σ bᵢeⁱ` is integral; reducing mod the maximal ideal turns the sum into a polynomial in
the residue of `e` over the residue field of the base, and *transcendentality of that residue*
forbids cancellation.  Hence

  `v (Σᵢ cᵢ e^{mᵢ}) = minᵢ v (cᵢ)`  (`val_sum_eq_one` below, in normalized form),

so the value of every expansion is the value of a base element (`exists_scalar_val`), and every
quotient of expansions — i.e. every element of `VF(Ŝ)(e)`, which is `VF(⟨Ŝ,e⟩)` by the
fraction-field step the paper uses in Lemma 3.5 — has value normalization
`∃ a, v (b / a) = 1` (`exists_scalar_div_of_quot`).  Those are exactly the two facts the paper
extracts from the dimension inequality at `qe.tex:741-747`.

Consequence for the frozen theorem: **EP 3.4.3 is removable from Lemma 3.6's hypothesis list**;
what remains is (a) `e` a unit, (b) `rv(e)` transcendental over the base residue field,
(c) the fraction-field representation of `VF(⟨Ŝ,e⟩)` (the tree's `VFInvClosedOn`/`IsVFGen`
residual, needed by Lemma 3.5 as well).  Note in particular that *divisibility of `Γ(Ŝ)` is not
used at all* here: the paper's own hypothesis `Γ(Ŝ)` divisible is redundant for Lemma 3.6.

The sharpness file `Sharpness.lean` shows the unit hypothesis cannot be dropped: a Hahn-series
model where `e` is transcendental over the base but not a unit, and the value group grows.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace M7

open Polynomial

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

/-- **`Γ` of an expansion is a base value** — the `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)` half of the paper's step
(`qe.tex:743`), with no dimension-theoretic input: some base element has the same value. -/
theorem exists_scalar_val {n : ℕ} (v : Valuation L Γ) (K : Subfield L)
    {e : L} (he : v e = 1) (hT : ResidueTranscendental v K he)
    {c : Fin n → K} {m : Fin n → ℕ} (hm : Function.Injective m) (hne : ∃ i, c i ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ v (∑ i, (c i : L) * e ^ m i) = v (a : L) := by
  classical
  -- a nonzero coefficient of maximal value
  set sf := Finset.univ.filter (fun i => c i ≠ 0) with hsf
  have hsfne : sf.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i₀, hi₀mem, hmax⟩ :=
    Finset.exists_max_image sf (fun i => v ((c i : L))) hsfne
  have hi₀ : c i₀ ≠ 0 := (Finset.mem_filter.mp hi₀mem).2
  have hi₀L : ((c i₀ : K) : L) ≠ 0 := fun h => hi₀ (by simpa using h)
  have hne0 : v ((c i₀ : L)) ≠ 0 := fun h => hi₀L ((Valuation.zero_iff v).mp h)
  have hpos : 0 < v ((c i₀ : L)) := lt_of_le_of_ne zero_le hne0.symm
  refine ⟨c i₀, hi₀, ?_⟩
  -- normalize by `c i₀`
  have hcoe : ∀ i, (((c i / c i₀ : K)) : L) = (c i : L) / (c i₀ : L) := fun i =>
    map_div₀ (Subfield.subtype K) (c i) (c i₀)
  have hd : ∀ i, v (((c i / c i₀ : K)) : L) ≤ 1 := by
    intro i
    by_cases hi : c i = 0
    · rw [hcoe, hi]; simp
    · rw [hcoe, Valuation.map_div, div_le_one₀ hpos]
      exact hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  have hi₀div : ((c i₀ / c i₀ : K)) = 1 := div_self hi₀
  have hsome : ∃ i, v (((c i / c i₀ : K)) : L) = 1 := by
    refine ⟨i₀, ?_⟩
    rw [hi₀div]
    simp
  have hstep := val_sum_eq_one v he hd hsome (hT n (fun i => c i / c i₀) m hm hd)
  -- identify the normalized expansion with `(Σ …)/c i₀`
  have hrel : (∑ i, (((c i / c i₀ : K)) : L) * e ^ m i)
      = (∑ i, (c i : L) * e ^ m i) / (c i₀ : L) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcoe]
    ring
  rw [hrel, Valuation.map_div] at hstep
  exact (div_eq_one_iff_eq hne0).mp hstep

/-- **Value normalization for elements of `K(e)`** — the other half of the paper's step
(`qe.tex:745`): every quotient of expansions can be moved to value `1` by a base element. -/
theorem exists_scalar_div_of_quot {n k : ℕ} (v : Valuation L Γ)
    (K : Subfield L) {e : L} (he : v e = 1) (hT : ResidueTranscendental v K he)
    {c : Fin n → K} {m : Fin n → ℕ} {q : Fin k → K} {nn : Fin k → ℕ}
    (hm : Function.Injective m) (hn : Function.Injective nn)
    (hc : ∃ i, c i ≠ 0) (hq : ∃ j, q j ≠ 0) :
    ∃ a : K, a ≠ 0 ∧
      v ((∑ i, (c i : L) * e ^ m i) / (∑ j, (q j : L) * e ^ nn j) / (a : L)) = 1 := by
  obtain ⟨a₁, ha₁, hv₁⟩ := exists_scalar_val v K he hT hm hc
  obtain ⟨a₂, ha₂, hv₂⟩ := exists_scalar_val v K he hT hn hq
  have ha₁L : ((a₁ : K) : L) ≠ 0 := fun h => ha₁ (by simpa using h)
  have ha₂L : ((a₂ : K) : L) ≠ 0 := fun h => ha₂ (by simpa using h)
  have h1 : v ((a₁ : K) : L) ≠ 0 := fun h => ha₁L ((Valuation.zero_iff v).mp h)
  have h2 : v ((a₂ : K) : L) ≠ 0 := fun h => ha₂L ((Valuation.zero_iff v).mp h)
  have ha : a₁ / a₂ ≠ 0 := div_ne_zero ha₁ ha₂
  refine ⟨a₁ / a₂, ha, ?_⟩
  have hcoe : (((a₁ / a₂ : K)) : L) = (a₁ : L) / (a₂ : L) :=
    map_div₀ (Subfield.subtype K) a₁ a₂
  rw [hcoe]
  simp only [Valuation.map_div]
  rw [hv₁, hv₂]
  exact div_self (div_ne_zero h1 h2)

/-- **Lemma 3.6's `Γ`-step, with no dimension inequality.**  For `b` a quotient of expansions in a
unit `e` whose residue is transcendental over the base field's residue field — i.e. for
`b ∈ VF(Ŝ)(e) = VF(⟨Ŝ,e⟩)` — the value of `b` is a base value, and `b` can be normalized to value
`1` by a base element.  This is the content the paper extracts from Engler–Prestel Thm 3.4.3
(`qe.tex:741-747`), so that quotation can be dropped from Lemma 3.6's hypotheses. -/
theorem gamma_step {n k : ℕ} (v : Valuation L Γ) (K : Subfield L)
    {e : L} (he : v e = 1) (hT : ResidueTranscendental v K he)
    {c : Fin n → K} {m : Fin n → ℕ} {q : Fin k → K} {nn : Fin k → ℕ}
    (hm : Function.Injective m) (hn : Function.Injective nn)
    (hc : ∃ i, c i ≠ 0) (hq : ∃ j, q j ≠ 0) :
    (∃ a : K, a ≠ 0 ∧
        v ((∑ i, (c i : L) * e ^ m i) / (∑ j, (q j : L) * e ^ nn j)) = v (a : L)) ∧
      (∃ a : K, a ≠ 0 ∧
        v ((∑ i, (c i : L) * e ^ m i) / (∑ j, (q j : L) * e ^ nn j) / (a : L)) = 1) := by
  obtain ⟨a, ha, hva⟩ := exists_scalar_div_of_quot v K he hT hm hn hc hq
  have haL : ((a : K) : L) ≠ 0 := fun h => ha (by simpa using h)
  have hane : v ((a : K) : L) ≠ 0 := fun h => haL ((Valuation.zero_iff v).mp h)
  refine ⟨⟨a, ha, ?_⟩, a, ha, hva⟩
  rw [Valuation.map_div] at hva
  rw [div_eq_one_iff_eq hane] at hva
  exact hva

end M7

/-! ## 4. Audit -/

#print axioms M7.val_sum_eq_one
#print axioms M7.exists_scalar_val
#print axioms M7.exists_scalar_div_of_quot
#print axioms M7.gamma_step
