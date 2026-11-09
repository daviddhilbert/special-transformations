import Mathlib.RingTheory.Valuation.ValuationSubring

/-! The prime ideal for the coarsening used in Gamma descent. In Mathlib's
multiplicative order, a positive additive threshold is strictly below one.
The thresholds used in the application are the nonzero values below one
realized in the algebraically closed coefficient field. -/

namespace SpecialTransformations.Section9

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-- Elements whose value is bounded above by some parameter threshold.
Localizing the fine valuation ring at this ideal makes every element of
infinitesimally positive additive value a unit. -/
def thresholdIdeal (v : Valuation K Γ) (T : Set Γ) (hne : T.Nonempty) :
    Ideal v.valuationSubring where
  carrier := {x | ∃ t ∈ T, v (x : K) ≤ t}
  zero_mem' := by
    obtain ⟨t, ht⟩ := hne
    exact ⟨t, ht, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    have hmax : max s t ∈ T := by
      rcases le_total s t with h | h
      · rwa [max_eq_right h]
      · rwa [max_eq_left h]
    refine ⟨max s t, hmax, ?_⟩
    exact (v.map_add (x : K) (y : K)).trans (max_le_max hx hy)
  smul_mem' := by
    rintro a x ⟨t, ht, hx⟩
    refine ⟨t, ht, ?_⟩
    change v ((a : K) * (x : K)) ≤ t
    rw [map_mul]
    exact (mul_le_of_le_one_left zero_le a.property).trans hx

theorem mem_thresholdIdeal (v : Valuation K Γ) (T : Set Γ) (hne : T.Nonempty)
    (x : v.valuationSubring) :
    x ∈ thresholdIdeal v T hne ↔ ∃ t ∈ T, v (x : K) ≤ t := Iff.rfl

/-- Halving the additive thresholds proves primeness of the ideal used
to coarsen the valuation. No assumption of rank one is involved. -/
theorem thresholdIdeal_isPrime (v : Valuation K Γ) (T : Set Γ) (hne : T.Nonempty)
    (hT : ∀ t ∈ T, t < 1) (hhalf : ∀ t ∈ T, ∃ s ∈ T, t ≤ s * s) :
    (thresholdIdeal v T hne).IsPrime := by
  classical
  refine Ideal.isPrime_iff.mpr ⟨?_, ?_⟩
  · intro he
    have h : (1 : v.valuationSubring) ∈ thresholdIdeal v T hne := by
      rw [he]
      trivial
    obtain ⟨t, ht, h1⟩ := (mem_thresholdIdeal v T hne 1).mp h
    have hle : 1 ≤ t := by simpa only [Subring.coe_one, map_one] using h1
    exact (not_le_of_gt (hT t ht)) hle
  · intro x y hxy
    by_contra hn
    push Not at hn
    obtain ⟨t, ht, hxy⟩ := (mem_thresholdIdeal v T hne (x * y)).mp hxy
    obtain ⟨s, hs, hts⟩ := hhalf t ht
    have hx : s < v (x : K) := lt_of_not_ge fun h =>
      hn.1 ((mem_thresholdIdeal v T hne x).mpr ⟨s, hs, h⟩)
    have hy : s < v (y : K) := lt_of_not_ge fun h =>
      hn.2 ((mem_thresholdIdeal v T hne y).mpr ⟨s, hs, h⟩)
    have hpos : 0 < v (y : K) := zero_le.trans_lt hy
    have hlt : t < v (x : K) * v (y : K) := hts.trans_lt
      ((mul_le_mul_of_nonneg_left hy.le zero_le).trans_lt (mul_lt_mul_of_pos_right hx hpos))
    change v ((x : K) * (y : K)) ≤ t at hxy
    rw [map_mul] at hxy
    exact (not_le_of_gt hlt) hxy

/-- The coarsening given by the prime of realized thresholds. -/
noncomputable def thresholdCoarsening (v : Valuation K Γ) (T : Set Γ) (hne : T.Nonempty)
    (hT : ∀ t ∈ T, t < 1) (hhalf : ∀ t ∈ T, ∃ s ∈ T, t ≤ s * s) :
    ValuationSubring K :=
  letI := thresholdIdeal_isPrime v T hne hT hhalf
  v.valuationSubring.ofPrime (thresholdIdeal v T hne)

theorem thresholdCoarsening_value_eq_one_iff
    (v : Valuation K Γ) (T : Set Γ) (hne : T.Nonempty)
    (hT : ∀ t ∈ T, t < 1) (hhalf : ∀ t ∈ T, ∃ s ∈ T, t ≤ s * s)
    (x : v.valuationSubring) :
    (thresholdCoarsening v T hne hT hhalf).valuation (x : K) = 1 ↔
      ∀ t ∈ T, t < v (x : K) := by
  letI := thresholdIdeal_isPrime v T hne hT hhalf
  change (v.valuationSubring.ofPrime (thresholdIdeal v T hne)).valuation (x : K) = 1 ↔ _
  rw [ValuationSubring.ofPrime_valuation_eq_one_iff_mem_primeCompl]
  change (¬ x ∈ thresholdIdeal v T hne) ↔ _
  rw [mem_thresholdIdeal]
  simp only [not_exists, not_and, not_le]

theorem thresholdCoarsening_value_lt_one_iff
    (v : Valuation K Γ) (T : Set Γ) (hne : T.Nonempty)
    (hT : ∀ t ∈ T, t < 1) (hhalf : ∀ t ∈ T, ∃ s ∈ T, t ≤ s * s)
    (x : v.valuationSubring) :
    (thresholdCoarsening v T hne hT hhalf).valuation (x : K) < 1 ↔
      ∃ t ∈ T, v (x : K) ≤ t := by
  letI := thresholdIdeal_isPrime v T hne hT hhalf
  let R := thresholdCoarsening v T hne hT hhalf
  have hle : R.valuation (x : K) ≤ 1 :=
    (R.valuation_le_one_iff _).mpr (ValuationSubring.le_ofPrime _ _ x.property)
  rw [lt_iff_le_and_ne, and_iff_right hle, ne_eq,
    thresholdCoarsening_value_eq_one_iff]
  push Not
  rfl

theorem thresholdCoarsening_le_of_fine_le
    (v : Valuation K Γ) (T : Set Γ) (hne : T.Nonempty)
    (hT : ∀ t ∈ T, t < 1) (hhalf : ∀ t ∈ T, ∃ s ∈ T, t ≤ s * s)
    (x y : K) (h : v x ≤ v y) :
    (thresholdCoarsening v T hne hT hhalf).valuation x ≤
      (thresholdCoarsening v T hne hT hhalf).valuation y := by
  letI := thresholdIdeal_isPrime v T hne hT hhalf
  let R := thresholdCoarsening v T hne hT hhalf
  by_cases hy : y = 0
  · have hvx : v x = 0 := le_antisymm (by simpa only [hy, map_zero] using h) zero_le
    rw [hy, v.zero_iff.mp hvx]
  have hr : v (x / y) ≤ 1 := by
    rw [map_div₀, div_le_one₀ (pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hy))]
    exact h
  apply (R.valuation_le_iff x y).mpr
  refine ⟨⟨x / y, ValuationSubring.le_ofPrime v.valuationSubring _ ?_⟩, div_mul_cancel₀ x hy⟩
  exact (Valuation.mem_valuationSubring_iff v _).mpr hr

end SpecialTransformations.Section9
