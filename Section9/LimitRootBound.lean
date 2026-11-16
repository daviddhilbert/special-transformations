module

public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

/-! The uniform root bound for the bounded chart in Lemma 9.5. After
dividing out the common input power, the nonzero specialization factors
into linear terms. The remaining terms have a common factor of the
input, and their value bound is uniform over integral outputs. -/

open scoped BigOperators

namespace SpecialTransformations.Section9

variable {K G I J : Type*} [Field K] [LinearOrderedCommGroupWithZero G]

theorem perturbed_root_near_factor (v : Valuation K G) (s : Finset I) (t : Finset J)
    (c x y : K) (a : I → K) (d : J → K) (k l : J → ℕ) (ε B : G)
    (hx : v x ≤ 1) (hy : v y ≤ 1) (hB : ∀ j ∈ t, v (d j) ≤ B)
    (hsmall : v x * B < v c * ∏ _i ∈ s, ε)
    (hroot : c * (∏ i ∈ s, (y - a i)) + x * (∑ j ∈ t, d j * x ^ k j * y ^ l j) = 0) :
    ∃ i ∈ s, v (y - a i) < ε := by
  classical
  have hsum : v (∑ j ∈ t, d j * x ^ k j * y ^ l j) ≤ B := by
    apply v.map_sum_le
    intro j hj
    rw [map_mul, map_mul, map_pow, map_pow]
    exact (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hy)).trans
      ((mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hx)).trans (hB j hj))
  by_contra hnone
  have hlower : v c * (∏ _i ∈ s, ε) ≤ v (c * ∏ i ∈ s, (y - a i)) := by
    rw [map_mul, map_prod]
    apply mul_le_mul_of_nonneg_left _ zero_le
    apply Finset.prod_le_prod₀ (fun _ _ => zero_le)
    intro i hi
    exact le_of_not_gt fun h => hnone ⟨i, hi, h⟩
  have he := eq_neg_of_add_eq_zero_left hroot
  rw [he, v.map_neg, map_mul] at hlower
  exact (not_le_of_gt hsmall) (hlower.trans (mul_le_mul_of_nonneg_left hsum zero_le))

end SpecialTransformations.Section9
