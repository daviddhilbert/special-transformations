import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Bounds for returning from the reciprocal chart in Lemma 9.5.
The value order here is the multiplicative valuation order. -/

open scoped BigOperators

namespace SpecialTransformations.Section9

variable {K G : Type*} [Field K] [LinearOrderedCommGroupWithZero G]

/-- Reversing the output exponents preserves the roots on the nonzero
chart. The uniform degree bound works even when specialization lowers
the output degree. -/
theorem reciprocal_eval_eq (D : Finset (ℕ × ℕ)) (c : ℕ × ℕ → K) (N : ℕ)
    (hN : ∀ d ∈ D, d.2 ≤ N) (x y : K) (hy : y ≠ 0) :
    (∑ d ∈ D, c d * x ^ d.1 * y⁻¹ ^ (N - d.2)) =
      (∑ d ∈ D, c d * x ^ d.1 * y ^ d.2) * y⁻¹ ^ N := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdegree : d.2 + (N - d.2) = N := by
    rw [Nat.add_comm, Nat.sub_add_cancel (hN d hd)]
  have hpow : y ^ d.2 * y⁻¹ ^ N = y⁻¹ ^ (N - d.2) := by
    calc
      _ = y ^ d.2 * (y⁻¹ ^ d.2 * y⁻¹ ^ (N - d.2)) := by rw [← pow_add, hdegree]
      _ = (y ^ d.2 * y⁻¹ ^ d.2) * y⁻¹ ^ (N - d.2) := (mul_assoc _ _ _).symm
      _ = _ := by rw [← mul_pow, mul_inv_cancel₀ hy, one_pow, one_mul]
  calc
    _ = (c d * x ^ d.1) * (y ^ d.2 * y⁻¹ ^ N) := congrArg (c d * x ^ d.1 * ·) hpow.symm
    _ = _ := (mul_assoc _ _ _).symm

/-- In the reciprocal chart, approaching zero gives the infinity
neighbourhood with the inverse radius. -/
theorem inv_mem_infinity_ball (v : Valuation K G) {z : K} (hz : z ≠ 0)
    {ε : G} (h : v z < ε) : ε⁻¹ < v z⁻¹ := by
  have hzv : 0 < v z := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hz)
  rw [map_inv₀]
  exact (inv_lt_inv₀ (hzv.trans h) hzv).mpr h

/-- A nonzero limit in the reciprocal chart gives an ordinary finite
limit. The minimum in the input radius keeps the value of the reciprocal
variable equal to the value of its centre. -/
theorem inv_mem_finite_ball (v : Valuation K G) {b z : K} (hb : b ≠ 0) (hz : z ≠ 0)
    {ε : G} (h : v (z - b) < min (v b) (ε * v b ^ 2)) :
    v (z⁻¹ - b⁻¹) < ε := by
  have hclose := h.trans_le (min_le_left (v b) (ε * v b ^ 2))
  have hvalue : v z = v b := v.map_eq_of_sub_lt hclose
  have hid : z⁻¹ - b⁻¹ = -(z - b) / (z * b) := by
    field_simp [hb, hz] <;> ring
  have hbv : 0 < v b := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hb)
  rw [hid, map_div₀, v.map_neg, map_mul, hvalue, ← pow_two]
  exact (div_lt_iff₀ (pow_pos hbv 2)).mpr (h.trans_le (min_le_right _ _))

end SpecialTransformations.Section9
