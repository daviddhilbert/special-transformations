module

public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

/-! The valuation estimate for a scalar simple-root equation. Once
the nonzero output derivative has been divided out, the output
increment is bounded by the input size and the remaining error has
quadratic order. The proof applies in any valuation rank. -/

namespace SpecialTransformations.Section9

variable {K G : Type*} [Field K] [LinearOrderedCommGroupWithZero G]

theorem value_implicitScalar_error_le_sq (v : Valuation K G) {u a e : K} {X C : G}
    (hzero : u + a + e = 0) (hlinear : v a ≤ X)
    (hquad : v e ≤ C * max X (v u) ^ 2) (hsmall : C * max X (v u) < 1) :
    v (u + a) ≤ C * X ^ 2 := by
  have heq : u = -(a + e) := eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using hzero)
  have hu : v u ≤ max X (C * max X (v u) ^ 2) := by
    calc
      v u = v (a + e) := by rw [heq, v.map_neg]
      _ ≤ max (v a) (v e) := v.map_add a e
      _ ≤ max X (C * max X (v u) ^ 2) := max_le_max hlinear hquad
  have hXu : v u ≤ X := by
    by_contra hnot
    have hlt : X < v u := lt_of_not_ge hnot
    rw [max_eq_right hlt.le] at hsmall hu
    have he' : C * v u ^ 2 < v u := by
      calc
        C * v u ^ 2 = (C * v u) * v u := by rw [pow_two, mul_assoc]
        _ < 1 * v u := mul_lt_mul_of_pos_right hsmall (zero_le.trans_lt hlt)
        _ = v u := one_mul _
    exact (not_lt_of_ge hu) (max_lt hlt he')
  have herror : u + a = -e := eq_neg_of_add_eq_zero_left hzero
  rw [herror, v.map_neg]
  simpa only [max_eq_left hXu] using hquad

end SpecialTransformations.Section9
