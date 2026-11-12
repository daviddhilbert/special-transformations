module

public import Section9.LimitRootBound
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Removing the least input exponent in the finite monomial form of
the polynomial from Lemma 9.5. This exposes the specialization and the
factor of the input in the remaining terms. -/

open scoped BigOperators

namespace SpecialTransformations.Section9

variable {K : Type*} [CommSemiring K]

theorem factor_input_power (D : Finset (ℕ × ℕ)) (c : ℕ × ℕ → K) (r : ℕ)
    (hr : ∀ d ∈ D, r ≤ d.1) (x y : K) :
    (∑ d ∈ D, c d * x ^ d.1 * y ^ d.2) = x ^ r *
      ((∑ d ∈ D.filter (fun d => d.1 = r), c d * y ^ d.2) +
        x * ∑ d ∈ D.filter (fun d => r < d.1), c d * x ^ (d.1 - r - 1) * y ^ d.2) := by
  let L := D.filter (fun d => d.1 = r)
  let H := D.filter (fun d => r < d.1)
  have hdis : Disjoint L H := by
    apply Finset.disjoint_left.mpr
    intro d hdL hdH
    exact (ne_of_gt (Finset.mem_filter.mp hdH).2) (Finset.mem_filter.mp hdL).2
  have hparts : L ∪ H = D := by
    ext d
    simp only [L, H, Finset.mem_union, Finset.mem_filter]
    refine ⟨fun h => h.elim And.left And.left, fun hd => ?_⟩
    rcases eq_or_lt_of_le (hr d hd) with h | h
    · exact Or.inl ⟨hd, h.symm⟩
    · exact Or.inr ⟨hd, h⟩
  have hL : (∑ d ∈ L, c d * x ^ d.1 * y ^ d.2) =
      x ^ r * ∑ d ∈ L, c d * y ^ d.2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [(Finset.mem_filter.mp hd).2]
    ac_rfl
  have hH : (∑ d ∈ H, c d * x ^ d.1 * y ^ d.2) =
      (x ^ r * x) * ∑ d ∈ H, c d * x ^ (d.1 - r - 1) * y ^ d.2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd' : r + 1 ≤ d.1 := (Finset.mem_filter.mp hd).2
    have hi : (r + 1) + (d.1 - r - 1) = d.1 := by
      rw [Nat.sub_sub, Nat.add_comm (r + 1), Nat.sub_add_cancel hd']
    have hx : x ^ d.1 = (x ^ r * x) * x ^ (d.1 - r - 1) := by
      rw [← pow_succ, ← pow_add, hi]
    rw [hx]
    ac_rfl
  calc
    _ = (∑ d ∈ L, c d * x ^ d.1 * y ^ d.2) + ∑ d ∈ H, c d * x ^ d.1 * y ^ d.2 := by
      rw [← Finset.sum_union hdis, hparts]
    _ = _ := by rw [hL, hH, mul_add, mul_assoc]

end SpecialTransformations.Section9

namespace SpecialTransformations.Section9

variable {K G I J : Type*} [Field K] [LinearOrderedCommGroupWithZero G]

/-- A bounded-chart root bound with a radius realized in VF. The
coefficient bound and the input radius are chosen inside the proof. -/
theorem exists_input_radius_near_factor (v : Valuation K G) (s : Finset I) (t : Finset J)
    (c : K) (hc : c ≠ 0) (a : I → K) (d : J → K) (k l : J → ℕ)
    (r : K) (hr : r ≠ 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∀ x y : K, v x < v δ → v y ≤ 1 →
      c * (∏ i ∈ s, (y - a i)) + x * (∑ j ∈ t, d j * x ^ k j * y ^ l j) = 0 →
        ∃ i ∈ s, v (y - a i) < v r := by
  classical
  let T := insert (1 : K) (t.image d)
  have hOne : (1 : K) ∈ T := Finset.mem_insert_self _ _
  obtain ⟨b, _, hmax⟩ := Finset.exists_max_image T v ⟨1, hOne⟩
  have hb : b ≠ 0 := by
    intro h
    have hbound := hmax 1 hOne
    rw [h, map_zero, map_one] at hbound
    exact (not_le_of_gt zero_lt_one) hbound
  let z := c * r ^ s.card / b
  have hz : z ≠ 0 := div_ne_zero (mul_ne_zero hc (pow_ne_zero _ hr)) hb
  obtain ⟨δ, hδ, hδz, hδ1⟩ : ∃ δ : K, δ ≠ 0 ∧ v δ ≤ v z ∧ v δ ≤ 1 := by
    by_cases h : v z ≤ 1
    · exact ⟨z, hz, le_rfl, h⟩
    · exact ⟨1, one_ne_zero, by simpa only [map_one] using le_of_not_ge h, by rw [map_one]⟩
  refine ⟨δ, hδ, fun x y hx hy hroot => ?_⟩
  have hval : v z = (v c * ∏ _i ∈ s, v r) / v b := by
    simp only [z, map_div₀, map_mul, map_pow, Finset.prod_const]
  have hsmall : v x * v b < v c * ∏ _i ∈ s, v r := by
    apply (lt_div_iff₀ (pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hb))).mp
    rw [← hval]
    exact hx.trans_le hδz
  exact perturbed_root_near_factor v s t c x y a d k l (v r) (v b) (hx.le.trans hδ1) hy
    (fun j hj => hmax (d j) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩)))
    hsmall hroot

end SpecialTransformations.Section9
