module

public import Section9.GaussDerivative
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section

/-! Extending the Gauss bound to an integral power basis. The simple
root computation uses the actual derivation and the valuation of the
polynomial derivative. The basis and value-group conditions are to be
established for the finite unramified extension in the comparison proof. -/

open Polynomial

namespace SpecialTransformations.Section9

variable {E K G : Type*} [Field E] [Field K] [Algebra E K]
variable [LinearOrderedCommGroupWithZero G]

private theorem derivation_eval_eq (D : Derivation E K K) (p : Polynomial K) (u : K) :
    D (p.eval u) = p.derivative.eval u * D u + ∑ i ∈ p.support, D (p.coeff i) * u ^ i := by
  have hcoeff : p.derivative.eval u = ∑ i ∈ p.support, p.coeff i * (i : K) * u ^ (i - 1) := by
    rw [Polynomial.derivative_apply, Polynomial.eval_sum, Polynomial.sum_def]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, map_sum, hcoeff, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [D.leibniz, D.leibniz_pow, smul_eq_mul, smul_eq_mul, smul_eq_mul, nsmul_eq_mul]
  ring

/-- The derivative of an integral simple root is integral when the
derivation is integral on the coefficients. -/
theorem value_derivation_le_one_of_simpleRoot (v : Valuation K G) (D : Derivation E K K)
    (p : Polynomial K) (u : K) (hu : v u ≤ 1) (hp : p.eval u = 0)
    (hunit : v (p.derivative.eval u) = 1)
    (hcoeff : ∀ i ∈ p.support, v (D (p.coeff i)) ≤ 1) :
    v (D u) ≤ 1 := by
  let a := p.derivative.eval u
  let b := ∑ i ∈ p.support, D (p.coeff i) * u ^ i
  have hb : v b ≤ 1 := by
    apply v.map_sum_le
    intro i hi
    rw [map_mul, map_pow]
    exact (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hu)).trans (hcoeff i hi)
  have he := derivation_eval_eq D p u
  rw [hp, map_zero] at he
  have he' : a * D u + b = 0 := he.symm
  have hz : a * D u = -b := by
    linear_combination he'
  have h := congrArg v hz
  rw [map_mul, show v a = 1 from hunit, one_mul, v.map_neg] at h
  exact h.trans_le hb

/-- Integral coefficients in a power expression preserve the derivative
bound once the generator and its derivative are integral. -/
theorem value_derivation_le_one_of_powerSum (v : Valuation K G) (D : Derivation E K K)
    (u : K) (hu : v u ≤ 1) (hDu : v (D u) ≤ 1) {m : ℕ} (c : Fin m → K)
    (hc : ∀ i, v (c i) ≤ 1) (hDc : ∀ i, v (D (c i)) ≤ 1) :
    v (D (∑ i, c i * u ^ (i : ℕ))) ≤ 1 := by
  have hp (i : ℕ) : v (D (u ^ i)) ≤ 1 := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, D.leibniz, smul_eq_mul, smul_eq_mul]
      apply v.map_add_le
      · rw [map_mul, map_pow]
        exact (mul_le_of_le_one_right zero_le hDu).trans (pow_le_one₀ zero_le hu)
      · rw [map_mul]
        exact (mul_le_of_le_one_right zero_le ih).trans hu
  rw [map_sum]
  apply v.map_sum_le
  intro i _
  rw [D.leibniz, smul_eq_mul, smul_eq_mul]
  apply v.map_add_le
  · rw [map_mul]
    exact (mul_le_of_le_one_right zero_le (hp i)).trans (hc i)
  · rw [map_mul, map_pow]
    exact (mul_le_of_le_one_right zero_le (hDc i)).trans (pow_le_one₀ zero_le hu)

/-- In an extension with the same values, a bound on the valuation ring
upgrades to a bound on every element. This yields preservation of the
maximal ideal as well as of the valuation ring. -/
theorem value_derivation_le_of_same_values (v : Valuation K G) (D : Derivation E K K)
    (F L : Subfield K) (hFL : F ≤ L)
    (hF : ∀ z ∈ F, v (D z) ≤ v z)
    (hL : ∀ z ∈ L, v z ≤ 1 → v (D z) ≤ 1)
    (hvalue : ∀ z ∈ L, ∃ c ∈ F, v c = v z)
    (z : K) (hz : z ∈ L) : v (D z) ≤ v z := by
  by_cases hz₀ : z = 0
  · rw [hz₀, map_zero]
  obtain ⟨c, hcF, hcz⟩ := hvalue z hz
  have hc₀ : v c ≠ 0 := hcz.trans_ne (v.ne_zero_iff.mpr hz₀)
  let q := z / c
  have hq : q ∈ L := L.div_mem hz (hFL hcF)
  have hvq : v q = 1 := by
    rw [show q = z / c from rfl, map_div₀, ← hcz, div_self hc₀]
  have he : q * c = z := div_mul_cancel₀ z (v.ne_zero_iff.mp hc₀)
  rw [← he, D.leibniz, smul_eq_mul, smul_eq_mul]
  apply v.map_add_le
  · rw [map_mul, map_mul, hvq, one_mul, one_mul]
    exact hF c hcF
  · rw [map_mul, map_mul, hvq, one_mul, mul_comm (v c)]
    exact mul_le_of_le_one_left zero_le (hL q hq hvq.le)

end SpecialTransformations.Section9
