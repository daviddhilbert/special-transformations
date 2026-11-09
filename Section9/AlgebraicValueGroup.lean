import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! No new values in an algebraic extension of a field with divisible
value group. The proof uses two maximal terms of an equation, and
does not use rank one or a finite-extension valuation theorem. -/

namespace SpecialTransformations.Section9

variable {F K G : Type*} [Field F] [Field K] [Algebra F K]
variable [LinearOrderedCommGroupWithZero G]

/-- An algebraic element has a value already realized in the base
when the base values are divisible. -/
theorem exists_same_value_of_isAlgebraic (v : Valuation K G)
    (hdiv : ∀ c : F, ∀ k : ℕ, k ≠ 0 →
      ∃ b : F, v (algebraMap F K b) ^ k = v (algebraMap F K c))
    (x : K) (hx : IsAlgebraic F x) :
    ∃ c : F, v x = v (algebraMap F K c) := by
  classical
  by_cases hx₀ : x = 0
  · exact ⟨0, by simp [hx₀]⟩
  obtain ⟨P, hP, hPx⟩ := hx
  let f (i : ℕ) : K := algebraMap F K (P.coeff i) * x ^ i
  have hsum : ∑ i ∈ P.support, f i = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hPx
    exact hPx
  have hnonzero (i : ℕ) (hi : i ∈ P.support) : v (f i) ≠ 0 :=
    v.ne_zero_iff.mpr (mul_ne_zero
      ((map_ne_zero (algebraMap F K)).mpr (Polynomial.mem_support_iff.mp hi)) (pow_ne_zero _ hx₀))
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image P.support (fun j => v (f j))
    (Polynomial.support_nonempty.mpr hP)
  have heq : ∃ j ∈ P.support, j ≠ i ∧ v (f j) = v (f i) := by
    by_contra! hn
    have hlt (j : ℕ) (hj : j ∈ P.support \ {i}) : v (f j) < v (f i) :=
      lt_of_le_of_ne (hmax j (Finset.mem_sdiff.mp hj).1)
        (hn j (Finset.mem_sdiff.mp hj).1 (by simpa only [Finset.mem_singleton] using (Finset.mem_sdiff.mp hj).2))
    have h := v.map_sum_eq_of_lt hi hlt
    rw [hsum, map_zero] at h
    exact hnonzero i hi h.symm
  obtain ⟨j, hj, hne, he⟩ := heq
  have hpair : ∃ a b, a ∈ P.support ∧ b ∈ P.support ∧ a < b ∧ v (f a) = v (f b) := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨j, i, hj, hi, h, he⟩
    · exact ⟨i, j, hi, hj, h, he.symm⟩
  obtain ⟨a, b, ha, hb, hab, he⟩ := hpair
  let A := v (algebraMap F K (P.coeff a))
  let B := v (algebraMap F K (P.coeff b))
  have hB : B ≠ 0 := v.ne_zero_iff.mpr
    ((map_ne_zero (algebraMap F K)).mpr (Polynomial.mem_support_iff.mp hb))
  have hpow : v x ^ a ≠ 0 := pow_ne_zero _ (v.ne_zero_iff.mpr hx₀)
  have h : A * v x ^ a = B * v x ^ b := by
    simpa only [f, map_mul, map_pow] using he
  have hb' : b = a + (b - a) := (Nat.add_sub_of_le hab.le).symm
  have h' : A * v x ^ a = (B * v x ^ (b - a)) * v x ^ a := by
    calc
      _ = B * v x ^ b := h
      _ = _ := by
        conv_lhs => rw [hb', pow_add]
        ac_rfl
  have hq : v x ^ (b - a) = v (algebraMap F K (P.coeff a / P.coeff b)) := by
    rw [map_div₀, map_div₀]
    apply (eq_div_iff hB).mpr
    rw [mul_comm]
    exact (mul_right_cancel₀ hpow h').symm
  have hn : b - a ≠ 0 := Nat.sub_ne_zero_of_lt hab
  obtain ⟨c, hc⟩ := hdiv (P.coeff a / P.coeff b) (b - a) hn
  exact ⟨c, (pow_left_inj₀ zero_le zero_le hn).mp (hq.trans hc.symm)⟩

end SpecialTransformations.Section9
