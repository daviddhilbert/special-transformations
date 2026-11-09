import Section9.LimitPolynomialRoots
import Section9.LimitReciprocal

/-! Combine the bounded chart and the reciprocal chart for a polynomial
relation with one input and one output. The radii are realized in the
field and the candidate set is fixed before the radii are chosen. -/

open scoped BigOperators

namespace SpecialTransformations.Section9

variable {K G : Type*} [Field K] [LinearOrderedCommGroupWithZero G]

def memValuedLimitSide (v : Valuation K G) (r : K) (b : Option K) (y : K) : Prop :=
  match b with
  | none => (v r)⁻¹ < v y
  | some a => v (y - a) < v r

variable [IsAlgClosed K]

theorem exists_projective_root_candidates (v : Valuation K G)
    (D : Finset (ℕ × ℕ)) (hD : D.Nonempty) (c : ℕ × ℕ → K) (hc : ∀ d ∈ D, c d ≠ 0) :
    ∃ L : Set (Option K), L.Finite ∧ ∀ r : K, r ≠ 0 → ∃ δ : K, δ ≠ 0 ∧
      ∀ x y : K, x ≠ 0 → v x < v δ →
        (∑ d ∈ D, c d * x ^ d.1 * y ^ d.2) = 0 →
          ∃ b ∈ L, memValuedLimitSide v r b y := by
  classical
  let N := D.sup Prod.snd
  have hN : ∀ d ∈ D, d.2 ≤ N := fun _ hd => Finset.le_sup hd
  let e (d : ℕ × ℕ) : ℕ × ℕ := (d.1, N - d.2)
  have he (d : ℕ × ℕ) (hd : d ∈ D) : e (e d) = d := by
    apply Prod.ext
    · rfl
    · change N - (N - d.2) = d.2
      have h := hN d hd
      omega
  have heinj : Set.InjOn e (D : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    exact (he a ha).symm.trans ((congrArg e hab).trans (he b hb))
  let D' := D.image e
  let c' := c ∘ e
  have hc' : ∀ d ∈ D', c' d ≠ 0 := by
    intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := Finset.mem_image.mp hd
    change c (e (e d₀)) ≠ 0
    rw [he d₀ hd₀]
    exact hc d₀ hd₀
  obtain ⟨B, hB, hbounded⟩ := exists_bounded_root_candidates v D hD c hc
  obtain ⟨B', hB', hreciprocal⟩ := exists_bounded_root_candidates v D' (hD.image e) c' hc'
  let inversePoint (b : K) : Option K := if b = 0 then none else some b⁻¹
  let L := (Option.some '' B) ∪ (inversePoint '' B')
  refine ⟨L, (hB.image _).union (hB'.image _), fun r hr => ?_⟩
  let rb (b : K) : K := if b = 0 then r else if v b ≤ v (r * b ^ 2) then b else r * b ^ 2
  have hrb (b : K) : rb b ≠ 0 := by
    by_cases h : b = 0
    · simpa only [rb, if_pos h] using hr
    · simp only [rb, if_neg h]
      split
      · exact h
      · exact mul_ne_zero hr (pow_ne_zero _ h)
  let T := insert r (hB'.toFinset.image rb)
  obtain ⟨ρ, hρT, hmin⟩ := Finset.exists_min_image T v ⟨r, Finset.mem_insert_self _ _⟩
  have hρ : ρ ≠ 0 := by
    rcases Finset.mem_insert.mp hρT with h | h
    · exact h.symm ▸ hr
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h
      exact hrb b
  have hρb (b : K) (hb : b ∈ B') : v ρ ≤ v (rb b) :=
    hmin _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b, hB'.mem_toFinset.mpr hb, rfl⟩))
  obtain ⟨δ₀, hδ₀, hbound⟩ := hbounded r hr
  obtain ⟨δ₁, hδ₁, hrec⟩ := hreciprocal ρ hρ
  obtain ⟨δ, hδ, hle₀, hle₁⟩ : ∃ δ : K, δ ≠ 0 ∧ v δ ≤ v δ₀ ∧ v δ ≤ v δ₁ := by
    rcases le_total (v δ₀) (v δ₁) with h | h
    · exact ⟨δ₀, hδ₀, le_rfl, h⟩
    · exact ⟨δ₁, hδ₁, h, le_rfl⟩
  refine ⟨δ, hδ, fun x y hx hsmall hroot => ?_⟩
  by_cases hy : v y ≤ 1
  · obtain ⟨b, hb, hclose⟩ := hbound x y hx (hsmall.trans_le hle₀) hy hroot
    exact ⟨some b, Or.inl ⟨b, hb, rfl⟩, hclose⟩
  have hy' : 1 < v y := lt_of_not_ge hy
  have hy₀ : y ≠ 0 := by
    intro heq
    rw [heq, map_zero] at hy'
    exact (not_lt_of_ge zero_le) hy'
  have hyinv : v y⁻¹ ≤ 1 := by
    rw [map_inv₀]
    exact (by simpa only [inv_one] using
      (inv_lt_inv₀ (zero_lt_one.trans hy') zero_lt_one).mpr hy' : (v y)⁻¹ < 1).le
  have hroot' : (∑ d ∈ D', c' d * x ^ d.1 * y⁻¹ ^ d.2) = 0 := by
    calc
      _ = ∑ d ∈ D, c' (e d) * x ^ (e d).1 * y⁻¹ ^ (e d).2 := Finset.sum_image heinj
      _ = ∑ d ∈ D, c d * x ^ d.1 * y⁻¹ ^ (N - d.2) := by
        apply Finset.sum_congr rfl
        intro d hd
        change c (e (e d)) * x ^ d.1 * y⁻¹ ^ (N - d.2) = _
        rw [he d hd]
      _ = (∑ d ∈ D, c d * x ^ d.1 * y ^ d.2) * y⁻¹ ^ N :=
        reciprocal_eval_eq D c N hN x y hy₀
      _ = 0 := by rw [hroot, zero_mul]
  obtain ⟨b, hb, hclose⟩ := hrec x y⁻¹ hx (hsmall.trans_le hle₁) hyinv hroot'
  refine ⟨inversePoint b, Or.inr ⟨b, hb, rfl⟩, ?_⟩
  have hnear := hclose.trans_le (hρb b hb)
  by_cases hb₀ : b = 0
  · subst b
    simp only [inversePoint, if_pos rfl, memValuedLimitSide]
    simp only [rb, if_pos rfl, sub_zero] at hnear
    simpa only [inv_inv] using inv_mem_infinity_ball v (inv_ne_zero hy₀) hnear
  · have hv : v (rb b) = min (v b) (v r * v b ^ 2) := by
      by_cases h : v b ≤ v (r * b ^ 2)
      · rw [map_mul, map_pow] at h
        simp only [rb, if_neg hb₀, map_mul, map_pow, if_pos h, min_eq_left h]
      · rw [map_mul, map_pow] at h
        simp only [rb, if_neg hb₀, map_mul, map_pow, if_neg h, min_eq_right (le_of_not_ge h)]
    rw [hv] at hnear
    simp only [inversePoint, if_neg hb₀, memValuedLimitSide]
    simpa only [inv_inv] using inv_mem_finite_ball v hb₀ (inv_ne_zero hy₀) hnear

end SpecialTransformations.Section9
