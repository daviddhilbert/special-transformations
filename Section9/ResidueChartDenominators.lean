import Mathlib.Algebra.MvPolynomial.Eval

/-! A polynomial on the chart with an inverse variable has a numerator
in the original variables. Its nonvanishing is unchanged on the chart. -/

open MvPolynomial

namespace SpecialTransformations.Section9

theorem exists_clear_residueChart_inverse {E K ι : Type} [Field E] [Field K] [Algebra E K]
    (Q : MvPolynomial ι E) (P : MvPolynomial (ι ⊕ Unit) E) :
    ∃ R : MvPolynomial ι E, ∃ d : ℕ, ∀ x : ι → K, aeval x Q ≠ 0 →
      aeval x R = aeval x Q ^ d * aeval (Sum.elim x (fun _ => (aeval x Q)⁻¹)) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    exact ⟨C c, 0, fun x _ => by rw [aeval_C, aeval_C, pow_zero, one_mul]⟩
  | add P₁ P₂ h₁ h₂ =>
    obtain ⟨R₁, d₁, h₁⟩ := h₁
    obtain ⟨R₂, d₂, h₂⟩ := h₂
    refine ⟨Q ^ d₂ * R₁ + Q ^ d₁ * R₂, d₁ + d₂, fun x hx => ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, h₁ x hx, h₂ x hx, pow_add, map_add, mul_add]
    ac_rfl
  | mul_X P i hP =>
    obtain ⟨R, d, hR⟩ := hP
    rcases i with i | ⟨⟩
    · refine ⟨R * X i, d, fun x hx => ?_⟩
      rw [map_mul, map_mul, aeval_X, aeval_X, hR x hx, mul_assoc]
      rfl
    · refine ⟨R, d + 1, fun x hx => ?_⟩
      rw [hR x hx, map_mul, aeval_X, Sum.elim_inr, pow_succ]
      rw [show (aeval x Q ^ d * aeval x Q) *
          (aeval (Sum.elim x fun _ => (aeval x Q)⁻¹) P * (aeval x Q)⁻¹) =
          (aeval x Q ^ d * aeval (Sum.elim x fun _ => (aeval x Q)⁻¹) P) *
            (aeval x Q * (aeval x Q)⁻¹) by ac_rfl, mul_inv_cancel₀ hx, mul_one]

end SpecialTransformations.Section9
