import Section9.Differentiation
import Section9.ValuedImplicitDerivative

set_option backward.isDefEq.respectTransparency false

/-! A simple polynomial equation differentiates a continuous local branch
in the actual VF value quotient, with no rank restriction. -/

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section8

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable {R : Type*} [CommRing R] [Algebra R (VFType (M := M))]

local notation "VF" => VFType (M := M)
local notation "Γ" => Values.Gamma (M := M)
local notation "v" => Values.vfValueHom (M := M)

/-- The simple branch approximation in the scalar output. The hypotheses
describe an equation and continuity on an input neighbourhood. -/
theorem implicitScalarSlope_isDerivative
    (f : (Fin n → VF) → VF) (a : Fin n → VF)
    (P : MvPolynomial (Fin n ⊕ Unit) R)
    (hroot : aeval (Sum.elim a (fun _ => f a)) P = 0)
    (hderiv : aeval (Sum.elim a (fun _ => f a)) (pderiv (Sum.inr ()) P) ≠ 0)
    (heq : ∃ δ : Γ, ∀ h, δ.val < vfTupleValue h →
      aeval (Sum.elim (a + h) (fun _ => f (a + h))) P = 0)
    (hcont : ∀ ε : Γ, ∃ δ : Γ, ∀ h, δ.val < vfTupleValue h →
      ε.val < v (f (a + h) - f a)) :
    ∀ ε : Γ, ∃ δ : Γ, ∀ h, h ≠ 0 → δ.val < vfTupleValue h →
      ε.val * vfTupleValue h <
        v (f (a + h) - f a - implicitScalarSlope P (Sum.elim a (fun _ => f a)) h) := by
  let G := MonoidWithZeroHom.ValueGroup₀ (.ofClass (Values.presentationValuation (M := M)))
  let w : Valuation VF G := Values.presentationValuation.restrict
  let φ : Values.GammaTop (M := M) ≃ OrderDual G := Values.paperValueEquiv
  let ψ (a : Values.GammaTop (M := M)) : G := OrderDual.ofDual (φ a)
  have hψ (z : VF) : ψ (v z) = w z :=
    Values.valueEquiv_apply_vf Values.presentationValuation Values.presentation_compatible z
  have hψ0 : ψ 0 = 0 := Values.paperValue_zero
  have hψmul (a b : Values.GammaTop (M := M)) : ψ (a * b) = ψ a * ψ b :=
    Values.paperValue_mul a b
  have positive (ε : Γ) : 0 < ψ ε.val :=
    pos_iff_ne_zero.mpr (fun h => finiteValue_ne_zero ε (φ.injective (h.trans hψ0.symm)))
  have finite (g : G) (hg : 0 < g) : ∃ δ : Γ, ψ δ.val = g := by
    have hpre : ψ (φ.symm (OrderDual.toDual g)) = g := φ.apply_symm_apply _
    refine ⟨⟨φ.symm (OrderDual.toDual g), fun h => hg.ne ?_⟩, hpre⟩
    rw [← hψ0]
    exact (congrArg ψ (Values.infinity_eq_zero.symm.trans h.symm)).trans hpre
  obtain ⟨B, C, hB, hC, hEst⟩ :=
    exists_value_implicitScalar_bounds w P (Sum.elim a (fun _ => f a)) hroot hderiv
  have hB₀ : 0 < B := zero_lt_one.trans_le hB
  let Q : G := min 1 C⁻¹
  have hQ : 0 < Q := lt_min zero_lt_one (inv_pos.mpr hC)
  obtain ⟨η, hη⟩ := finite Q hQ
  obtain ⟨δc, hδc⟩ := hcont η
  obtain ⟨δp, hδp⟩ := heq
  intro ε
  let E : G := ψ ε.val
  let T : G := min (Q / B) (E / (C * B ^ 2))
  have hT : 0 < T :=
    lt_min (div_pos hQ hB₀) (div_pos (positive ε) (mul_pos hC (pow_pos hB₀ 2)))
  obtain ⟨δt, hδt⟩ := finite T hT
  refine ⟨max δp (max δc δt), fun h hn hsmall => ?_⟩
  have hp : δp.val < vfTupleValue h :=
    (show δp.val ≤ (max δp (max δc δt)).val from le_max_left _ _).trans_lt hsmall
  have hc : δc.val < vfTupleValue h :=
    (show δc.val ≤ (max δp (max δc δt)).val from
      (le_max_left _ _).trans (le_max_right _ _)).trans_lt hsmall
  have ht : δt.val < vfTupleValue h :=
    (show δt.val ≤ (max δp (max δc δt)).val from
      (le_max_right _ _).trans (le_max_right _ _)).trans_lt hsmall
  let r : G := ψ (vfTupleValue h)
  let u : VF := f (a + h) - f a
  have hu : w u < Q := by
    have hu' : ψ (v u) < ψ η.val := hδc h hc
    rwa [hψ, hη] at hu'
  have hrT : r < T := by
    have ht' : r < ψ δt.val := ht
    rwa [hδt] at ht'
  have hrB : B * r < Q :=
    (mul_comm B r) ▸ (lt_div_iff₀ hB₀).mp (hrT.trans_le (min_le_left _ _))
  have hr : r ≤ 1 := by
    have hle : r ≤ B * r := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hB (zero_le : 0 ≤ r)
    exact hle.trans ((hrB.trans_le (min_le_left _ _)).le)
  have hh (i : Fin n) : w (h i) ≤ r := by
    rw [← hψ]
    exact vfTupleValue_le_component h i
  have hmax : max (B * r) (w u) < Q := max_lt hrB hu
  have hq : C * max (B * r) (w u) < 1 := by
    calc
      _ < C * C⁻¹ := mul_lt_mul_of_pos_left (hmax.trans_le (min_le_right _ _)) hC
      _ = 1 := mul_inv_cancel₀ hC.ne'
  have hnew :
      aeval (Sum.elim a (fun _ => f a) + Sum.elim h (fun _ => u)) P = 0 := by
    have hz : Sum.elim a (fun _ : Unit => f a) + Sum.elim h (fun _ => u) =
        Sum.elim (a + h) (fun _ => f (a + h)) := by
      funext j
      cases j with
      | inl i => rfl
      | inr i =>
        change f a + (f (a + h) - f a) = f (a + h)
        abel
    rw [hz]
    exact hδp h hp
  have hErr := hEst h u r hr hh (hmax.le.trans (min_le_left _ _)) hq hnew
  have hn' : r ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, h i ≠ 0 := by
      by_contra! he
      exact hn (funext he)
    intro he
    have hi' := hh i
    rw [he] at hi'
    exact (w.ne_zero_iff.mpr hi) (nonpos_iff_eq_zero.mp hi')
  have hs : C * B ^ 2 * r < E := by
    rw [mul_comm (C * B ^ 2)]
    exact (lt_div_iff₀ (mul_pos hC (pow_pos hB₀ 2))).mp
      (hrT.trans_le (min_le_right _ _))
  change ψ (v (u - implicitScalarSlope P (Sum.elim a (fun _ => f a)) h)) <
    ψ (ε.val * vfTupleValue h)
  rw [hψmul, hψ]
  refine hErr.trans_lt ?_
  change C * (B * r) ^ 2 < E * r
  rw [mul_pow, pow_two r, ← mul_assoc, ← mul_assoc]
  exact mul_lt_mul_of_pos_right hs (pos_iff_ne_zero.mpr hn')

end SpecialTransformations.Section9
