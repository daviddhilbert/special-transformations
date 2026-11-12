module

public import Section9.ValuedPolynomialTaylor
public import Section9.ImplicitEstimate
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section

/-! The implicit linear approximation of a continuous scalar branch.
The scalar equation with nonzero output derivative gives the error
bound before any choices of topological neighbourhood are made. -/

open MvPolynomial
open scoped BigOperators

namespace SpecialTransformations.Section9

variable {K G R : Type*} [Field K] [LinearOrderedCommGroupWithZero G]
variable [CommRing R] [Algebra R K] {n : ℕ}

public noncomputable def scalarInputLinearTerm (P : MvPolynomial (Fin n ⊕ Unit) R)
    (x : Fin n ⊕ Unit → K) (h : Fin n → K) : K :=
  ∑ i, aeval x (pderiv (Sum.inl i) P) * h i

noncomputable def implicitScalarSlope (P : MvPolynomial (Fin n ⊕ Unit) R)
    (x : Fin n ⊕ Unit → K) : (Fin n → K) →ₗ[K] K where
  toFun h := -scalarInputLinearTerm P x h / aeval x (pderiv (Sum.inr ()) P)
  map_add' h k := by
    simp only [scalarInputLinearTerm, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' t h := by
    simp only [scalarInputLinearTerm, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    have hs : (∑ i, aeval x (pderiv (Sum.inl i) P) * (t * h i)) =
        t * ∑ i, aeval x (pderiv (Sum.inl i) P) * h i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ac_rfl
    rw [hs]
    ring

/-- In an implicit scalar equation the branch error is quadratic in the
input size once both increments are sufficiently small. The two constants
are chosen from the equation and the point. -/
theorem exists_value_implicitScalar_bounds (v : Valuation K G)
    (P : MvPolynomial (Fin n ⊕ Unit) R) (x : Fin n ⊕ Unit → K) (hroot : aeval x P = 0)
    (hd : aeval x (pderiv (Sum.inr ()) P) ≠ 0) :
    ∃ B C : G, 1 ≤ B ∧ 0 < C ∧ ∀ (h : Fin n → K) (u : K) (r : G),
      r ≤ 1 → (∀ i, v (h i) ≤ r) → max (B * r) (v u) ≤ 1 → C * max (B * r) (v u) < 1 →
      aeval (x + Sum.elim h (fun _ => u)) P = 0 →
      v (u - implicitScalarSlope P x h) ≤ C * (B * r) ^ 2 := by
  obtain ⟨B₀, C₀, _, hC₀, hTaylor⟩ := exists_value_polynomialTaylor_bounds v P x
  let d := aeval x (pderiv (Sum.inr ()) P)
  have hvd : 0 < v d := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hd)
  let B := max 1 (B₀ / v d)
  let C := C₀ / v d
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B, C, hB, div_pos (zero_lt_one.trans_le hC₀) hvd,
    fun h u r hr hh hsmall hsmall' hnew => ?_⟩
  have hsplit (z : K) : polynomialLinearTerm P x (Sum.elim h (fun _ => z)) =
      scalarInputLinearTerm P x h + d * z := by
    simp [polynomialLinearTerm, scalarInputLinearTerm, Fintype.sum_sum_type, d]
  have hzeroBound (i : Fin n ⊕ Unit) : v (Sum.elim h (fun _ => (0 : K)) i) ≤ r := by
    cases i with
    | inl i => exact hh i
    | inr i => simpa only [Sum.elim_inr, map_zero] using (zero_le : 0 ≤ r)
  have hlin₀ := (hTaylor r hr _ hzeroBound).1
  rw [hsplit 0, mul_zero, add_zero] at hlin₀
  have hlin : v (scalarInputLinearTerm P x h / d) ≤ B * r := by
    rw [map_div₀]
    calc
      _ ≤ (B₀ * r) / v d := by
        simp only [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hlin₀ zero_le
      _ = (B₀ / v d) * r := by simp only [div_eq_mul_inv]; ac_rfl
      _ ≤ B * r := mul_le_mul_of_nonneg_right (le_max_right _ _) zero_le
  let Δ : Fin n ⊕ Unit → K := Sum.elim h (fun _ => u)
  let t := max (B * r) (v u)
  have hrB : r ≤ B * r := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hB (zero_le : 0 ≤ r)
  have hΔ (i : Fin n ⊕ Unit) : v (Δ i) ≤ t := by
    cases i with
    | inl i => exact (hh i).trans (hrB.trans (le_max_left _ _))
    | inr i => exact le_max_right _ _
  let E := polynomialRemainder P x Δ
  have hErr : v (E / d) ≤ C * t ^ 2 := by
    rw [map_div₀]
    calc
      _ ≤ (C₀ * t ^ 2) / v d := by
        simp only [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (hTaylor t hsmall Δ hΔ).2 zero_le
      _ = _ := by simp only [C, div_eq_mul_inv]; ac_rfl
  have hEq : d * u + scalarInputLinearTerm P x h + E = 0 := by
    change d * u + scalarInputLinearTerm P x h + polynomialRemainder P x Δ = 0
    rw [polynomialRemainder, hroot, hnew, hsplit u]
    ring
  have hEq' : u + scalarInputLinearTerm P x h / d + E / d = 0 := by
    calc
      _ = (d * u + scalarInputLinearTerm P x h + E) / d := by
        field_simp [show d ≠ 0 from hd] <;> ring
      _ = _ := by rw [hEq, zero_div]
  change v (u - (-scalarInputLinearTerm P x h / d)) ≤ _
  rw [neg_div, sub_neg_eq_add]
  exact value_implicitScalar_error_le_sq v hEq' hlin hErr hsmall'

end SpecialTransformations.Section9
