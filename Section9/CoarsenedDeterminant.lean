import Section9.GammaCoarsening
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Integrality of the derivative entries gives one side of Gamma
descent. The inverse derivative gives the other side. -/

namespace SpecialTransformations.Section9

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] {n : ℕ}

theorem determinant_value_le_one_of_entries (v : Valuation K Γ)
    (D : Matrix (Fin n) (Fin n) K) (hD : ∀ i j, v (D i j) ≤ 1) :
    v D.det ≤ 1 := by
  let A : Matrix (Fin n) (Fin n) v.valuationSubring := fun i j =>
    ⟨D i j, (Valuation.mem_valuationSubring_iff v _).mpr (hD i j)⟩
  have he : v.valuationSubring.subtype A.det = D.det := by
    rw [RingHom.map_det]
    rfl
  exact (Valuation.mem_valuationSubring_iff v _).mp (he ▸ A.det.property)

/-- A coarsened integral matrix has integral determinant for the fine
valuation whenever its determinant value comes from the thresholds'
coefficient field. -/
theorem fine_det_le_one_of_coarsened_integral
    (v : Valuation K Γ) (T : Set Γ) (hne : T.Nonempty)
    (hT : ∀ t ∈ T, t < 1) (hhalf : ∀ t ∈ T, ∃ s ∈ T, t ≤ s * s)
    (D : Matrix (Fin n) (Fin n) K)
    (hD : ∀ i j, (thresholdCoarsening v T hne hT hhalf).valuation (D i j) ≤ 1)
    (hthreshold : 1 < v D.det → (v D.det)⁻¹ ∈ T) : v D.det ≤ 1 := by
  let w := (thresholdCoarsening v T hne hT hhalf).valuation
  have hdet : w D.det ≤ 1 := determinant_value_le_one_of_entries w D hD
  by_contra! hv
  have hvinv : v D.det⁻¹ ≤ 1 := by
    rw [map_inv₀]
    exact (inv_le_one₀ (zero_lt_one.trans hv)).mpr hv.le
  let a : v.valuationSubring := ⟨D.det⁻¹, (Valuation.mem_valuationSubring_iff v _).mpr hvinv⟩
  have hwa : w D.det⁻¹ < 1 :=
    (thresholdCoarsening_value_lt_one_iff v T hne hT hhalf a).mpr
      ⟨(v D.det)⁻¹, hthreshold hv, (map_inv₀ v D.det).le⟩
  rw [map_inv₀] at hwa
  have hpos : 0 < w D.det := pos_iff_ne_zero.mpr
    (w.ne_zero_iff.mpr (v.ne_zero_iff.mp (zero_lt_one.trans hv).ne'))
  exact hdet.not_gt ((inv_lt_one₀ hpos).mp hwa)

/-- The two directions of a bijection give opposite bounds on the
constant determinant value. -/
theorem constant_value_one_of_coarsened_integral_determinants
    (v : Valuation K Γ) (T : Set Γ) (hne : T.Nonempty)
    (hT : ∀ t ∈ T, t < 1) (hhalf : ∀ t ∈ T, ∃ s ∈ T, t ≤ s * s)
    (A B : Matrix (Fin n) (Fin n) K) (c : Γ) (hc : c ≠ 0)
    (ha : v A.det = c) (hb : v B.det = c⁻¹)
    (ht₁ : 1 < c → c⁻¹ ∈ T) (ht₂ : c < 1 → c ∈ T)
    (hA : ∀ i j, (thresholdCoarsening v T hne hT hhalf).valuation (A i j) ≤ 1)
    (hB : ∀ i j, (thresholdCoarsening v T hne hT hhalf).valuation (B i j) ≤ 1) : c = 1 := by
  have h₁ := fine_det_le_one_of_coarsened_integral v T hne hT hhalf A hA (by rwa [ha])
  have h₂ := fine_det_le_one_of_coarsened_integral v T hne hT hhalf B hB (by
    rw [hb, inv_inv]
    intro h
    apply ht₂
    simpa only [inv_inv] using (inv_lt_one₀ (pos_iff_ne_zero.mpr (inv_ne_zero hc))).mpr h)
  rw [ha] at h₁
  rw [hb] at h₂
  exact h₁.antisymm ((inv_le_one₀ (pos_iff_ne_zero.mpr hc)).mp h₂)

end SpecialTransformations.Section9
