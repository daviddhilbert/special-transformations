import Section9.GaussEvaluation

/-! Residue-independent powers form an orthogonal family for the
valuation. In a finite extension of the same degree as its residue
extension, this is the integral power-basis calculation. -/

set_option backward.isDefEq.respectTransparency false

open IsLocalRing

namespace SpecialTransformations.Section9

variable {K G : Type*} [Field K] [LinearOrderedCommGroupWithZero G] {d : ℕ}

/-- No cancellation among residue-independent powers can decrease the
absolute value of an expansion below that of any of its coefficients. -/
theorem value_coeff_le_powerSum
    (v : Valuation K G) (F : Subfield K) (u : v.valuationSubring)
    (hInd : ∀ c : Fin d → ResidueField (v.comap F.subtype).valuationSubring,
      (∑ j, residueFieldInclusion v F (c j) * residue v.valuationSubring u ^ (j : ℕ)) = 0 →
      c = 0)
    (c : Fin d → F) (i : Fin d) :
    v (c i : K) ≤ v (∑ j, (c j : K) * (u : K) ^ (j : ℕ)) := by
  classical
  let w := v.comap F.subtype
  let A := w.valuationSubring
  let B := v.valuationSubring
  let f : A →+* B := valuationRingInclusion v F
  obtain ⟨s, _, hs⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin d))
    (fun j => w (c j)) ⟨i, Finset.mem_univ i⟩
  have hmax (j : Fin d) : w (c j) ≤ w (c s) := hs j (Finset.mem_univ j)
  by_cases hc : c s = 0
  · have hi := hmax i
    rw [hc, map_zero] at hi
    exact hi.trans zero_le
  let a (j : Fin d) : A :=
    ⟨c j / c s, (Valuation.mem_valuationSubring_iff w _).mpr (by
      rw [map_div₀]
      exact (div_le_one₀ (pos_iff_ne_zero.mpr (w.ne_zero_iff.mpr hc))).mpr (hmax j))⟩
  let q : B := ∑ j, f (a j) * u ^ (j : ℕ)
  have has : a s = 1 := Subtype.ext (div_self hc)
  have hq : residue B q ≠ 0 := by
    intro hz
    have he : (∑ j, residueFieldInclusion v F (residue A (a j)) * residue B u ^ (j : ℕ)) = 0 := by
      have hmap (j : Fin d) : residueFieldInclusion v F (residue A (a j)) = residue B (f (a j)) :=
        ResidueField.map_residue f (a j)
      simpa only [q, map_sum, map_mul, map_pow, ← hmap] using hz
    have hzero := congrFun (hInd (fun j => residue A (a j)) he) s
    exact one_ne_zero (by simpa only [has, map_one, Pi.zero_apply] using hzero)
  have hqunit : v (q : K) = 1 := by
    have hle := (Valuation.mem_valuationSubring_iff v _).mp q.property
    rw [ne_eq, residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff, not_lt] at hq
    exact hle.antisymm hq
  have he : (∑ j, (c j : K) * (u : K) ^ (j : ℕ)) = (c s : K) * (q : K) := by
    change _ = (c s : K) * B.subtype (∑ j, f (a j) * u ^ (j : ℕ))
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, map_pow, ← mul_assoc]
    change _ = (c s : K) * ((c j : K) / (c s : K)) * (u : K) ^ (j : ℕ)
    rw [mul_comm (c s : K), div_mul_cancel₀ _ (fun h => hc (Subtype.ext h))]
  rw [he, map_mul, hqunit, mul_one]
  exact hmax i

end SpecialTransformations.Section9
