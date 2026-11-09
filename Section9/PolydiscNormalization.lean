import Section9.AffineTail

/-! A product of nonzero RV balls becomes the maximal-ideal polydisc
under an explicit affine bijection. -/

open SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] {n : ℕ}

theorem normalizePolydisc_bijOn (v : Valuation K Γ) (a : Fin n → K) (ha : ∀ i, a i ≠ 0) :
    Set.BijOn (fun x : Fin n → K => fun i => a i * x i + a i)
      {x | ∀ i, v (x i) < 1} (RVFibre v (fun i => RVCalc.rv v (a i))) := by
  have hmem (x : Fin n → K) (i : Fin n) :
      RVCalc.rv v (a i * x i + a i) = RVCalc.rv v (a i) ↔ v (x i) < 1 := by
    rw [rv_eq_centre_iff v (ha i), add_sub_cancel_right, map_mul]
    have hpos := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr (ha i))
    simpa only [mul_one] using
      (mul_lt_mul_iff_right₀ hpos : v (a i) * v (x i) < v (a i) * 1 ↔ v (x i) < 1)
  refine ⟨fun x hx i => (hmem x i).mpr (hx i), ?_, ?_⟩
  · intro x _ y _ hxy
    funext i
    exact mul_left_cancel₀ (ha i) (add_right_cancel (congrFun hxy i))
  · intro y hy
    let x (i : Fin n) := (y i - a i) / a i
    have he (i : Fin n) : a i * x i + a i = y i := by
      rw [show x i = (y i - a i) / a i from rfl, mul_comm, div_mul_cancel₀ _ (ha i), sub_add_cancel]
    exact ⟨x, fun i => (hmem x i).mp ((he i).symm ▸ hy i), funext he⟩

end SpecialTransformations.Section9
