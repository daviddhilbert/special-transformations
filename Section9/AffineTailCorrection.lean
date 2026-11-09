import Section9.AffineTail

/-! The affine tail is a bijection on every fibre. At a head with the
correct determinant value its slope product gives the prescribed
total determinant. -/

open SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] {m : ℕ}

def affineTailCorrectionGood (v : Valuation K Γ) (a b : Fin m → K) (D c : K) : Prop :=
  v D ≠ 0 ∧ v D * (∏ i, v (b i) / v (a i)) = v c

noncomputable def affineTailSlopesForHead (v : Valuation K Γ) (a b : Fin m → K)
    (j : Fin m) (D c : K) : Fin m → K := by
  classical
  exact if affineTailCorrectionGood v a b D c then affineTailSlopes a b j (c / D) else fun i => b i / a i

theorem affineTailSlopesForHead_spec (v : Valuation K Γ) (a b : Fin m → K)
    (j : Fin m) (D c : K) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    let s := affineTailSlopesForHead v a b j D c
    Set.BijOn (affineTail a b s) (RVFibre v (fun i => RVCalc.rv v (a i)))
      (RVFibre v (fun i => RVCalc.rv v (b i))) ∧
    (affineTailCorrectionGood v a b D c → D * (∏ i, s i) = c) := by
  classical
  by_cases h : affineTailCorrectionGood v a b D c
  · have hv : v (c / D) = ∏ i, v (b i) / v (a i) := by
      rw [map_div₀]
      exact (div_eq_iff h.1).mpr (h.2.symm.trans (mul_comm _ _))
    have hh := affineTailSlopes_spec v a b j (c / D) ha hb hv
    simp only [affineTailSlopesForHead, if_pos h]
    refine ⟨hh.2, fun _ => ?_⟩
    rw [hh.1, mul_comm, div_mul_cancel₀ _ (v.ne_zero_iff.mp h.1)]
  · simp only [affineTailSlopesForHead, if_neg h]
    refine ⟨affineTail_bijOn v a b _ ha hb (fun i => div_ne_zero (hb i) (ha i)) ?_,
      fun h' => (h h').elim⟩
    intro i
    change v (b i / a i) * v (a i) = v (b i)
    rw [map_div₀, div_mul_cancel₀ _ (v.ne_zero_iff.mpr (ha i))]

theorem affineTailCorrectionGood_of_weighted_head (v : Valuation K Γ)
    (a b : Fin m → K) (D c : K) (A B : Γ)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hD : v D = B / A)
    (hc : v c = (B * ∏ i, v (b i)) / (A * ∏ i, v (a i))) :
    affineTailCorrectionGood v a b D c := by
  refine ⟨hD.symm ▸ div_ne_zero hB hA, ?_⟩
  rw [hD, Finset.prod_div_distrib, hc, div_mul_div_comm]

end SpecialTransformations.Section9
