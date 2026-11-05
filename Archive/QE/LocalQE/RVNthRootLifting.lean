import RVHenselLifting
import ResidueTranscendentalTransport

namespace RVCalc

open Polynomial

variable {K Γ : Type*} [Field K] [IsAlgClosed K]
    [LinearOrderedCommGroupWithZero Γ]

/-- Lift an nth-root equation with a prescribed leading term. This also
handles residue characteristics dividing n; no derivative condition is used. -/
theorem nth_root_with_rv (v : Valuation K Γ) {n : ℕ} (hn : 0 < n)
    {a c : K} (ha : a ≠ 0) (hc : c ≠ 0)
    (hclass : rv v (c ^ n) = rv v a) :
    ∃ d : K, d ^ n = a ∧ rv v d = rv v c := by
  have hcn : c ^ n ≠ 0 := pow_ne_zero _ hc
  have hvc : v (c ^ n) ≠ 0 := (Valuation.ne_zero_iff v).mpr hcn
  have hclose : v (c ^ n - a) < v (c ^ n) := (rv_eq_iff hcn ha).mp hclass
  have hsmall : v (1 - a / c ^ n) < 1 := by
    have he : 1 - a / c ^ n = (c ^ n - a) / c ^ n := by
      field_simp [hcn]
    rw [he, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hvc)]
    exact hclose
  let p : K[X] := X ^ n - C (a / c ^ n)
  have hp : p.Monic := monic_X_pow_sub_C _ (Nat.ne_of_gt hn)
  have heval : v (p.eval 1) < 1 := by simpa [p] using hsmall
  obtain ⟨b, hb, hbrv⟩ := exists_root_rv_eq v hp heval (map_one v)
  have hbn : b ^ n = a / c ^ n := by
    apply sub_eq_zero.mp
    simpa [Polynomial.IsRoot.def, p] using hb
  refine ⟨c * b, ?_, ?_⟩
  · rw [mul_pow, hbn, mul_div_cancel₀ _ hcn]
  · rw [ResidueTranscendentalTransport.rv_mul_all, hbrv,
      ← ResidueTranscendentalTransport.rv_mul_all, mul_one]

end RVCalc

#print axioms RVCalc.nth_root_with_rv
