module

public import Mathlib

@[expose] public section
namespace SpecialTransformations.Section3.RVMonomial

/-- Uniform estimates use only ordered-group laws, with no Archimedean
assumption and no extraction of a value-group root. -/
theorem positive_zpow_mul_lt_one {G : Type*} [LinearOrderedCommGroupWithZero G]
    {x c hi : G} {e : ℤ} (hx : 0 < x) (hx1 : x ≤ 1) (he : 0 < e)
    (hc : c ≤ hi) (hsmall : x * hi < 1) : x ^ e * c < 1 := by
  have hp : x ^ e ≤ x := by
    simpa only [zpow_one] using
      (zpow_le_zpow_right_of_le_one₀ hx hx1 (show (1 : ℤ) ≤ e by omega))
  calc
    x ^ e * c ≤ x * hi := by gcongr
    _ < 1 := hsmall

theorem one_lt_negative_zpow_mul {G : Type*} [LinearOrderedCommGroupWithZero G]
    {x c lo : G} {e : ℤ} (hx : 0 < x) (hx1 : x ≤ 1) (he : e < 0)
    (hc : lo ≤ c) (hsmall : 1 < x⁻¹ * lo) : 1 < x ^ e * c := by
  have hxi : 1 ≤ x⁻¹ := (one_le_inv₀ hx).mpr hx1
  have hp : x⁻¹ ≤ x ^ e := by
    have hh := zpow_le_zpow_right₀ hxi (show (1 : ℤ) ≤ -e by omega)
    simpa only [zpow_one,inv_zpow,zpow_neg,inv_inv] using hh
  calc
    1 < x⁻¹ * lo := hsmall
    _ ≤ x ^ e * c := by gcongr

end SpecialTransformations.Section3.RVMonomial
