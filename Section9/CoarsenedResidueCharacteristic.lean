module

public import Section9.GammaCoarsening

@[expose] public section

/-! Residue characteristic zero passes to any valuation whose order
comparisons respect those of the original valuation. -/

namespace SpecialTransformations.Section9

open IsLocalRing

variable {K Γ Δ : Type*} [Field K]
variable [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

theorem residueCharZero_of_coarsening (v : Valuation K Γ) (w : Valuation K Δ)
    [CharZero (ResidueField v.valuationSubring)]
    (h : ∀ a b : K, v a ≤ v b → w a ≤ w b) : CharZero (ResidueField w.valuationSubring) := by
  constructor
  intro n m he
  by_contra hnm
  let a : v.valuationSubring := (n : v.valuationSubring) - (m : v.valuationSubring)
  let b : w.valuationSubring := (n : w.valuationSubring) - (m : w.valuationSubring)
  have hval : (a : K) = (b : K) := by
    change v.valuationSubring.subtype a = w.valuationSubring.subtype b
    simp [a, b]
  have hv : v (a : K) = v 1 := by
    rw [map_one]
    apply le_antisymm a.property
    by_contra! hlt
    have hz := (residue_eq_zero_iff a).mpr ((Valuation.mem_maximalIdeal_iff K v).mpr hlt)
    apply hnm
    exact Nat.cast_injective (by simpa only [a, map_sub, map_natCast, sub_eq_zero] using hz)
  have hw : w (b : K) = 1 := by
    rw [← hval, ← map_one w]
    exact le_antisymm (h _ _ hv.le) (h _ _ hv.ge)
  have hb : residue w.valuationSubring b = 0 := by
    simp only [b, map_sub, map_natCast, sub_eq_zero]
    exact he
  exact (not_lt_of_ge hw.ge) ((Valuation.mem_maximalIdeal_iff K w).mp ((residue_eq_zero_iff b).mp hb))

end SpecialTransformations.Section9
