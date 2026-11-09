import Section9.ValuedEtaleDerivation
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Localization.FractionRing

open IsLocalRing
open scoped nonZeroDivisors

namespace SpecialTransformations.Section9

variable {A K Γ : Type} [CommRing A] [IsDomain A] [ValuationRing A] [Field K]
variable [LinearOrderedCommGroupWithZero Γ]

theorem exists_map_eq_integral_quotient (v : Valuation K Γ)
    (f : A →+* v.valuationSubring) [IsLocalHom f] (a b : A) :
    let g := v.valuationSubring.subtype.comp f
    g b ≠ 0 → v (g a) ≤ v (g b) → ∃ c : A, g a / g b = g c := by
  let g := v.valuationSubring.subtype.comp f
  change g b ≠ 0 → v (g a) ≤ v (g b) → ∃ c : A, g a / g b = g c
  intro hb hv
  obtain ⟨d, hd | hd⟩ := ValuationRing.cond a b
  · have he : g a * g d = g b := (map_mul g a d).symm.trans (congrArg g hd)
    have hga : g a ≠ 0 := left_ne_zero_of_mul (show g a * g d ≠ 0 by rwa [he])
    have hpos : 0 < v (g a) := lt_of_le_of_ne zero_le ((v.ne_zero_iff.mpr hga).symm)
    have hdv : 1 ≤ v (g d) := by
      by_contra! h
      have hlt := mul_lt_mul_of_pos_left h hpos
      rw [mul_one, ← map_mul, he] at hlt
      exact (not_lt_of_ge hv) hlt
    have hunit : IsUnit (f d) := by
      apply notMem_maximalIdeal.mp
      intro hm
      exact (not_lt_of_ge hdv) ((Valuation.mem_maximalIdeal_iff K v).mp hm)
    obtain ⟨hlocal⟩ := (inferInstance : IsLocalHom f)
    obtain ⟨u, hu⟩ := hlocal d hunit
    have hmul : g (u : A) * g ((u⁻¹ : Aˣ) : A) = 1 := by
      rw [← map_mul]
      simp
    refine ⟨((u⁻¹ : Aˣ) : A), (div_eq_iff hb).mpr ?_⟩
    calc
      g a = g a * (g (u : A) * g ((u⁻¹ : Aˣ) : A)) := by rw [hmul, mul_one]
      _ = g ((u⁻¹ : Aˣ) : A) * g b := by rw [← he, ← hu]; ac_rfl
  · exact ⟨d, (div_eq_iff hb).mpr ((congrArg g hd).symm.trans ((map_mul g b d).trans (mul_comm _ _)))⟩

theorem localValuationRing_range_eq_intersection (v : Valuation K Γ)
    (f : A →+* v.valuationSubring) [IsLocalHom f]
    (h : Function.Injective (v.valuationSubring.subtype.comp f)) :
    let g := v.valuationSubring.subtype.comp f
    let i : FractionRing A →+* K := IsFractionRing.lift h
    g.range = valuationRingInside v i.fieldRange := by
  let g := v.valuationSubring.subtype.comp f
  let i : FractionRing A →+* K := IsFractionRing.lift h
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨⟨algebraMap A (FractionRing A) a, ?_⟩, (f a).property⟩
    change i (algebraMap A (FractionRing A) a) = g a
    rw [IsFractionRing.lift_algebraMap]
  · rintro ⟨⟨y, rfl⟩, hv⟩
    obtain ⟨a, b, hb, hy⟩ := IsFractionRing.div_surjective A y
    have hb' : g b ≠ 0 := (h.ne (nonZeroDivisors.ne_zero hb)).trans_eq (map_zero g)
    have hy' : i y = g a / g b := by
      rw [← hy, map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
    have hv' : v (g a) ≤ v (g b) := by
      change v (i y) ≤ 1 at hv
      rw [hy', map_div₀] at hv
      have hpos : 0 < v (g b) := lt_of_le_of_ne zero_le ((v.ne_zero_iff.mpr hb').symm)
      simpa only [one_mul] using (div_le_iff₀ hpos).mp hv
    obtain ⟨c, hc⟩ := exists_map_eq_integral_quotient v f a b hb' hv'
    exact ⟨c, hc.symm.trans hy'.symm⟩


end SpecialTransformations.Section9
