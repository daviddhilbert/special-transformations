import Section9.AlgebraicValueGroup
import Section9.GaussEvaluation
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! The Gauss field has the coefficient field's divisible value group.
An algebraic extension of it therefore realizes the same values. -/

namespace SpecialTransformations.Section9

open IsLocalRing

variable {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem exists_same_value_of_isAlgebraic_over_gaussField
    (v : Valuation K Γ) (E : Subfield K) [IsAlgClosed E] (x : ι → K)
    (hx : ∀ i, v (x i) ≤ 1) (hGauss : IsGaussEvaluation (E := E) v x)
    (z : K) (hz : IsAlgebraic (IntermediateField.adjoin E (Set.range x)) z) :
    ∃ c : E, v z = v (c : K) := by
  let F := IntermediateField.adjoin E (Set.range x)
  have hdiv (a : F) (j : ℕ) (hj : j ≠ 0) :
      ∃ b : F, v (algebraMap F K b) ^ j = v (algebraMap F K a) := by
    obtain ⟨c, hc⟩ := exists_same_value_of_mem_gaussField v x hx hGauss (a : K) a.property
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hj)
    refine ⟨algebraMap E F b, ?_⟩
    change v (algebraMap E K b) ^ j = v (a : K)
    rw [← map_pow, ← map_pow, hb, hc]
  obtain ⟨a, ha⟩ := exists_same_value_of_isAlgebraic v hdiv z hz
  obtain ⟨c, hc⟩ := exists_same_value_of_mem_gaussField v x hx hGauss (a : K) a.property
  exact ⟨c, ha.trans hc⟩

theorem residueCharZero_of_subfield (v : Valuation K Γ) (F : Subfield K)
    [CharZero (ResidueField v.valuationSubring)] :
    CharZero (ResidueField (v.comap F.subtype).valuationSubring) := by
  constructor
  intro m n h
  apply Nat.cast_injective (R := ResidueField v.valuationSubring)
  simpa only [map_natCast] using congrArg (residueFieldInclusion v F) h


end SpecialTransformations.Section9
