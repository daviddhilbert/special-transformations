import Section4.Imported.NoetherNormalizationTrdeg
import Section4.Imported.IntegralKrullDimension
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

noncomputable section

namespace SpecialTransformations.Section4.AffineKrullDimension

universe u

variable (K A : Type u) [Field K] [CommRing A] [IsDomain A] [Algebra K A]
  [Algebra.FiniteType K A]

/-- Actual Krull dimension and quotient-field transcendence degree agree
for a finite-type domain. The two general ingredients are attributed ports
of NYLL's normalization bridge and Mathlib PR 41904. -/
theorem exists_dimension_and_trdeg :
    ∃ d : ℕ, ringKrullDim A = d ∧ Algebra.trdeg K (FractionRing A) = (d : Cardinal) := by
  obtain ⟨d, g, hg, hint, htr⟩ := FieldArithmetic.Chapter06.exists_normalization_with_trdeg K A
  refine ⟨d, ?_, htr⟩
  simpa using (hint.ringKrullDim_eq_of_injective hg).symm

theorem ringKrullDim_eq_trdeg_toNat :
    ringKrullDim A = (Algebra.trdeg K (FractionRing A)).toNat := by
  obtain ⟨d, hd, htr⟩ := exists_dimension_and_trdeg K A
  rw [htr]
  simpa using hd

end SpecialTransformations.Section4.AffineKrullDimension

end
