import Section9.AlgebraicCoordinateDerivations
import Section9.BoundedGraphDerivations
import Section9.CoarsenedGauss

/-! The graph field supplied by henselization and residue degree has
coordinate derivations that preserve the valuation bound. -/

namespace SpecialTransformations.Section9

open IsLocalRing

variable {K Γ : Type} [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ]

theorem exists_bounded_coordinate_derivations
    (v : Valuation K Γ) (E : Subfield K) [IsAlgClosed E] {n : ℕ} (x : Fin n → K)
    (hx : ∀ i, v (x i) ≤ 1) (hGauss : IsGaussEvaluation (E := E) v x)
    (H : Subfield K) [FiniteDimensional H K] [HenselianLocalRing v.valuationSubring]
    [CharZero (ResidueField v.valuationSubring)]
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin E (Set.range x)) K)
    (hFH : (IntermediateField.adjoin E (Set.range x)).toSubfield ≤ H)
    (hcover : EtaleCovered (valuationRingInside v (IntermediateField.adjoin E (Set.range x)).toSubfield)
      (valuationRingInside v H) (valuationRingInside_mono v hFH))
    (hImmediate : ∀ z ∈ H, ∃ a ∈ IntermediateField.adjoin E (Set.range x), v a = v z)
    (hdegree : letI := (residueFieldInclusion v H).toAlgebra
      Module.finrank H K = Module.finrank (ResidueField (v.comap H.subtype).valuationSubring)
        (ResidueField v.valuationSubring)) :
    ∃ D : Fin n → Derivation E K K, (∀ j i, D j (x i) = if j = i then 1 else 0) ∧
      ∀ j z, v (D j z) ≤ v z := by
  have hi := algebraicIndependent_of_isGaussEvaluation v x hGauss
  choose D hD hStable using fun j => exists_algebraic_coordinate_derivation x hi j halg
  exact ⟨D, hD, fun j => value_coordinate_derivation_le_of_gauss_and_unramified v E x hx hGauss
    j (D j) (hD j) H hFH (hStable j) hcover hImmediate hdegree⟩

end SpecialTransformations.Section9
