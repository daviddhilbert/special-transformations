import Section9.GaussDerivative
import Section9.AlgebraicValueGroup
import Section9.ValuedEtaleDerivation
import Section9.UnramifiedDerivation
import Section9.UnramifiedGenerator
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! From the Gauss field to the finite graph field, the derivative
bound passes through the immediate étale extension and then the
unramified extension. The henselization and residue degree facts are
explicit inputs at this interface. -/

namespace SpecialTransformations.Section9

open IsLocalRing

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem value_coordinate_derivation_le_of_gauss_and_unramified
    (v : Valuation K Γ) (E : Subfield K) [IsAlgClosed E] {n : ℕ} (x : Fin n → K)
    (hx : ∀ i, v (x i) ≤ 1) (hGauss : IsGaussEvaluation (E := E) v x)
    (j : Fin n) (D : Derivation E K K) (hD : ∀ i, D (x i) = if j = i then 1 else 0)
    (H : Subfield K) [FiniteDimensional H K] [HenselianLocalRing v.valuationSubring]
    [CharZero (ResidueField v.valuationSubring)]
    (hFH : (IntermediateField.adjoin E (Set.range x)).toSubfield ≤ H)
    (hDF : ∀ z ∈ IntermediateField.adjoin E (Set.range x), D z ∈ IntermediateField.adjoin E (Set.range x))
    (hcover : EtaleCovered (valuationRingInside v (IntermediateField.adjoin E (Set.range x)).toSubfield)
      (valuationRingInside v H) (valuationRingInside_mono v hFH))
    (hImmediate : ∀ z ∈ H, ∃ a ∈ IntermediateField.adjoin E (Set.range x), v a = v z)
    (hdegree : letI := (residueFieldInclusion v H).toAlgebra
      Module.finrank H K = Module.finrank (ResidueField (v.comap H.subtype).valuationSubring)
        (ResidueField v.valuationSubring)) :
    ∀ z : K, v (D z) ≤ v z := by
  let F := IntermediateField.adjoin E (Set.range x)
  have hDerF : ∀ z ∈ F.toSubfield, v (D z) ≤ v z :=
    fun z hz => value_derivation_le_of_mem_gaussField v x hx hGauss j D hD z hz
  have hDerH := value_derivation_le_of_immediate_etale v D F.toSubfield H hFH hDF
    hDerF hcover hImmediate
  have hdiv (c : H) (p : ℕ) (hp : p ≠ 0) : ∃ b : H, v (algebraMap H K b) ^ p = v (algebraMap H K c) := by
    obtain ⟨z, hz, hvz⟩ := hImmediate (c : K) c.property
    obtain ⟨q, hvq⟩ := exists_same_value_of_mem_gaussField v x hx hGauss z hz
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq q (Nat.pos_of_ne_zero hp)
    refine ⟨⟨(r : K), hFH (F.algebraMap_mem r)⟩, ?_⟩
    change v ((r : E) : K) ^ p = v (c : K)
    rw [← map_pow]
    exact (congrArg (fun c : E => v (c : K)) hr).trans (hvq.symm.trans hvz)
  have hSame : ∀ z ∈ (⊤ : Subfield K), ∃ c ∈ H, v c = v z := by
    intro z _
    obtain ⟨c, hc⟩ := exists_same_value_of_isAlgebraic v hdiv z (Algebra.IsAlgebraic.isAlgebraic z)
    exact ⟨c.val, c.property, hc.symm⟩
  obtain ⟨u, P, d, hroot, hunit, hcoeff, hind, hspan⟩ := exists_unramified_powerBasis_of_residue_degree v H hdegree
  intro z
  exact value_derivation_le_of_unramified_powerBasis v D H ⊤ le_top hDerH hSame u P
    hroot hunit hcoeff hind (fun y _ => hspan y) z (Set.mem_univ _)

end SpecialTransformations.Section9
