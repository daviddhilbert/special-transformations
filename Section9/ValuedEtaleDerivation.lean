module

public import Section9.EtaleDerivationBound
public import Section9.IntegralDerivativeReduction

@[expose] public section

/-! The elementwise étale presentation and preservation of values
give a pointwise bound on derivations across an immediate extension. -/

namespace SpecialTransformations.Section9

variable {K E Γ : Type} [Field K] [Field E] [Algebra E K]
variable [LinearOrderedCommGroupWithZero Γ]

def valuationRingInside (v : Valuation K Γ) (F : Subfield K) : Subring K :=
  F.toSubring ⊓ v.valuationSubring.toSubring

theorem valuationRingInside_mono (v : Valuation K Γ) {F H : Subfield K} (hFH : F ≤ H) :
    valuationRingInside v F ≤ valuationRingInside v H :=
  fun _ h => ⟨hFH h.1, h.2⟩

theorem value_derivation_le_of_immediate_etale (v : Valuation K Γ) (D : Derivation E K K)
    (F H : Subfield K) (hFH : F ≤ H)
    (hDF : ∀ z ∈ F, D z ∈ F)
    (hF : ∀ z ∈ F, v (D z) ≤ v z)
    (hcover : EtaleCovered (valuationRingInside v F) (valuationRingInside v H)
      (valuationRingInside_mono v hFH))
    (hvalue : ∀ z ∈ H, ∃ c ∈ F, v c = v z) :
    ∀ z ∈ H, v (D z) ≤ v z := by
  let A := valuationRingInside v F
  let B := valuationRingInside v H
  have hDA (a : A) : (D.restrictScalars ℤ) (a : K) ∈ A := by
    have ha : (a : K) ∈ F ∧ (a : K) ∈ v.valuationSubring := a.property
    have hDa : v (D (a : K)) ≤ 1 := (hF _ ha.1).trans ha.2
    exact ⟨hDF _ ha.1, hDa⟩
  have hDB := derivation_maps_subring_of_etaleCovered A B (valuationRingInside_mono v hFH)
    hcover (D.restrictScalars ℤ) hDA
  apply value_derivation_le_of_same_values v D F H hFH hF _ hvalue
  intro z hz hval
  let b : B := ⟨z, hz, hval⟩
  exact (hDB b).2

end SpecialTransformations.Section9
