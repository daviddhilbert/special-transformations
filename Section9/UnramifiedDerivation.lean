module

public import Section9.IntegralDerivativeReduction
public import Section9.ValuedPowerBasis

@[expose] public section

/-! A simple integral generator whose powers form a residue basis
preserves a valuation bound on derivations. The generator and power
basis are supplied by the residue degree calculation in the application. -/

set_option backward.isDefEq.respectTransparency false

open IsLocalRing

namespace SpecialTransformations.Section9

variable {E K G : Type*} [Field E] [Field K] [Algebra E K] [LinearOrderedCommGroupWithZero G]

theorem value_derivation_le_of_unramified_powerBasis
    (v : Valuation K G) (D : Derivation E K K)
    (F L : Subfield K) (hFL : F ≤ L)
    (hF : ∀ z ∈ F, v (D z) ≤ v z)
    (hvalues : ∀ z ∈ L, ∃ c ∈ F, v c = v z)
    (u : v.valuationSubring) (P : Polynomial K) (hroot : P.eval (u : K) = 0)
    (hunit : v (P.derivative.eval (u : K)) = 1)
    (hcoeff : ∀ i ∈ P.support, P.coeff i ∈ F ∧ v (P.coeff i) ≤ 1)
    {d : ℕ}
    (hind : ∀ c : Fin d → ResidueField (v.comap F.subtype).valuationSubring,
      (∑ j, residueFieldInclusion v F (c j) * residue v.valuationSubring u ^ (j : ℕ)) = 0 →
      c = 0)
    (hspan : ∀ z ∈ L, ∃ c : Fin d → F, ∑ j, (c j : K) * (u : K) ^ (j : ℕ) = z) :
    ∀ z ∈ L, v (D z) ≤ v z := by
  have hDu : v (D (u : K)) ≤ 1 :=
    value_derivation_le_one_of_simpleRoot v D P u u.property hroot hunit
      (fun i hi => (hF _ (hcoeff i hi).1).trans (hcoeff i hi).2)
  have hL (z : K) (hz : z ∈ L) (hvz : v z ≤ 1) : v (D z) ≤ 1 := by
    obtain ⟨c, hc⟩ := hspan z hz
    have hci (i : Fin d) : v (c i : K) ≤ 1 := by
      have h := value_coeff_le_powerSum v F u hind c i
      rw [hc] at h
      exact h.trans hvz
    rw [← hc]
    exact value_derivation_le_one_of_powerSum v D u u.property hDu (fun i => (c i : K)) hci
      (fun i => (hF _ (c i).property).trans (hci i))
  exact value_derivation_le_of_same_values v D F L hFL hF hL hvalues

end SpecialTransformations.Section9
