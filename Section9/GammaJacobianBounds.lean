module

public import Section9.MixedInverseJacobian
public import Section9.CoarsenedDeterminant

@[expose] public section

/-! Combine the two coarsened derivative bounds at possibly different
graph points. The fine Jacobian value of the inverse is obtained from
the forward constant value and the actual chart chain rule. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section9

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ] {n r s : ℕ}
local notation "VF" => VFType (M := M)
local notation "V" => Fin n → VF
local notation "RV" => CanonicalRV.RVSort M

theorem mixed_constantJacobian_value_one_of_coarsened_bounds
    {A : Set (V × (Fin r → RV))} {B : Set (V × (Fin s → RV))}
    (f : A → B) (g : B → A) (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f)
    (v : Valuation VF Γ) (T : Set Γ) (hne : T.Nonempty)
    (hT : ∀ t ∈ T, t < 1) (hhalf : ∀ t ∈ T, ∃ s ∈ T, t ≤ s * s)
    (c : Γ) (hc : c ≠ 0) (ht₁ : 1 < c → c⁻¹ ∈ T) (ht₂ : c < 1 → c ∈ T)
    (q : B) (L : Matrix (Fin n) (Fin n) VF) (D : V →ₗ[VF] V)
    (hD : HasMixedVFDerivativeAt g q D) (hc₁ : v L.det = c)
    (L' : V →ₗ[VF] V) (hL' : HasMixedVFDerivativeAt f (g q) L')
    (hc₂ : v (LinearMap.toMatrix' L').det = c)
    (hboundL : ∀ i j, (thresholdCoarsening v T hne hT hhalf).valuation (L i j) ≤ 1)
    (hboundD : ∀ i j, (thresholdCoarsening v T hne hT hhalf).valuation (LinearMap.toMatrix' D i j) ≤ 1) :
    c = 1 := by
  have hD' : HasMixedVFDerivativeAt g (f (g q)) D := by rwa [hfg q]
  have he := mixedVFJacobian_inverse_product f g hgf (g q) L' D hL' hD'
  have hv := congrArg v he
  rw [map_mul, map_one, hc₂] at hv
  have hvc : v (LinearMap.toMatrix' D).det = c⁻¹ := by
    apply (eq_div_iff hc).mpr at hv
    simpa only [one_div] using hv
  exact constant_value_one_of_coarsened_integral_determinants v T hne hT hhalf
    L (LinearMap.toMatrix' D) c hc hc₁ hvc ht₁ ht₂ hboundL hboundD

end SpecialTransformations.Section9
