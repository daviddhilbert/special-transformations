module

public import Section9.MixedJacobian

@[expose] public section

/-! On fixed-label charts the derivative of an inverse has reciprocal
determinant. This is the inverse step for intrinsic Gamma descent. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ}
local notation "VF" => VFType (M := M)
local notation "V" => Fin n → VF
local notation "RV" => CanonicalRV.RVSort M

theorem mixedVFJacobian_inverse_product
    {A : Set (V × (Fin r → RV))} {B : Set (V × (Fin s → RV))}
    (f : A → B) (g : B → A) (hg : Function.LeftInverse g f)
    (p : A) (L D : V →ₗ[VF] V)
    (hL : HasMixedVFDerivativeAt f p L) (hD : HasMixedVFDerivativeAt g (f p) D) :
    (LinearMap.toMatrix' D).det * (LinearMap.toMatrix' L).det = 1 := by
  have hProd := (mixedVFJacobian_comp_of_full_derivative hL hD).2.2
  obtain ⟨F, ⟨ρ, hρ⟩, _⟩ := hL
  have hId : IsVFChartAt (g ∘ f) p (fun x : V => x) := by
    refine ⟨ρ, fun x hx => ?_⟩
    obtain ⟨hxA, _⟩ := hρ x hx
    refine ⟨hxA, ?_⟩
    change (g (f ⟨(x, p.val.2), hxA⟩)).val = (x, (g (f p)).val.2)
    rw [hg _, hg p]
  have hDer : HasVFDerivativeAt (fun x : V => x) p.val.1 LinearMap.id := by
    simpa only [LinearMap.id_apply, add_zero] using
      hasVFDerivativeAt_affine (LinearMap.id : V →ₗ[VF] V) 0 p.val.1
  have hOne : HasMixedVFJacobianAt (g ∘ f) p 1 := by
    refine ⟨_, hId, ?_⟩
    simpa only [LinearMap.toMatrix'_id, Matrix.det_one] using hDer.hasJacobianAt
  exact hProd.unique hOne

end SpecialTransformations.Section9
