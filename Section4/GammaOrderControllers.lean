import Section4.CanonicalOrderController
import Section3.GammaThresholdGeometry

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Reuse the given C-minimality consequence on the actual Gamma carrier,
including arbitrary Gamma parameters, and make its endpoint set intrinsic. -/
theorem exists_unique_gamma_order_controller (h00 : M ⊨ Axioms.ACVF00)
    (B : GammaParameters.Base (M := M)) (A : Set (Values.Gamma (M := M)))
    (hA : GammaParameters.GammaDefinableOverBase B A) :
    ∃! F : Finset (Values.Gamma (M := M)), FiniteOrder.Controls F A ∧
      ∀ H, FiniteOrder.Controls H A → F.card ≤ H.card := by
  obtain ⟨E, hE⟩ := GammaParameters.gamma_definable_finite_thresholds h00 B A hA
  exact FiniteOrder.exists_unique_minimal_controller ⟨E, hE⟩

end SpecialTransformations.Section4

end
