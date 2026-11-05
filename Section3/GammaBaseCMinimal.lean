import Section3.GammaSpecialization
import Section3.RVUnaryLift
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Theorem2.8 for sets defined with actual Gamma names as well as real
parameters. Only ACVF is assumed. -/
theorem c_minimal_gamma_base (B : Base (M := M)) (A : Set M)
    (hA : DefinableAtBase B .vf A) : IsBoolComb {C | IsBall C} A := by
  obtain ⟨k,t,hA⟩ := hA.specialize
  exact hA.isBoolComb_balls

end SpecialTransformations.Section3.GammaParameters
