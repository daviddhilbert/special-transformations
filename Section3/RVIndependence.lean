import Section3.VFDefinableClosure
import Section3.VFAlgebraicity
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem algebraicAt_vf_union_rv_iff (S : Set M)
    (B : Set M) (hB : ∀ t ∈ B, iRV t) (b : VFType (M := M)) :
    AlgebraicAt (S ∪ B) .vf b.val ↔ AlgebraicAt S .vf b.val := by
  rw [algebraicAt_vf_iff_parameterField, algebraicAt_vf_iff_parameterField,
    vfParameterField_union_rv S B hB]

/-- The VF assertion of Corollary 3.7, strengthened to any RV parameter set. -/
theorem corollary_3_7_vf (S : Set M)
    (B : Set M) (hB : ∀ t ∈ B, iRV t) (b : VFType (M := M))
    (hb : ¬ AlgebraicAt S .vf b.val) : ¬ AlgebraicAt (S ∪ B) .vf b.val := by
  exact fun h => hb ((algebraicAt_vf_union_rv_iff S B hB b).mp h)

end SpecialTransformations.Section3
