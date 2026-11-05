import Section3.FieldBase
import Section3.VFAlgebraicity
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem algebraicAt_vf_union_rv_iff (S : Set M) (F : VFFieldBase S)
    (B : Set M) (hB : ∀ t ∈ B, iRV t) (b : VFType (M := M)) :
    AlgebraicAt (S ∪ B) .vf b.val ↔ AlgebraicAt S .vf b.val := by
  constructor
  · intro hb
    apply (VFFieldBase.algebraicAt_iff S F b).mpr
    apply algebraicAt_vf_isAlgebraic (S ∪ B) F.field ?_ b hb
    intro x hx
    rcases hx with hx | hx
    · exact (F.mem_iff x).mpr hx
    · have hh := CanonicalStructure.sort_unique hM (s := .vf) (t := .rv)
        x.property (hB x.val hx)
      cases hh
  · exact AlgebraicAt.mono Set.subset_union_left

/-- The VF assertion of Corollary 3.7, strengthened to any RV parameter set. -/
theorem corollary_3_7_vf (S : Set M) (F : VFFieldBase S)
    (B : Set M) (hB : ∀ t ∈ B, iRV t) (b : VFType (M := M))
    (hb : ¬ AlgebraicAt S .vf b.val) : ¬ AlgebraicAt (S ∪ B) .vf b.val := by
  exact fun h => hb ((algebraicAt_vf_union_rv_iff S F B hB b).mp h)

end SpecialTransformations.Section3
