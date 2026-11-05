import Section3.VFDefinableClosure
import Section3.FieldBase
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open scoped IntermediateField.algebraAdjoinAdjoin
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem VFFieldBase.parameterField_union_image (S : Set M) (F : VFFieldBase S)
    (X : Set (VFType (M := M))) :
    vfParameterField (S ∪ Subtype.val '' X) =
      (IntermediateField.adjoin F.field X).toSubfield := by
  unfold vfParameterField
  rw [IntermediateField.adjoin_toSubfield]
  congr 1
  ext x
  change (x.val ∈ S ∨ ∃ y ∈ X, y.val = x.val) ↔
    (∃ c : F.field, c.val = x) ∨ x ∈ X
  constructor
  · rintro (hx | ⟨y, hy, he⟩)
    · exact Or.inl ⟨⟨x, (F.mem_iff x).mpr hx⟩, rfl⟩
    · exact Or.inr ((Subtype.ext he : y = x) ▸ hy)
  · rintro (⟨c, rfl⟩ | hx)
    · exact Or.inl ((F.mem_iff c.val).mp c.property)
    · exact Or.inr ⟨x, hx, rfl⟩

theorem algebraicAt_vf_iff_matroid_closure
    (S : Set M) (F : VFFieldBase S)
    (X : Set (VFType (M := M))) (x : VFType (M := M)) :
    AlgebraicAt (S ∪ Subtype.val '' X) .vf x.val ↔
      x ∈ (AlgebraicIndependent.matroid F.field (VFType (M := M))).closure X := by
  rw [algebraicAt_vf_iff_parameterField, VFFieldBase.parameterField_union_image S F X,
    AlgebraicIndependent.matroid_closure_eq]
  change IsAlgebraic (IntermediateField.adjoin F.field X) x ↔
    IsAlgebraic (Algebra.adjoin F.field X) x
  constructor
  · exact fun h => h.restrictScalars (Algebra.adjoin F.field X)
  · exact fun h => h.extendScalars (FaithfulSMul.algebraMap_injective
      (Algebra.adjoin F.field X) (IntermediateField.adjoin F.field X))

/-- The VF exchange assertion in Lemma 3.6, over the original field base. -/
theorem lemma_3_6_vf
    (S : Set M) (F : VFFieldBase S) (a b : VFType (M := M))
    (hab : AlgebraicAt (insert b.val S) .vf a.val)
    (ha : ¬ AlgebraicAt S .vf a.val) : AlgebraicAt (insert a.val S) .vf b.val := by
  let N := AlgebraicIndependent.matroid F.field (VFType (M := M))
  have hab' : a ∈ N.closure {b} :=
    (algebraicAt_vf_iff_matroid_closure S F {b} a).mp (by simpa using hab)
  have ha' : a ∉ N.closure ∅ := by
    intro h
    have h' := (algebraicAt_vf_iff_matroid_closure S F ∅ a).mpr h
    exact ha (by simpa using h')
  have hb' := (N.closure_exchange (X := ∅) ⟨by simpa using hab', ha'⟩).1
  have h := (algebraicAt_vf_iff_matroid_closure S F {a} b).mpr (by simpa using hb')
  simpa using h

end SpecialTransformations.Section3
