import Section3.VFDefinableClosure
import Section3.VFAlgebraicity
import Section3.FieldBase
import Section3.SubfieldTrdeg
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def vfAlgebraicClosureField (S : Set M) : Subfield (VFType (M := M)) :=
  (algebraicClosure (vfParameterField S) (VFType (M := M))).toSubfield

theorem mem_vfAlgebraicClosureField
    (S : Set M) (x : VFType (M := M)) :
    x ∈ vfAlgebraicClosureField S ↔ AlgebraicAt S .vf x.val :=
  (mem_algebraicClosure_iff).trans (algebraicAt_vf_iff_parameterField S x).symm

theorem vfDefinableClosureField_le_algebraicClosureField
    (S : Set M) :
    vfDefinableClosureField S ≤ vfAlgebraicClosureField S := by
  intro x hx
  exact (mem_vfAlgebraicClosureField S x).mpr hx.algebraic

theorem vfParameterField_le_dcl_union_rv
    (A B : Set M)
    (hB : ∀ b ∈ B, iRV b) :
    vfParameterField A ≤ vfDefinableClosureField (A ∪ B) := by
  rw [← vfParameterField_union_rv A B hB]
  exact vfParameterField_le_definableClosureField (A ∪ B)

theorem vfAlgebraicClosureField_algebraic_union_rv (A B : Set M)
    (hB : ∀ b ∈ B, iRV b) (x : VFType (M := M))
    (hx : x ∈ vfAlgebraicClosureField (A ∪ B)) : IsAlgebraic (vfParameterField A) x := by
  have h : IsAlgebraic (vfParameterField (A ∪ B)) x := mem_algebraicClosure_iff.mp hx
  rwa [vfParameterField_union_rv A B hB] at h

theorem VFFieldBase.le_parameterField_tuple (S : Set M) (F : VFFieldBase S)
    {n : ℕ} (a : Fin n → VFType (M := M)) :
    F.field ≤ vfParameterField (S ∪ Set.range (fun i => (a i).val)) := by
  intro x hx
  exact Subfield.subset_closure (Or.inl ((F.mem_iff x).mp hx))

/-- Corollary 3.4: the VF-generated field, the VF part of definable closure,
and the VF part of model-theoretic algebraic closure have the same
transcendence degree over VF(S). B is any RV parameter set. -/
theorem corollary_3_4
    (S : Set M) (F : VFFieldBase S) {n : ℕ} (a : Fin n → VFType (M := M))
    (B : Set M) (hB : ∀ b ∈ B, iRV b) :
    let A := S ∪ Set.range (fun i => (a i).val)
    let E := vfParameterField A
    let D := vfDefinableClosureField (A ∪ B)
    let C := vfAlgebraicClosureField (A ∪ B)
    let hSE := VFFieldBase.le_parameterField_tuple S F a
    let hED := vfParameterField_le_dcl_union_rv A B hB
    let hDC := vfDefinableClosureField_le_algebraicClosureField (A ∪ B)
    relativeTrdeg F.field E hSE = relativeTrdeg F.field D (hSE.trans hED) ∧
      relativeTrdeg F.field E hSE = relativeTrdeg F.field C (hSE.trans (hED.trans hDC)) := by
  let A := S ∪ Set.range (fun i => (a i).val)
  let E := vfParameterField A
  let D := vfDefinableClosureField (A ∪ B)
  let C := vfAlgebraicClosureField (A ∪ B)
  have hSE := VFFieldBase.le_parameterField_tuple S F a
  have hED := vfParameterField_le_dcl_union_rv A B hB
  have hDC := vfDefinableClosureField_le_algebraicClosureField (A ∪ B)
  change relativeTrdeg F.field E hSE = relativeTrdeg F.field D (hSE.trans hED) ∧
    relativeTrdeg F.field E hSE = relativeTrdeg F.field C (hSE.trans (hED.trans hDC))
  constructor
  · apply relativeTrdeg_eq_of_algebraic F.field E D hSE hED
    intro x hx
    exact vfAlgebraicClosureField_algebraic_union_rv A B hB x (hDC hx)
  · exact relativeTrdeg_eq_of_algebraic F.field E C hSE (hED.trans hDC)
      (vfAlgebraicClosureField_algebraic_union_rv A B hB)

end SpecialTransformations.Section3
