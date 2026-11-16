module

public import Section3.AlgebraicRVLifting
public import Section3.AlgebraicTransitivity
public import Section3.SortedFunctionClosure
public import Section3.TranscendenceDegrees

@[expose] public section

/- Component: AclRVImage -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Relative algebraic closure inside the ambient algebraically closed
VF field is algebraically closed. This uses the relative-closure instance,
not the unrelated constructed type `AlgebraicClosure`. -/
noncomputable instance vfAlgebraicClosureField_isAlgClosed (S : Set M) :
    IsAlgClosed (vfAlgebraicClosureField S) := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  exact IsAlgClosure.isAlgClosed (vfParameterField S)
    (K := algebraicClosure (vfParameterField S) (VFType (M := M)))

theorem vf_parameters_in_algebraicClosureField (S : Set M) (hS : ∀ a ∈ S, iVF a) :
    S ⊆ Subtype.val '' (vfAlgebraicClosureField S : Set (VFType (M := M))) := by
  intro a ha
  let x : VFType (M := M) := ⟨a,hS a ha⟩
  have hx : x ∈ vfParameterField S := Subfield.subset_closure ha
  have hd := vfParameterField_le_definableClosureField S hx
  exact ⟨x,vfDefinableClosureField_le_algebraicClosureField S hd,rfl⟩

theorem rv_algebraic_of_algebraic_lift (S : Set M) (x : VFType (M := M))
    (hx : AlgebraicAt S .vf x.val) : AlgebraicAt S .rv (CanonicalRV.encodedRv x).val := by
  have hd : DefinableClosureAt {x.val} .rv (CanonicalRV.encodedRv x).val :=
    definableClosureAt_function_symbol {x.val} Fn.rvMap (![x.val] : Fin 1 → M)
      (fun i => by fin_cases i; exact x.property)
      (fun i => by fin_cases i; exact definableClosureAt_of_mem (Set.mem_singleton x.val) x.property)
  apply hd.algebraic.eliminate_algebraic_params
  rintro a rfl
  exact ⟨.vf,hx⟩

theorem rv_algebraicClosure_iff_lift (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hS : ∀ a ∈ S, iVF a) (t : CanonicalRV.RVSort M) :
    AlgebraicAt S .rv t.val ↔
      ∃ x : vfAlgebraicClosureField S, CanonicalRV.encodedRv x.val = t := by
  constructor
  · exact algebraic_rv_lifts_algebraically_closed_subfield h00 (vfAlgebraicClosureField S) S
      (vf_parameters_in_algebraicClosureField S hS) t
  · rintro ⟨x,rfl⟩
    exact rv_algebraic_of_algebraic_lift S x.val ((mem_vfAlgebraicClosureField S x.val).mp x.property)

end SpecialTransformations.Section3
