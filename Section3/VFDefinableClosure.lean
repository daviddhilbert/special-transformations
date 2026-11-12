module

public import Section3.SortedInverseClosure
public import Section3.DefinableConstants
public import Section3.ClosureBridge
public import Section3.RootDefinability
public import Section3.VFAlgebraicity

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem definableClosureAt_iff_raw (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (σ : SortTag) (x : M) :
    DefinableClosureAt S σ x ↔ S.Definable₁ LRV {x} ∧ sortEval σ x := by
  constructor
  · intro h
    exact ⟨h.raw_definable, h.algebraic.sorted⟩
  · rintro ⟨h, hx⟩
    apply raw_definable_sorted hc S {x} σ h
    rintro y rfl
    exact hx

theorem AlgebraicAt.eliminate_definable_params
    (hc : CanonicalStructure.IsCanonical (M := M)) {S B : Set M} {σ : SortTag} {x : M}
    (hB : ∀ b ∈ B, S.Definable₁ LRV {b}) (hx : AlgebraicAt B σ x) :
    AlgebraicAt S σ x := by
  obtain ⟨s, hs, hf, hxs⟩ := hx
  have hraw := DefinableConstants.eliminate_parameters {y : Fin 1 → M | y 0 ∈ s}
    hB hs.raw_definable
  exact ⟨s, raw_definable_sorted hc S s σ hraw hs.2, hf, hxs⟩

/-- The VF part of sorted definable closure, for an arbitrary ACVF model. -/
noncomputable def vfDefinableClosureField (S : Set M) : Subfield (VFType (M := M)) where
  carrier := {x | DefinableClosureAt S .vf x.val}
  zero_mem' := definableClosureAt_function_symbol S Fn.vfZero Fin.elim0
    (fun i => i.elim0) (fun i => i.elim0)
  one_mem' := definableClosureAt_function_symbol S Fn.vfOne Fin.elim0
    (fun i => i.elim0) (fun i => i.elim0)
  add_mem' := by
    intro x y hx hy
    exact definableClosureAt_function_symbol S Fn.vfAdd ![x.val, y.val]
      (by intro i; fin_cases i; exact x.property; exact y.property)
      (by intro i; fin_cases i; exact hx; exact hy)
  mul_mem' := by
    intro x y hx hy
    exact definableClosureAt_function_symbol S Fn.vfMul ![x.val, y.val]
      (by intro i; fin_cases i; exact x.property; exact y.property)
      (by intro i; fin_cases i; exact hx; exact hy)
  neg_mem' := by
    intro x hx
    exact definableClosureAt_function_symbol S Fn.vfNeg ![x.val]
      (by intro i; fin_cases i; exact x.property)
      (by intro i; fin_cases i; exact hx)
  inv_mem' := definableClosureAt_vf_inv S

theorem vfParameterField_le_definableClosureField (S : Set M) :
    vfParameterField S ≤ vfDefinableClosureField S := by
  apply Subfield.closure_le.mpr
  intro x hx
  exact definableClosureAt_of_mem hx x.property

/-- VF model-theoretic algebraicity is exactly algebraicity over the generated
VF parameter field, with no canonical-totalization restriction. -/
theorem algebraicAt_vf_iff_parameterField (S : Set M) (b : VFType (M := M)) :
    AlgebraicAt S .vf b.val ↔ IsAlgebraic (vfParameterField S) b := by
  constructor
  · exact algebraicAt_vf_parameterField S b
  · intro hb
    let D : Set M := {x | DefinableClosureAt S .vf x}
    have hE (x : vfParameterField S) : x.val.val ∈ D :=
      vfParameterField_le_definableClosureField S x.property
    have halg := PolynomialRoots.algebraicAt_of_isAlgebraic_named D
      (vfParameterField S) hE b hb
    exact halg.eliminate_sorted_definable_params (fun x hx => ⟨.vf, hx⟩)

end SpecialTransformations.Section3
