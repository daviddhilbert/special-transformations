import Section3.GammaBaseVFAlgebraicity
import Section3.GammaClosureLaws
import Section3.TranscendenceDegrees

/- Component: GammaDefinableClosureField -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem DefinableClosureAtBase.algebraic {B : Base (M := M)} {σ : SortTag} {b : M}
    (hb : DefinableClosureAtBase B σ b) : AlgebraicAtBase B σ b :=
  ⟨{b},hb,Set.finite_singleton b,Set.mem_singleton b⟩

theorem real_definable_eliminate_base {B : Base (M := M)} {S U : Set M} {σ : SortTag}
    (hU : DefinableAt S σ U)
    (hS : ∀ s ∈ S, ∃ τ, DefinableClosureAtBase B τ s) : DefinableAtBase B σ U := by
  have h := real_definableAtBase (⟨S,∅⟩ : Base (M := M)) σ U hU
  exact h.eliminate_definable_params hS (fun _ h => False.elim h)

theorem definableClosureAtBase_function_symbol (B : Base (M := M)) {k : ℕ} (f : Fn k)
    (xs : Fin k → M) (hs : ∀ i, sortEval (Fn.argSort f i) (xs i))
    (hd : ∀ i, DefinableClosureAtBase B (Fn.argSort f i) (xs i)) :
    DefinableClosureAtBase B (Fn.resSort f) (Structure.funMap (L := LRV) f xs) := by
  have h := definableClosureAt_function_symbol (Set.range xs) f xs hs
    (fun i => definableClosureAt_of_mem (Set.mem_range_self i) (hs i))
  apply real_definable_eliminate_base h
  rintro b ⟨i,rfl⟩
  exact ⟨Fn.argSort f i,hd i⟩

theorem definableClosureAtBase_vf_inv (B : Base (M := M)) (x : VFType (M := M))
    (hx : DefinableClosureAtBase B .vf x.val) : DefinableClosureAtBase B .vf (x⁻¹).val := by
  have h := definableClosureAt_vf_inv {x.val} x
    (definableClosureAt_of_mem (Set.mem_singleton x.val) x.property)
  apply real_definable_eliminate_base h
  rintro b rfl
  exact ⟨.vf,hx⟩

/-- The actual VF definable closure over a real/Gamma base. The field
operations are inherited from VF, not supplied as an extra closure premise. -/
noncomputable def vfDefinableClosureFieldBase (B : Base (M := M)) : Subfield (VFType (M := M)) where
  carrier := {x | DefinableClosureAtBase B .vf x.val}
  zero_mem' := definableClosureAtBase_function_symbol B Fn.vfZero Fin.elim0
    (fun i => i.elim0) (fun i => i.elim0)
  one_mem' := definableClosureAtBase_function_symbol B Fn.vfOne Fin.elim0
    (fun i => i.elim0) (fun i => i.elim0)
  add_mem' := by
    intro x y hx hy
    exact definableClosureAtBase_function_symbol B Fn.vfAdd ![x.val,y.val]
      (by intro i; fin_cases i; exact x.property; exact y.property)
      (by intro i; fin_cases i; exact hx; exact hy)
  mul_mem' := by
    intro x y hx hy
    exact definableClosureAtBase_function_symbol B Fn.vfMul ![x.val,y.val]
      (by intro i; fin_cases i; exact x.property; exact y.property)
      (by intro i; fin_cases i; exact hx; exact hy)
  neg_mem' := by
    intro x hx
    exact definableClosureAtBase_function_symbol B Fn.vfNeg ![x.val]
      (by intro i; fin_cases i; exact x.property)
      (by intro i; fin_cases i; exact hx)
  inv_mem' := definableClosureAtBase_vf_inv B

noncomputable def vfAlgebraicClosureFieldBase (B : Base (M := M)) : Subfield (VFType (M := M)) :=
  vfAlgebraicClosureField B.real

theorem mem_vfAlgebraicClosureFieldBase (B : Base (M := M)) (x : VFType (M := M)) :
    x ∈ vfAlgebraicClosureFieldBase B ↔ AlgebraicAtBase B .vf x.val :=
  (mem_vfAlgebraicClosureField B.real x).trans (algebraic_vf_iff_real B x).symm

theorem vfDefinableClosureFieldBase_le_algebraicClosureFieldBase (B : Base (M := M)) :
    vfDefinableClosureFieldBase B ≤ vfAlgebraicClosureFieldBase B := by
  intro x hx
  exact (mem_vfAlgebraicClosureFieldBase B x).mpr hx.algebraic

theorem vfParameterField_le_definableClosureFieldBase (B : Base (M := M)) :
    vfParameterField B.real ≤ vfDefinableClosureFieldBase B := by
  apply Subfield.closure_le.mpr
  intro x hx
  exact real_definableAtBase B .vf {x.val} (definableClosureAt_of_mem hx x.property)

theorem vfParameterField_le_dclBase_union_rv (A T : Set M) (hT : ∀ t ∈ T, iRV t)
    (G : Set (Values.Gamma (M := M))) :
    vfParameterField A ≤ vfDefinableClosureFieldBase (⟨A ∪ T,G⟩ : Base (M := M)) := by
  rw [← vfParameterField_union_rv A T hT]
  exact vfParameterField_le_definableClosureFieldBase (⟨A ∪ T,G⟩ : Base (M := M))

/-- Corollary3.4 over genuine Gamma-named bases. Both intermediate fields
are the actual VF parts of dcl and acl over that same base. -/
theorem corollary_3_4_gamma_base (B : Base (M := M)) (F : VFFieldBase B.real)
    {n : ℕ} (a : Fin n → VFType (M := M)) (T : Set M) (hT : ∀ t ∈ T, iRV t) :
    let A := B.real ∪ Set.range (fun i => (a i).val)
    let P : Base (M := M) := ⟨A ∪ T,B.gamma⟩
    let E := vfParameterField A
    let D := vfDefinableClosureFieldBase P
    let C := vfAlgebraicClosureFieldBase P
    let hSE := VFFieldBase.le_parameterField_tuple B.real F a
    let hED := vfParameterField_le_dclBase_union_rv A T hT B.gamma
    let hDC := vfDefinableClosureFieldBase_le_algebraicClosureFieldBase P
    relativeTrdeg F.field E hSE = relativeTrdeg F.field D (hSE.trans hED) ∧
      relativeTrdeg F.field E hSE = relativeTrdeg F.field C (hSE.trans (hED.trans hDC)) := by
  let A := B.real ∪ Set.range (fun i => (a i).val)
  let P : Base (M := M) := ⟨A ∪ T,B.gamma⟩
  let E := vfParameterField A
  let D := vfDefinableClosureFieldBase P
  let C := vfAlgebraicClosureFieldBase P
  have hSE := VFFieldBase.le_parameterField_tuple B.real F a
  have hED := vfParameterField_le_dclBase_union_rv A T hT B.gamma
  have hDC := vfDefinableClosureFieldBase_le_algebraicClosureFieldBase P
  have hAlg (x : VFType (M := M)) (hx : x ∈ C) : IsAlgebraic E x :=
    vfAlgebraicClosureField_algebraic_union_rv A T hT x hx
  change relativeTrdeg F.field E hSE = relativeTrdeg F.field D (hSE.trans hED) ∧
    relativeTrdeg F.field E hSE = relativeTrdeg F.field C (hSE.trans (hED.trans hDC))
  exact ⟨relativeTrdeg_eq_of_algebraic F.field E D hSE hED (fun x hx => hAlg x (hDC hx)),
    relativeTrdeg_eq_of_algebraic F.field E C hSE (hED.trans hDC) hAlg⟩

end SpecialTransformations.Section3.GammaParameters
