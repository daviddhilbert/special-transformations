module

public import Section3.VFAclField
public import Section3.RootDefinability

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The standing convention after Definition 2.4 that the VF part of S is
a field, stated separately from the genuine saturation assumptions. -/
structure VFFieldBase (S : Set M) where
  field : Subfield (VFType (M := M))
  mem_iff : ∀ x : VFType (M := M), x ∈ field ↔ x.val ∈ S

noncomputable def vfFieldOfInverseClosed (S : LRV.Substructure M)
    (hinv : ∀ x : VFType (M := M), x.val ∈ S → (x⁻¹).val ∈ S) :
    Subfield (VFType (M := M)) where
  carrier := {x | x.val ∈ S}
  zero_mem' := S.fun_mem Fn.vfZero Fin.elim0 (fun i => i.elim0)
  one_mem' := S.fun_mem Fn.vfOne Fin.elim0 (fun i => i.elim0)
  add_mem' := by
    intro x y hx hy
    exact S.fun_mem Fn.vfAdd ![x.val, y.val]
      (by intro i; fin_cases i; exact hx; exact hy)
  mul_mem' := by
    intro x y hx hy
    exact S.fun_mem Fn.vfMul ![x.val, y.val]
      (by intro i; fin_cases i; exact hx; exact hy)
  neg_mem' := by
    intro x hx
    exact S.fun_mem Fn.vfNeg ![x.val] (by intro i; fin_cases i; exact hx)
  inv_mem' := hinv

noncomputable def VFFieldBase.ofSubstructure (S : LRV.Substructure M)
    (hinv : ∀ x : VFType (M := M), x.val ∈ S → (x⁻¹).val ∈ S) :
    VFFieldBase (S : Set M) := ⟨vfFieldOfInverseClosed S hinv, fun _ => Iff.rfl⟩

theorem VFFieldBase.algebraicAt_iff (S : Set M) (F : VFFieldBase S)
    (b : VFType (M := M)) : AlgebraicAt S .vf b.val ↔ IsAlgebraic F.field b := by
  constructor
  · exact algebraicAt_vf_isAlgebraic S F.field (fun x hx => (F.mem_iff x).mpr hx) b
  · exact PolynomialRoots.algebraicAt_of_isAlgebraic_named S F.field
      (fun x => (F.mem_iff x.val).mp x.property) b

end SpecialTransformations.Section3