import Section3.AclFieldImages
import Section3.GammaBaseVFAlgebraicity
import Section3.GammaClosureLaws
import Section3.RVGammaAlgebraicity

/- Component: GeneratedBaseLifting -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem VFGeneratedBase.closure_eq_self {B : Base (M := M)} (hB : VFGeneratedBase B) :
    closureBase B = B := by
  obtain ⟨A,_,_,hgen⟩ := hB
  rw [← hgen,closureBase_idempotent]

theorem VFGammaGeneratedBase.closure_eq_self {B : Base (M := M)} (hB : VFGammaGeneratedBase B) :
    closureBase B = B := by
  obtain ⟨A,G,_,_,_,hgen⟩ := hB
  rw [← hgen,closureBase_idempotent]

theorem VFGeneratedBase.vfGammaGenerated {B : Base (M := M)} (hB : VFGeneratedBase B) :
    VFGammaGeneratedBase B := by
  obtain ⟨A,hAB,hA,hgen⟩ := hB
  exact ⟨A,∅,hAB,Set.empty_subset _,hA,hgen⟩

theorem vfGammaGenerated_closure (A : Set M) (hA : ∀ a ∈ A, iVF a)
    (G : Set (Values.Gamma (M := M))) :
    VFGammaGeneratedBase (closureBase (⟨A,G⟩ : Base (M := M))) :=
  ⟨A,G,(subset_closureBase (⟨A,G⟩ : Base (M := M))).1,
    (subset_closureBase (⟨A,G⟩ : Base (M := M))).2,hA,rfl⟩

theorem algebraic_vf_closure_generated_iff (A : Set M)
    (G : Set (Values.Gamma (M := M))) (b : VFType (M := M)) :
    AlgebraicAtBase (closureBase (⟨A,G⟩ : Base (M := M))) .vf b.val ↔
      AlgebraicAt A .vf b.val :=
  (AlgebraicAtBase.closureBase_iff _ .vf b.val).trans (algebraic_vf_iff_real _ b)

theorem algebraic_rv_closure_generated_iff {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (A : Set M)
    (hsmall : Cardinal.mk A < κ) (G : Set (Values.Gamma (M := M))) (b : M) :
    AlgebraicAtBase (closureBase (⟨A,G⟩ : Base (M := M))) .rv b ↔ AlgebraicAt A .rv b :=
  (AlgebraicAtBase.closureBase_iff _ .rv b).trans
    (algebraic_rv_gamma_base_iff hκ hs h00 ⟨A,G⟩ hsmall b)

/-- The RV-lifting input for general ball centers: Gamma-generated names
and the dcl generation step introduce no new RV algebraic elements. -/
theorem algebraic_rv_closure_generated_lifts {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (A : Set M) (hA : ∀ a ∈ A, iVF a) (hsmall : Cardinal.mk A < κ)
    (G : Set (Values.Gamma (M := M))) (t : CanonicalRV.RVSort M)
    (ht : AlgebraicAtBase (closureBase (⟨A,G⟩ : Base (M := M))) .rv t.val) :
    ∃ x : vfAlgebraicClosureField A, CanonicalRV.encodedRv x.val = t :=
  (rv_algebraicClosure_iff_lift h00 A hA t).mp
    ((algebraic_rv_closure_generated_iff hκ hs h00 A hsmall G t.val).mp ht)

end SpecialTransformations.Section3.GammaParameters
