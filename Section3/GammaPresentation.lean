module

public import Section3.GammaValueEquiv

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Values
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- An internal compatible valuation presentation. This makes no choice
of RV representatives as parameters and does not extend the base S. -/
noncomputable def presentationType : Type := Classical.choose (VFValued.exists_valuation_predV (M := M))

noncomputable instance presentationOrder : LinearOrderedCommGroupWithZero (presentationType (M := M)) :=
  Classical.choose (Classical.choose_spec (VFValued.exists_valuation_predV (M := M)))

noncomputable def presentationValuation : Valuation (VFType (M := M)) (presentationType (M := M)) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (VFValued.exists_valuation_predV (M := M))))

theorem presentation_compatible (x y : VFType (M := M)) :
    VFValued.predV x y ↔ presentationValuation x ≤ presentationValuation y :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (VFValued.exists_valuation_predV (M := M)))) x y

noncomputable def paperValueEquiv : GammaTop (M := M) ≃
    OrderDual (MonoidWithZeroHom.ValueGroup₀ (.ofClass (presentationValuation (M := M)))) :=
  valueEquiv presentationValuation presentation_compatible

noncomputable def paperGammaEquiv : Gamma (M := M) ≃
    OrderDual ((MonoidWithZeroHom.ValueGroup₀ (.ofClass (presentationValuation (M := M))))ˣ) :=
  gammaUnitsEquiv presentationValuation presentation_compatible

end SpecialTransformations.Section3.Values
