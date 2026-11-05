import Section3.GammaPresentation
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Values
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The zero of this group-with-zero is the paper's infinity. Its order
is reversed, so no ordered-group-with-zero instance asserting zero-minimality
is introduced. The transfer follows Mathlib's Apache-2.0 Equiv transfer
pattern in Algebra/GroupWithZero/TransferInstance.lean (Johannes Hoelzl)
and uses Algebra/GroupWithZero/InjSurj.lean. -/
noncomputable instance gammaTopGroup : CommGroupWithZero (GammaTop (M := M)) := by
  let e := paperValueEquiv (M := M)
  letI := e.zero
  letI := e.one
  letI := e.mul
  letI := e.Inv
  letI := e.div
  letI := e.pow ℕ
  letI := e.pow ℤ
  apply e.injective.commGroupWithZero e <;> intros <;> exact e.apply_symm_apply _

noncomputable instance gammaTopOrder : LinearOrder (GammaTop (M := M)) := by
  classical
  exact (paperValueEquiv (M := M)).linearOrder

theorem paperValue_zero : paperValueEquiv (M := M) 0 = 0 :=
  (paperValueEquiv (M := M)).apply_symm_apply _

theorem paperValue_one : paperValueEquiv (M := M) 1 = 1 :=
  (paperValueEquiv (M := M)).apply_symm_apply _

theorem paperValue_mul (x y : GammaTop (M := M)) :
    paperValueEquiv (x*y) = paperValueEquiv x * paperValueEquiv y :=
  (paperValueEquiv (M := M)).apply_symm_apply _

theorem paperValue_inv (x : GammaTop (M := M)) :
    paperValueEquiv x⁻¹ = (paperValueEquiv x)⁻¹ :=
  (paperValueEquiv (M := M)).apply_symm_apply _

theorem infinity_eq_zero : infinity (M := M) = (0 : GammaTop (M := M)) := by
  apply (paperValueEquiv (M := M)).injective
  rw [paperValue_zero]
  exact valueEquiv_infinity presentationValuation presentation_compatible

instance gammaTopIsOrderedMonoid : IsOrderedMonoid (GammaTop (M := M)) :=
  Function.Injective.isOrderedMonoid (paperValueEquiv (M := M)) paperValue_mul (fun {_ _} => Iff.rfl)

/-- Comparisons are exactly those of the frozen RV preorder. -/
theorem vrv_le_iff (t u : CanonicalRV.RVSort M) : vrv t ≤ vrv u ↔ iLe t.val u.val :=
  (valueEquiv_rv_le presentationValuation presentation_compatible t u).symm

/-- Multiplication descends from the actual RV multiplication, including
its one absorbing class. Internal presentation choices cannot change it. -/
theorem vrv_mul (t u : CanonicalRV.RVSort M) :
    vrv ⟨iRVMul t.val u.val,rv_mul_mem hM t.property u.property⟩ = vrv t * vrv u := by
  apply (paperValueEquiv (M := M)).injective
  rw [paperValue_mul]
  exact valueEquiv_rv_mul presentationValuation presentation_compatible t u

noncomputable def gammaTopUnitsEquiv : Gamma (M := M) ≃ (GammaTop (M := M))ˣ where
  toFun γ := Units.mk0 γ.val (fun h => γ.property (h.trans infinity_eq_zero.symm))
  invFun u := ⟨u.val,fun h => Units.ne_zero u (h.trans infinity_eq_zero)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Units.ext rfl

/-- Gamma inherits the reversed order on its actual non-infinity subtype. -/
noncomputable instance gammaOrder : LinearOrder (Gamma (M := M)) :=
  inferInstanceAs (LinearOrder {γ : GammaTop (M := M) // γ ≠ infinity})

noncomputable instance gammaGroup : CommGroup (Gamma (M := M)) :=
  (gammaTopUnitsEquiv (M := M)).commGroup

theorem gammaUnits_mul (x y : Gamma (M := M)) :
    gammaTopUnitsEquiv (x*y) = gammaTopUnitsEquiv x * gammaTopUnitsEquiv y :=
  (gammaTopUnitsEquiv (M := M)).apply_symm_apply _

theorem gamma_val_one : (1 : Gamma (M := M)).val = (1 : GammaTop (M := M)) := rfl

theorem gamma_val_mul (x y : Gamma (M := M)) : (x*y).val = x.val*y.val := rfl

theorem gamma_val_inv (x : Gamma (M := M)) : (x⁻¹).val = x.val⁻¹ := rfl

theorem gamma_le_iff (x y : Gamma (M := M)) :
    x ≤ y ↔ gammaTopUnitsEquiv x ≤ gammaTopUnitsEquiv y := Iff.rfl

instance gammaIsOrderedMonoid : IsOrderedMonoid (Gamma (M := M)) :=
  Function.Injective.isOrderedMonoid (gammaTopUnitsEquiv (M := M)) gammaUnits_mul
    (fun {_ _} => (gamma_le_iff _ _).symm)

end SpecialTransformations.Section3.Values
