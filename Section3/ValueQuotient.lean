module

public import CanonicalRV

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Values
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Equality of values, rather than equality of RV classes. -/
def sameValue (x y : CanonicalRV.RVSort M) : Prop := iLe x.val y.val ∧ iLe y.val x.val

def valueSetoid : Setoid (CanonicalRV.RVSort M) where
  r := sameValue
  iseqv := ⟨fun x => ⟨RVCalc.le_refl_rv hM x.property, RVCalc.le_refl_rv hM x.property⟩,
    fun h => ⟨h.2, h.1⟩,
    fun {x y z} hxy hyz =>
      ⟨RVCalc.le_trans_rv hM x.property y.property z.property hxy.1 hyz.1,
        RVCalc.le_trans_rv hM z.property y.property x.property hyz.2 hxy.2⟩⟩

/-- The actual imaginary quotient, including its one infinity class.
Ordered-group operations are not asserted by this definition alone. -/
def GammaTop := Quotient (valueSetoid (M := M))

def vrv (t : CanonicalRV.RVSort M) : GammaTop (M := M) := Quotient.mk _ t

def infinity : GammaTop (M := M) := vrv ⟨iRVZero, rv_zero_mem hM⟩

theorem vrv_eq_iff (x y : CanonicalRV.RVSort M) : vrv x = vrv y ↔ sameValue x y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem vrv_surjective : Function.Surjective (vrv (M := M)) := by
  intro γ
  refine Quotient.inductionOn γ ?_
  intro t
  exact ⟨t, rfl⟩

theorem vrv_eq_infinity_iff (t : CanonicalRV.RVSort M) :
    vrv t = infinity (M := M) ↔ t.val = iRVZero := by
  constructor
  · intro ht
    exact RVCalc.le_infty_eq hM t.property ((vrv_eq_iff t _).mp ht).2
  · intro ht
    have he : t = (⟨iRVZero, rv_zero_mem hM⟩ : CanonicalRV.RVSort M) := Subtype.ext ht
    exact congrArg vrv he

/-- The genuine value-group carrier excludes the absorbing infinity class. -/
def Gamma := {γ : GammaTop (M := M) // γ ≠ infinity}

theorem gamma_has_nonzero_representative (γ : Gamma (M := M)) :
    ∃ t : CanonicalRV.RVSort M, t.val ≠ iRVZero ∧ vrv t = γ.val := by
  obtain ⟨t, ht⟩ := vrv_surjective γ.val
  refine ⟨t, ?_, ht⟩
  intro hz
  exact γ.property (ht.symm.trans ((vrv_eq_infinity_iff t).mpr hz))

theorem vf_value_eq_iff {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (x y : VFType (M := M)) :
    vrv (CanonicalRV.encodedRv x) = vrv (CanonicalRV.encodedRv y) ↔ v x = v y := by
  rw [vrv_eq_iff]
  change (VFValued.predV y x ∧ VFValued.predV x y) ↔ v x = v y
  rw [hv, hv]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

end SpecialTransformations.Section3.Values
