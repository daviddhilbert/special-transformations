/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/ba6249a11b39e8e71fd0130ab0087e7185b95433/section%205/GammaQEValueAlgebra.lean
Original declaration namespaces and notices are retained.
-/
import Section3.GammaQERVBasics

/-! Cancellation and residue-factor calculations for the actual RV
valuation. The reversed GammaTop order is retained throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5.GammaQE
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open CanonicalRV
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem gammaTop_mul_le_mul_iff (a b c : Values.GammaTop (M := M)) (hc : c ≠ 0) :
    a*c ≤ b*c ↔ a ≤ b := by
  constructor
  · intro h
    have he := mul_le_mul_right h c⁻¹
    simp only [mul_comm c⁻¹] at he
    simpa only [mul_assoc,mul_inv_cancel₀ hc,mul_one] using he
  · intro h
    simpa only [mul_comm c] using mul_le_mul_right h c

theorem rv_value_ne_zero (t : RVSort M) (ht : t ≠ 0) : Values.vrv t ≠ 0 := by
  intro h
  have hi : Values.vrv t = Values.infinity := h.trans Values.infinity_eq_zero.symm
  exact ht (Subtype.ext (((Values.vrv_eq_infinity_iff t).mp hi).trans RVOperations.zero_val.symm))

theorem rv_residue_value_one (t : RVSort M) (ht : t ≠ 0) (hK : ValuedModelMap.inK t) :
    Values.vrv t = 1 := ((rv_inK_iff t).mp hK).resolve_left ht

theorem scaled_residue_zero (a u t : RVSort M) (ht : t ≠ 0) (p : ℤ) :
    (a*t^p)*u = 0 ↔ a*u = 0 := by
  rw [mul_right_comm a (t^p) u,mul_eq_zero]
  simp only [zpow_ne_zero _ ht,or_false]

theorem scaled_residue_equality (a b u v t : RVSort M) (ht : t ≠ 0)
    (hu : ValuedModelMap.inK u) (hv : ValuedModelMap.inK v) (p q : ℤ)
    (hsep : a ≠ 0 → b ≠ 0 → Values.vrv a = Values.vrv b → p = q)
    (hsafe : Values.vrv (a*t^p) = Values.vrv (b*t^q) → Values.vrv a = Values.vrv b) :
    (a*t^p)*u = (b*t^q)*v ↔ a*u = b*v := by
  by_cases hpq : p = q
  · subst q
    rw [mul_right_comm a (t^p) u,mul_right_comm b (t^p) v]
    exact ⟨fun h => mul_right_cancel₀ (zpow_ne_zero _ ht) h,
      fun h => congrArg (fun w : RVSort M => w*t^p) h⟩
  · have hzl := scaled_residue_zero a u t ht p
    have hzr := scaled_residue_zero b v t ht q
    by_cases hA : a*u = 0
    · have hA' := hzl.mpr hA
      rw [hA',hA]
      exact (eq_comm.trans hzr).trans eq_comm
    · by_cases hB : b*v = 0
      · have hB' := hzr.mpr hB
        rw [hB',hB]
        exact hzl
      · have ha : a ≠ 0 := (mul_ne_zero_iff.mp hA).1
        have hb : b ≠ 0 := (mul_ne_zero_iff.mp hB).1
        have hu0 : u ≠ 0 := (mul_ne_zero_iff.mp hA).2
        have hv0 : v ≠ 0 := (mul_ne_zero_iff.mp hB).2
        have hu1 := rv_residue_value_one u hu0 hu
        have hv1 := rv_residue_value_one v hv0 hv
        have hn : ¬ a*u = b*v := by
          intro he
          have he' := congrArg Values.vrv he
          rw [RVOperations.vrv_mul,RVOperations.vrv_mul,hu1,hv1,mul_one,mul_one] at he'
          exact hpq (hsep ha hb he')
        have hn' : ¬ (a*t^p)*u = (b*t^q)*v := by
          intro he
          have he' : Values.vrv (a*t^p) = Values.vrv (b*t^q) := by
            simpa only [RVOperations.vrv_mul,hu1,hv1,mul_one] using congrArg Values.vrv he
          exact hpq (hsep ha hb (hsafe he'))
        exact iff_of_false hn' hn

theorem gammaTop_le_zero (a : Values.GammaTop (M := M)) : a ≤ 0 := by
  simpa only [Values.infinity_eq_zero] using Values.le_infinity a

theorem gammaTop_zero_le (a : Values.GammaTop (M := M)) : 0 ≤ a ↔ a = 0 :=
  ⟨fun h => le_antisymm (gammaTop_le_zero a) h,fun h => h ▸ le_rfl⟩

theorem scaled_value_order_zero (a b t : RVSort M) (ht : t ≠ 0) (p q : ℤ)
    (hz : a = 0 ∨ b = 0) :
    (Values.vrv (a*t^p) ≤ Values.vrv (b*t^q) ↔ Values.vrv a ≤ Values.vrv b) := by
  rcases hz with rfl | rfl
  · simp only [zero_mul,RVOperations.vrv_zero,gammaTop_zero_le,
      RVOperations.vrv_mul,mul_eq_zero,rv_value_zpow]
    simp only [zpow_ne_zero _ (rv_value_ne_zero t ht),or_false]
  · simp only [zero_mul,RVOperations.vrv_zero]
    exact iff_of_true (gammaTop_le_zero _) (gammaTop_le_zero _)

end DiamondIntegral.Section5.GammaQE
