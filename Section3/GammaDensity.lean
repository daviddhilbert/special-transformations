module

public import Section3.GammaValueLaws

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.Values
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

instance gammaDenselyOrdered : DenselyOrdered (Gamma (M := M)) where
  dense a b hab := by
    obtain ⟨δ,hδpow⟩ := gamma_pow_surjective 2 (by decide) (b/a)
    change δ^2 = b/a at hδpow
    have hδ : (1 : Gamma (M := M)) < δ :=
      (one_lt_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp (by rw [hδpow]; exact one_lt_div'.mpr hab)
    have hδsq : δ < δ^2 := by
      simpa only [mul_one,pow_two] using mul_lt_mul_right hδ δ
    refine ⟨a*δ,?_,?_⟩
    · simpa only [mul_one] using mul_lt_mul_right hδ a
    · calc
        a*δ < a*δ^2 := mul_lt_mul_right hδsq a
        _ = b := by rw [hδpow, ← mul_div_assoc, mul_div_cancel_left]

end SpecialTransformations.Section3.Values
