/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/ba6249a11b39e8e71fd0130ab0087e7185b95433/section%205/GammaQERVBasics.lean
Original declaration namespaces and notices are retained.
-/
import Section3.GuardedRationalNormalForm
import Section3.GammaDensity

/-! Actual RV arithmetic used in the Gamma graph perturbation argument.
All values and residue guards are those of the original language. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.GammaQE
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open CanonicalRV
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvGamma (t : RVSort M) (ht : t ≠ 0) : Values.Gamma (M := M) :=
  Values.gammaOf t (fun h => ht (Subtype.ext (h.trans RVOperations.zero_val.symm)))

theorem rvGamma_val (t : RVSort M) (ht : t ≠ 0) : (rvGamma t ht).val = Values.vrv t := rfl

theorem rv_inK_iff (t : RVSort M) : ValuedModelMap.inK t ↔ t = 0 ∨ Values.vrv t = 1 := by
  rw [RVOperations.inK_iff]
  have he : RVOperations.absoluteHom t = 1 ↔ Values.vrv t = 1 := by
    change Values.paperValueEquiv (Values.vrv t) = 1 ↔ _
    rw [← Values.paperValue_one]
    exact (Values.paperValueEquiv (M := M)).injective.eq_iff
  rw [he]

theorem gamma_val_zpow (x : Values.Gamma (M := M)) (p : ℤ) :
    (x ^ p).val = x.val ^ p := by
  have hn (n : ℕ) : (x ^ n).val = x.val ^ n := by
    induction n with
    | zero => simpa only [pow_zero] using (Values.gamma_val_one (M := M))
    | succ n ih => rw [pow_succ,Values.gamma_val_mul,ih,pow_succ]
  cases p with
  | ofNat n =>
    change (x ^ (n : ℤ)).val = x.val ^ (n : ℤ)
    rw [zpow_natCast,zpow_natCast]
    exact hn n
  | negSucc n => simp only [zpow_negSucc,Values.gamma_val_inv,hn]

theorem rv_value_zpow (t : RVSort M) (p : ℤ) :
    Values.vrv (t ^ p) = Values.vrv t ^ p := map_zpow₀ RVOperations.vrvHom t p

theorem rvGamma_one : rvGamma (1 : RVSort M) one_ne_zero = 1 := by
  apply Subtype.ext
  exact RVOperations.vrv_one

theorem rvGamma_mul (x y : RVSort M) (hx : x ≠ 0) (hy : y ≠ 0) :
    rvGamma (x*y) (mul_ne_zero hx hy) = rvGamma x hx * rvGamma y hy := by
  apply Subtype.ext
  exact RVOperations.vrv_mul x y

theorem rvGamma_inv (x : RVSort M) (hx : x ≠ 0) :
    rvGamma x⁻¹ (inv_ne_zero hx) = (rvGamma x hx)⁻¹ := by
  apply Subtype.ext
  exact map_inv₀ RVOperations.vrvHom x

theorem rvGamma_zpow (x : RVSort M) (hx : x ≠ 0) (p : ℤ) :
    rvGamma (x ^ p) (zpow_ne_zero p hx) = (rvGamma x hx)^p := by
  apply Subtype.ext
  rw [rvGamma_val,gamma_val_zpow,rvGamma_val]
  exact map_zpow₀ RVOperations.vrvHom x p

theorem rvGamma_eq_iff (x y : RVSort M) (hx : x ≠ 0) (hy : y ≠ 0) :
    rvGamma x hx = rvGamma y hy ↔ Values.vrv x = Values.vrv y := by
  rw [Subtype.ext_iff]
  rfl

theorem rvGamma_surjective (g : Values.Gamma (M := M)) :
    ∃ t : RVSort M, ∃ ht : t ≠ 0, rvGamma t ht = g := by
  obtain ⟨t,ht,hg⟩ := Values.gamma_has_nonzero_representative g
  refine ⟨t,fun he => ht (congrArg Subtype.val he |>.trans RVOperations.zero_val),?_⟩
  exact Subtype.ext hg

end DiamondIntegral.Section5.GammaQE
