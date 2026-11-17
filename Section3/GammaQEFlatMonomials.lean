module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/ba6249a11b39e8e71fd0130ab0087e7185b95433/section%205/GammaQEFlatMonomials.lean
Original declaration namespaces and notices are retained.
-/
public import Section3.GammaQERVBasics

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Every flat original-language RV monomial scales by one integer
power when the second RV coordinate is multiplied. Its value has the
corresponding fixed rational-affine exponent data. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.GammaQE
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open CanonicalRV GuardedRVNormalForm
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {I R : Type}
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def perturbRV (x : Fin 2 → RVSort M) (t : RVSort M) : Fin 2 → RVSort M :=
  ![x 0,x 1 * t]

def flatCoefficient (P : Monomial I R (Fin 2)) (a : I → VFType (M := M))
    (r : R → RVSort M) : RVSort M :=
  RVOperations.rvHom (P.numerator.realize a) / RVOperations.rvHom (P.denominator.realize a) *
    P.coefficient.prod (fun i n => r i ^ n)

theorem flat_rawEval (P : Monomial I R (Fin 2)) (a : I → VFType (M := M))
    (r : R → RVSort M) (x : Fin 2 → RVSort M) :
    P.rawEval a r x = flatCoefficient P a r * (x 0)^P.powers 0 * (x 1)^P.powers 1 := by
  have he := P.powers.prod_fintype (fun i n => x i ^ n) (fun i => zpow_zero (x i))
  rw [Monomial.rawEval,he,Fin.prod_univ_two]
  exact (mul_assoc _ _ _).symm

theorem flat_rawEval_perturb (P : Monomial I R (Fin 2)) (a : I → VFType (M := M))
    (r : R → RVSort M) (x : Fin 2 → RVSort M) (t : RVSort M) :
    P.rawEval a r (perturbRV x t) = P.rawEval a r x * t ^ P.powers 1 := by
  rw [flat_rawEval,flat_rawEval]
  simp only [perturbRV,Matrix.cons_val_zero,Matrix.cons_val_one,mul_zpow]
  exact (mul_assoc _ _ _).symm

theorem flat_rawEval_ne_zero (P : Monomial I R (Fin 2)) (a : I → VFType (M := M))
    (r : R → RVSort M) (x : Fin 2 → RVSort M) (hx : ∀ i,x i ≠ 0) :
    P.rawEval a r x ≠ 0 ↔ flatCoefficient P a r ≠ 0 := by
  constructor
  · intro h hz
    apply h
    rw [flat_rawEval,hz,zero_mul,zero_mul]
  · intro hc
    rw [flat_rawEval]
    exact mul_ne_zero (mul_ne_zero hc (zpow_ne_zero _ (hx 0))) (zpow_ne_zero _ (hx 1))

def flatValue (P : Monomial I R (Fin 2)) (a : I → VFType (M := M))
    (r : R → RVSort M) (hc : flatCoefficient P a r ≠ 0)
    (x y : Values.Gamma (M := M)) : Values.Gamma (M := M) :=
  rvGamma (flatCoefficient P a r) hc * x ^ P.powers 0 * y ^ P.powers 1

theorem flat_value (P : Monomial I R (Fin 2)) (a : I → VFType (M := M))
    (r : R → RVSort M) (hc : flatCoefficient P a r ≠ 0)
    (x : Fin 2 → RVSort M) (hx : ∀ i,x i ≠ 0) :
    rvGamma (P.rawEval a r x) ((flat_rawEval_ne_zero P a r x hx).mpr hc) =
      flatValue P a r hc (rvGamma (x 0) (hx 0)) (rvGamma (x 1) (hx 1)) := by
  apply Subtype.ext
  rw [rvGamma_val,flat_rawEval]
  simp only [RVOperations.vrv_mul,rv_value_zpow,flatValue,
    Values.gamma_val_mul,gamma_val_zpow,rvGamma_val]

end DiamondIntegral.Section5.GammaQE
