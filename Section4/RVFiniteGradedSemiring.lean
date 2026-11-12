module

public import Section4.RVFiniteHomogeneousProducts

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

abbrev RVFiniteGradedKPlus (S : Set M) := DirectSum ℕ (RVFiniteKPlus (M := M) S)

def rvFiniteGradedForget : RVFiniteGradedKPlus (M := M) S →+ RVGradedKPlus (M := M) S :=
  DirectSum.map (fun _ => rvFiniteForgetKPlus)

theorem rvFiniteGradedForget_injective :
    Function.Injective (rvFiniteGradedForget (M := M) (S := S)) :=
  (DirectSum.map_injective (fun _ => rvFiniteForgetKPlus)).mpr
    (fun _ => rvFiniteForgetKPlus_injective)

@[simp] theorem rvFiniteGradedForget_one :
    rvFiniteGradedForget (1 : RVFiniteGradedKPlus (M := M) S) = 1 := by
  change DirectSum.map (fun _ => rvFiniteForgetKPlus)
    (DirectSum.of (RVFiniteKPlus S) 0 (rvFiniteClass (rvFiniteUnitObject S))) =
      DirectSum.of (RVKPlus S) 0 (rvClass (rvUnitObject S))
  rw [DirectSum.map_of, rvFiniteForgetKPlus_class]
  rfl

@[simp] theorem rvFiniteGradedForget_mul : ∀ a b : RVFiniteGradedKPlus (M := M) S,
    rvFiniteGradedForget (a * b) = rvFiniteGradedForget a * rvFiniteGradedForget b := by
  intro a b
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      change rvFiniteGradedForget (DirectSum.of (RVFiniteKPlus S) i a * DirectSum.of (RVFiniteKPlus S) j b) =
        rvFiniteGradedForget (DirectSum.of (RVFiniteKPlus S) i a) *
          rvFiniteGradedForget (DirectSum.of (RVFiniteKPlus S) j b)
      simp only [rvFiniteGradedForget, DirectSum.of_mul_of, DirectSum.map_of]
      exact congrArg (DirectSum.of (RVKPlus S) (i + j)) (rvFiniteClassMul_forget a b)
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

instance rvFiniteGradedKPlusCommMonoid : CommMonoid (RVFiniteGradedKPlus (M := M) S) where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := by
    apply rvFiniteGradedForget_injective
    simp only [rvFiniteGradedForget_mul, mul_assoc]
  one_mul a := by
    apply rvFiniteGradedForget_injective
    simp only [rvFiniteGradedForget_mul, rvFiniteGradedForget_one, one_mul]
  mul_one a := by
    apply rvFiniteGradedForget_injective
    simp only [rvFiniteGradedForget_mul, rvFiniteGradedForget_one, mul_one]
  mul_comm a b := by
    apply rvFiniteGradedForget_injective
    simp only [rvFiniteGradedForget_mul, mul_comm]

instance rvFiniteGradedKPlusCommSemiring : CommSemiring (RVFiniteGradedKPlus (M := M) S) where
  toAddCommMonoid := inferInstance
  toCommMonoid := inferInstance
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := mul_add
  right_distrib := add_mul
  natCast n := n • (1 : RVFiniteGradedKPlus S)
  natCast_zero := zero_nsmul _
  natCast_succ n := by simp only [succ_nsmul, one_nsmul]

def rvFiniteGradedForgetSemiring : RVFiniteGradedKPlus (M := M) S →+* RVGradedKPlus (M := M) S where
  __ := rvFiniteGradedForget
  map_one' := rvFiniteGradedForget_one
  map_mul' := rvFiniteGradedForget_mul

theorem rvFiniteGradedForgetSemiring_injective :
    Function.Injective (rvFiniteGradedForgetSemiring (M := M) (S := S)) :=
  rvFiniteGradedForget_injective

def rvFiniteGradedClass {k : ℕ} (U : RVFiniteObject (M := M) S k) : RVFiniteGradedKPlus (M := M) S :=
  DirectSum.of (RVFiniteKPlus S) k (rvFiniteClass U)

theorem rvFiniteGradedClass_product {k l : ℕ} (U : RVFiniteObject (M := M) S k)
    (V : RVFiniteObject (M := M) S l) :
    rvFiniteGradedClass (rvFiniteProductObject U V) = rvFiniteGradedClass U * rvFiniteGradedClass V := by
  rw [rvFiniteGradedClass, rvFiniteGradedClass, rvFiniteGradedClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (RVFiniteKPlus S) (k + l)) (rvFiniteClassMul_class U V).symm

end SpecialTransformations.Section4

end
