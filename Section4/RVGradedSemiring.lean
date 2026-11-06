import Section4.RVHomogeneousProducts
import Mathlib.Algebra.DirectSum.Ring

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

instance rvKPlusGNonUnitalNonAssocSemiring : DirectSum.GNonUnitalNonAssocSemiring (RVKPlus (M := M) S) where
  mul_zero := rvClassMul_zero
  zero_mul := rvClassMul_zero_left
  mul_add := rvClassMul_add
  add_mul := rvClassMul_add_left

instance rvKPlusGSemiring : DirectSum.GSemiring (RVKPlus (M := M) S) where
  natCast n := n • rvClass (rvUnitObject S)
  natCast_zero := zero_nsmul _
  natCast_succ n := by
    simp only [succ_nsmul, one_nsmul]
    rfl

instance rvKPlusGCommSemiring : DirectSum.GCommSemiring (RVKPlus (M := M) S) where

/-- Finite sums of the genuine positive RV scissors in all degrees,
with multiplication induced by the actual cartesian RV product. -/
abbrev RVGradedKPlus (S : Set M) := DirectSum ℕ (RVKPlus (M := M) S)

def rvGradedClass {k : ℕ} (U : RVObject (M := M) S k) : RVGradedKPlus (M := M) S :=
  DirectSum.of (RVKPlus S) k (rvClass U)

theorem rvGradedClass_product {k l : ℕ} (U : RVObject (M := M) S k)
    (V : RVObject (M := M) S l) :
    rvGradedClass (rvProductObject U V) = rvGradedClass U * rvGradedClass V := by
  rw [rvGradedClass, rvGradedClass, rvGradedClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (RVKPlus S) (k + l)) (rvClassMul_class U V).symm

theorem rvGradedClass_coprod {k : ℕ} (U V : RVObject (M := M) S k) :
    rvGradedClass (rvCoprodObject U V) = rvGradedClass U + rvGradedClass V := by
  change DirectSum.of (RVKPlus S) k (rvClass (rvCoprodObject U V)) = _
  rw [rvClass_coprod, map_add]
  rfl

theorem rvGradedClass_unit : rvGradedClass (rvUnitObject (M := M) S) = 1 := rfl

end SpecialTransformations.Section4

end
