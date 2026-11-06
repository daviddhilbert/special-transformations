import Section4.RVGradedSemiring
import Section4.RVFinitePositiveComparison

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

def rvFiniteProductObject {k l : ℕ} (U : RVFiniteObject (M := M) S k)
    (V : RVFiniteObject (M := M) S l) : RVFiniteObject (M := M) S (k + l) :=
  ⟨rvProductObject U.obj V.obj, rvProductObject_finite_volume U.obj V.obj U.property V.property⟩

def rvFiniteUnitObject (S : Set M) : RVFiniteObject (M := M) S 0 :=
  ⟨rvUnitObject S, rvUnitObject_finite_volume S⟩

def rvFiniteClassRepresentative {k : ℕ} (a : RVFiniteKPlus (M := M) S k) :
    RVFiniteObject (M := M) S k := Classical.choose (rvFiniteClass_surjective a)

@[simp] theorem rvFiniteClassRepresentative_class {k : ℕ} (a : RVFiniteKPlus (M := M) S k) :
    rvFiniteClass (rvFiniteClassRepresentative a) = a := Classical.choose_spec (rvFiniteClass_surjective a)

def rvFiniteClassMul {k l : ℕ} (a : RVFiniteKPlus (M := M) S k) (b : RVFiniteKPlus S l) :
    RVFiniteKPlus (M := M) S (k + l) :=
  rvFiniteClass (rvFiniteProductObject (rvFiniteClassRepresentative a) (rvFiniteClassRepresentative b))

@[simp] theorem rvFiniteClassMul_forget {k l : ℕ} (a : RVFiniteKPlus (M := M) S k)
    (b : RVFiniteKPlus S l) :
    rvFiniteForgetKPlus (rvFiniteClassMul a b) =
      rvClassMul (rvFiniteForgetKPlus a) (rvFiniteForgetKPlus b) := by
  have ha : rvClass (rvFiniteClassRepresentative a).obj = rvFiniteForgetKPlus a := by
    rw [← rvFiniteForgetKPlus_class, rvFiniteClassRepresentative_class]
  have hb : rvClass (rvFiniteClassRepresentative b).obj = rvFiniteForgetKPlus b := by
    rw [← rvFiniteForgetKPlus_class, rvFiniteClassRepresentative_class]
  change rvFiniteForgetKPlus (rvFiniteClass
    (rvFiniteProductObject (rvFiniteClassRepresentative a) (rvFiniteClassRepresentative b))) = _
  rw [rvFiniteForgetKPlus_class, ← ha, ← hb, rvClassMul_class]
  rfl

@[simp] theorem rvFiniteClassMul_class {k l : ℕ} (U : RVFiniteObject (M := M) S k)
    (V : RVFiniteObject (M := M) S l) :
    rvFiniteClassMul (rvFiniteClass U) (rvFiniteClass V) = rvFiniteClass (rvFiniteProductObject U V) := by
  apply rvFiniteForgetKPlus_injective
  rw [rvFiniteClassMul_forget, rvFiniteForgetKPlus_class, rvFiniteForgetKPlus_class,
    rvFiniteForgetKPlus_class, rvClassMul_class]
  rfl

instance rvFiniteKPlusGMul : GradedMonoid.GMul (RVFiniteKPlus (M := M) S) := ⟨rvFiniteClassMul⟩

instance rvFiniteKPlusGOne : GradedMonoid.GOne (RVFiniteKPlus (M := M) S) :=
  ⟨rvFiniteClass (rvFiniteUnitObject S)⟩

instance rvFiniteKPlusGNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring (RVFiniteKPlus (M := M) S) where
  mul_zero a := by
    change rvFiniteClassMul a 0 = 0
    apply rvFiniteForgetKPlus_injective
    simp only [rvFiniteClassMul_forget, map_zero, rvClassMul_zero]
  zero_mul b := by
    change rvFiniteClassMul 0 b = 0
    apply rvFiniteForgetKPlus_injective
    simp only [rvFiniteClassMul_forget, map_zero, rvClassMul_zero_left]
  mul_add a b c := by
    change rvFiniteClassMul a (b + c) = rvFiniteClassMul a b + rvFiniteClassMul a c
    apply rvFiniteForgetKPlus_injective
    simp only [rvFiniteClassMul_forget, map_add, rvClassMul_add]
  add_mul a b c := by
    change rvFiniteClassMul (a + b) c = rvFiniteClassMul a c + rvFiniteClassMul b c
    apply rvFiniteForgetKPlus_injective
    simp only [rvFiniteClassMul_forget, map_add, rvClassMul_add_left]

end SpecialTransformations.Section4

end
