module

public import Section4.VFFinitePositiveComparison
public import Section4.VFAllSemiring
public import Section4.VFProducts

@[expose] public section

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

def vfFiniteRepresentative (a : VFFiniteKPlus (M := M) S) : VFFiniteAllObject (M := M) S :=
  Classical.choose (vfFiniteClass_surjective a)

@[simp] theorem vfFiniteRepresentative_class (a : VFFiniteKPlus (M := M) S) :
    vfFiniteClass (vfFiniteRepresentative a) = a := Classical.choose_spec (vfFiniteClass_surjective a)

def vfFiniteUnitObject (S : Set M) : VFFiniteAllObject (M := M) S :=
  ⟨vfAllUnitObject S, by
    intro a
    apply Set.Subsingleton.finite
    intro t ht u hu
    apply funext
    intro i
    exact i.elim0⟩

instance vfFiniteKPlusMul : Mul (VFFiniteKPlus (M := M) S) :=
  ⟨fun a b => vfFiniteClass
    (vfFiniteAllProductObject (vfFiniteRepresentative a) (vfFiniteRepresentative b))⟩

instance vfFiniteKPlusOne : One (VFFiniteKPlus (M := M) S) :=
  ⟨vfFiniteClass (vfFiniteUnitObject S)⟩

@[simp] theorem vfFiniteClass_mul (U V : VFFiniteAllObject (M := M) S) :
    vfFiniteClass U * vfFiniteClass V = vfFiniteClass (vfFiniteAllProductObject U V) := by
  obtain ⟨e⟩ := vfFiniteClass_eq_iff_iso.mp (vfFiniteRepresentative_class (vfFiniteClass U))
  obtain ⟨d⟩ := vfFiniteClass_eq_iff_iso.mp (vfFiniteRepresentative_class (vfFiniteClass V))
  exact vfFiniteClass_iso (vfFiniteAllIsoOfAmbient
    (vfAllProductIso ((vfFiniteProperty S).ι.mapIso e) ((vfFiniteProperty S).ι.mapIso d)))

@[simp] theorem vfFiniteForgetKPlus_mul (a b : VFFiniteKPlus (M := M) S) :
    vfFiniteForgetKPlus (a * b) = vfFiniteForgetKPlus a * vfFiniteForgetKPlus b := by
  obtain ⟨U, rfl⟩ := vfFiniteClass_surjective a
  obtain ⟨V, rfl⟩ := vfFiniteClass_surjective b
  rw [vfFiniteClass_mul, vfFiniteForgetKPlus_class, vfFiniteForgetKPlus_class,
    vfFiniteForgetKPlus_class, vfAllClass_mul]
  rfl

@[simp] theorem vfFiniteForgetKPlus_one :
    vfFiniteForgetKPlus (1 : VFFiniteKPlus (M := M) S) = 1 :=
  vfFiniteForgetKPlus_class (vfFiniteUnitObject S)

instance vfFiniteKPlusCommMonoid : CommMonoid (VFFiniteKPlus (M := M) S) where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := by
    apply vfFiniteForgetKPlus_injective
    simp only [vfFiniteForgetKPlus_mul, mul_assoc]
  one_mul a := by
    apply vfFiniteForgetKPlus_injective
    simp only [vfFiniteForgetKPlus_mul, vfFiniteForgetKPlus_one, one_mul]
  mul_one a := by
    apply vfFiniteForgetKPlus_injective
    simp only [vfFiniteForgetKPlus_mul, vfFiniteForgetKPlus_one, mul_one]
  mul_comm a b := by
    apply vfFiniteForgetKPlus_injective
    simp only [vfFiniteForgetKPlus_mul, mul_comm]

instance vfFiniteKPlusCommSemiring : CommSemiring (VFFiniteKPlus (M := M) S) where
  toAddCommMonoid := inferInstance
  toCommMonoid := inferInstance
  zero_mul a := by
    apply vfFiniteForgetKPlus_injective
    simp only [vfFiniteForgetKPlus_mul, map_zero, zero_mul]
  mul_zero a := by
    apply vfFiniteForgetKPlus_injective
    simp only [vfFiniteForgetKPlus_mul, map_zero, mul_zero]
  left_distrib a b c := by
    apply vfFiniteForgetKPlus_injective
    simp only [vfFiniteForgetKPlus_mul, map_add, left_distrib]
  right_distrib a b c := by
    apply vfFiniteForgetKPlus_injective
    simp only [vfFiniteForgetKPlus_mul, map_add, right_distrib]
  natCast n := n • (1 : VFFiniteKPlus (M := M) S)
  natCast_zero := zero_nsmul _
  natCast_succ n := by simp only [succ_nsmul, one_nsmul]

def vfFiniteForgetSemiring : VFFiniteKPlus (M := M) S →+* VFAllKPlus (M := M) S where
  __ := vfFiniteForgetKPlus
  map_one' := vfFiniteForgetKPlus_one
  map_mul' := vfFiniteForgetKPlus_mul

theorem vfFiniteForgetSemiring_injective :
    Function.Injective (vfFiniteForgetSemiring (M := M) (S := S)) := vfFiniteForgetKPlus_injective

end SpecialTransformations.Section4

end
