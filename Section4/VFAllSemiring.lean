import Section4.VFProductDistributivity

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

def vfAllRepresentative (a : VFAllKPlus (M := M) S) : VFAllObject (M := M) S :=
  Classical.choose (vfAllClass_surjective a)

@[simp] theorem vfAllRepresentative_class (a : VFAllKPlus (M := M) S) :
    vfAllClass (vfAllRepresentative a) = a := Classical.choose_spec (vfAllClass_surjective a)

instance vfAllKPlusMul : Mul (VFAllKPlus (M := M) S) :=
  ⟨fun a b => vfAllClass (vfAllProductObject (vfAllRepresentative a) (vfAllRepresentative b))⟩

instance vfAllKPlusOne : One (VFAllKPlus (M := M) S) := ⟨vfAllClass (vfAllUnitObject S)⟩

/-- Multiplication of the actual positive classes is cartesian product,
independently of the representative chosen to define the operation. -/
@[simp] theorem vfAllClass_mul (U V : VFAllObject (M := M) S) :
    vfAllClass U * vfAllClass V = vfAllClass (vfAllProductObject U V) := by
  obtain ⟨e⟩ := vfAllClass_eq_iff_iso.mp (vfAllRepresentative_class (vfAllClass U))
  obtain ⟨d⟩ := vfAllClass_eq_iff_iso.mp (vfAllRepresentative_class (vfAllClass V))
  exact vfAllClass_iso (vfAllProductIso e d)

@[simp] theorem vfAllClass_unit : vfAllClass (vfAllUnitObject (M := M) S) = 1 := rfl

instance vfAllKPlusCommMonoid : CommMonoid (VFAllKPlus (M := M) S) where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := by
    obtain ⟨U, rfl⟩ := vfAllClass_surjective a
    obtain ⟨V, rfl⟩ := vfAllClass_surjective b
    obtain ⟨W, rfl⟩ := vfAllClass_surjective c
    rw [vfAllClass_mul, vfAllClass_mul, vfAllClass_mul, vfAllClass_mul]
    exact vfAllClass_iso (vfAllProductAssocIso U V W)
  one_mul a := by
    obtain ⟨U, rfl⟩ := vfAllClass_surjective a
    change vfAllClass (vfAllUnitObject S) * vfAllClass U = vfAllClass U
    rw [vfAllClass_mul]
    exact vfAllClass_iso (vfAllProductLeftUnitIso U)
  mul_one a := by
    obtain ⟨U, rfl⟩ := vfAllClass_surjective a
    change vfAllClass U * vfAllClass (vfAllUnitObject S) = vfAllClass U
    rw [vfAllClass_mul]
    exact vfAllClass_iso (vfAllProductRightUnitIso U)
  mul_comm a b := by
    obtain ⟨U, rfl⟩ := vfAllClass_surjective a
    obtain ⟨V, rfl⟩ := vfAllClass_surjective b
    rw [vfAllClass_mul, vfAllClass_mul]
    exact vfAllClass_iso (vfAllProductCommIso U V)

theorem vfAllKPlus_mul_zero (a : VFAllKPlus (M := M) S) : a * 0 = 0 := by
  obtain ⟨U, rfl⟩ := vfAllClass_surjective a
  rw [← vfAllClass_empty (M := M) (S := S), vfAllClass_mul]
  exact vfAllClass_iso (vfAllProductEmptyIso U)

theorem vfAllKPlus_left_distrib (a b c : VFAllKPlus (M := M) S) : a * (b + c) = a * b + a * c := by
  obtain ⟨U, rfl⟩ := vfAllClass_surjective a
  obtain ⟨V, rfl⟩ := vfAllClass_surjective b
  obtain ⟨W, rfl⟩ := vfAllClass_surjective c
  rw [← vfAllClass_coprod V W, vfAllClass_mul, vfAllClass_mul, vfAllClass_mul,
    ← vfAllClass_coprod]
  exact vfAllClass_iso (vfAllRightDistribIso U V W)

/-- The semiring laws follow from the actual definable product, unit,
empty-set and distributivity isomorphisms, after the additive scissors. -/
instance vfAllKPlusCommSemiring : CommSemiring (VFAllKPlus (M := M) S) where
  toAddCommMonoid := inferInstance
  toCommMonoid := inferInstance
  zero_mul a := by rw [mul_comm, vfAllKPlus_mul_zero]
  mul_zero := vfAllKPlus_mul_zero
  left_distrib := vfAllKPlus_left_distrib
  right_distrib a b c := by
    rw [mul_comm _ c, vfAllKPlus_left_distrib, mul_comm c a, mul_comm c b]
  natCast n := n • (1 : VFAllKPlus (M := M) S)
  natCast_zero := zero_nsmul _
  natCast_succ n := by simp only [succ_nsmul, one_nsmul]

end SpecialTransformations.Section4

end
