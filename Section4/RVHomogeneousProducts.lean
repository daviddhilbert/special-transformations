import Section4.RVClassReindexing
import Section4.RVProductSymmetry
import Section4.RVProductAssociativity
import Section4.RVProductUnits
import Section4.RVProductDistributivity
import Mathlib.Algebra.GradedMonoid

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

def rvClassRepresentative {k : ℕ} (a : RVKPlus (M := M) S k) : RVObject (M := M) S k :=
  Classical.choose (rvClass_surjective a)

@[simp] theorem rvClassRepresentative_class {k : ℕ} (a : RVKPlus (M := M) S k) :
    rvClass (rvClassRepresentative a) = a := Classical.choose_spec (rvClass_surjective a)

def rvClassMul {k l : ℕ} (a : RVKPlus (M := M) S k) (b : RVKPlus (M := M) S l) :
    RVKPlus (M := M) S (k + l) :=
  rvClass (rvProductObject (rvClassRepresentative a) (rvClassRepresentative b))

@[simp] theorem rvClassMul_class {k l : ℕ} (U : RVObject (M := M) S k)
    (V : RVObject (M := M) S l) :
    rvClassMul (rvClass U) (rvClass V) = rvClass (rvProductObject U V) := by
  obtain ⟨e⟩ := rvClass_eq_iff_iso.mp (rvClassRepresentative_class (rvClass U))
  obtain ⟨d⟩ := rvClass_eq_iff_iso.mp (rvClassRepresentative_class (rvClass V))
  exact rvClass_iso (rvProductIso e d)

def rvKPlusCast {k l : ℕ} (h : k = l) (a : RVKPlus (M := M) S k) : RVKPlus (M := M) S l := h ▸ a

theorem rvKPlusCast_add {k l : ℕ} (h : k = l) (a b : RVKPlus (M := M) S k) :
    rvKPlusCast h (a + b) = rvKPlusCast h a + rvKPlusCast h b := by
  cases h
  rfl

theorem rvClassMul_comm_cast {k l : ℕ} (a : RVKPlus (M := M) S k) (b : RVKPlus (M := M) S l) :
    rvKPlusCast (Nat.add_comm l k) (rvClassMul b a) = rvClassMul a b := by
  obtain ⟨U, rfl⟩ := rvClass_surjective a
  obtain ⟨V, rfl⟩ := rvClass_surjective b
  rw [rvClassMul_class, rvClassMul_class]
  exact (rvClass_cast_reindex (Nat.add_comm l k) (rvProductObject V U) finAddFlip).trans
    (rvClass_iso (rvProductCommReindexedIso U V)).symm

theorem rvClass_heq_of_reindexedIso {k l : ℕ} (h : k = l)
    (U : RVObject (M := M) S k) (V : RVObject (M := M) S l)
    (e : Fin k ≃ Fin l) (hi : U ≅ V.reindexVolume e) : HEq (rvClass U) (rvClass V) := by
  have hc : (h.symm ▸ rvClass V) = rvClass U :=
    (rvClass_cast_reindex h.symm V e).trans (rvClass_iso hi).symm
  have hh : HEq (h.symm ▸ rvClass V) (rvClass V) := by cases h; rfl
  exact (heq_of_eq hc.symm).trans hh

instance rvKPlusGMul : GradedMonoid.GMul (RVKPlus (M := M) S) := ⟨rvClassMul⟩

instance rvKPlusGOne : GradedMonoid.GOne (RVKPlus (M := M) S) := ⟨rvClass (rvUnitObject S)⟩

theorem rvHomogeneous_mul_comm (a b : GradedMonoid (RVKPlus (M := M) S)) : a * b = b * a := by
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  obtain ⟨U, rfl⟩ := rvClass_surjective a
  obtain ⟨V, rfl⟩ := rvClass_surjective b
  change (⟨k + l, rvClassMul (rvClass U) (rvClass V)⟩ : GradedMonoid (RVKPlus S)) =
    ⟨l + k, rvClassMul (rvClass V) (rvClass U)⟩
  rw [rvClassMul_class, rvClassMul_class]
  exact Sigma.ext (Nat.add_comm k l)
    (rvClass_heq_of_reindexedIso (Nat.add_comm k l) _ _ finAddFlip (rvProductCommReindexedIso U V))

theorem rvHomogeneous_mul_one (a : GradedMonoid (RVKPlus (M := M) S)) : a * 1 = a := by
  obtain ⟨k, a⟩ := a
  obtain ⟨U, rfl⟩ := rvClass_surjective a
  change (⟨k + 0, rvClassMul (rvClass U) (rvClass (rvUnitObject S))⟩ :
    GradedMonoid (RVKPlus S)) = ⟨k, rvClass U⟩
  rw [rvClassMul_class]
  exact Sigma.ext (Nat.add_zero k) (heq_of_eq (rvClass_iso (rvProductRightUnitIso U)))

theorem rvHomogeneous_mul_assoc (a b c : GradedMonoid (RVKPlus (M := M) S)) :
    a * b * c = a * (b * c) := by
  obtain ⟨k, a⟩ := a
  obtain ⟨l, b⟩ := b
  obtain ⟨j, c⟩ := c
  obtain ⟨U, rfl⟩ := rvClass_surjective a
  obtain ⟨V, rfl⟩ := rvClass_surjective b
  obtain ⟨W, rfl⟩ := rvClass_surjective c
  change (⟨(k + l) + j, rvClassMul (rvClassMul (rvClass U) (rvClass V)) (rvClass W)⟩ :
    GradedMonoid (RVKPlus S)) =
      ⟨k + (l + j), rvClassMul (rvClass U) (rvClassMul (rvClass V) (rvClass W))⟩
  rw [rvClassMul_class, rvClassMul_class, rvClassMul_class, rvClassMul_class]
  exact Sigma.ext (Nat.add_assoc k l j)
    (rvClass_heq_of_reindexedIso (Nat.add_assoc k l j) _ _ (finCongr (Nat.add_assoc k l j))
      (rvProductAssocReindexedIso U V W))

instance rvKPlusGCommMonoid : GradedMonoid.GCommMonoid (RVKPlus (M := M) S) where
  toGMul := inferInstance
  toGOne := inferInstance
  one_mul a := by rw [rvHomogeneous_mul_comm, rvHomogeneous_mul_one]
  mul_one := rvHomogeneous_mul_one
  mul_assoc := rvHomogeneous_mul_assoc
  mul_comm := rvHomogeneous_mul_comm

theorem rvClassMul_zero {k l : ℕ} (a : RVKPlus (M := M) S k) :
    rvClassMul a (0 : RVKPlus S l) = 0 := by
  obtain ⟨U, rfl⟩ := rvClass_surjective a
  rw [← rvClass_empty (M := M) (S := S) (k := l), rvClassMul_class]
  exact (rvClass_iso (rvProductEmptyIso (l := l) U)).trans rvClass_empty

theorem rvClassMul_zero_left {k l : ℕ} (b : RVKPlus (M := M) S l) :
    rvClassMul (0 : RVKPlus S k) b = 0 := by
  obtain ⟨V, rfl⟩ := rvClass_surjective b
  rw [← rvClass_empty (M := M) (S := S) (k := k), rvClassMul_class]
  exact (rvClass_iso (rvEmptyProductIso (k := k) V)).trans rvClass_empty

theorem rvClassMul_add {k l : ℕ} (a : RVKPlus (M := M) S k) (b c : RVKPlus S l) :
    rvClassMul a (b + c) = rvClassMul a b + rvClassMul a c := by
  obtain ⟨U, rfl⟩ := rvClass_surjective a
  obtain ⟨V, rfl⟩ := rvClass_surjective b
  obtain ⟨W, rfl⟩ := rvClass_surjective c
  rw [← rvClass_coprod V W, rvClassMul_class, rvClassMul_class, rvClassMul_class,
    ← rvClass_coprod]
  exact rvClass_iso (rvProductRightDistribIso U V W)

theorem rvClassMul_add_left {k l : ℕ} (a b : RVKPlus (M := M) S k) (c : RVKPlus S l) :
    rvClassMul (a + b) c = rvClassMul a c + rvClassMul b c := by
  rw [← rvClassMul_comm_cast (a + b) c, rvClassMul_add, rvKPlusCast_add,
    rvClassMul_comm_cast, rvClassMul_comm_cast]

end SpecialTransformations.Section4

end
