import Section4.RVFiniteGradedRepresentatives

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open scoped BigOperators

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

def rvGradedBoundedPositive (S : Set M) (b : ℕ) : AddSubmonoid (RVGradedKPlus (M := M) S) where
  carrier := {x | ∀ k, b < k → x k = 0}
  zero_mem' := by intro k hk; rfl
  add_mem' := by
    intro x y hx hy k hk
    rw [DFinsupp.add_apply, hx k hk, hy k hk, zero_add]

theorem rvGradedBoundedPositive_mono {b c : ℕ} (hbc : b ≤ c) :
    rvGradedBoundedPositive (M := M) S b ≤ rvGradedBoundedPositive S c :=
  fun _ hx k hk => hx k (hbc.trans_lt hk)

theorem rvGradedBoundedPositive_of {k b : ℕ} (hkb : k ≤ b) (a : RVKPlus (M := M) S k) :
    DirectSum.of (RVKPlus S) k a ∈ rvGradedBoundedPositive S b := by
  intro j hj
  exact DirectSum.of_eq_of_ne k j a (Ne.symm (Nat.ne_of_lt (hkb.trans_lt hj)))

theorem rvGradedBoundedPositive_mul {b c : ℕ} {x y : RVGradedKPlus (M := M) S}
    (hx : x ∈ rvGradedBoundedPositive S b) (hy : y ∈ rvGradedBoundedPositive S c) :
    x * y ∈ rvGradedBoundedPositive S (b + c) := by
  rw [DirectSum.mul_eq_sum_support_ghas_mul]
  apply (rvGradedBoundedPositive S (b + c)).sum_mem
  intro ij hij
  have hxi : ij.1 ≤ b := by
    by_contra h
    exact (DFinsupp.mem_support_iff.mp (Finset.mem_product.mp hij).1)
      (hx ij.1 (Nat.lt_of_not_ge h))
  have hyj : ij.2 ≤ c := by
    by_contra h
    exact (DFinsupp.mem_support_iff.mp (Finset.mem_product.mp hij).2)
      (hy ij.2 (Nat.lt_of_not_ge h))
  exact rvGradedBoundedPositive_of (Nat.add_le_add hxi hyj) _

theorem rvGradedBoundedPositive_one :
    (1 : RVGradedKPlus (M := M) S) ∈ rvGradedBoundedPositive S 0 :=
  rvGradedBoundedPositive_of le_rfl (rvClass (rvUnitObject S))

theorem rvGradedBoundedPositive_exhaustive (x : RVGradedKPlus (M := M) S) :
    ∃ b, x ∈ rvGradedBoundedPositive S b := by
  refine ⟨x.support.sup id, ?_⟩
  intro k hk
  by_contra hn
  exact (not_le_of_gt hk) (Finset.le_sup (f := id) (DFinsupp.mem_support_iff.mpr hn))

theorem rvGradedFamilyClass_bounded_iff (U : RVGradedObject (M := M) S) (b : ℕ) :
    rvGradedFamilyClass U ∈ rvGradedBoundedPositive S b ↔
      ∀ k, b < k → (U.obj k).domain.carrier = ∅ := by
  constructor
  · intro h k hk
    apply (rvClass_eq_zero_iff _).mp
    simpa only [rvGradedFamilyClass_apply] using h k hk
  · intro h k hk
    rw [rvGradedFamilyClass_apply]
    exact (rvClass_eq_zero_iff _).mpr (h k hk)

def rvFiniteGradedBoundedPositive (S : Set M) (b : ℕ) :
    AddSubmonoid (RVFiniteGradedKPlus (M := M) S) :=
  (rvGradedBoundedPositive S b).comap rvFiniteGradedForget

theorem rvFiniteGradedBoundedPositive_mono {b c : ℕ} (hbc : b ≤ c) :
    rvFiniteGradedBoundedPositive (M := M) S b ≤ rvFiniteGradedBoundedPositive S c :=
  fun _ hx => rvGradedBoundedPositive_mono hbc hx

theorem rvFiniteGradedBoundedPositive_mul {b c : ℕ} {x y : RVFiniteGradedKPlus (M := M) S}
    (hx : x ∈ rvFiniteGradedBoundedPositive S b) (hy : y ∈ rvFiniteGradedBoundedPositive S c) :
    x * y ∈ rvFiniteGradedBoundedPositive S (b + c) := by
  change rvFiniteGradedForget (x * y) ∈ rvGradedBoundedPositive S (b + c)
  rw [rvFiniteGradedForget_mul]
  exact rvGradedBoundedPositive_mul hx hy

theorem rvFiniteGradedBoundedPositive_one :
    (1 : RVFiniteGradedKPlus (M := M) S) ∈ rvFiniteGradedBoundedPositive S 0 := by
  change rvFiniteGradedForget 1 ∈ rvGradedBoundedPositive S 0
  rw [rvFiniteGradedForget_one]
  exact rvGradedBoundedPositive_one

theorem rvFiniteGradedBoundedPositive_exhaustive (x : RVFiniteGradedKPlus (M := M) S) :
    ∃ b, x ∈ rvFiniteGradedBoundedPositive S b :=
  rvGradedBoundedPositive_exhaustive (rvFiniteGradedForget x)

theorem rvFiniteGradedFamilyClass_bounded_iff (U : RVFiniteGradedObject (M := M) S) (b : ℕ) :
    rvFiniteGradedFamilyClass U ∈ rvFiniteGradedBoundedPositive S b ↔
      ∀ k, b < k → (U.obj.obj k).domain.carrier = ∅ := by
  change rvFiniteGradedForget (rvFiniteGradedFamilyClass U) ∈ rvGradedBoundedPositive S b ↔ _
  rw [rvFiniteGradedFamilyClass_forget]
  exact rvGradedFamilyClass_bounded_iff U.obj b

end SpecialTransformations.Section4

end
