module

public import Section3.BallGeometry

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Balls
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Notation 2.9: apply rv to VF coordinates and keep RV coordinates fixed. -/
def mixedRV {n m : ℕ} (p : (Fin n → VF M) × (Fin m → RV M)) :
    (Fin n → RV M) × (Fin m → RV M) := (tupleRV p.1, p.2)

@[simp] theorem mixedRV_vf {n m : ℕ} (a : Fin n → VF M) (t : Fin m → RV M)
    (i : Fin n) : ((mixedRV (a, t)).1 i).val = iRv (a i).val := rfl

@[simp] theorem mixedRV_rv {n m : ℕ} (a : Fin n → VF M) (t : Fin m → RV M) :
    (mixedRV (a, t)).2 = t := rfl

/-- Notation 2.9: rv inverse notation fixes the given VF coordinates and
replaces each RV coordinate by its entire VF fibre. -/
def mixedRVFibre {n m : ℕ} (a : Fin n → VF M) (t : Fin m → RV M) :
    Set ((Fin n → VF M) × (Fin m → VF M)) :=
  {p | p.1 = a ∧ ∀ j, p.2 j ∈ rvFibre (t j)}

omit hM in
@[simp] theorem mem_mixedRVFibre {n m : ℕ} (a : Fin n → VF M) (t : Fin m → RV M)
    (p : (Fin n → VF M) × (Fin m → VF M)) :
    p ∈ mixedRVFibre a t ↔ p.1 = a ∧ ∀ j, iRv (p.2 j).val = (t j).val := Iff.rfl

theorem mixedRVFibre_nonempty {n m : ℕ} (a : Fin n → VF M) (t : Fin m → RV M) :
    (mixedRVFibre a t).Nonempty := by
  have h (j : Fin m) : ∃ x : VF M, iRv x.val = (t j).val := by
    obtain ⟨x, hx⟩ := CanonicalRV.encodedRv_surjective (t j)
    exact ⟨x, congrArg Subtype.val hx⟩
  choose x hx using h
  exact ⟨(a, x), rfl, hx⟩

theorem mixedRVFibre_zero_coordinate {n m : ℕ} (a : Fin n → VF M) (t : Fin m → RV M)
    (j : Fin m) (hj : (t j).val = iRVZero)
    (p : (Fin n → VF M) × (Fin m → VF M)) (hp : p ∈ mixedRVFibre a t) :
    p.2 j = 0 := by
  have h := hp.2 j
  rw [rvFibre_zero (t j) hj] at h
  exact h

end SpecialTransformations.Section3.Balls
