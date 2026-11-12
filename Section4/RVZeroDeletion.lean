module

public import Section4.RVPadding
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Set.Finite.Range

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M]

theorem rvWeight_le_arity {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) : rvWeight t ≤ n := by
  rw [rvWeight_eq_card]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_le Finset.univ (fun i : Fin n => (t i).val ≠ iRVZero))

theorem rvWeight_delete_zero {k : ℕ} (t : Fin (k + 1) → CanonicalRV.RVSort M)
    (i : Fin (k + 1)) (hi : (t i).val = iRVZero) :
    rvWeight (t ∘ i.succAbove) = rvWeight t := by
  symm
  unfold rvWeight
  rw [Fin.sum_univ_succAbove _ i]
  simp only [hi, ne_eq, not_true_eq_false, ↓reduceIte, zero_add, Function.comp_apply]

theorem rvWeight_le_pred_iff_zero {k : ℕ} (t : Fin (k + 1) → CanonicalRV.RVSort M) :
    rvWeight t ≤ k ↔ ∃ i, (t i).val = iRVZero := by
  constructor
  · intro h
    by_contra hn
    have hnonzero (i : Fin (k + 1)) : (t i).val ≠ iRVZero := fun hi => hn ⟨i, hi⟩
    have he : rvWeight t = k + 1 := by simp [rvWeight, hnonzero]
    rw [he] at h
    exact Nat.not_succ_le_self k h
  · rintro ⟨i, hi⟩
    rw [← rvWeight_delete_zero t i hi]
    exact rvWeight_le_arity _

/-- Delete one occurrence of the existing absorbing RV element. -/
def RVZeroDeletion {k : ℕ} (t : Fin (k + 1) → CanonicalRV.RVSort M)
    (u : Fin k → CanonicalRV.RVSort M) : Prop :=
  ∃ i : Fin (k + 1), (t i).val = iRVZero ∧ u = t ∘ i.succAbove

theorem RVZeroDeletion.weight {k : ℕ} {t : Fin (k + 1) → CanonicalRV.RVSort M}
    {u : Fin k → CanonicalRV.RVSort M} (h : RVZeroDeletion t u) : rvWeight u = rvWeight t := by
  obtain ⟨i, hi, rfl⟩ := h
  exact rvWeight_delete_zero t i hi

variable [hM : M ⊨ Axioms.ACVF]

/-- Every shorter label has only finitely many original labels obtained
by inserting a zero. This is the fibre bound needed for label compression. -/
theorem rvZeroDeletion_fibre_finite {k : ℕ} (u : Fin k → CanonicalRV.RVSort M) :
    {t | RVZeroDeletion t u}.Finite := by
  let z : CanonicalRV.RVSort M := ⟨iRVZero, rv_zero_mem hM⟩
  apply (Set.finite_range (fun i : Fin (k + 1) => Fin.insertNth i z u)).subset
  rintro t ⟨i, hi, hu⟩
  refine ⟨i, Fin.insertNth_eq_iff.mpr ⟨Subtype.ext hi.symm, ?_⟩⟩
  exact hu

end SpecialTransformations.Section4

end
