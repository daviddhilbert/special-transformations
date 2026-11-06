import Section6.AlignedComparison
import Mathlib.Data.Fintype.EquivFin

/-! Reindex a finite sorted context by its VF and RV coordinates,
including empty sorts. This is syntax-only and preserves the sort of
every original variable. -/

noncomputable section
open Classical
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.FiniteSortContext

variable {I : Type}

abbrev VFPart (s : I → SortTag) := {i // s i = .vf}
abbrev RVPart (s : I → SortTag) := {i // s i = .rv}

def partition (s : I → SortTag) : I ≃ VFPart s ⊕ RVPart s where
  toFun i := match h : s i with
    | .vf => .inl ⟨i, h⟩
    | .rv => .inr ⟨i, h⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv i := by dsimp only; split <;> rfl
  right_inv j := by
    rcases j with ⟨i, hi⟩ | ⟨i, hi⟩
    · dsimp only
      split
      · rfl
      · rename_i h
        have h' : s i = .rv := h
        cases hi.symm.trans h'
    · dsimp only
      split
      · rename_i h
        have h' : s i = .vf := h
        cases hi.symm.trans h'
      · rfl

def vfCount [Finite I] (s : I → SortTag) : ℕ := @Fintype.card (VFPart s) (Fintype.ofFinite _)
def rvCount [Finite I] (s : I → SortTag) : ℕ := @Fintype.card (RVPart s) (Fintype.ofFinite _)

def reindex [Finite I] (s : I → SortTag) :
    I ≃ AlignedComparison.Context (vfCount s) (rvCount s) := by
  letI := Fintype.ofFinite (VFPart s)
  letI := Fintype.ofFinite (RVPart s)
  exact (partition s).trans
    (((Fintype.equivFin (VFPart s)).sumCongr (Fintype.equivFin (RVPart s))).trans
      ((Equiv.refl _).sumCongr (Equiv.sumEmpty _ Empty).symm))

theorem reindex_sort [Finite I] (s : I → SortTag) (i : I) :
    AlignedComparison.sorts (reindex s i) = s i := by
  obtain ⟨j, rfl⟩ := (partition s).symm.surjective i
  simp only [reindex, Equiv.trans_apply, Equiv.apply_symm_apply]
  cases j with
  | inl j => exact j.property.symm
  | inr j => exact j.property.symm

end SpecialTransformations.Section6.FiniteSortContext
