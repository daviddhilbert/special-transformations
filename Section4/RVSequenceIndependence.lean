module

public import Section4.RVRank
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Ordered independence in the actual sorted algebraic closure. -/
def RVSequenceIndependent (S : Set M) : {n : ℕ} → (Fin n → CanonicalRV.RVSort M) → Prop
  | 0, _ => True
  | n + 1, t => RVSequenceIndependent S (Fin.init t) ∧
      ¬ AlgebraicAt (S ∪ Set.range (rvValues (Fin.init t))) .rv (t (Fin.last n)).val

theorem rv_sequence_closure_iff
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    (S : Set M) {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) (u : CanonicalRV.RVSort M) :
    u ∈ (rvAlgebraicMatroid hcan hex S).closure (Set.range t) ↔
      AlgebraicAt (S ∪ Set.range (rvValues t)) .rv u.val := by
  rw [rvAlgebraicMatroid_closure]
  change AlgebraicAt (S ∪ rvParameterNames (Set.range t)) .rv u.val ↔ _
  rw [rvParameterNames_range]

/-- Ordered independence agrees exactly with an injective enumeration of
an independent set in the genuine RV algebraic-closure matroid. -/
theorem rvSequenceIndependent_iff
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    (S : Set M) {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) :
    RVSequenceIndependent S t ↔ Function.Injective t ∧
      (rvAlgebraicMatroid hcan hex S).Indep (Set.range t) := by
  induction n with
  | zero =>
    have hrange : Set.range t = ∅ := by ext x; simp
    simp only [RVSequenceIndependent, true_iff, hrange]
    exact ⟨fun i => i.elim0, (rvAlgebraicMatroid hcan hex S).empty_indep⟩
  | succ n ih =>
    let N := rvAlgebraicMatroid hcan hex S
    have hrange : Set.range t = insert (t (Fin.last n)) (Set.range (Fin.init t)) := by
      rw [← Fin.snoc_init_self t, Fin.range_snoc, Fin.init_snoc, Fin.snoc_last]
    have hinj : Function.Injective t ↔ Function.Injective (Fin.init t) ∧
        t (Fin.last n) ∉ Set.range (Fin.init t) := by
      rw [← Fin.snoc_init_self t, Fin.snoc_injective_iff, Fin.init_snoc, Fin.snoc_last]
    change (RVSequenceIndependent S (Fin.init t) ∧
      ¬ AlgebraicAt (S ∪ Set.range (rvValues (Fin.init t))) .rv (t (Fin.last n)).val) ↔ _
    rw [ih]
    constructor
    · rintro ⟨⟨hi, hI⟩, hlast⟩
      have hnot : t (Fin.last n) ∉ N.closure (Set.range (Fin.init t)) :=
        fun h => hlast ((rv_sequence_closure_iff hcan hex S _ _).mp h)
      obtain ⟨hins, hnotin⟩ := (hI.notMem_closure_iff (by
        change t (Fin.last n) ∈ Set.univ
        exact Set.mem_univ _)).mp hnot
      refine ⟨hinj.mpr ⟨hi, hnotin⟩, ?_⟩
      rwa [hrange]
    · rintro ⟨hi, hI⟩
      obtain ⟨hipre, hnotin⟩ := hinj.mp hi
      have hIpre : N.Indep (Set.range (Fin.init t)) := hI.subset (by
        rintro _ ⟨i, rfl⟩
        exact ⟨i.castSucc, rfl⟩)
      refine ⟨⟨hipre, hIpre⟩, ?_⟩
      have hins : N.Indep (insert (t (Fin.last n)) (Set.range (Fin.init t))) := by
        rwa [← hrange]
      have hground : t (Fin.last n) ∈ N.E := by
        change t (Fin.last n) ∈ Set.univ
        exact Set.mem_univ _
      have hnot := (hIpre.notMem_closure_iff hground).mpr ⟨hins, hnotin⟩
      exact fun h => hnot ((rv_sequence_closure_iff hcan hex S _ _).mpr h)

end SpecialTransformations.Section4

end
