module

public import Section4.ResidueAlgebraicityReverse
public import Section4.RVRank
public import Section4.TupleIndependence

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))

theorem residue_trdeg_le_rvTupleRank (B : LRV.Substructure M) {n : ℕ}
    (a : Fin n → ModelResidue M) :
    relativeTrdeg (residueParameterField B) (tupleField (residueParameterField B) a)
      (le_tupleField _ _) ≤ (rvTupleRank hcan hex (B : Set M) (residueRV ∘ a) : Cardinal) := by
  obtain ⟨v, hv⟩ := exists_rv_coordinate_basis hcan hex (B : Set M) (residueRV ∘ a)
  apply tupleField_trdeg_le_of_isAlgebraic (residueParameterField B) a (a ∘ v)
  intro j
  apply residue_isAlgebraic_over_tuple B (a ∘ v) (a j)
  exact hv j

theorem residue_rvTupleRank_le_of_trdeg_le (B : LRV.Substructure M) {n k : ℕ}
    (a : Fin n → ModelResidue M)
    (hdeg : relativeTrdeg (residueParameterField B) (tupleField (residueParameterField B) a)
      (le_tupleField _ _) ≤ (k : Cardinal)) :
    rvTupleRank hcan hex (B : Set M) (residueRV ∘ a) ≤ k := by
  obtain ⟨d, hd, v, hv⟩ := exists_algebraic_coordinate_basis (residueParameterField B) a hdeg
  have h := rvTupleRank_le_of_algebraic hcan hex (B : Set M)
    (residueRV ∘ (a ∘ v)) (residueRV ∘ a) (fun j =>
      (residue_algebraicAt_iff_isAlgebraic hcan B (a ∘ v) (a j)).mpr (hv j))
  exact (h.trans (rvTupleRank_le_arity hcan hex _ _)).trans hd

/-- The genuine RV algebraic-closure rank of a residue tuple equals its
ordinary field transcendence degree over the actual residue base field. -/
theorem residue_trdeg_eq_rvTupleRank (B : LRV.Substructure M) {n : ℕ}
    (a : Fin n → ModelResidue M) :
    relativeTrdeg (residueParameterField B) (tupleField (residueParameterField B) a)
      (le_tupleField _ _) = (rvTupleRank hcan hex (B : Set M) (residueRV ∘ a) : Cardinal) := by
  apply le_antisymm (residue_trdeg_le_rvTupleRank hcan hex B a)
  obtain ⟨d, hd, he⟩ := Cardinal.exists_nat_eq_of_le_nat
    (tupleField_trdeg_le (residueParameterField B) a)
  have hr := residue_rvTupleRank_le_of_trdeg_le hcan hex B a he.le
  rw [he]
  exact_mod_cast hr

theorem residue_independent_iff_rvTupleRank_eq_arity (B : LRV.Substructure M) {n : ℕ}
    (a : Fin n → ModelResidue M) :
    AlgebraicIndependent (residueParameterField B) a ↔
      rvTupleRank hcan hex (B : Set M) (residueRV ∘ a) = n := by
  rw [← tupleField_trdeg_eq_arity_iff, residue_trdeg_eq_rvTupleRank hcan hex]
  exact_mod_cast (Iff.rfl :
    rvTupleRank hcan hex (B : Set M) (residueRV ∘ a) = n ↔
      rvTupleRank hcan hex (B : Set M) (residueRV ∘ a) = n)

end SpecialTransformations.Section4.ResiduePurity

end
