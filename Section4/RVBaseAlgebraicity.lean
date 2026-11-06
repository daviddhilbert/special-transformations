import Section4.RVRank

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rvAlgebraicClosure_subset_of_algebraic_base {S T : Set M}
    (hT : T ⊆ algebraicClosureSet S) (X : Set (CanonicalRV.RVSort M)) :
    rvAlgebraicClosure T X ⊆ rvAlgebraicClosure S X := by
  intro t ht
  apply ht.eliminate_algebraic_params
  rintro b (hb | hb)
  · obtain ⟨σ, hσ⟩ := hT hb
    exact ⟨σ, hσ.mono Set.subset_union_left⟩
  · exact subset_algebraicClosureSet (S ∪ rvParameterNames X) (Or.inr hb)

/-- Mutually algebraic parameter sets induce exactly the same RV matroid.
This is algebraic-parameter elimination, not arbitrary parameter invariance
of the dimension of a definable set. -/
theorem rvAlgebraicMatroid_eq_of_mutually_algebraic
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {S T : Set M} (hST : S ⊆ algebraicClosureSet T) (hTS : T ⊆ algebraicClosureSet S) :
    rvAlgebraicMatroid hcan hex S = rvAlgebraicMatroid hcan hex T := by
  apply Matroid.ext_closure
  intro X
  rw [rvAlgebraicMatroid_closure, rvAlgebraicMatroid_closure]
  exact (rvAlgebraicClosure_subset_of_algebraic_base hST X).antisymm
    (rvAlgebraicClosure_subset_of_algebraic_base hTS X)

theorem rvTupleRank_eq_of_mutually_algebraic
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {S T : Set M} (hST : S ⊆ algebraicClosureSet T) (hTS : T ⊆ algebraicClosureSet S)
    {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) :
    rvTupleRank hcan hex S t = rvTupleRank hcan hex T t := by
  unfold rvTupleRank rvTupleERank
  rw [rvAlgebraicMatroid_eq_of_mutually_algebraic hcan hex hST hTS]

end SpecialTransformations.Section4

end
