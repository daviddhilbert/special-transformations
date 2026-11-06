import CanonicalCountable
import Section3.SmallFiniteParameters
import Mathlib.ModelTheory.Substructures

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M]

/-- Closing a small parameter set under the actual countable LRV language
preserves smallness below an uncountable saturation cardinal. -/
theorem small_generated_substructure {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (S : Set M) (hS : Cardinal.mk S < κ) :
    Cardinal.mk (Substructure.closure LRV S) < κ := by
  letI : Countable (Σ i, LRV.Functions i) :=
    Function.Injective.countable
      (show Function.Injective (Sum.inl : (Σ i, LRV.Functions i) → LRV.Symbols) from
        Sum.inl_injective)
  have hfun : Cardinal.mk (Σ i, LRV.Functions i) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have hbound : Cardinal.mk (Substructure.closure LRV S) ≤
      max Cardinal.aleph0 (Cardinal.mk S + Cardinal.mk (Σ i, LRV.Functions i)) := by
    simpa only [Cardinal.lift_id] using
      (Substructure.lift_card_closure_le (L := LRV) (s := S))
  exact hbound.trans_lt (max_lt hκ
    (Cardinal.add_lt_of_lt hκ.le hS (hfun.trans_lt hκ)))

theorem small_generated_finite_extension {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    (F : Set M) (hF : F.Finite) :
    Cardinal.mk (Substructure.closure LRV ((B : Set M) ∪ F)) < κ :=
  small_generated_substructure hκ _ (small_union_finite hκ.le _ hB F hF)

end SpecialTransformations.Section4
