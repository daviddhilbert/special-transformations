import Section4.RVProjectionScissors
import Section4.RVRelabelIso

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem rvPadding_label_has_zero (S : Set M) (t : DefSet.univ (rawRVSpace (M := M) k) S) :
    (rvPadding S t).val ∈ (lowZeroLabels S k).carrier := by
  refine ⟨Fin.last k, ?_⟩
  change (padRV t.val (Fin.last k)).val = iRVZero
  rw [padRV, Fin.snoc_last]

def rvCompressedPaddingMap (S : Set M) (k : ℕ) :
    Map (DefSet.univ (rawRVSpace (M := M) k) S) (DefSet.univ (rawRVSpace k) S) :=
  (labelCompressionOver S k).comp ((rvPadding S).corestrict (rvPadding_label_has_zero S))

theorem rvCompressedPaddingMap_finite (S : Set M) (k : ℕ) :
    (rvCompressedPaddingMap (M := M) S k).FiniteFibres :=
  (labelCompressionOver_finite S k).comp
    (Map.finiteFibres_of_injective
      (Map.corestrict_injective (rvPadding_injective S) (rvPadding_label_has_zero S)))

theorem rvCompressedPaddingMap_weight (S : Set M) (k : ℕ)
    (t : DefSet.univ (rawRVSpace (M := M) k) S) :
    rvWeight (rvCompressedPaddingMap S k t).val = rvWeight t.val := by
  have h : rvWeight (rvCompressedPaddingMap S k t).val = rvWeight (padRV t.val) :=
    labelCompression_weight ⟨padRV t.val, rvPadding_label_has_zero S t⟩
  exact h.trans (rvWeight_padRV t.val)

def rvWeightProjection_pad_iso (U : RVObject (M := M) S k) :
    rvWeightProjection (rvPadObject U) ≅ U := by
  let c := rvCompressedPaddingMap (M := M) S k
  have hcarrier : (rvWeightProjection (rvPadObject U)).domain.carrier = U.domain.carrier := by
    apply Set.Subset.antisymm (rvLowDomain_subset (rvPadObject U))
    intro x hx
    apply (mem_rvLowDomain (rvPadObject U) ⟨x, hx⟩).mpr
    rw [rvPadObject_value, rvWeight_padRV]
    exact rvWeight_le_arity _
  have e : rvWeightProjection (rvPadObject U) ≅ U.relabel c :=
    rvIsoOfCarrierEq _ _ _ _ hcarrier (fun _ => rfl)
  exact e.trans (rvRelabelIso U c (rvCompressedPaddingMap_finite S k)
    (rvCompressedPaddingMap_weight S k)).symm

/-- The weight projection is a left inverse on the actual positive scissor
quotient. This includes all scissor relations, without cancellation. -/
theorem rvWeightProjectionKPlus_comp_padding :
    (rvWeightProjectionKPlus (M := M) (S := S) (k := k)).comp rvPaddingKPlus =
      AddMonoidHom.id (RVKPlus (M := M) S k) := by
  apply PositiveAdditiveGrothendieck.hom_ext (rvScissorPresentation S k)
  intro U
  change rvWeightProjectionKPlus (rvPaddingKPlus (rvClass U)) = rvClass U
  rw [rvPaddingKPlus_class, rvWeightProjectionKPlus_class]
  exact rvClass_iso (rvWeightProjection_pad_iso U)

/-- The final injectivity assertion of Section 4.3, after imposing the
actual geometric scissor relations. -/
theorem rvPaddingKPlus_injective :
    Function.Injective (rvPaddingKPlus (M := M) (S := S) (k := k)) := by
  apply Function.LeftInverse.injective (f := rvPaddingKPlus) (g := rvWeightProjectionKPlus)
  intro z
  exact congrArg (fun f : RVKPlus (M := M) S k →+ RVKPlus S k => f z)
    rvWeightProjectionKPlus_comp_padding

end SpecialTransformations.Section4

end
