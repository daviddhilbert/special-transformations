import Section9.GenericRVJacobian
import Section9.LiftComparison
import Section9.ZeroArityVolumeJacobian

/-! The RV comparison for arbitrary lifts in the finite-volume
categories. The exceptional set lies in the source volume image. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section7 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "VF" => VFType (M := M)

theorem lemma_9_15_finite_volume_of_reference_input [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {U V : RVFiniteObject (M := M) (C.base : Set M) n} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (f : Map (rvLift U.obj) (rvLift V.obj)) (hf : Function.Bijective f)
    (hlabel : ∀ p : rvLift U.obj, ((finiteVolumeProperty (C.base : Set M) n).ι.mapIso e).hom.map.graph
      p.val.2 (f p).val.2)
    (hgraph : HenselizedGaussGraphInput VF) :
    let E := (finiteVolumeProperty (C.base : Set M) n).ι.mapIso e
    ∃ D : DefSet (rawRVSpace (M := M) n) (C.base : Set M),
      D.carrier ⊆ U.obj.volume.image.carrier ∧ rvDim D < n ∧
      ∀ p : rvLift U.obj, U.obj.value (liftLabelMap U.obj p) ∉ D.carrier →
        ∃ J : VF, HasMixedVFJacobianAt f p J ∧
          IsRVJacobianAt (volumeCorrespondence E.hom.map).carrier (U.obj.value (liftLabelMap U.obj p))
            (V.obj.value (E.hom.map (liftLabelMap U.obj p))) (CanonicalRV.encodedRv J) := by
  obtain ⟨ω, X, _, hX, hω⟩ := exists_definable_generic_RVJacobian hc C hn e hU hV
  exact lemma_9_15_finite_volume_of_definable_candidate hc C hn e hU hV f hf hlabel ω X hX hω hgraph

theorem lemma_9_15_zero_arity {S : Set M} {U V : RVFiniteObject (M := M) S 0} (e : U ≅ V)
    (f : Map (rvLift U.obj) (rvLift V.obj)) (p : rvLift U.obj) :
    let E := (finiteVolumeProperty S 0).ι.mapIso e
    HasMixedVFJacobianAt f p (1 : VF) ∧
      IsRVJacobianAt (volumeCorrespondence E.hom.map).carrier (U.obj.value (liftLabelMap U.obj p))
        (V.obj.value (E.hom.map (liftLabelMap U.obj p))) (CanonicalRV.encodedRv (1 : VF)) := by
  dsimp only
  refine ⟨hasMixedVFJacobianAt_zero_arity f p, ?_⟩
  rw [RVOperations.rv_one]
  exact isRVJacobianAt_zero_arity _ _ _ ⟨liftLabelMap U.obj p, rfl⟩

end SpecialTransformations.Section9
