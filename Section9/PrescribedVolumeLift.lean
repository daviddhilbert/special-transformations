module

public import Section9.RepairLiftOnSmallLabels
public import Section9.LiftComparison

@[expose] public section

/-! The finite-volume statement of Theorem 9.16 in positive arity.
Use the arbitrary-lift comparison only on a full-dimensional
discrepancy candidate, then repair the lower-dimensional remainder. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section7 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}
local notation "VF" => VFType (M := M)
local notation "n" => (k + 1)

theorem theorem_9_16_finite_volume_of_reference_input [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hB : VFGammaGeneratedBase ⟨(C.base : Set M), Ξ⟩)
    {U V : RVFiniteObject (M := M) (C.base : Set M) n} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (ω : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) (C.base : Set M)))
    (hΓ : let E := (finiteVolumeProperty (C.base : Set M) n).ι.mapIso e
      ∀ u : U.obj.domain, Values.vrv ((ω u).val 0) =
        (rvGammaJacobian (U.obj.value u) (V.obj.value (E.hom.map u)) (hU u) (hV (E.hom.map u))).val)
    (hRV : let E := (finiteVolumeProperty (C.base : Set M) n).ι.mapIso e
      ∃ X : DefSet (rawRVSpace (M := M) U.obj.arity) (C.base : Set M), rvDim X < n ∧
        ∀ u : U.obj.domain, u.val ∉ X.carrier →
          IsRVJacobianAt (volumeCorrespondence E.hom.map).carrier
            (U.obj.value u) (V.obj.value (E.hom.map u)) ((ω u).val 0))
    (hgraph : HenselizedGaussGraphInput VF) :
    ∃ G : Map (rvLift U.obj) (rvLift V.obj), Function.Bijective G ∧
      (∀ p : rvLift U.obj, ((finiteVolumeProperty (C.base : Set M) n).ι.mapIso e).hom.map.graph
        p.val.2 (G p).val.2) ∧
      ∃ Z : DefSet (rawMixedSpace (M := M) n U.obj.arity) (C.base : Set M),
        Z.carrier ⊆ (rvLift U.obj).carrier ∧ vfDim (rawRVSpace (M := M) 1) Z < n ∧
        ∀ p : rvLift U.obj, p.val ∉ Z.carrier → ∃ J : VF, HasMixedVFJacobianAt G p J ∧
          CanonicalRV.encodedRv J = (ω (liftLabelMap U.obj p)).val 0 := by
  let S := (C.base : Set M)
  let B : Base (M := M) := ⟨S, Ξ⟩
  let E := (finiteVolumeProperty S n).ι.mapIso e
  let v := Values.presentationValuation (M := M)
  obtain ⟨f, hf, hlabel, _⟩ := exists_weighted_liftMap_of_rvIso hc C.uncountable.le C.saturated C.model00
    B C.small hB v Values.presentation_compatible E hU hV
  obtain ⟨X, hX, hω⟩ := hRV
  obtain ⟨D, hD, hsmallD, hgood⟩ := exists_small_liftComparison_discrepancy hc C (Nat.zero_lt_succ k)
    e hU hV f hf hlabel ω X hX hω hgraph
  apply exists_repaired_lift_on_small_labels hc C.uncountable.le C.saturated C.model00 B C.small hB v
    Values.presentation_compatible e hU hV ω hΓ f hf hlabel D hD hsmallD
  intro p hp _
  obtain ⟨L, ⟨F, hF, hDer⟩, hrep⟩ := hgood p hp
  exact ⟨_, ⟨F, hF, hDer.hasJacobianAt⟩, hrep⟩

end SpecialTransformations.Section9
