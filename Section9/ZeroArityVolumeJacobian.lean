module

public import Section9.WeightedLiftJacobian
public import Section9.VolumeResidueCorrespondence
public import Section9.LiftLabelRepresentatives

@[expose] public section

/-! At arity zero, the empty determinant is one, including for actual
lifts. This treats the case separately from the positive-arity
dimension bounds. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section7 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
local notation "VF" => VFType (M := M)
local notation "RV" => CanonicalRV.RVSort M

theorem isRVJacobianAt_zero_arity (C : Set (Fin (0 + 0) → RV)) (t s : Fin 0 → RV)
    (h : productTuple t s ∈ C) : IsRVJacobianAt C t s 1 := by
  refine ⟨h, (fun i => i.elim0), (fun i => i.elim0), 0, ?_, ?_, ?_⟩
  · intro x y
    have ht : IsPolynomialTangent (normalizedCorrespondence C t s) (fun _ => 1) (productTuple x y) :=
      fun _ _ => Finset.sum_empty
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => ht⟩
  · simp
  · simp

theorem exists_prescribed_lift_zero_arity [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    {U V : RVFiniteObject (M := M) B.real 0} (e : U ≅ V)
    (ω : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) B.real))
    (hω : let E := (finiteVolumeProperty B.real 0).ι.mapIso e
      ∀ u : U.obj.domain, IsRVJacobianAt (volumeCorrespondence E.hom.map).carrier
        (U.obj.value u) (V.obj.value (E.hom.map u)) ((ω u).val 0)) :
    ∃ G : Map (rvLift U.obj) (rvLift V.obj), Function.Bijective G ∧
      (∀ p : rvLift U.obj, ((finiteVolumeProperty B.real 0).ι.mapIso e).hom.map.graph p.val.2 (G p).val.2) ∧
      ∀ p : rvLift U.obj, HasMixedVFJacobianAt G p (1 : VF) ∧
        CanonicalRV.encodedRv (1 : VF) = (ω (liftLabelMap U.obj p)).val 0 := by
  let E := (finiteVolumeProperty B.real 0).ι.mapIso e
  obtain ⟨G, hG, hlabel, _⟩ := exists_weighted_liftMap_of_rvIso hc hκ hs h00 B hsmall hB
    Values.presentationValuation Values.presentation_compatible E (fun _ i => i.elim0) (fun _ i => i.elim0)
  refine ⟨G, hG, hlabel, fun p => ⟨hasMixedVFJacobianAt_zero_arity G p, ?_⟩⟩
  let u := liftLabelMap U.obj p
  have hpair : productTuple (U.obj.value u) (V.obj.value (E.hom.map u)) ∈
      (volumeCorrespondence E.hom.map).carrier := ⟨u, rfl⟩
  have he := (isRVJacobianAt_zero_arity _ _ _ hpair).unique (hω u)
  exact (map_one (RVOperations.rvHom (M := M))).trans he

end SpecialTransformations.Section9
