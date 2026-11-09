import Section9.RVComparisonGenericLabels
import Section9.LiftJacobianDiscrepancy

/-! Compare an arbitrary lift with a definable candidate for the RV
Jacobian. Once the candidate is known to agree with the residue
tangent off an RV-small set, the actual discrepancy is RV-small. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "VF" => VFType (M := M)

theorem exists_small_liftComparison_discrepancy [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {U V : RVFiniteObject (M := M) (C.base : Set M) n} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (f : Map (rvLift U.obj) (rvLift V.obj)) (hf : Function.Bijective f)
    (hlabel : ∀ p : rvLift U.obj, ((finiteVolumeProperty (C.base : Set M) n).ι.mapIso e).hom.map.graph
      p.val.2 (f p).val.2)
    (ω : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) (C.base : Set M)))
    (X : DefSet (rawRVSpace (M := M) U.obj.arity) (C.base : Set M)) (hX : rvDim X < n)
    (hω : let E := (finiteVolumeProperty (C.base : Set M) n).ι.mapIso e
      ∀ u : U.obj.domain, u.val ∉ X.carrier →
        IsRVJacobianAt (volumeCorrespondence E.hom.map).carrier
          (U.obj.value u) (V.obj.value (E.hom.map u)) ((ω u).val 0))
    (hgraph : HenselizedGaussGraphInput VF) :
    ∃ D : DefSet (rawRVSpace (M := M) U.obj.arity) (C.base : Set M),
      D.carrier ⊆ U.obj.domain.carrier ∧ rvDim D < n ∧
      ∀ p : rvLift U.obj, p.val.2 ∉ D.carrier →
        ∃ L, HasMixedVFDerivativeAt f p L ∧
          CanonicalRV.encodedRv (LinearMap.toMatrix' L).det = (ω (liftLabelMap U.obj p)).val 0 := by
  let hex := rvExchangeInput_of_earlier C.uncountable.le C.saturated C.model00
  obtain ⟨D, hD, hbad⟩ := exists_liftJacobian_discrepancy hn U.obj V.obj f ω
  refine ⟨D, hD, ?_, ?_⟩
  · by_contra h
    have hd : rvDim D = n := ((rvDim_le_of_finite_map (U.obj.volume.restrict hD)
      (U.property.restrict hD)).trans (rvDim_le_arity _)).antisymm (Nat.le_of_not_gt h)
    let D' := D.sdiff X
    let hD' : D'.carrier ⊆ U.obj.domain.carrier := Set.sdiff_subset.trans hD
    have hd' : rvDim D' = n := (rvDim_sdiff_eq_of_lt hc hex C.saturated C.small D X (hd.symm ▸ hX)).trans hd
    obtain ⟨u, hcmp⟩ := exists_comparison_label_of_full_rvDim hc C hn e hU hV f hf hlabel D' hD' hd' hgraph
    let u₀ : U.obj.domain := ⟨u.val, hD' u.property⟩
    obtain ⟨p, hp, hpBad⟩ := (hbad u₀).mp u.property.1
    obtain ⟨L, hDer, hRVJ⟩ := hcmp p hp
    exact hpBad ⟨L, hDer, hRVJ.unique (hω u₀ u.property.2)⟩
  · intro p hp
    by_contra hn
    exact hp ((hbad (liftLabelMap U.obj p)).mpr ⟨p, rfl, hn⟩)

theorem lemma_9_15_finite_volume_of_definable_candidate [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {U V : RVFiniteObject (M := M) (C.base : Set M) n} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (f : Map (rvLift U.obj) (rvLift V.obj)) (hf : Function.Bijective f)
    (hlabel : ∀ p : rvLift U.obj, ((finiteVolumeProperty (C.base : Set M) n).ι.mapIso e).hom.map.graph
      p.val.2 (f p).val.2)
    (ω : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) (C.base : Set M)))
    (X : DefSet (rawRVSpace (M := M) U.obj.arity) (C.base : Set M)) (hX : rvDim X < n)
    (hω : let E := (finiteVolumeProperty (C.base : Set M) n).ι.mapIso e
      ∀ u : U.obj.domain, u.val ∉ X.carrier →
        IsRVJacobianAt (volumeCorrespondence E.hom.map).carrier
          (U.obj.value u) (V.obj.value (E.hom.map u)) ((ω u).val 0))
    (hgraph : HenselizedGaussGraphInput VF) :
    let E := (finiteVolumeProperty (C.base : Set M) n).ι.mapIso e
    ∃ D : DefSet (rawRVSpace (M := M) n) (C.base : Set M),
      D.carrier ⊆ U.obj.volume.image.carrier ∧ rvDim D < n ∧
      ∀ p : rvLift U.obj, U.obj.value (liftLabelMap U.obj p) ∉ D.carrier →
        ∃ J : VF, HasMixedVFJacobianAt f p J ∧
          IsRVJacobianAt (volumeCorrespondence E.hom.map).carrier (U.obj.value (liftLabelMap U.obj p))
            (V.obj.value (E.hom.map (liftLabelMap U.obj p))) (CanonicalRV.encodedRv J) := by
  obtain ⟨D, _, hD, hgood⟩ := exists_small_liftComparison_discrepancy hc C hn e hU hV f hf hlabel ω X hX hω hgraph
  let hex := rvExchangeInput_of_earlier C.uncountable.le C.saturated C.model00
  let H := (D.union X).inter U.obj.domain
  let hH : H.carrier ⊆ U.obj.domain.carrier := fun _ h => h.2
  let w := U.obj.volume.restrict hH
  have hHdim : rvDim H < n := by
    let i : Map H (D.union X) := Map.inclusion (fun _ h => h.1)
    have hi : Function.Injective i := by
      intro a b h
      have he := congrArg Subtype.val h
      exact Subtype.ext he
    exact (rvDim_le_of_finite_map i (Map.finiteFibres_of_injective hi)).trans_lt
      ((rvDim_union_le_max hc hex C.saturated C.small D X).trans_lt (max_lt hD hX))
  have hw : rvDim w.image < n :=
    (rvDim_mapImage_eq_of_finiteFibres hc hex C.saturated C.small w (U.property.restrict hH)).trans_lt hHdim
  refine ⟨w.image, ?_, hw, fun p hp => ?_⟩
  · rintro _ ⟨u, rfl⟩
    exact ⟨⟨u.val, hH u.property⟩, rfl⟩
  let u := liftLabelMap U.obj p
  have hOutside (h : u.val ∈ (D.union X).carrier) : False :=
    hp ⟨⟨u.val, h, u.property⟩, rfl⟩
  obtain ⟨L, ⟨F, hF, hDer⟩, he⟩ := hgood p (fun h => hOutside (Or.inl h))
  exact ⟨_, ⟨F, hF, hDer.hasJacobianAt⟩,
    he.symm ▸ hω u (fun h => hOutside (Or.inr h))⟩

end SpecialTransformations.Section9
