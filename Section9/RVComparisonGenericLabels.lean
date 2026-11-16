module

public import Section9.RVComparisonOnResidueFibre
public import Section9.NormalizationBases
public import Section9.FullRVValueFibre
public import Section9.GenericVolumePair
public import Section9.LiftRestriction
public import Section9.LiftLabelRepresentatives
public import Section7.ResidueCharacteristic

@[expose] public section

/-! Every full-dimensional definable label set contains a fibre on
which an arbitrary lift agrees with the RV Jacobian. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "VF" => VFType (M := M)

private theorem tupleRV_eq_liftLabel_volume {S : Set M} {d : ℕ} (U : RVObject (M := M) S d)
    (p : rvLift U) : tupleRV p.val.1 = U.value (liftLabelMap U p) := by
  obtain ⟨u, hu, ht⟩ := p.property
  have he : u = liftLabelMap U p := Subtype.ext hu
  exact (he ▸ ht).symm

theorem exists_comparison_label_of_full_rvDim [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {U V : RVFiniteObject (M := M) (C.base : Set M) n} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (f : Map (rvLift U.obj) (rvLift V.obj)) (hf : Function.Bijective f)
    (hlabel : ∀ p : rvLift U.obj, ((finiteVolumeProperty (C.base : Set M) n).ι.mapIso e).hom.map.graph
      p.val.2 (f p).val.2)
    (D : DefSet (rawRVSpace (M := M) U.obj.arity) (C.base : Set M))
    (hD : D.carrier ⊆ U.obj.domain.carrier) (hd : rvDim D = n)
    (hgraph : HenselizedGaussGraphInput VF) :
    let E := (finiteVolumeProperty (C.base : Set M) n).ι.mapIso e
    ∃ u : D, ∀ p : rvLift U.obj, liftLabelMap U.obj p = ⟨u.val, hD u.property⟩ →
      ∃ L, HasMixedVFDerivativeAt f p L ∧
        IsRVJacobianAt (volumeCorrespondence E.hom.map).carrier
          (U.obj.value ⟨u.val, hD u.property⟩) (V.obj.value (E.hom.map ⟨u.val, hD u.property⟩))
          (CanonicalRV.encodedRv (LinearMap.toMatrix' L).det) := by
  let S := (C.base : Set M)
  let E := (finiteVolumeProperty S n).ι.mapIso e
  let v := Values.presentationValuation (M := M)
  let hex := rvExchangeInput_of_earlier C.uncountable.le C.saturated C.model00
  letI : CharZero (ModelResidue M) := residueField_charZero_of_model00 v Values.presentation_compatible C.model00

  let E' := rvIsoRestrict E D hD
  let P := volumeCorrespondence E'.hom.map
  let α := volumePairMap E'.hom.map
  have hα := volumePairMap_finite E'.hom.map (U.property.restrict hD)
  have hP : α.image = P := by
    apply DefSet.eq_of_carrier_eq
    ext p
    constructor
    · rintro ⟨u, rfl⟩
      exact (α u).property
    · intro hp
      obtain ⟨u, hu⟩ := volumePairMap_surjective E'.hom.map ⟨p, hp⟩
      exact ⟨u, congrArg Subtype.val hu⟩
  have hPd : rvDim P = n := by
    rw [← hP, rvDim_mapImage_eq_of_finiteFibres hc hex C.saturated C.small α hα]
    exact hd
  have hP₀ (t) (ht : t ∈ P.carrier) (i : Fin (n+n)) : (t i).val ≠ iRVZero := by
    obtain ⟨u, rfl⟩ := ht
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective i
    · change (productTuple (U.obj.value ⟨u.val, hD u.property⟩)
        (V.obj.value (E.hom.map ⟨u.val, hD u.property⟩)) (productLeft n n j)).val ≠ iRVZero
      rw [productTuple_left]
      exact hU ⟨u.val, hD u.property⟩ j
    · change (productTuple (U.obj.value ⟨u.val, hD u.property⟩)
        (V.obj.value (E.hom.map ⟨u.val, hD u.property⟩)) (productRight n n j)).val ≠ iRVZero
      rw [productTuple_right]
      exact hV (E.hom.map ⟨u.val, hD u.property⟩) j
  obtain ⟨F, s, hFP, hFd, hval⟩ := exists_full_nonzero_rvValueFibre hc C P hP₀ (hPd.symm ▸ hn)
  choose c hc' using fun i => CanonicalRV.encodedRv_surjective (s.val i)
  let a := c ∘ productLeft n n
  let b := c ∘ productRight n n
  have haRV : tupleRV a = s.val ∘ productLeft n n := funext (fun i => hc' (productLeft n n i))
  have hbRV : tupleRV b = s.val ∘ productRight n n := funext (fun i => hc' (productRight n n i))
  have ha (i : Fin n) : a i ≠ 0 := by
    intro h
    exact hP₀ s.val (hFP s.property) (productLeft n n i)
      ((congrArg Subtype.val (congrFun haRV i)).symm.trans
        ((congrArg (fun x : VF => (CanonicalRV.encodedRv x).val) h).trans (RVCalc.rv_zero_eq C.model)))
  have hb (i : Fin n) : b i ≠ 0 := by
    intro h
    exact hP₀ s.val (hFP s.property) (productRight n n i)
      ((congrArg Subtype.val (congrFun hbRV i)).symm.trans
        ((congrArg (fun x : VF => (CanonicalRV.encodedRv x).val) h).trans (RVCalc.rv_zero_eq C.model)))
  obtain ⟨B₀, B₁, T, hB₀, hB₀T, hTB₁, _, hB₁, hT, hcl, hcoeff₀, hcoeff₁,
    haB, hbB, haN, hbN, hzero⟩ := exists_normalization_bases C.uncountable C.base C.small a b
  letI : IsAlgClosed (vfParameterField T) := hcl
  have hST : S ⊆ T := fun _ h => hB₀T (hB₀ h)
  have hSB₁ : S ⊆ (B₁ : Set M) := hST.trans hTB₁
  have hsB₁ (i : Fin (n+n)) : (s.val i).val ∈ B₁ := by
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective i
    · exact hTB₁ (hB₀T ((congrArg Subtype.val (congrFun haRV j)) ▸ haB j))
    · exact hTB₁ (hB₀T ((congrArg Subtype.val (congrFun hbRV j)) ▸ hbB j))
  have hπ : (rvHeadSelect (productLeft n n) F).FiniteFibres := by
    have hh := (volumePair_leftProjection_finite E'.hom.map (U.property.restrict hD)).restrict hFP
    exact hh
  obtain ⟨q, hq⟩ := exists_generic_pair_on_fixed_value_fibre hc hex C.uncountable.le C.saturated C.homogeneous
    C.small B₁ hB₁ hSB₁ F hπ (hFd.trans hPd) s hsB₁ hval
  obtain ⟨u, hu⟩ := hFP q.property
  let u₀ : U.obj.domain := ⟨u.val, hD u.property⟩
  refine ⟨u, fun p hp => ?_⟩
  have hp₁ : tupleRV p.val.1 = U.obj.value u₀ := (tupleRV_eq_liftLabel_volume U.obj p).trans (congrArg U.obj.value hp)
  have hp₂ : tupleRV (f p).val.1 = V.obj.value (E.hom.map u₀) := by
    rw [tupleRV_eq_liftLabel_volume]
    apply congrArg V.obj.value
    apply Subtype.ext
    have hh := (E.hom.map.graph_apply (liftLabelMap U.obj p) _).mp (hlabel p)
    exact hh.symm.trans (congrArg (fun u => (E.hom.map u).val) hp)
  have hpair : q.val = productTuple (tupleRV p.val.1) (tupleRV (f p).val.1) := by
    rw [hp₁, hp₂]
    exact hu.symm
  have hleft : q.val ∘ productLeft n n = tupleRV p.val.1 :=
    funext fun i => (congrFun hpair (productLeft n n i)).trans (productTuple_left _ _ i)
  have hright : q.val ∘ productRight n n = tupleRV (f p).val.1 :=
    funext fun i => (congrFun hpair (productRight n n i)).trans (productTuple_right _ _ i)
  have hpa (i : Fin n) : Values.vrv (tupleRV p.val.1 i) = Values.vrv (tupleRV a i) := by
    exact (congrArg Values.vrv (congrFun hleft i)).symm.trans
      ((hval q.val q.property (productLeft n n i)).trans (congrArg Values.vrv (congrFun haRV i)).symm)
  have hpb (i : Fin n) : Values.vrv (tupleRV (f p).val.1 i) = Values.vrv (tupleRV b i) := by
    exact (congrArg Values.vrv (congrFun hright i)).symm.trans
      ((hval q.val q.property (productRight n n i)).trans (congrArg Values.vrv (congrFun hbRV i)).symm)
  have hInd : AlgebraicIndependent (residueParameterField B₁) (residueNormalize (tupleRV a) (tupleRV p.val.1)) := by
    rw [haRV, ← hleft]
    exact hq
  let W := volumeCorrespondence E.hom.map
  have hW := normalizedCorrespondence_definable_of_base hc B₀ (W.extend hB₀) _ _
    (fun i => (RVOperations.rv_ne_zero _).mpr (ha i))
    (fun i => (RVOperations.rv_ne_zero _).mpr (hb i)) haB hbB
  obtain ⟨hR, hL⟩ := normalizedVolumeCorrespondence_finite E (tupleRV a) (tupleRV b)
    (fun i => (RVOperations.rv_ne_zero _).mpr (ha i)) (fun i => (RVOperations.rv_ne_zero _).mpr (hb i))
  have hmem : productTuple (tupleRV p.val.1) (tupleRV (f p).val.1) ∈ W.carrier :=
    ⟨u₀, (congrArg₂ productTuple hp₁ hp₂).symm⟩
  obtain ⟨L, hDer, hRVJ⟩ := rvComparison_at_generic_fixed_value_pair hc C.uncountable.le C.saturated hT
    B₀ B₁ hB₁ hcoeff₀ hcoeff₁ (f.extend hST) hf p a b ha hb haN hbN hzero hpa hpb
    W.carrier hW hmem hR hL hInd hgraph
  change IsRVJacobianAt (M := M) W.carrier (tupleRV p.val.1) (tupleRV (f p).val.1)
    (CanonicalRV.encodedRv (LinearMap.toMatrix' L).det) at hRVJ
  rw [hp₁, hp₂] at hRVJ
  exact ⟨L, hDer, hRVJ⟩

end SpecialTransformations.Section9
