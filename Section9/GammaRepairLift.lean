import Section9.RepairLiftOnSmallLabels
import Section9.GammaLowerDimensionalLift

/-! Gamma counterpart of `exists_repaired_lift_on_small_labels`: repair a
lift with a Gamma graph on a Gamma-definable lower-dimensional set of labels,
keeping a Gamma graph. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)

namespace SpecialTransformations.Section9.GammaLift

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ] {k : ℕ}
local notation "VF" => VFType (M := M)
local notation "n" => (k + 1)

theorem gamma_repaired_lift_on_small_labels [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (B : Base (M := M)) (hB : VFGammaGeneratedBase B) (hBS : B.real ⊆ (C.base : Set M))
    (v : Valuation VF Γ) (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    {U V : RVFiniteObject (M := M) (C.base : Set M) n} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (hUΓ : RVMapGamma U.obj.volume B) (hVΓ : RVMapGamma V.obj.volume B)
    (heΓ : RVMapGamma ((finiteVolumeProperty (C.base : Set M) n).ι.mapIso e).hom.map B)
    (ω : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) (C.base : Set M))) (hωΓ : RVMapGamma ω B)
    (hω : let E := (finiteVolumeProperty (C.base : Set M) n).ι.mapIso e
      ∀ u : U.obj.domain, Values.vrv ((ω u).val 0) =
        (rvGammaJacobian (U.obj.value u) (V.obj.value (E.hom.map u)) (hU u) (hV (E.hom.map u))).val)
    (f : Map (rvLift U.obj) (rvLift V.obj)) (hf : Function.Bijective f) (hfΓ : MixedMapGamma f B)
    (hlabel : ∀ p : rvLift U.obj, ((finiteVolumeProperty (C.base : Set M) n).ι.mapIso e).hom.map.graph
      p.val.2 (f p).val.2)
    (D : DefSet (rawRVSpace (M := M) U.obj.arity) (C.base : Set M)) (hD : D.carrier ⊆ U.obj.domain.carrier)
    (hDΓ : RVSetGamma D B) (hd : rvDim D < n)
    (hgood : ∀ p : rvLift U.obj, p.val.2 ∉ D.carrier →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) p.val.1 →
      ∃ J : VF, HasMixedVFJacobianAt f p J ∧ CanonicalRV.encodedRv J = (ω (liftLabelMap U.obj p)).val 0) :
    ∃ G : Map (rvLift U.obj) (rvLift V.obj), Function.Bijective G ∧ MixedMapGamma G B ∧
      (∀ p : rvLift U.obj, ((finiteVolumeProperty (C.base : Set M) n).ι.mapIso e).hom.map.graph
        p.val.2 (G p).val.2) ∧
      ∃ Z : DefSet (rawMixedSpace (M := M) n U.obj.arity) (C.base : Set M),
        Z.carrier ⊆ (rvLift U.obj).carrier ∧ vfDim (rawRVSpace (M := M) 1) Z < n ∧
        ∀ p : rvLift U.obj, p.val ∉ Z.carrier → ∃ J : VF, HasMixedVFJacobianAt G p J ∧
          CanonicalRV.encodedRv J = (ω (liftLabelMap U.obj p)).val 0 := by
  have hκ : Cardinal.aleph0 ≤ C.κ := C.uncountable.le
  have hs := C.saturated
  have h00 := C.model00
  have hsmall := C.small
  classical
  let E := (finiteVolumeProperty (C.base : Set M) n).ι.mapIso e
  let D₁ := (E.hom.map.restrict hD).image
  let hD₁ := rvLabelImage_subset E D hD
  let U₀ := rvFiniteRestrict U D hD
  let V₀ := rvFiniteRestrict V D₁ hD₁
  let e₀ : U₀ ≅ V₀ := rvFiniteIsoOfAmbient (rvIsoRestrict E D hD)
  let hex := rvExchangeInput_of_earlier hκ hs h00
  have hU₀ : rvDim U₀.obj.volume.image ≤ k :=
    (rvDim_mapImage_eq_of_finiteFibres hc hex hs hsmall _ U₀.property).le.trans (Nat.le_of_lt_succ hd)
  have hDdim : rvDim D₁ = rvDim D := by
    apply rvDim_mapImage_eq_of_finiteFibres hc hex hs hsmall
    apply Map.finiteFibres_of_injective
    intro a b he
    have h := congrArg E.inv.map he
    change E.inv.map (E.hom.map ⟨a.val, hD a.property⟩) =
      E.inv.map (E.hom.map ⟨b.val, hD b.property⟩) at h
    rw [Section4.rvIso_inv_apply, Section4.rvIso_inv_apply] at h
    have he' := congrArg Subtype.val h
    exact Subtype.ext he'
  have hV₀ : rvDim V₀.obj.volume.image ≤ k :=
    (rvDim_mapImage_eq_of_finiteFibres hc hex hs hsmall _ V₀.property).le.trans
      (hDdim.le.trans (Nat.le_of_lt_succ hd))
  have hU₀Γ : RVMapGamma U₀.obj.volume B := RVMapGamma.restrict hUΓ hD hDΓ
  have hD₁Γ : RVSetGamma D₁ B := rv_image_gamma' (RVMapGamma.restrict heΓ hD hDΓ)
  have hV₀Γ : RVMapGamma V₀.obj.volume B := RVMapGamma.restrict hVΓ hD₁ hD₁Γ
  have he₀Γ : RVMapGamma ((finiteVolumeProperty (C.base : Set M) (k + 1)).ι.mapIso e₀).hom.map B :=
    RVMapGamma.corestrict (RVMapGamma.restrict heΓ hD hDΓ) _
  obtain ⟨g, hg, hgΓ, hglabel, hZ⟩ := gamma_prescribed_lift_of_lower_rvDim
    hc C B hB hBS v hv e₀ (fun u => hU ⟨u.val, hD u.property⟩)
    (fun w => hV ⟨w.val, hD₁ w.property⟩) hU₀ hV₀ hU₀Γ hV₀Γ he₀Γ (0 : Fin 1) (ω.restrict hD)
    (RVMapGamma.restrict hωΓ hD hDΓ) (fun u => hω ⟨u.val, hD u.property⟩)
  let D₂ := U.obj.domain.sdiff D
  let hD₂ : D₂.carrier ⊆ U.obj.domain.carrier := Set.sdiff_subset
  have hD₂Γ : RVSetGamma D₂ B := (gammaLogicInput B).sdiff hUΓ.domain hDΓ
  obtain ⟨f', hf', hf'Γ, hfagree⟩ := gamma_restricted_actual_lift E D₂ hD₂ hD₂Γ f hf hfΓ hlabel
  let P : Bool → DefSet (rawRVSpace (M := M) U.obj.arity) (C.base : Set M) := fun i => if i then D else D₂
  have hP : ∀ i, (P i).carrier ⊆ U.obj.domain.carrier := by
    intro i
    cases i
    · exact hD₂
    · exact hD
  have hcover (u : U.obj.domain) : ∃ i, u.val ∈ (P i).carrier := by
    by_cases hu : u.val ∈ D.carrier
    · exact ⟨true, hu⟩
    · exact ⟨false, u.property, hu⟩
  have hdisj (i j : Bool) (z) : z ∈ (P i).carrier → z ∈ (P j).carrier → i = j := by
    cases i <;> cases j
    · exact fun _ _ => rfl
    · intro hu hd
      exact (hu.2 hd).elim
    · intro hd hu
      exact (hu.2 hd).elim
    · exact fun _ _ => rfl
  let G : ∀ i, Map (rvLift (U.obj.restrict (P i) (hP i)))
      (rvLift (V.obj.restrict (E.hom.map.restrict (hP i)).image (rvLabelImage_subset E (P i) (hP i)))) :=
    fun i => by
      cases i
      · exact f'
      · exact g
  have hG : ∀ i, Function.Bijective (G i) := by
    intro i
    cases i
    · exact hf'
    · exact hg
  have hGlab (i) (p : rvLift (U.obj.restrict (P i) (hP i))) :
      E.hom.map.graph p.val.2 (G i p).val.2 := by
    cases i
    · let q : rvLift U.obj := ⟨p.val, ((rvLift_restrict_mem_iff U.obj D₂ hD₂ _).mp p.property).1⟩
      exact (hfagree p q rfl).symm ▸ hlabel q
    · obtain ⟨u, hu, hv⟩ := hglabel p
      exact ⟨⟨u.val, hD u.property⟩, hu, hv⟩
  have hGΓ : ∀ i, MixedMapGamma (G i) B := by
    intro i
    cases i
    · exact hf'Γ
    · exact hgΓ
  obtain ⟨F, hF, hFΓ, hFlab, hFagree⟩ := gamma_glued_label_lift E P hP hcover hdisj G hG hGΓ hGlab
  letI : Valued VF Γ := Valued.mk' v
  refine ⟨F, hF, hFΓ, hFlab, exists_mixedRVJacobian_exception hc hs hsmall (Nat.zero_lt_succ k) F
    (ω.comp (liftLabelMap U.obj)) ?_⟩
  intro p hp
  obtain ⟨L, hL⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv F p hp
  obtain ⟨H, hH, hDer⟩ := hL
  refine ⟨L, ⟨H, hH, hDer⟩, ?_⟩
  by_cases hpD : p.val.2 ∈ D.carrier
  · let q : rvLift U₀.obj :=
      ⟨p.val, (rvLift_restrict_mem_iff U.obj D hD _).mpr ⟨p.property, hpD⟩⟩
    obtain ⟨J, hJ, hrep⟩ := hZ q hp
    have hJF := HasMixedVFJacobianAt.of_label_restriction (U := U.obj) (V := V.obj)
      D hD g F q p rfl (hFagree true) hJ
    have hEq := (show HasMixedVFJacobianAt F p _ from ⟨H, hH, hDer.hasJacobianAt⟩).unique hJF
    exact (congrArg CanonicalRV.encodedRv hEq).trans hrep
  · let q : rvLift (U.obj.restrict D₂ hD₂) :=
      ⟨p.val, (rvLift_restrict_mem_iff U.obj D₂ hD₂ _).mpr ⟨p.property, (liftLabelMap U.obj p).property, hpD⟩⟩
    obtain ⟨J, hJ, hrep⟩ := hgood p hpD hp
    have hFf : ∀ (q' : rvLift (U.obj.restrict D₂ hD₂)) (p' : rvLift U.obj), q'.val = p'.val →
        (f p').val = (F p').val := fun q' p' h =>
      (hfagree q' p' h).symm.trans (hFagree false q' p' h)
    obtain ⟨K, ⟨ρ, hρ⟩, hK⟩ := hJ
    have hJF : HasMixedVFJacobianAt F p J := by
      refine ⟨K, ⟨ρ, fun x hx => ?_⟩, hK⟩
      obtain ⟨hxU, hxF⟩ := hρ x hx
      let p' : rvLift U.obj := ⟨(x,p.val.2), hxU⟩
      let q' : rvLift (U.obj.restrict D₂ hD₂) :=
        ⟨p'.val, (rvLift_restrict_mem_iff U.obj D₂ hD₂ _).mpr
          ⟨hxU, (liftLabelMap U.obj p).property, hpD⟩⟩
      refine ⟨hxU, ?_⟩
      change (F p').val = _
      rw [← hFf q' p' rfl, hxF, congrArg Prod.snd (hFf q p rfl)]
    have hEq := (show HasMixedVFJacobianAt F p _ from ⟨H, hH, hDer.hasJacobianAt⟩).unique hJF
    exact (congrArg CanonicalRV.encodedRv hEq).trans hrep

end SpecialTransformations.Section9.GammaLift
