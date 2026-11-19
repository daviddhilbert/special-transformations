import Section9.LowerDimensionalPrescribedLift
import Section9.GammaReindexedLift
import Section9.GammaSimultaneousCover

/-! Gamma counterpart of `exists_prescribed_lift_of_lower_rvDim`: the
lower RV-dimensional branch of the prescribed lift, with Gamma head covers,
Gamma partition pieces, Gamma local lifts and Gamma gluing. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)

namespace SpecialTransformations.Section9.GammaLift

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ] {k m : ℕ}
local notation "VF" => VFType (M := M)

theorem RVMapGamma.restrict {S : Set M} {B : Base (M := M)} {a b : ℕ}
    {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) b) S}
    {f : Map A D} (hf : RVMapGamma f B) {A' : DefSet (rawRVSpace (M := M) a) S}
    (h : A'.carrier ⊆ A.carrier) (hA' : RVSetGamma A' B) : RVMapGamma (f.restrict h) B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr ((gammaLogicInput B).restrict_graph hA' hf)
  intro p q
  constructor
  · rintro ⟨hp, u, hu, hq⟩
    exact ⟨⟨p.2, hp⟩, rfl, by rw [← hq]; exact congrArg (fun x => (f x).val) (Subtype.ext hu.symm)⟩
  · rintro ⟨u, hu, hq⟩
    refine ⟨?_, ⟨u.val, h u.property⟩, hu, hq⟩
    change p.2 ∈ A'.carrier
    rw [← hu]
    exact u.property

theorem RVMapGamma.corestrict {S : Set M} {B : Base (M := M)} {a b : ℕ}
    {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) b) S}
    {f : Map A D} (hf : RVMapGamma f B) {D' : DefSet (rawRVSpace (M := M) b) S}
    (h : ∀ x, (f x).val ∈ D'.carrier) : RVMapGamma (f.corestrict h) B := hf

theorem rv_image_gamma' {S : Set M} {B : Base (M := M)} {a b : ℕ}
    {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) b) S}
    {f : Map A D} (hf : RVMapGamma f B) : RVSetGamma f.image B := by
  have h := (gammaLogicInput B).image_graph hf
  unfold RVSetGamma
  convert h using 1
  ext q
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨(Fin.elim0, u.val), u, rfl, hu⟩
  · rintro ⟨p, u, _, hu⟩
    exact ⟨u, hu⟩

theorem gamma_prescribed_lift_of_lower_rvDim [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (B : Base (M := M)) (hB : VFGammaGeneratedBase B) (hBS : B.real ⊆ (C.base : Set M))
    (v : Valuation VF Γ) (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    {U V : RVFiniteObject (M := M) (C.base : Set M) (k + m)} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (hUdim : rvDim U.obj.volume.image ≤ k) (hVdim : rvDim V.obj.volume.image ≤ k)
    (hUΓ : RVMapGamma U.obj.volume B) (hVΓ : RVMapGamma V.obj.volume B)
    (heΓ : RVMapGamma ((finiteVolumeProperty (C.base : Set M) (k + m)).ι.mapIso e).hom.map B)
    (j : Fin m) (ω : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) (C.base : Set M)))
    (hωΓ : RVMapGamma ω B)
    (hω : let E := (finiteVolumeProperty (C.base : Set M) (k + m)).ι.mapIso e
      ∀ u : U.obj.domain, Values.vrv ((ω u).val 0) =
        (rvGammaJacobian (U.obj.value u) (V.obj.value (E.hom.map u)) (hU u) (hV (E.hom.map u))).val) :
    ∃ G : Map (rvLift U.obj) (rvLift V.obj), Function.Bijective G ∧ MixedMapGamma G B ∧
      (∀ p : rvLift U.obj, ((finiteVolumeProperty (C.base : Set M) (k + m)).ι.mapIso e).hom.map.graph
        p.val.2 (G p).val.2) ∧
      ∀ p : rvLift U.obj, AlgebraicIndependent (vfParameterField (C.base : Set M)) p.val.1 →
        ∃ J : VF, HasMixedVFJacobianAt G p J ∧
          CanonicalRV.encodedRv J = (ω (liftLabelMap U.obj p)).val 0 := by
  have hκ : Cardinal.aleph0 ≤ C.κ := C.uncountable.le
  have hs := C.saturated
  have h00 := C.model00
  have hsmall : Cardinal.mk B.real < C.κ := (Cardinal.mk_le_mk_of_subset hBS).trans_lt C.small
  let E := (finiteVolumeProperty (C.base : Set M) (k + m)).ι.mapIso e
  obtain ⟨a, b, P, l, r, hP, hcover, hfin⟩ := gamma_exists_simultaneous_finite_head_cover hc C B hBS
    (Nat.le_add_right k m) e hUΓ hVΓ heΓ hUdim hVdim
  obtain ⟨D, hDP, hDΓ, hDcover, hdisj⟩ := gamma_exists_disjoint_definable_refinement P (fun i => (hP i).2)
  let hD (i : Fin a × Fin b) := (hDP i).trans (hP i).1
  let Q (i : Fin a × Fin b) := (E.hom.map.restrict (hD i)).image
  let hQ (i : Fin a × Fin b) := rvLabelImage_subset E (D i) (hD i)
  let U' i := rvFiniteRestrict U (D i) (hD i)
  let V' i := rvFiniteRestrict V (Q i) (hQ i)
  let e' (i : Fin a × Fin b) : U' i ≅ V' i :=
    rvFiniteIsoOfAmbient (rvIsoRestrict E (D i) (hD i))
  let ιU (i) (u : (U' i).obj.domain) : U.obj.domain := ⟨u.val, hD i u.property⟩
  let ιV (i) (w : (V' i).obj.domain) : V.obj.domain := ⟨w.val, hQ i w.property⟩
  have hfinU (i) : (rvHeadVolume (U' i).obj (l i)).FiniteFibres := by
    have hinj : Function.Injective (ιU i) := by
      intro u w h
      have he := congrArg Subtype.val h
      exact Subtype.ext he
    intro x
    apply Set.Finite.of_finite_image (f := ιU i) ?_ hinj.injOn
    refine ((hfin i x.val).1).subset ?_
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨hDP i u.property, congrArg Subtype.val hu⟩
  have hfinV (i) : (rvHeadVolume (V' i).obj (r i)).FiniteFibres := by
    let f (w : (V' i).obj.domain) := E.inv.map (ιV i w)
    have hf : Function.Injective f := by
      intro w w' he
      have h := congrArg E.hom.map he
      rw [show f w = E.inv.map (ιV i w) from rfl,
        show f w' = E.inv.map (ιV i w') from rfl, rvIso_apply_inv, rvIso_apply_inv] at h
      have he := congrArg Subtype.val h
      exact Subtype.ext he
    intro x
    apply Set.Finite.of_finite_image (f := f) ?_ hf.injOn
    refine ((hfin i x.val).2).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨u, hu⟩ := w.property
    have he : E.hom.map (ιU i u) = ιV i w := Subtype.ext hu
    have he' : f w = ιU i u := by
      change E.inv.map (ιV i w) = _
      rw [← he, Section4.rvIso_inv_apply]
    refine ⟨he' ▸ hDP i u.property, ?_⟩
    change V.obj.value (E.hom.map (E.inv.map (ιV i w))) ∘ r i = x.val
    rw [rvIso_apply_inv]
    exact congrArg Subtype.val hw
  have hU'Γ (i : Fin a × Fin b) : RVMapGamma (U' i).obj.volume B :=
    RVMapGamma.restrict hUΓ (hD i) (hDΓ i)
  have hQΓ (i : Fin a × Fin b) : RVSetGamma (Q i) B :=
    rv_image_gamma' (RVMapGamma.restrict heΓ (hD i) (hDΓ i))
  have hV'Γ (i : Fin a × Fin b) : RVMapGamma (V' i).obj.volume B :=
    RVMapGamma.restrict hVΓ (hQ i) (hQΓ i)
  have he'Γ (i : Fin a × Fin b) : RVMapGamma ((finiteVolumeProperty (C.base : Set M) (k + m)).ι.mapIso (e' i)).hom.map B :=
    RVMapGamma.corestrict (RVMapGamma.restrict heΓ (hD i) (hDΓ i)) _
  have localLift (i : Fin a × Fin b) :=
    gamma_prescribed_lift_with_reindexed_heads hc hκ hs h00 B hsmall hB hBS C.small v hv (e' i)
      (fun u => hU (ιU i u)) (fun w => hV (ιV i w)) (l i) (r i) (hfinU i) (hfinV i)
      (hU'Γ i) (hV'Γ i) (he'Γ i) j (ω.restrict (hD i)) (RVMapGamma.restrict hωΓ (hD i) (hDΓ i))
      (fun u => hω (ιU i u))
  choose F hF hFΓ hFlabel hFJ using localLift
  have hlabel (i) (p : rvLift (U' i).obj) : E.hom.map.graph p.val.2 (F i p).val.2 := by
    obtain ⟨u, hu, hFu⟩ := hFlabel i p
    exact ⟨ιU i u, hu, hFu⟩
  obtain ⟨G, hG, hGΓ, hGlabel, hGlocal⟩ := gamma_glued_label_lift E D hD
    (fun u => hDcover u.val (hcover u)) hdisj F hF hFΓ hlabel
  refine ⟨G, hG, hGΓ, hGlabel, fun p hp => ?_⟩
  let u := liftLabelMap U.obj p
  obtain ⟨i, hi⟩ := hDcover u.val (hcover u)
  let q : rvLift (U' i).obj :=
    ⟨p.val, (rvLift_restrict_mem_iff U.obj (D i) (hD i) _).mpr ⟨p.property, hi⟩⟩
  obtain ⟨J, hJ, hrep⟩ := hFJ i q hp
  have hGJ := HasMixedVFJacobianAt.of_label_restriction (U := U.obj) (V := V.obj)
    (D i) (hD i) (F i) G q p rfl
    (hGlocal i) hJ
  refine ⟨J, hGJ, ?_⟩
  have he : ιU i (liftLabelMap (U' i).obj q) = u := Subtype.ext rfl
  exact hrep.trans (congrArg (fun a => (ω a).val 0) he)

end SpecialTransformations.Section9.GammaLift
