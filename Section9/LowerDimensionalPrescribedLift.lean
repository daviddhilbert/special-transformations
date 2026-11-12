module

public import Section9.ReindexedHeadPrescribedLift
public import Section9.SimultaneousHeadCover
public import Section9.FiniteLabelPartition
public import Section9.GlueLabelLifts

@[expose] public section

/-! The lower RV-dimensional branch of the prescribed lift. Finite
heads, their reindexing, and the label partition are all chosen over
the original base. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ] {k m : ℕ}
local notation "VF" => VFType (M := M)

theorem exists_prescribed_lift_of_lower_rvDim [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation VF Γ) (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    {U V : RVFiniteObject (M := M) B.real (k + m)} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (hUdim : rvDim U.obj.volume.image ≤ k) (hVdim : rvDim V.obj.volume.image ≤ k)
    (j : Fin m) (ω : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) B.real))
    (hω : let E := (finiteVolumeProperty B.real (k + m)).ι.mapIso e
      ∀ u : U.obj.domain, Values.vrv ((ω u).val 0) =
        (rvGammaJacobian (U.obj.value u) (V.obj.value (E.hom.map u)) (hU u) (hV (E.hom.map u))).val) :
    ∃ G : Map (rvLift U.obj) (rvLift V.obj), Function.Bijective G ∧
      (∀ p : rvLift U.obj, ((finiteVolumeProperty B.real (k + m)).ι.mapIso e).hom.map.graph p.val.2 (G p).val.2) ∧
      ∀ p : rvLift U.obj, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
        ∃ J : VF, HasMixedVFJacobianAt G p J ∧
          CanonicalRV.encodedRv J = (ω (liftLabelMap U.obj p)).val 0 := by
  let E := (finiteVolumeProperty B.real (k + m)).ι.mapIso e
  obtain ⟨a, b, P, l, r, hP, hcover, hfin⟩ := exists_simultaneous_finite_head_cover hc hκ hs h00
    hsmall (Nat.le_add_right k m) e hUdim hVdim
  obtain ⟨D, hDP, hDcover, hdisj⟩ := exists_disjoint_definable_refinement P
  let hD (i : Fin a × Fin b) := (hDP i).trans (hP i)
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
  have localLift (i : Fin a × Fin b) :=
    exists_prescribed_lift_with_reindexed_heads hc hκ hs h00 B hsmall hB v hv (e' i)
      (fun u => hU (ιU i u)) (fun w => hV (ιV i w)) (l i) (r i) (hfinU i) (hfinV i) j
      (ω.restrict (hD i)) (fun u => hω (ιU i u))
  choose F hF hFlabel hFJ using localLift
  have hlabel (i) (p : rvLift (U' i).obj) : E.hom.map.graph p.val.2 (F i p).val.2 := by
    obtain ⟨u, hu, hFu⟩ := hFlabel i p
    exact ⟨ιU i u, hu, hFu⟩
  obtain ⟨G, hG, hGlabel, hGlocal⟩ := exists_glued_label_lift E D hD
    (fun u => hDcover u.val (hcover u)) hdisj F hF hlabel
  refine ⟨G, hG, hGlabel, fun p hp => ?_⟩
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

end SpecialTransformations.Section9
