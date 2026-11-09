import Section9.AffineLiftPrescribedJacobian
import Section9.WeightedLiftJacobian
import Section9.MixedJacobianValue
import Section9.VFCoordinateAssembly

/-! The lower-dimensional construction with both finite heads already
placed first. All maps, representatives and the final lift are over
the original generated base. -/

set_option backward.isDefEq.respectTransparency false

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

theorem exists_prescribed_lift_of_finite_heads [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation VF Γ) (hv : ∀ x y : VF, VFValued.predV x y ↔ v x ≤ v y)
    {U V : RVFiniteObject (M := M) B.real (k + m)} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (hheadU : (rvHeadVolume U.obj (productLeft k m)).FiniteFibres)
    (hheadV : (rvHeadVolume V.obj (productLeft k m)).FiniteFibres)
    (j : Fin m)
    (ω : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) B.real))
    (hω₀ : ∀ u, ((ω u).val 0).val ≠ iRVZero)
    (hω : let e₀ := (finiteVolumeProperty B.real (k + m)).ι.mapIso e
      ∀ (u : U.obj.domain) (x y : Fin (k + m) → VF) (c : VF),
        tupleRV x = U.obj.value u → tupleRV y = V.obj.value (e₀.hom.map u) →
        CanonicalRV.encodedRv c = (ω u).val 0 → v c = (∏ i, v (y i)) / ∏ i, v (x i)) :
    ∃ G : Map (rvLift U.obj) (rvLift V.obj), Function.Bijective G ∧
      (∀ p : rvLift U.obj, ((finiteVolumeProperty B.real (k + m)).ι.mapIso e).hom.map.graph p.val.2 (G p).val.2) ∧
      ∀ p : rvLift U.obj, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
        ∃ J : VF, HasMixedVFJacobianAt G p J ∧ CanonicalRV.encodedRv J = (ω (liftLabelMap U.obj p)).val 0 := by
  let l := productLeft k m
  let r := productRight k m
  let U₁ := rvFiniteHead U l hheadU
  let V₁ := rvFiniteHead V l hheadV
  let e₀ := (finiteVolumeProperty B.real (k + m)).ι.mapIso e
  let e₁ := (finiteVolumeProperty B.real k).ι.mapIso (rvFiniteHeadIso e l l hheadU hheadV hU hV)
  obtain ⟨F, hF, hlabel, hweight⟩ := exists_weighted_liftMap_of_rvIso hc hκ hs h00 B hsmall hB v hv e₁
    (fun u i => hU u (l i)) (fun u i => hV u (l i))
  have htag (p : rvLift U₁.obj) : liftLabelMap V₁.obj (F p) = e₀.hom.map (liftLabelMap U₁.obj p) := by
    obtain ⟨u, hu, hFu⟩ := hlabel p
    have hu' : u = liftLabelMap U₁.obj p := Subtype.ext hu
    apply Subtype.ext
    change (F p).val.2 = (e₀.hom.map (liftLabelMap U₁.obj p)).val
    exact hFu.symm.trans (congrArg (fun u => (e₀.hom.map u).val) hu')
  let τ (Q : RVObject (M := M) B.real (k+m)) (i : Fin m) :=
    rvHeadVolume Q (fun _ : Fin 1 => r i)
  choose A hA using fun i : Fin m => exists_liftLabelRepresentative hc hκ hs h00 B hsmall hB U₁ (τ U.obj i)
    (fun u => hU u (r i))
  choose B₁ hB₁ using fun i : Fin m => exists_liftLabelRepresentative hc hκ hs h00 B hsmall hB V₁ (τ V.obj i)
    (fun u => hV u (r i))
  obtain ⟨c, hC⟩ := exists_liftLabelRepresentative hc hκ hs h00 B hsmall hB U₁ ω hω₀
  obtain ⟨D, hD⟩ := exists_totalMixedJacobianMap F
  let a := vfTupleMap A
  let b := (vfTupleMap B₁).comp F
  have haRV (p : rvLift U₁.obj) : tupleRV (a p).val = U.obj.value (liftLabelMap U₁.obj p) ∘ r :=
    funext fun i => hA i p
  have hbRV (p : rvLift U₁.obj) : tupleRV (b p).val = V.obj.value (liftLabelMap V₁.obj (F p)) ∘ r :=
    funext fun i => hB₁ i (F p)
  have hne (x : VF) (t : CanonicalRV.RVSort M) (ht : t.val ≠ iRVZero)
      (hx : CanonicalRV.encodedRv x = t) : x ≠ 0 := by
    intro hz
    subst x
    exact ht ((congrArg Subtype.val hx).symm.trans (RVCalc.rv_zero_eq ‹M ⊨ Axioms.ACVF›))
  have ha (p : rvLift U₁.obj) (i : Fin m) : (a p).val i ≠ 0 := hne _ _ (hU _ (r i)) (congrFun (haRV p) i)
  have hb (p : rvLift U₁.obj) (i : Fin m) : (b p).val i ≠ 0 := hne _ _ (hV _ (r i)) (congrFun (hbRV p) i)
  have hUhead (p : rvLift U₁.obj) (i : Fin k) : p.val.1 i ≠ 0 := by
    obtain ⟨u, _, hu⟩ := p.property
    exact hne _ _ (hU u (l i)) (congrFun hu i).symm
  have hVhead (p : rvLift V₁.obj) (i : Fin k) : p.val.1 i ≠ 0 := by
    obtain ⟨u, _, hu⟩ := p.property
    exact hne _ _ (hV u (l i)) (congrFun hu i).symm
  have hprod (x : Fin k → VF) (y : Fin m → VF) :
      (∏ i, v (productTuple x y i)) = (∏ i, v (x i)) * ∏ i, v (y i) := by
    rw [← (finSumFinEquiv : Fin k ⊕ Fin m ≃ Fin (k+m)).prod_comp, Fintype.prod_sum_type]
    change (∏ i, v (productTuple x y (l i))) * ∏ i, v (productTuple x y (r i)) = _
    simp only [l, r, productTuple_left, productTuple_right]
  have hgood (p : rvLift U₁.obj) (hp : AlgebraicIndependent (vfParameterField B.real) p.val.1) :
      affineTailCorrectionGood v (a p).val (b p).val ((D p).val 0) ((c p).val 0) := by
    letI : Valued VF Γ := Valued.mk' v
    obtain ⟨J, hJ, hvJ⟩ := hweight p hp
    obtain ⟨L, hL⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv F p hp
    have hDJ : (D p).val 0 = J := by
      rw [hD p L hL]
      obtain ⟨Q, hQ, hL'⟩ := hL
      exact (show HasMixedVFJacobianAt F p _ from ⟨Q, hQ, hL'.hasJacobianAt⟩).unique hJ
    let u := liftLabelMap U₁.obj p
    let x := productTuple p.val.1 (a p).val
    let y := productTuple (F p).val.1 (b p).val
    have hx : tupleRV x = U.obj.value u := by
      obtain ⟨u', hu', hv'⟩ := (rvLift_product_mem_iff_tail U hheadU p _).mpr (haRV p)
      have he : u' = u := Subtype.ext hu'
      exact (he ▸ hv').symm
    have hy : tupleRV y = V.obj.value (e₀.hom.map u) := by
      obtain ⟨u', hu', hv'⟩ := (rvLift_product_mem_iff_tail V hheadV (F p) _).mpr (hbRV p)
      have he : u' = liftLabelMap V₁.obj (F p) := Subtype.ext hu'
      exact ((he.trans (htag p)) ▸ hv').symm
    have hvc := hω u x y ((c p).val 0) hx hy (hC p)
    change v ((c p).val 0) = (∏ i, v (productTuple (F p).val.1 (b p).val i)) /
      ∏ i, v (productTuple p.val.1 (a p).val i) at hvc
    rw [hprod, hprod] at hvc
    exact affineTailCorrectionGood_of_weighted_head v _ _ _ _ _ _
      (Finset.prod_ne_zero_iff.mpr (fun i _ => v.ne_zero_iff.mpr (hUhead p i)))
      (Finset.prod_ne_zero_iff.mpr (fun i _ => v.ne_zero_iff.mpr (hVhead (F p) i)))
      (hDJ.symm ▸ hvJ) hvc
  obtain ⟨G, hG, hGlabel, hGjac⟩ := exists_affineLift_with_jacobian hc hκ hs hsmall v hv U V hheadU hheadV
    F hF a b D c j ha hb haRV hbRV hD hgood
  refine ⟨G, hG, ?_, ?_⟩
  · intro p
    rw [hGlabel]
    exact hlabel (rvLiftHeadSelect U l hheadU p)
  · intro p hp
    let x := rvLiftHeadSelect U l hheadU p
    have hx : liftLabelMap U₁.obj x = liftLabelMap U.obj p := Subtype.ext rfl
    exact ⟨(c x).val 0, hGjac p hp, hx ▸ hC x⟩

end SpecialTransformations.Section9
