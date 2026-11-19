import Section9.WeightedAffineLift
import Section9.GammaAffineLift
import Section9.GammaWeightedLift
import Section9.GammaLiftRepresentatives
import Section9.GammaMixedJacobianValue

/-! Gamma counterpart of `exists_prescribed_lift_of_finite_heads` (the
lower-dimensional construction with both finite heads placed first). Each
ingredient of the original construction is replaced by its Gamma
counterpart: the weighted head lift, the lift-label representatives, the
total Jacobian of the head lift, and the affine tail lift. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput
  gammaPointCode gammaPointSort vfAt)

namespace SpecialTransformations.Section9.GammaLift

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)}
variable [LinearOrderedCommGroupWithZero Γ]
local notation "VF" => VFType (M := M)

/-- Finite intersections of Gamma graphs. -/
theorem gamma_iInter_graph {I : Type} [Finite I] {a b c d : ℕ}
    {r : I → Point (M := M) a b → Point (M := M) c d → Prop}
    (h : ∀ i, GammaGraphDefinable B (r i)) :
    GammaGraphDefinable B (fun p q => ∀ i, r i p q) := by
  classical
  letI := Fintype.ofFinite I
  have L := gammaLogicInput B
  have hs : ∀ s : Finset I, GammaGraphDefinable B (fun p q => ∀ i ∈ s, r i p q) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      apply SpecialTransformations.Section5.GammaGraphDefinable.congr gamma_true_graph
      intro p q
      simp
    | insert j s hj ih =>
      apply SpecialTransformations.Section5.GammaGraphDefinable.congr
        (SpecialTransformations.Section5.GammaGraphDefinable.inter (h j) ih)
      intro p q
      simp only [Finset.mem_insert, forall_eq_or_imp]
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (hs Finset.univ)
  intro p q
  simp

theorem gamma_vfTupleMap {S : Set M} {n a m : ℕ} {A : DefSet (rawMixedSpace (M := M) n a) S}
    (hA : MixedSetGamma A B) (f : Fin m → Map A (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hf : ∀ i, VFMapGamma (f i) B) : VFMapGamma (vfTupleMap f) B := by
  have L := gammaLogicInput B
  have hR := gamma_iInter_graph (fun i => L.comp_graph (hf i) (L.swap_graph
    (gamma_coordinate_graph (B := B) (n := m) (m := 0) (u := 1) (w := 0) (fun _ => i) Fin.elim0)))
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (L.restrict_graph hA hR)
  intro p z
  constructor
  · rintro ⟨hp, hz⟩
    refine ⟨⟨p, hp⟩, rfl, funext (fun i => ?_)⟩
    obtain ⟨y, ⟨x, hx, hxy⟩, hy⟩ := hz i
    have hxe : x = ⟨p, hp⟩ := Subtype.ext hx
    subst hxe
    show (f i ⟨p, hp⟩).val 0 = z.1 i
    rw [hxy, hy]
    rfl
  · rintro ⟨x, rfl, hz⟩
    refine ⟨x.property, fun i => ⟨((fun _ => z.1 i), Fin.elim0), ⟨x, rfl, ?_⟩, ?_⟩⟩
    · funext t
      fin_cases t
      rw [← hz]
      rfl
    · exact Prod.ext rfl (funext (fun t => Fin.elim0 t))

theorem rvHeadVolume_gamma {S : Set M} {n k : ℕ} (U : RVObject (M := M) S n) (v : Fin k → Fin n)
    (hU : RVMapGamma U.volume B) : RVMapGamma (rvHeadVolume U v) B := by
  have L := gammaLogicInput B
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    (L.comp_graph hU (gamma_coordinate_graph (B := B) (n := 0) (m := n) (u := 0) (w := k) Fin.elim0 v))
  intro p q
  constructor
  · rintro ⟨y, ⟨u, hu, hy⟩, rfl⟩
    refine ⟨u, hu, ?_⟩
    rw [rvHeadVolume_apply]
    change (U.volume u).val ∘ v = y.2 ∘ v
    rw [hy]
  · rintro ⟨u, hu, hq⟩
    refine ⟨(Fin.elim0, (U.volume u).val), ⟨u, hu, rfl⟩, ?_⟩
    refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
    rw [← hq, rvHeadVolume_apply]
    rfl

/-- Gamma total Jacobian map in every VF dimension (constant `1` in dimension zero). -/
theorem gamma_exists_totalMixedJacobianMap_any (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {D : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A D) (hf : MixedMapGamma f B) :
    ∃ j : Map A (DefSet.univ (rawVFSpace (M := M) 1) S), VFMapGamma j B ∧
      ∀ p L, HasMixedVFDerivativeAt f p L → (j p).val 0 = (LinearMap.toMatrix' L).det := by
  by_cases hn : 0 < n
  · exact gamma_exists_totalMixedJacobianMap hc hn f hf
  have hzero : n = 0 := by omega
  subst n
  let P := rawMixedSpace (M := M) 0 r
  let Q := rawVFSpace (M := M) 1
  let C (z : P.Index → M) : Q.Index → M := fun _ => iVFOne
  have hconst : ∀ T : Set M, ∀ {ι : Type}, T.DefinableFun LRV (fun _ : ι → M => iVFOne) :=
    fun T ι => DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfOne Fin.elim0 (fun i => i.elim0))
  have hdom (z : P.domain) : C z.val ∈ Q.domain := ⟨fun _ => (1 : VF), rfl⟩
  let J : Map A (DefSet.univ Q S) := Map.ofCodes A (fun _ _ => (1 : VF)) C
    (fun _ => hconst S) hdom
    (fun z => vfValues_injective (vfValues_decode ⟨C z.val,hdom z⟩))
  refine ⟨J, ?_, fun p L hL => ?_⟩
  · have L := gammaLogicInput B
    have hK : GammaGraphDefinable B (fun (_ : Point (M := M) 0 r) (z : Point (M := M) 1 0) =>
        (z.1 0).val = iVFOne) := by
      apply gamma_graph_of_raw hc _ {w | w (Fin.natAdd (0 + r) (0 : Fin (1 + 0))) = iVFOne}
      · exact (Set.DefinableFun.proj LRV).ofPred_eq (hconst B.real)
      · intro p z
        change _ ↔ Fin.append (gammaPointCode p) (gammaPointCode z) (Fin.natAdd (0 + r) (0 : Fin (1 + 0))) = iVFOne
        rw [Fin.append_right]
        rfl
    apply SpecialTransformations.Section5.GammaGraphDefinable.congr (L.restrict_graph hf.domain hK)
    intro p z
    constructor
    · rintro ⟨hp, hz⟩
      refine ⟨⟨p, hp⟩, rfl, funext (fun i => ?_)⟩
      fin_cases i
      exact (Subtype.ext hz).symm
    · rintro ⟨x, rfl, hz⟩
      refine ⟨x.property, ?_⟩
      rw [← hz]
      rfl
  · obtain ⟨F, hF, hD⟩ := hL
    exact (hasMixedVFJacobianAt_zero_arity f p).unique ⟨F, hF, hD.hasJacobianAt⟩

variable {k m : ℕ}

theorem gamma_affineLift_with_jacobian [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (v : Valuation VF Γ) (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    (U V : RVFiniteObject (M := M) S (k + m))
    (hU : (rvHeadVolume U.obj (productLeft k m)).FiniteFibres)
    (hV : (rvHeadVolume V.obj (productLeft k m)).FiniteFibres)
    (hUΓ : RVMapGamma U.obj.volume B)
    (F : Map (rvLift (rvFiniteHead U (productLeft k m) hU).obj)
      (rvLift (rvFiniteHead V (productLeft k m) hV).obj)) (hF : Function.Bijective F)
    (hFΓ : MixedMapGamma F B)
    (a b : Map (rvLift (rvFiniteHead U (productLeft k m) hU).obj)
      (DefSet.univ (rawVFSpace (M := M) m) S))
    (D c : Map (rvLift (rvFiniteHead U (productLeft k m) hU).obj)
      (DefSet.univ (rawVFSpace (M := M) 1) S)) (j : Fin m)
    (haΓ : VFMapGamma a B) (hbΓ : VFMapGamma b B) (hDΓ : VFMapGamma D B) (hcΓ : VFMapGamma c B)
    (ha : ∀ p i, (a p).val i ≠ 0) (hb : ∀ p i, (b p).val i ≠ 0)
    (haRV : ∀ p, tupleRV (a p).val = U.obj.value
      (liftLabelMap (rvFiniteHead U (productLeft k m) hU).obj p) ∘ productRight k m)
    (hbRV : ∀ p, tupleRV (b p).val = V.obj.value
      (liftLabelMap (rvFiniteHead V (productLeft k m) hV).obj (F p)) ∘ productRight k m)
    (hD : ∀ p L, HasMixedVFDerivativeAt F p L → (D p).val 0 = (LinearMap.toMatrix' L).det)
    (hgood : ∀ p : rvLift (rvFiniteHead U (productLeft k m) hU).obj,
      AlgebraicIndependent (vfParameterField S) p.val.1 →
      affineTailCorrectionGood v (a p).val (b p).val ((D p).val 0) ((c p).val 0)) :
    ∃ G : Map (rvLift U.obj) (rvLift V.obj), Function.Bijective G ∧ MixedMapGamma G B ∧
      (∀ p : rvLift U.obj, (G p).val.2 = (F (rvLiftHeadSelect U (productLeft k m) hU p)).val.2) ∧
      ∀ p : rvLift U.obj, AlgebraicIndependent (vfParameterField S) p.val.1 →
        HasMixedVFJacobianAt G p ((c (rvLiftHeadSelect U (productLeft k m) hU p)).val 0) := by
  obtain ⟨G, hG, hGΓ, hEq⟩ := gamma_affineLift_of_headLift hc v hv U V hU hV hUΓ F hF hFΓ a b D c j
    haΓ hbΓ hDΓ hcΓ ha hb haRV hbRV
  refine ⟨G, hG, hGΓ, fun p => congrArg Prod.snd (hEq p), ?_⟩
  letI : Valued VF Γ := Valued.mk' v
  intro p hp
  let x := rvLiftHeadSelect U (productLeft k m) hU p
  have hx : AlgebraicIndependent (vfParameterField S) x.val.1 :=
    hp.comp (productLeft k m) (productLeft k m).injective
  obtain ⟨L, hL⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv G p hp
  obtain ⟨L₁, hL₁⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv F x hx
  let s p := affineTailSlopesForHead v (a p).val (b p).val j ((D p).val 0) ((c p).val 0)
  have hdet := det_affineLift_of_mixed_derivatives U V hU hV F G (fun p => (a p).val) (fun p => (b p).val) s
    (fun p => congrArg Prod.fst (hEq p)) p L₁ L hL₁ hL
  have hval : (LinearMap.toMatrix' L).det = (c x).val 0 := by
    rw [hdet, ← hD x L₁ hL₁]
    exact (affineTailSlopesForHead_spec v (a x).val (b x).val j ((D x).val 0) ((c x).val 0)
      (ha x) (hb x)).2 (hgood x hx)
  obtain ⟨Q, hQ, hder⟩ := hL
  exact ⟨Q, hQ, hval ▸ hder.hasJacobianAt⟩

theorem gamma_prescribed_lift_of_finite_heads [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    {S : Set M} (hBS : B.real ⊆ S) (hsmallS : Cardinal.mk S < κ)
    (v : Valuation VF Γ) (hv : ∀ x y : VF, VFValued.predV x y ↔ v x ≤ v y)
    {U V : RVFiniteObject (M := M) S (k + m)} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (hheadU : (rvHeadVolume U.obj (productLeft k m)).FiniteFibres)
    (hheadV : (rvHeadVolume V.obj (productLeft k m)).FiniteFibres)
    (hUΓ : RVMapGamma U.obj.volume B) (hVΓ : RVMapGamma V.obj.volume B)
    (heΓ : RVMapGamma ((finiteVolumeProperty S (k + m)).ι.mapIso e).hom.map B)
    (j : Fin m)
    (ω : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S))
    (hωΓ : RVMapGamma ω B)
    (hω₀ : ∀ u, ((ω u).val 0).val ≠ iRVZero)
    (hω : let e₀ := (finiteVolumeProperty S (k + m)).ι.mapIso e
      ∀ (u : U.obj.domain) (x y : Fin (k + m) → VF) (c : VF),
        tupleRV x = U.obj.value u → tupleRV y = V.obj.value (e₀.hom.map u) →
        CanonicalRV.encodedRv c = (ω u).val 0 → v c = (∏ i, v (y i)) / ∏ i, v (x i)) :
    ∃ G : Map (rvLift U.obj) (rvLift V.obj), Function.Bijective G ∧ MixedMapGamma G B ∧
      (∀ p : rvLift U.obj, ((finiteVolumeProperty S (k + m)).ι.mapIso e).hom.map.graph p.val.2 (G p).val.2) ∧
      ∀ p : rvLift U.obj, AlgebraicIndependent (vfParameterField S) p.val.1 →
        ∃ J : VF, HasMixedVFJacobianAt G p J ∧ CanonicalRV.encodedRv J = (ω (liftLabelMap U.obj p)).val 0 := by
  let l := productLeft k m
  let r := productRight k m
  let U₁ := rvFiniteHead U l hheadU
  let V₁ := rvFiniteHead V l hheadV
  let e₀ := (finiteVolumeProperty S (k + m)).ι.mapIso e
  let e₁ := (finiteVolumeProperty S k).ι.mapIso (rvFiniteHeadIso e l l hheadU hheadV hU hV)
  have hU₁Γ : RVMapGamma U₁.obj.volume B := rvHeadVolume_gamma U.obj l hUΓ
  have hV₁Γ : RVMapGamma V₁.obj.volume B := rvHeadVolume_gamma V.obj l hVΓ
  have he₁Γ : RVMapGamma e₁.hom.map B := heΓ
  obtain ⟨F, hF, hFΓ, hlabel, hweight⟩ := gamma_exists_weighted_liftMap_of_rvIso hc hκ hs h00 B hsmall hB
    hBS hsmallS v hv e₁ (fun u i => hU u (l i)) (fun u i => hV u (l i)) hU₁Γ hV₁Γ he₁Γ
  have htag (p : rvLift U₁.obj) : liftLabelMap V₁.obj (F p) = e₀.hom.map (liftLabelMap U₁.obj p) := by
    obtain ⟨u, hu, hFu⟩ := hlabel p
    have hu' : u = liftLabelMap U₁.obj p := Subtype.ext hu
    apply Subtype.ext
    change (F p).val.2 = (e₀.hom.map (liftLabelMap U₁.obj p)).val
    exact hFu.symm.trans (congrArg (fun u => (e₀.hom.map u).val) hu')
  let τ (Q : RVObject (M := M) S (k+m)) (i : Fin m) :=
    rvHeadVolume Q (fun _ : Fin 1 => r i)
  choose A hAΓ hA using fun i : Fin m => gamma_exists_liftLabelRepresentative hc hκ hs h00 B hsmall hB
    hBS U₁ hU₁Γ (τ U.obj i) (rvHeadVolume_gamma U.obj _ hUΓ) (fun u => hU u (r i))
  choose B₁ hB₁Γ hB₁ using fun i : Fin m => gamma_exists_liftLabelRepresentative hc hκ hs h00 B hsmall hB
    hBS V₁ hV₁Γ (τ V.obj i) (rvHeadVolume_gamma V.obj _ hVΓ) (fun u => hV u (r i))
  obtain ⟨c, hcΓ, hC⟩ := gamma_exists_liftLabelRepresentative hc hκ hs h00 B hsmall hB hBS U₁ hU₁Γ ω hωΓ hω₀
  obtain ⟨D, hDΓ, hD⟩ := gamma_exists_totalMixedJacobianMap_any hc F hFΓ
  let a := vfTupleMap A
  let b := (vfTupleMap B₁).comp F
  have haΓ : VFMapGamma a B := gamma_vfTupleMap (lift_gamma U₁.obj hU₁Γ) A hAΓ
  have hbΓ : VFMapGamma b B := by
    have hB' := gamma_vfTupleMap (lift_gamma V₁.obj hV₁Γ) B₁ hB₁Γ
    apply SpecialTransformations.Section5.GammaGraphDefinable.congr
      ((gammaLogicInput B).comp_graph hFΓ hB')
    intro p z
    constructor
    · rintro ⟨y, ⟨x, rfl, rfl⟩, x', hx', hz⟩
      have hxx : x' = F x := Subtype.ext hx'
      subst hxx
      exact ⟨x, rfl, hz⟩
    · rintro ⟨x, rfl, hz⟩
      exact ⟨_, ⟨x, rfl, rfl⟩, F x, rfl, hz⟩
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
  have hgood (p : rvLift U₁.obj) (hp : AlgebraicIndependent (vfParameterField S) p.val.1) :
      affineTailCorrectionGood v (a p).val (b p).val ((D p).val 0) ((c p).val 0) := by
    letI : Valued VF Γ := Valued.mk' v
    obtain ⟨J, hJ, hvJ⟩ := hweight p hp
    obtain ⟨L, hL⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmallS hv F p hp
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
  obtain ⟨G, hG, hGΓ, hGlabel, hGjac⟩ := gamma_affineLift_with_jacobian hc hκ hs hsmallS v hv U V hheadU hheadV
    hUΓ F hF hFΓ a b D c j haΓ hbΓ hDΓ hcΓ ha hb haRV hbRV hD hgood
  refine ⟨G, hG, hGΓ, ?_, ?_⟩
  · intro p
    rw [hGlabel]
    exact hlabel (rvLiftHeadSelect U l hheadU p)
  · intro p hp
    let x := rvLiftHeadSelect U l hheadU p
    have hx : liftLabelMap U₁.obj x = liftLabelMap U.obj p := Subtype.ext rfl
    exact ⟨(c x).val 0, hGjac p hp, hx ▸ hC x⟩

end SpecialTransformations.Section9.GammaLift
