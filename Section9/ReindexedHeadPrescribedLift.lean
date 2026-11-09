import Section9.FiniteHeadPrescribedLift
import Section9.FiniteHeadCover
import Section9.PermutationVolumeSigns

/-! The finite-head construction can use different coordinate
selections on the source and target. The two permutation signs are
included in the prescribed form before applying the fixed-head result. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

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
local notation "RV" => CanonicalRV.RVSort M

theorem exists_prescribed_lift_with_reindexed_heads [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation VF Γ) (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    {U V : RVFiniteObject (M := M) B.real (k + m)} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (a b : Fin k ↪ Fin (k + m))
    (hheadU : (rvHeadVolume U.obj a).FiniteFibres)
    (hheadV : (rvHeadVolume V.obj b).FiniteFibres) (j : Fin m)
    (ω : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) B.real))
    (hω : let E := (finiteVolumeProperty B.real (k + m)).ι.mapIso e
      ∀ u : U.obj.domain, Values.vrv ((ω u).val 0) =
        (rvGammaJacobian (U.obj.value u) (V.obj.value (E.hom.map u)) (hU u) (hV (E.hom.map u))).val) :
    ∃ G : Map (rvLift U.obj) (rvLift V.obj), Function.Bijective G ∧
      (∀ p : rvLift U.obj, ((finiteVolumeProperty B.real (k + m)).ι.mapIso e).hom.map.graph p.val.2 (G p).val.2) ∧
      ∀ p : rvLift U.obj, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
        ∃ J : VF, HasMixedVFJacobianAt G p J ∧ CanonicalRV.encodedRv J = (ω (liftLabelMap U.obj p)).val 0 := by
  obtain ⟨σ, hσ⟩ := exists_head_reindex a
  obtain ⟨τ, hτ⟩ := exists_head_reindex b
  let U' := rvFiniteReindexVolume U σ
  let V' := rvFiniteReindexVolume V τ
  let I := (finiteVolumeProperty B.real (k + m)).ι
  let E := I.mapIso e
  let IU := rvFiniteReindexIso U σ
  let IV := rvFiniteReindexIso V τ
  let E' := IU.symm ≪≫ e ≪≫ IV
  have hmap (u : U'.obj.domain) : (I.mapIso E').hom.map u = E.hom.map u := by
    have hInv : (I.mapIso IU).inv.map u = u := by
      have h := rvIso_apply_inv (I.mapIso IU) u
      exact h
    change (I.mapIso IV).hom.map (E.hom.map ((I.mapIso IU).inv.map u)) = _
    rw [hInv]
    rfl
  have ha' : (rvHeadVolume U'.obj (productLeft k m)).FiniteFibres := by
    intro x
    apply (hheadU x).subset
    intro u hu
    change rvHeadVolume U.obj a u = x
    change rvHeadVolume U'.obj (productLeft k m) u = x at hu
    apply Subtype.ext
    funext i
    have h := congrFun (congrArg Subtype.val hu) i
    change U.obj.value u (σ (productLeft k m i)) = x.val i at h
    rwa [hσ] at h
  have hb' : (rvHeadVolume V'.obj (productLeft k m)).FiniteFibres := by
    intro x
    apply (hheadV x).subset
    intro u hu
    change rvHeadVolume V.obj b u = x
    change rvHeadVolume V'.obj (productLeft k m) u = x at hu
    apply Subtype.ext
    funext i
    have h := congrFun (congrArg Subtype.val hu) i
    change V.obj.value u (τ (productLeft k m i)) = x.val i at h
    rwa [hτ] at h
  obtain ⟨P, hP⟩ := exists_permutationSign_map (M := M) B.real σ
  obtain ⟨Q, hQ⟩ := exists_permutationSign_map (M := M) B.real τ
  let ω' := Q.comp (P.comp ω)
  let φ : VF →*₀ RV := RVOperations.rvHom
  have hω' (u : U'.obj.domain) :
      (ω' u).val 0 = φ (Equiv.Perm.sign τ : VF) * (φ (Equiv.Perm.sign σ : VF) * (ω u).val 0) :=
    (hQ (P (ω u)) 0).trans (congrArg (fun t => φ (Equiv.Perm.sign τ : VF) * t) (hP (ω u) 0))
  have hn (u : U'.obj.domain) : ((ω' u).val 0).val ≠ iRVZero := by
    have h := rv_nonzero_of_gammaJacobian_value _ _ (hU u) (hV (E.hom.map u)) _ (hω u)
    have ho : (ω u).val 0 ≠ 0 := fun e => h ((congrArg Subtype.val e).trans RVOperations.zero_val)
    have hsign (ρ : Equiv.Perm (Fin (k + m))) : φ (Equiv.Perm.sign ρ : VF) ≠ 0 :=
      (RVOperations.rv_ne_zero _).mpr (fun hz => by
        have hv := vfPermSign_sq (M := M) ρ
        rw [hz, zero_pow (by decide : 2 ≠ 0)] at hv
        exact zero_ne_one hv)
    have hg := mul_ne_zero (hsign τ) (mul_ne_zero (hsign σ) ho)
    intro he
    exact hg (Subtype.ext ((congrArg Subtype.val (hω' u)).symm.trans (he.trans RVOperations.zero_val.symm)))
  have hValue (u : U'.obj.domain) (x y : Fin (k+m) → VF) (c : VF)
      (hx : tupleRV x = U'.obj.value u)
      (hy : tupleRV y = V'.obj.value ((I.mapIso E').hom.map u))
      (hrep : CanonicalRV.encodedRv c = (ω' u).val 0) :
      v c = (∏ i, v (y i)) / ∏ i, v (x i) := by
    obtain ⟨c₀, hc₀⟩ := CanonicalRV.encodedRv_surjective ((ω u).val 0)
    have hxc : tupleRV (x ∘ σ.symm) = U.obj.value u := by
      funext i
      have h := congrFun hx (σ.symm i)
      change tupleRV x (σ.symm i) = U.obj.value u (σ (σ.symm i)) at h
      rwa [σ.apply_symm_apply] at h
    have hyc : tupleRV (y ∘ τ.symm) = V.obj.value (E.hom.map u) := by
      rw [hmap] at hy
      funext i
      have h := congrFun hy (τ.symm i)
      change tupleRV y (τ.symm i) = V.obj.value (E.hom.map u) (τ (τ.symm i)) at h
      rwa [τ.apply_symm_apply] at h
    have h := rvGammaJacobian_value_of_representatives v hv _ _ (hU u) (hV (E.hom.map u))
      _ (hω u) _ _ c₀ hxc hyc hc₀
    let d := (Equiv.Perm.sign τ : VF) * ((Equiv.Perm.sign σ : VF) * c₀)
    have he : φ c = φ d := by
      change _ = φ (_ * (_ * c₀))
      rw [show φ c = (ω' u).val 0 from hrep, hω', map_mul, map_mul, show φ c₀ = _ from hc₀]
    have hvcd : v c = v d := by
      have he' : Values.vfValueHom c = Values.vfValueHom d := congrArg Values.vrv he
      exact le_antisymm ((hv c d).mp ((Values.vf_pred_iff_gamma_le c d).mpr he'.ge))
        ((hv d c).mp ((Values.vf_pred_iff_gamma_le d c).mpr he'.le))
    rw [hvcd]
    change v ((Equiv.Perm.sign τ : VF) * ((Equiv.Perm.sign σ : VF) * c₀)) = _
    rw [map_mul, map_mul, vfPermSign_valuation, vfPermSign_valuation, one_mul, one_mul, h]
    exact congrArg₂ (· / ·) (Equiv.prod_comp τ.symm (fun i => v (y i)))
      (Equiv.prod_comp σ.symm (fun i => v (x i)))
  obtain ⟨F, hF, hlabel, hFJ⟩ := exists_prescribed_lift_of_finite_heads hc hκ hs h00 B hsmall hB v hv E'
    (fun u i => hU u (σ i)) (fun u i => hV u (τ i)) ha' hb' j ω' hn hValue
  let s := rvLiftReindexMap U σ
  let t := rvLiftUnreindexMap V τ
  let G := t.comp (F.comp s)
  letI : Valued VF Γ := Valued.mk' v
  refine ⟨G, (rvLiftUnreindexMap_bijective V τ).comp (hF.comp (rvLiftReindexMap_bijective U σ)), ?_, ?_⟩
  · intro p
    obtain ⟨u, hu, hu'⟩ := hlabel (s p)
    refine ⟨u, hu, ?_⟩
    change _ = (t (F (s p))).val.2
    rw [← hmap u, rvLiftUnreindexMap_apply]
    exact hu'
  · intro p hp
    have hsp := independent_map_of_finiteFibres hc s
      (Map.finiteFibres_of_injective (rvLiftReindexMap_bijective U σ).injective) p hp
    have hFp := independent_map_of_finiteFibres hc F
      (Map.finiteFibres_of_injective hF.injective) (s p) hsp
    obtain ⟨L, hL⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv F (s p) hsp
    obtain ⟨K, hK⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv (F.comp s) p hp
    have hsDer := hasMixedVFDerivativeAt_liftReindex_of_independent hc hκ hs hsmall hv U σ p hp
    have htDer := hasMixedVFDerivativeAt_liftUnreindex_of_independent hc hκ hs hsmall hv V τ (F (s p)) hFp
    obtain ⟨_, hFL, hsL⟩ := mixedVFJacobian_comp_of_full_derivative hsDer hL
    obtain ⟨hFK, _, hGdet⟩ := mixedVFJacobian_comp_of_full_derivative hK htDer
    obtain ⟨J, hJ, hrep⟩ := hFJ (s p) hsp
    have hst : (LinearMap.toMatrix' K).det = (LinearMap.toMatrix' L).det * (Equiv.Perm.sign σ : VF) := by
      rw [hFK.unique hsL, det_vfReindexLinear]
    have hτsign : (Equiv.Perm.sign τ.symm : VF) * (Equiv.Perm.sign τ : VF) = 1 := by
      simpa only [Equiv.Perm.sign_symm, pow_two] using vfPermSign_sq (M := M) τ
    have hσsign : (Equiv.Perm.sign σ : VF) * (Equiv.Perm.sign σ : VF) = 1 := by
      simpa only [pow_two] using vfPermSign_sq (M := M) σ
    have hlabelEq : liftLabelMap U'.obj (s p) = liftLabelMap U.obj p := Subtype.ext rfl
    refine ⟨_, hGdet, ?_⟩
    change φ _ = _
    rw [det_vfReindexLinear, hst, hFL.unique hJ, map_mul, map_mul, show φ J = _ from hrep,
      hω', hlabelEq]
    calc
      _ = φ ((Equiv.Perm.sign τ.symm : VF) * (Equiv.Perm.sign τ : VF)) *
          (φ ((Equiv.Perm.sign σ : VF) * (Equiv.Perm.sign σ : VF)) * (ω (liftLabelMap U.obj p)).val 0) := by
        rw [map_mul, map_mul]
        ac_rfl
      _ = _ := by rw [hτsign, hσsign, map_one, one_mul, one_mul]

end SpecialTransformations.Section9
