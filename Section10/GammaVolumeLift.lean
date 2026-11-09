import Section10.EssentialVFMap
import Section10.WeightedJacobianLocus
import Section9.RVFiniteEssential
import Section9.GammaCompatibility
import Section9.LiftLabelRepresentatives
import Section8.GammaRadiusBase
import Section4.Spaces

/-! Forward lifting for finite-volume Gamma forms in positive degree. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open scoped BigOperators

namespace SpecialTransformations.Section10

noncomputable section

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k r s : ℕ}
local notation "VF" => VFType (M := M)
local notation "Δ" => rawRVSpace (M := M) 1
local notation "n" => (k + 1)
local notation "v" => Values.vfValueHom (M := M)

/-- The existing imaginary Gamma presentation, transported from the
normalization of an already canonical structure. -/
def volumeGammaSpace (hc : CanonicalStructure.IsCanonical (M := M)) : Space LRV M :=
  (normalize_eq_of_isCanonical hc) ▸ (@gammaSpace M sM hM)

private theorem gammaCarrier (hc : CanonicalStructure.IsCanonical (M := M)) :
    (volumeGammaSpace hc).Carrier = Values.Gamma (M := M) := by
  have transport {s t : LRV.Structure M} (h : s = t) (D : @Space LRV M s) :
      (@Space.Carrier LRV M t (h ▸ D)) = (@Space.Carrier LRV M s D) := by
    cases h
    rfl
  exact transport (normalize_eq_of_isCanonical hc) _

/-- A definable map into the actual Gamma imaginary, using all its RV
codes in the graph presentation. -/
abbrev GammaVolumeForm (hc : CanonicalStructure.IsCanonical (M := M))
    {P : Space LRV M} (A : DefSet P S) := Map A (DefSet.univ (volumeGammaSpace hc) S)

def gammaFormValue {hc : CanonicalStructure.IsCanonical (M := M)}
    {P : Space LRV M} {A : DefSet P S} (ω : GammaVolumeForm hc A) (p : A) :
    Values.Gamma (M := M) :=
  cast (gammaCarrier hc) (ω p).val

structure GammaVolumeObject (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) where
  underlying : RVFiniteObject (M := M) S (k + 1)
  form : GammaVolumeForm hc underlying.obj.domain

namespace GammaVolumeObject

variable {hc : CanonicalStructure.IsCanonical (M := M)}

def essential (U : GammaVolumeObject hc S k) : GammaVolumeObject hc S k :=
  ⟨rvFiniteEssential U.underlying,
    U.form.comp (Map.inclusion (rvEssentialLabels_subset U.underlying.obj))⟩

def liftForm (U : GammaVolumeObject hc S k) : GammaVolumeForm hc (rvLift U.underlying.obj) :=
  U.form.comp (liftLabelMap U.underlying.obj)

end GammaVolumeObject

/-- The Gamma form of Definition 10.3 has the pointwise Gamma rule. -/
structure GammaVolumeIso {hc : CanonicalStructure.IsCanonical (M := M)}
    (U V : GammaVolumeObject hc S k) where
  labels : RVFiniteEssentialIso U.underlying V.underlying
  rule : let E := (finiteVolumeProperty S n).ι.mapIso labels
    ∀ u : U.essential.underlying.obj.domain,
      gammaFormValue U.essential.form u =
        gammaFormValue V.essential.form (E.hom.map u) *
          rvGammaJacobian (U.essential.underlying.obj.value u)
            (V.essential.underlying.obj.value (E.hom.map u))
            (rvEssential_value_nonzero U.underlying.obj u)
            (rvEssential_value_nonzero V.underlying.obj (E.hom.map u))

def GammaMeasurePreserving {hc : CanonicalStructure.IsCanonical (M := M)}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : EssentialVFMap A B) (ω : GammaVolumeForm hc A) (η : GammaVolumeForm hc B) : Prop :=
  ∀ p : f.source, ∃ J : VF, HasMixedVFJacobianAt f.map p J ∧
    (gammaFormValue ω ⟨p.val, f.source_subset p.property⟩).val =
      (gammaFormValue η ⟨(f.map p).val, f.target_subset (f.map p).property⟩).val * v J

private theorem lift_volume (U : RVObject (M := M) S n) (p : rvLift U) :
    U.value (liftLabelMap U p) = tupleRV p.val.1 := by
  obtain ⟨u, hu, hvol⟩ := p.property
  exact (Subtype.ext hu.symm : liftLabelMap U p = u).symm ▸ hvol

private theorem rvVolumeGamma_value (t : Fin n → CanonicalRV.RVSort M)
    (ht : ∀ i, (t i).val ≠ iRVZero) (x : Fin n → VF) (hx : tupleRV x = t) :
    (rvVolumeGamma t ht).val = v (∏ i, x i) := by
  subst t
  rw [map_prod]
  exact map_prod Values.gammaValHom (fun i => Values.gammaOf (tupleRV x i) (ht i)) Finset.univ

/-- The Gamma-valued forward lift uses the weighted lift and needs no
residue-Jacobian comparison. -/
theorem theorem_10_5_gamma_volume [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hB : VFGammaGeneratedBase ⟨(C.base : Set M), Ξ⟩)
    {U V : GammaVolumeObject hc (C.base : Set M) k} (e : GammaVolumeIso U V) :
    let E := (finiteVolumeProperty (C.base : Set M) n).ι.mapIso e.labels
    ∃ g : EssentialVFMap (rvLift U.underlying.obj) (rvLift V.underlying.obj),
      GammaMeasurePreserving g U.liftForm V.liftForm ∧
        ∀ p : g.source, E.hom.map.graph p.val.2 (g.map p).val.2 := by
  let S := (C.base : Set M)
  let E := (finiteVolumeProperty S n).ι.mapIso e.labels
  let w := Values.presentationValuation (M := M)
  have hU := rvEssential_value_nonzero U.underlying.obj
  have hV := rvEssential_value_nonzero V.underlying.obj
  obtain ⟨f, hf, hlabel, hW⟩ := exists_weighted_liftMap_of_rvIso hc C.uncountable.le C.saturated
    C.model00 ⟨S, Ξ⟩ C.small hB w Values.presentation_compatible E hU hV
  have htag (p : rvLift U.essential.underlying.obj) :
      E.hom.map (liftLabelMap U.essential.underlying.obj p) =
        liftLabelMap V.essential.underlying.obj (f p) :=
    Subtype.ext ((E.hom.map.graph_apply (liftLabelMap U.essential.underlying.obj p) _).mp (hlabel p))
  have hweight (p : rvLift U.essential.underlying.obj) :
      let u := liftLabelMap U.essential.underlying.obj p
      (rvGammaJacobian (U.essential.underlying.obj.value u)
        (V.essential.underlying.obj.value (E.hom.map u)) (hU u) (hV (E.hom.map u))).val =
        v (∏ i, (f p).val.1 i) / v (∏ i, p.val.1 i) := by
    let u := liftLabelMap U.essential.underlying.obj p
    have hx : tupleRV p.val.1 = U.essential.underlying.obj.value u :=
      (lift_volume U.essential.underlying.obj p).symm
    have hy : tupleRV (f p).val.1 = V.essential.underlying.obj.value (E.hom.map u) :=
      (lift_volume V.essential.underlying.obj (f p)).symm.trans
        (congrArg V.essential.underlying.obj.value (htag p).symm)
    have hdiv (a b : Values.Gamma (M := M)) : (a / b).val = a.val / b.val := by
      rw [div_eq_mul_inv, Values.gamma_val_mul, Values.gamma_val_inv, div_eq_mul_inv]
    change (rvVolumeGamma _ (hV (E.hom.map u)) / rvVolumeGamma _ (hU u)).val = _
    exact (hdiv _ _).trans (congrArg₂ (fun a b : Values.GammaTop (M := M) => a / b)
      (rvVolumeGamma_value _ _ _ hy) (rvVolumeGamma_value _ _ _ hx))
  have hsource (p : rvLift U.essential.underlying.obj) : (∏ i, p.val.1 i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    exact fun i _ => ((mem_rvEssentialLift U.underlying.obj p.val).mp p.property).2 i
  obtain ⟨Z, hZ, hJ⟩ := exists_weightedJacobian_exception hc C.uncountable.le C.saturated C.small
    (Nat.zero_lt_succ k) f (by
      intro p hp
      obtain ⟨J, hJ, hw⟩ := hW p hp
      refine ⟨J, hJ, ?_⟩
      have hne : (∏ i, w (p.val.1 i)) ≠ 0 := by
        rw [← map_prod]
        exact (map_ne_zero w).mpr (hsource p)
      have hNative : w (J * ∏ i, p.val.1 i) = w (∏ i, (f p).val.1 i) := by
        rw [map_mul, map_prod, map_prod, hw, div_mul_cancel₀ _ hne]
      exact le_antisymm
        ((Values.vf_pred_iff_gamma_le _ _).mp ((Values.presentation_compatible _ _).mpr hNative.ge))
        ((Values.vf_pred_iff_gamma_le _ _).mp ((Values.presentation_compatible _ _).mpr hNative.le)))
  obtain ⟨g, hg⟩ := EssentialVFMap.exists_restriction_preserving_jacobian hc C.saturated C.small
    (Nat.zero_lt_succ k) f hf Z hZ
  let g' := g.widen hc C.saturated C.small
    (fun p hp => ((mem_rvEssentialLift U.underlying.obj p).mp hp).1)
    (fun p hp => ((mem_rvEssentialLift V.underlying.obj p).mp hp).1)
    (rvEssentialLift_complement_dim_lt Δ U.underlying.obj)
    (rvEssentialLift_complement_dim_lt Δ V.underlying.obj)
  refine ⟨g', ?_, ?_⟩
  · intro p
    obtain ⟨hz, hval, htransfer⟩ := hg p
    let q : rvLift U.essential.underlying.obj := ⟨p.val, g.source_subset p.property⟩
    let u := liftLabelMap U.essential.underlying.obj q
    obtain ⟨J, hder, hdet⟩ := hJ q hz
    have hvalJ : v J = v (∏ i, (f q).val.1 i) / v (∏ i, q.val.1 i) :=
      (eq_div_iff ((map_ne_zero v).mpr (hsource q))).mpr
        (by simpa only [map_mul] using hdet)
    have he : gammaFormValue V.liftForm ⟨(g'.map p).val, g'.target_subset (g'.map p).property⟩ =
        gammaFormValue V.essential.form (E.hom.map u) := by
      have ht := (congrArg Subtype.val (htag q)).trans (congrArg Prod.snd hval).symm
      change gammaFormValue V.form _ = gammaFormValue V.form _
      exact congrArg (gammaFormValue V.form) (Subtype.ext ht.symm)
    refine ⟨J, htransfer J hder, ?_⟩
    rw [he, hvalJ, ← hweight q]
    exact congrArg Subtype.val (e.rule u)
  · intro p
    have he := congrArg Prod.snd (hg p).2.1
    exact he.symm ▸ hlabel ⟨p.val, g.source_subset p.property⟩

end

end SpecialTransformations.Section10
