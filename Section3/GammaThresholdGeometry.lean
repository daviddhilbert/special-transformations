module

public import Section3.AlgebraicRVLifting
public import Section3.CMinimal
public import Section3.GammaDensity
public import Section3.RVFibreGeometry

@[expose] public section

/- Component: GammaThresholdGeometry -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.GammaThresholdGeometry
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

include hv in
/-- The ball code gives an actual FV representative of its radius.
This follows the checked encodedBall_disc proof without forgetting that
representative when passing to the arbitrary valuation codomain. -/
theorem encodedBall_good (B : Set M) (hB : IsBall B) :
    ValOneEC.Good (RingHom.id (VFType (M := M))) v {x | x.val ∈ B} := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  rcases hB with hB | ⟨a,t,ha,ht,ht0,hB⟩ | (⟨a,t,ha,ht,ht0,hB⟩ | ⟨a,ha,hB⟩)
  · have he : {x : VFType (M := M) | x.val ∈ B} = Set.univ := by
      ext x
      rw [hB]
      exact iff_true_intro x.property
    rw [he]
    exact ValOneEC.good_univ _ _
  · let a' : VFType (M := M) := ⟨a,ha⟩
    obtain ⟨b,hb⟩ := CanonicalRV.encodedRv_surjective (⟨t,ht⟩ : CanonicalRV.RVSort M)
    have hb' : iRv b.val = t := congrArg Subtype.val hb
    have he : {x : VFType (M := M) | x.val ∈ B} = ValOneEC.closedBall v a' (v b) := by
      ext x
      change x.val ∈ B ↔ v (x-a') ≤ v b
      rw [hB]
      change (iVF x.val ∧ iLe t (iRv (iVFAdd x.val (iVFNeg a)))) ↔ _
      rw [and_iff_right x.property]
      have hd : (x-a').val = iVFAdd x.val (iVFNeg a) := by rw [sub_eq_add_neg]; rfl
      have hh := hv (x-a') b
      change iLe (iRv b.val) (iRv (x-a').val) ↔ _ at hh
      rw [hb',hd] at hh
      exact hh
    rw [he]
    exact ValOneEC.good_of_isKBall (ValOneEC.IsKBall.closed a' b)
  · let a' : VFType (M := M) := ⟨a,ha⟩
    obtain ⟨b,hb⟩ := CanonicalRV.encodedRv_surjective (⟨t,ht⟩ : CanonicalRV.RVSort M)
    have hb' : iRv b.val = t := congrArg Subtype.val hb
    have he : {x : VFType (M := M) | x.val ∈ B} = ValOneEC.openBall v a' (v b) := by
      ext x
      change x.val ∈ B ↔ v (x-a') < v b
      rw [hB]
      change (iVF x.val ∧ iLe t (iRv (iVFAdd x.val (iVFNeg a))) ∧
        ¬ iLe (iRv (iVFAdd x.val (iVFNeg a))) t) ↔ _
      rw [and_iff_right x.property]
      have hd : (x-a').val = iVFAdd x.val (iVFNeg a) := by rw [sub_eq_add_neg]; rfl
      have hle := hv (x-a') b
      have hge := hv b (x-a')
      change iLe (iRv b.val) (iRv (x-a').val) ↔ _ at hle
      change iLe (iRv (x-a').val) (iRv b.val) ↔ _ at hge
      rw [hb',hd] at hle hge
      rw [hle,hge,lt_iff_le_not_ge]
    rw [he]
    exact ValOneEC.good_of_isKBall (ValOneEC.IsKBall.openball a' b)
  · let a' : VFType (M := M) := ⟨a,ha⟩
    have he : {x : VFType (M := M) | x.val ∈ B} = {a'} := by
      ext x
      rw [hB]
      change (iVF x.val ∧ x.val = a) ↔ x = a'
      rw [and_iff_right x.property]
      exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
    rw [he]
    exact ValOneEC.good_singleton _ _ a'

include hv in
theorem boolean_good (A : Set M) (hA : IsBoolComb {B : Set M | IsBall B} A) :
    ValOneEC.Good (RingHom.id (VFType (M := M))) v {x | x.val ∈ A} := by
  induction hA with
  | basic hB => exact encodedBall_good v hv _ hB
  | univ => exact ValOneEC.good_univ _ _
  | compl _ ih => exact ValOneEC.good_compl ih
  | union _ _ ih ih' => exact ValOneEC.good_union ih ih'

def vfGamma (x : VFType (M := M)) (hx : x ≠ 0) : Values.Gamma (M := M) :=
  Values.gammaOf (CanonicalRV.encodedRv x) (fun h => hx ((CanonicalRV.encodedRv_zero_iff x).mp h))

include hv in
theorem value_le_gamma (x y : VFType (M := M)) (hx : x ≠ 0) (hy : y ≠ 0) :
    v x ≤ v y ↔ vfGamma y hy ≤ vfGamma x hx := by
  change v x ≤ v y ↔ Values.vrv (CanonicalRV.encodedRv y) ≤ Values.vrv (CanonicalRV.encodedRv x)
  rw [Values.vrv_le_iff]
  exact (hv x y).symm

include hv in
theorem value_lt_gamma (x y : VFType (M := M)) (hx : x ≠ 0) (hy : y ≠ 0) :
    v x < v y ↔ vfGamma y hy < vfGamma x hx := by
  rw [lt_iff_le_not_ge,lt_iff_le_not_ge,
    value_le_gamma v hv x y hx hy,value_le_gamma v hv y x hy hx]

theorem lift_avoiding (h00 : M ⊨ Axioms.ACVF00) (γ : Values.Gamma (M := M))
    (T : Set (CanonicalRV.RVSort M)) (hT : T.Finite) :
    ∃ x : VFType (M := M), ∃ hx : x ≠ 0, vfGamma x hx = γ ∧ CanonicalRV.encodedRv x ∉ T := by
  obtain ⟨t,htγ,htT⟩ := ((Values.infinite_gamma_fibre h00 γ).sdiff hT).nonempty
  obtain ⟨x,hx⟩ := CanonicalRV.encodedRv_surjective t
  have hx0 : x ≠ 0 := by
    intro hz
    apply γ.property
    rw [← htγ,← hx,hz]
    exact (Values.vrv_eq_infinity_iff _).mpr ((CanonicalRV.encodedRv_zero_iff _).mpr rfl)
  refine ⟨x,hx0,Subtype.ext ?_,?_⟩
  · change Values.vrv (CanonicalRV.encodedRv x) = γ.val
    rw [hx]; exact htγ
  · rw [hx]; exact htT

include hv in
theorem ball_cut_pattern (B : Set (VFType (M := M)))
    (hB : ValOneEC.IsKBall (RingHom.id (VFType (M := M))) v B) :
    ∃ c : VFType (M := M), ∃ δ : Values.Gamma (M := M),
      ∀ x y : VFType (M := M), ∀ hx : x ≠ 0, ∀ hy : y ≠ 0,
        CanonicalRV.encodedRv x ≠ CanonicalRV.encodedRv c →
        CanonicalRV.encodedRv y ≠ CanonicalRV.encodedRv c →
        FiniteThresholds.SameCuts {δ} (vfGamma x hx) (vfGamma y hy) → (x ∈ B ↔ y ∈ B) := by
  cases hB with
  | univ => exact ⟨0,1,fun _ _ _ _ _ _ _ => Iff.rfl⟩
  | closed a b =>
    by_cases hb : b = 0
    · subst b
      refine ⟨a,1,fun x y hx hy hxa hya _ => ?_⟩
      simp only [RingHom.id_apply,map_zero,ValOneEC.closedBall_zero_radius,Set.mem_singleton_iff]
      exact iff_of_false (fun h => hxa (congrArg CanonicalRV.encodedRv h))
        (fun h => hya (congrArg CanonicalRV.encodedRv h))
    · refine ⟨a,vfGamma b hb,fun x y hx hy hxa hya hcuts => ?_⟩
      have hc := not_congr (hcuts (vfGamma b hb) (Finset.mem_singleton_self _)).1
      have hle : vfGamma b hb ≤ vfGamma x hx ↔ vfGamma b hb ≤ vfGamma y hy := by
        simpa only [not_lt] using hc
      change v (x-a) ≤ v b ↔ v (y-a) ≤ v b
      rw [CoefficientRVGeometry.distance_eq_max v hv x a hxa,
        CoefficientRVGeometry.distance_eq_max v hv y a hya,max_le_iff,max_le_iff]
      exact and_congr ((value_le_gamma v hv x b hx hb).trans
        (hle.trans (value_le_gamma v hv y b hy hb).symm)) Iff.rfl
  | openball a b =>
    by_cases hb : b = 0
    · subst b
      refine ⟨a,1,fun x y _ _ _ _ _ => ?_⟩
      simp only [RingHom.id_apply,ValOneEC.openBall,map_zero,not_lt_zero,Set.mem_ofPred_eq]
    · refine ⟨a,vfGamma b hb,fun x y hx hy hxa hya hcuts => ?_⟩
      have hlt := (hcuts (vfGamma b hb) (Finset.mem_singleton_self _)).2
      change v (x-a) < v b ↔ v (y-a) < v b
      rw [CoefficientRVGeometry.distance_eq_max v hv x a hxa,
        CoefficientRVGeometry.distance_eq_max v hv y a hya,max_lt_iff,max_lt_iff]
      exact and_congr ((value_lt_gamma v hv x b hx hb).trans
        (hlt.trans (value_lt_gamma v hv y b hy hb).symm)) Iff.rfl

include hv in
/-- A radial Good set induces a finite actual-threshold basis on Gamma.
The finite centers and angular representatives are only proof data. -/
theorem good_finite_thresholds (h00 : M ⊨ Axioms.ACVF00)
    (U : Set (VFType (M := M))) (hU : ValOneEC.Good (RingHom.id _) v U)
    (A : Set (Values.Gamma (M := M)))
    (hRadial : ∀ x hx, x ∈ U ↔ vfGamma x hx ∈ A) :
    ∃ E : Finset (Values.Gamma (M := M)), FiniteThresholds.Determines E A := by
  obtain ⟨ι,hι,B,b,hB,hb⟩ := hU
  letI := hι
  choose c δ hc using fun i => ball_cut_pattern v hv (B i) (hB i)
  let T := Set.range (fun i => CanonicalRV.encodedRv (c i))
  have hT : T.Finite := Set.finite_range _
  let E := Finset.univ.image δ
  refine ⟨E,fun γ η hcuts => ?_⟩
  obtain ⟨x,hx,hxγ,hxT⟩ := lift_avoiding h00 γ T hT
  obtain ⟨y,hy,hyη,hyT⟩ := lift_avoiding h00 η T hT
  have hprofile : {i | x ∈ B i} = {i | y ∈ B i} := by
    ext i
    have hi : δ i ∈ E := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    have hsingle : FiniteThresholds.SameCuts {δ i} γ η := by
      intro e he
      have he' : e = δ i := Finset.mem_singleton.mp he
      exact he'.symm ▸ hcuts (δ i) hi
    rw [← hxγ,← hyη] at hsingle
    exact hc i x y hx hy (fun he => hxT ⟨i,he.symm⟩) (fun he => hyT ⟨i,he.symm⟩) hsingle
  have hxy : x ∈ U ↔ y ∈ U := by rw [hb x,hb y,hprofile]
  have hxA := hRadial x hx
  have hyA := hRadial y hy
  rw [hxγ] at hxA
  rw [hyη] at hyA
  exact hxA.symm.trans (hxy.trans hyA)

end SpecialTransformations.Section3.GammaThresholdGeometry

namespace SpecialTransformations.Section3.GammaParameters
open GammaThresholdGeometry
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Every actual Gamma-definable unary set has a finite actual-threshold
basis. This is derived from C-minimality and angular infinitude, with full
imaginary parameters allowed and no order-completeness premise. -/
theorem gamma_definable_finite_thresholds (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (A : Set (Values.Gamma (M := M)))
    (hA : GammaDefinableOverBase B A) :
    ∃ E : Finset (Values.Gamma (M := M)), FiniteThresholds.Determines E A := by
  let S := commonRealNames B
  have hArv : DefinableAt S .rv (Values.gammaPullback A) := hA.common_names
  have hU := hArv.rv_preimage
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  let U : Set (VFType (M := M)) :=
    {x | iVF x.val ∧ iRv x.val ∈ Values.gammaPullback A}
  have hGood : ValOneEC.Good (RingHom.id _) v U := boolean_good v hv _ hU.isBoolComb_balls
  have hRadial (x : VFType (M := M)) (hx : x ≠ 0) : x ∈ U ↔ vfGamma x hx ∈ A := by
    change (iVF x.val ∧ iRv x.val ∈ Values.gammaPullback A) ↔ _
    rw [and_iff_right x.property]
    constructor
    · rintro ⟨hr,h0,hmem⟩
      exact hmem
    · intro hmem
      exact ⟨rv_mem hM x.property,fun h => hx ((CanonicalRV.encodedRv_zero_iff x).mp h),hmem⟩
  exact good_finite_thresholds v hv h00 U hGood A hRadial

theorem gamma_canonical_endpoint_exists (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (A : Set (Values.Gamma (M := M)))
    (hA : GammaDefinableOverBase B A) (hne : A.Nonempty) (hcomp : Aᶜ.Nonempty) :
    ∃ c : Values.Gamma (M := M), FiniteThresholds.CanonicalEndpoint A c := by
  obtain ⟨E,hE⟩ := gamma_definable_finite_thresholds h00 B A hA
  exact FiniteThresholds.canonicalEndpoint_exists E A hE hne hcomp

end SpecialTransformations.Section3.GammaParameters
