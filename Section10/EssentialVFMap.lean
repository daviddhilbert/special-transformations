module

public import Section8.VFDefinableTopology
public import Section9.LimitTopology
public import Section9.MixedDifferentiationAE
public import Section4.CoordinateMaps
public import Section4.RVRestrictions
public import Section4.VFUnions

@[expose] public section

/-! Representatives of essential VF bijections and preservation of
fixed-label Jacobians when a small exceptional set is removed. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace SpecialTransformations.Section10

noncomputable section

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
local notation "VF" => VFType (M := M)
local notation "Δ" => rawRVSpace (M := M) 1

/-- A same-base bijection between definable subsets whose complements
have VF dimension strictly below the ambient degree `n`. -/
structure EssentialVFMap (A : DefSet (rawMixedSpace (M := M) n r) S)
    (B : DefSet (rawMixedSpace (M := M) n s) S) where
  source : DefSet (rawMixedSpace (M := M) n r) S
  target : DefSet (rawMixedSpace (M := M) n s) S
  source_subset : source.carrier ⊆ A.carrier
  target_subset : target.carrier ⊆ B.carrier
  source_small : vfDim Δ (A.sdiff source) < n
  target_small : vfDim Δ (B.sdiff target) < n
  map : Map source target
  bijective : Function.Bijective map

namespace EssentialVFMap

variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) n s) S}

public theorem complement_dim_lt {m : ℕ}
    {X Y Z : DefSet (rawMixedSpace (M := M) n m) S}
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hs : Saturated M κ) (hS : Cardinal.mk S < κ)
    (hXY : vfDim Δ (X.sdiff Y) < n) (hYZ : vfDim Δ (Y.sdiff Z) < n) :
    vfDim Δ (X.sdiff Z) < n := by
  let T := (X.sdiff Y).union (Y.sdiff Z)
  have hsub : (X.sdiff Z).carrier ⊆ T.carrier := by
    intro x hx
    by_cases hy : x ∈ Y.carrier
    · exact Or.inr ⟨hy, hx.2⟩
    · exact Or.inl ⟨hx.1, hy⟩
  have hle : vfDim Δ (X.sdiff Z) ≤ vfDim Δ T :=
    Dimension.dim_mono rawVFSpace (AuxiliaryCoordinates.space Δ)
      hsub ⟨n, mixed_has_dimension_bound Δ T⟩
  have hT : vfDim Δ T < n := by
    change vfDim Δ ((X.sdiff Y).union (Y.sdiff Z)) < n
    rw [vfDim_union hc hs hS Δ (rawRVSpace_rvCoded 1)]
    exact max_lt_iff.mpr ⟨hXY, hYZ⟩
  exact lt_of_le_of_lt hle hT

/-- Extend the ambient objects across small complements while keeping
the same representative and the same pointwise Jacobian. -/
def widen {A' : DefSet (rawMixedSpace (M := M) n r) S}
    {B' : DefSet (rawMixedSpace (M := M) n s) S}
    (f : EssentialVFMap A' B') (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hS : Cardinal.mk S < κ)
    (hA : A'.carrier ⊆ A.carrier) (hB : B'.carrier ⊆ B.carrier)
    (hAdim : vfDim Δ (A.sdiff A') < n) (hBdim : vfDim Δ (B.sdiff B') < n) :
    EssentialVFMap A B where
  source := f.source
  target := f.target
  source_subset := f.source_subset.trans hA
  target_subset := f.target_subset.trans hB
  source_small := complement_dim_lt hc hs hS hAdim f.source_small
  target_small := complement_dim_lt hc hs hS hBdim f.target_small
  map := f.map
  bijective := f.bijective

omit [M ⊨ Axioms.ACVF] in
private theorem vfProjectionCodes_definable
    (Z : DefSet (rawMixedSpace (M := M) n r) S) :
    S.Definable LRV {z | ∃ p : Z, vfValues p.val.1 = z} := by
  let Q := rawMixedSpace (M := M) n r
  have hraw : S.Definable LRV (Q.preimage Z.carrier) := Z.definable
  have h : S.Definable LRV {z : Fin n → M | ∃ t : Fin r → M,
      Sum.elim z t ∈ Q.preimage Z.carrier} := hraw.exists_of_finite
  have he : {z | ∃ p : Z, vfValues p.val.1 = z} =
      {z : Fin n → M | ∃ t : Fin r → M, Sum.elim z t ∈ Q.preimage Z.carrier} := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨rvValues p.val.2, mixedValues_mem_domain p.val,
        (decode_mixedValues p.val).symm ▸ p.property⟩
    · rintro ⟨t, ht, hp⟩
      let p : Z := ⟨Q.decode ⟨Sum.elim z t, ht⟩, hp⟩
      exact ⟨p, funext (fun i => congrFun (mixedValues_decode ⟨Sum.elim z t, ht⟩) (.inl i))⟩
  rw [he]
  exact h

/-- Restrict a definable bijection away from the closure of the VF
projection of its exceptional set. Every Jacobian at a retained point
transfers to the actual restriction, with its original determinant. -/
theorem exists_restriction_preserving_jacobian
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hs : Saturated M κ) (hS : Cardinal.mk S < κ) (hn : 0 < n)
    (f : Map A B) (hf : Function.Bijective f)
    (Z : DefSet (rawMixedSpace (M := M) n r) S) (hZ : vfDim Δ Z < n) :
    ∃ g : EssentialVFMap A B, ∀ p : g.source,
      let q : A := ⟨p.val, g.source_subset p.property⟩
      q.val ∉ Z.carrier ∧ (g.map p).val = (f q).val ∧
        ∀ J : VF, HasMixedVFJacobianAt f q J → HasMixedVFJacobianAt g.map p J := by
  let _ : Valued VF (Values.presentationType (M := M)) := Valued.mk' Values.presentationValuation
  have hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y :=
    Values.presentation_compatible
  let P := {z | ∃ p : Z, vfValues p.val.1 = z}
  have hP : S.Definable LRV P := vfProjectionCodes_definable Z
  have hPdim : vfDim Δ (vfObjectOfRaw hP) < n := by
    apply vfDim_lt_of_no_independent hc hs hS Δ (rawRVSpace_rvCoded 1) hn hP
    rintro a ⟨z, hz⟩ ha
    have he : z.val.1 = a := vfValues_injective hz
    have hr : vfTupleTrdeg S a = n :=
      (tupleField_trdeg_eq_arity_iff (vfParameterField S) a).mpr ha
    have hle := vfTupleTrdeg_le_vfDim hc Δ (rawRVSpace_rvCoded 1) Z z
    rw [he, hr] at hle
    exact (not_le_of_gt hZ) (by exact_mod_cast hle)
  let K := vfRawClosure P
  have hK := vfRawClosure_definable hP
  have hKdim := vfRawClosure_dim_lt_arity hc hs hS Δ (rawRVSpace_rvCoded 1) hn hv hP hPdim
  let Bad : DefSet (rawMixedSpace (M := M) n r) S :=
    ⟨{p ∈ A.carrier | vfValues p.1 ∈ K}, by
      let P' := rawMixedSpace (M := M) n r
      have hd := Set.Definable.inter A.definable
        (hK.preimage_comp (Sum.inl : Fin n → Fin n ⊕ Fin r))
      have he : P'.preimage {p ∈ A.carrier | vfValues p.1 ∈ K} =
          P'.preimage A.carrier ∩ {z | z ∘ Sum.inl ∈ K} := by
        ext z
        have hdecode (hz : z ∈ P'.domain) :
            vfValues (P'.decode ⟨z, hz⟩).1 = z ∘ Sum.inl :=
          funext (fun i => congrFun (mixedValues_decode ⟨z, hz⟩) (.inl i))
        constructor
        · rintro ⟨hz, ha, hk⟩
          refine ⟨⟨hz, ha⟩, ?_⟩
          change z ∘ Sum.inl ∈ K
          rw [← hdecode hz]
          exact hk
        · rintro ⟨⟨hz, ha⟩, hk⟩
          refine ⟨hz, ha, ?_⟩
          rw [hdecode hz]
          exact hk
      change S.Definable LRV (P'.preimage _)
      rw [he]
      exact hd⟩
  have hBad : Bad.carrier ⊆ A.carrier := fun _ h => h.1
  have hBadDim : vfDim Δ Bad < n := by
    apply mixed_vfDim_lt_of_no_independent hc hs hS Δ (rawRVSpace_rvCoded 1) hn Bad
    intro p hp
    let a : vfObjectOfRaw hK := ⟨(p.val.1, Fin.elim0), p.property.2⟩
    have hr : vfTupleTrdeg S p.val.1 = n :=
      (tupleField_trdeg_eq_arity_iff (vfParameterField S) p.val.1).mpr hp
    have hle := vfTupleTrdeg_le_vfDim hc Δ (rawRVSpace_rvCoded 1) (vfObjectOfRaw hK) a
    change vfTupleTrdeg S p.val.1 ≤ _ at hle
    rw [hr] at hle
    exact (not_le_of_gt hKdim) (by exact_mod_cast hle)
  let G := A.sdiff Bad
  let fG := f.restrict (A' := G) (fun _ h => h.1)
  let fBad := f.restrict hBad
  have hsrc : (A.sdiff G) = Bad := DefSet.eq_of_carrier_eq (by
    ext x
    change (x ∈ A.carrier ∧ ¬ (x ∈ A.carrier ∧ x ∉ Bad.carrier)) ↔ x ∈ Bad.carrier
    exact ⟨fun h => by by_contra hn; exact h.2 ⟨h.1, hn⟩,
      fun h => ⟨hBad h, fun h' => h'.2 h⟩⟩)
  have htar : (B.sdiff fG.image) = fBad.image := DefSet.eq_of_carrier_eq (by
    ext y
    constructor
    · intro hy
      obtain ⟨p, hp⟩ := hf.surjective ⟨y, hy.1⟩
      have he : (f p).val = y := congrArg Subtype.val hp
      have hb : p.val ∈ Bad.carrier := by
        by_contra hn
        exact hy.2 ⟨⟨p.val, p.property, hn⟩, he⟩
      exact ⟨⟨p.val, hb⟩, he⟩
    · rintro ⟨p, rfl⟩
      refine ⟨(fBad p).property, ?_⟩
      rintro ⟨q, hq⟩
      have he : fG q = fBad p := Subtype.ext hq
      exact q.property.2 ((congrArg Subtype.val (hf.injective he)).symm ▸ p.property))
  have htarDim : vfDim Δ (B.sdiff fG.image) < n := by
    rw [htar]
    exact lt_of_le_of_lt (vfDim_image_le hc hs hS Δ (rawRVSpace_rvCoded 1) fBad) hBadDim
  have htarSub : fG.image.carrier ⊆ B.carrier := by
    rintro _ ⟨p, hp⟩
    exact hp ▸ (fG p).property
  let g : EssentialVFMap A B :=
    ⟨G, fG.image, fun _ h => h.1, htarSub,
      hsrc.symm ▸ hBadDim, htarDim, fG.toImage, ⟨by
        intro a b hab
        have he : fG a = fG b := Subtype.ext (congrArg (fun y => y.val) hab)
        exact Subtype.ext (congrArg (fun x => x.val) (hf.injective he)),
        by
          rintro ⟨_, p, hp⟩
          exact ⟨p, Subtype.ext hp⟩⟩⟩
  refine ⟨g, fun p => ?_⟩
  let q : A := ⟨p.val, g.source_subset p.property⟩
  have hk : vfValues p.val.1 ∉ K := fun h => p.property.2 ⟨p.property.1, h⟩
  have hclosed : {a : Fin n → VF | vfValues a ∈ K} =
      closure {a : Fin n → VF | vfValues a ∈ P} :=
    Set.ext (fun a => mem_vfRawClosure_iff hv P a)
  have hball : ∃ δ : Values.Gamma (M := M), ∀ x ∈ vfBall p.val.1 δ, vfValues x ∉ K := by
    by_contra! h
    have hcl : p.val.1 ∈ vfClosure {a : Fin n → VF | vfValues a ∈ K} := by
      intro δ
      obtain ⟨x, hx, hxK⟩ := h δ
      exact ⟨x, hxK, hx⟩
    rw [vfClosure_eq_closure hv, hclosed, closure_closure, ← hclosed] at hcl
    exact hk hcl
  refine ⟨fun hz => hk ((mem_vfRawClosure_iff hv P p.val.1).mpr
      (subset_closure ⟨⟨p.val, hz⟩, rfl⟩)), rfl, ?_⟩
  intro J hJ
  obtain ⟨F, ⟨ρ, hρ⟩, hder⟩ := hJ
  obtain ⟨δ, hδ⟩ := hball
  refine ⟨F, ⟨max ρ δ, fun x hx => ?_⟩, hder⟩
  obtain ⟨hxA, hF⟩ := hρ x (vfBall_anti (le_max_left _ _) hx)
  have hxG : (x, p.val.2) ∈ G.carrier :=
    ⟨hxA, fun hb => hδ x (vfBall_anti (le_max_right _ _) hx) hb.2⟩
  exact ⟨hxG, hF⟩

end EssentialVFMap

end

end SpecialTransformations.Section10
