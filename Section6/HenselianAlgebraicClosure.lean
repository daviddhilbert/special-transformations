module

public import Section6.ConcreteACVF
public import Section6.HenselianInvariance
public import Section6.HenselianRVClosure
public import Section6.HenselianValuationRing
public import Section6.NativeAmalgamation
public import Mathlib.FieldTheory.AlgebraicClosure

@[expose] public section

/-! Lemma 6.2 for a henselian substructure of a given ACVF model. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section6.Paper

open ConcreteValued

/-- Lemma 6.2 for a given henselian substructure. The elementary envelope
is the leading-term model of the algebraic closure of its valued field
inside the given ambient field. -/
theorem lemma_6_2 {M Γ : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    [LinearOrderedCommGroupWithZero Γ] (h00 : M ⊨ Axioms.ACVF00)
    (X : LRV.Substructure M) (K : Subfield (VFType (M := M)))
    (hK : ∀ a : VFType (M := M), a ∈ K ↔ a.val ∈ X)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (hnt : ∃ a : K, a ≠ 0 ∧ v a.val < 1)
    (hH : HenselianLocalRing (v.comap K.subtype).valuationSubring)
    (hRV : ∀ t ∈ X, iRV t → ∃ a : K, iRv a.val.val = t) :
    NormalizedFunctionallyClosed (X : Set M) := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : CharZero (VFType (M := M)) := charZero_of_inj_zero fun n hn => by
    by_contra hne
    exact Section3.Barycentre.natCast_ne_zero h00 n hne hn
  let A := algebraicClosure K (VFType (M := M))
  let L := ↥A
  let w : Valuation L Γ := v.comap A.subtype
  letI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  letI : CharZero L := inferInstance
  letI : CharZero (ConcreteRV.Residue w) := by
    apply (CharZero.charZero_iff_forall_prime_ne_zero _).mpr
    intro p hp hz
    have hpw : w (p : L) = 1 := by
      change v (A.subtype (p : L)) = 1
      rw [map_natCast]
      exact Section3.Barycentre.natCast_value_one v hv h00 p hp.ne_zero
    let z : w.valuationSubring := p
    have hz' : IsLocalRing.residue w.valuationSubring z = 0 := by
      simpa only [z, map_natCast] using hz
    have hsmall := (Valuation.mem_maximalIdeal_iff L w).mp
      ((IsLocalRing.residue_eq_zero_iff z).mp hz')
    change w (w.valuationSubring.subtype z) < 1 at hsmall
    rw [show w.valuationSubring.subtype z = (p : L) from
      map_natCast w.valuationSubring.subtype p, hpw] at hsmall
    exact lt_irrefl _ hsmall
  let ι := algebraMap K L
  have hwnt : ∃ a : L, a ≠ 0 ∧ w a < 1 := by
    obtain ⟨a, ha, hva⟩ := hnt
    exact ⟨ι a, (map_ne_zero ι).mpr ha, hva⟩
  let U := Carrier w
  letI : LRV.Structure U := nativeStructure w
  have hU : U ⊨ Axioms.ACVF00 := model_ACVF00 w hwnt
  letI hUA : U ⊨ Axioms.ACVF := hU.mono (fun _ hσ => Or.inl (Or.inl hσ))
  let θ := fieldEquiv w
  let W := w.comap θ.symm.toRingHom
  have hW (a b : VFType (M := U)) : VFValued.predV a b ↔ W a ≤ W b :=
    fieldEquiv_valuation w a b
  let g := A.subtype.comp θ.symm.toRingHom
  have hg (a b : VFType (M := U)) :
      VFValued.predV (g a) (g b) ↔ VFValued.predV a b :=
    (hv _ _).trans (hW _ _).symm
  let j : @ElementaryEmbedding LRV U M
      (CanonicalStructure.normalize (M := U)) (CanonicalStructure.normalize (M := M)) :=
    @NativeAmalgamation.elementaryEmbedding_of_fullQE LRV CanonicalTheory.CanonicalACVF
      LocalAssembly.fullQE U M
      (CanonicalStructure.normalize (M := U)) (CanonicalStructure.normalize (M := M))
      (CanonicalTheory.normalized_model hUA) (CanonicalTheory.normalized_model hM)
      (ValuedModelMap.toCanonicalEmbedding g hg)
  have hj_vf (a : VFType (M := U)) : j a.val = (g a).val :=
    (ValuedModelMap.components g hg).carrierMap_vf a.property
  have hj_rv (a : VFType (M := U)) : j (iRv a.val) = iRv (g a).val := by
    change (ValuedModelMap.components g hg).carrierMap (iRv a.val) = _
    rw [(ValuedModelMap.components g hg).carrierMap_rv_map a.property,
      (ValuedModelMap.components g hg).carrierMap_vf a.property]
    rfl
  let Y : Set U := j ⁻¹' (X : Set M)
  let baseMap := θ.toRingHom.comp ι
  let F := baseMap.fieldRange
  let e : K ≃+* F := baseMap.rangeRestrictFieldEquiv
  have hbase (a : K) : g (baseMap a) = a.val := by
    exact congrArg A.subtype (θ.symm_apply_apply (ι a))
  letI : IsGalois K L := inferInstance
  letI : IsGalois F (VFType (M := U)) :=
    IsGalois.of_equiv_equiv (f := e) (g := θ) (RingHom.ext fun _ => rfl)
  have hF (a : VFType (M := U)) : a ∈ F ↔ a.val ∈ Y := by
    change a ∈ F ↔ j a.val ∈ X
    rw [hj_vf, ← hK, RingHom.mem_fieldRange]
    constructor
    · rintro ⟨b, rfl⟩
      rw [hbase]
      exact b.property
    · intro ha
      exact ⟨⟨g a, ha⟩, g.injective (hbase ⟨g a, ha⟩)⟩
  have hYRV (t : U) (ht : t ∈ Y) (hr : iRV t) : ∃ a : F, iRv a.val.val = t := by
    obtain ⟨a, ha⟩ := hRV (j t) ht ((ValuedModelMap.components g hg).carrierMap_rv_mem hr)
    refine ⟨e a, (ValuedModelMap.components g hg).carrierMap_injective ?_⟩
    change j (iRv (baseMap a).val) = j t
    rw [hj_rv, hbase, ha]
  have hYrv (a : VFType (M := U)) (ha : a.val ∈ Y) : iRv a.val ∈ Y := by
    change j a.val ∈ X at ha
    rw [hj_vf] at ha
    change j (iRv a.val) ∈ X
    rw [hj_rv]
    exact X.fun_mem Fn.rvMap ![(g a).val] (by intro i; fin_cases i; exact ha)
  have hFH : HenselianLocalRing (W.comap F.subtype).valuationSubring := by
    letI := hH
    apply HenselianTheory.henselian_of_compatible_equiv (v.comap K.subtype) _ e
    intro x y
    change v (g (baseMap x)) ≤ v (g (baseMap y)) ↔ v x.val ≤ v y.val
    rw [hbase, hbase]
  have hEP : HenselianAutomorphismInvariance W F := by
    intro hring σ a b
    letI := hring
    apply henselian_automorphism_invariance W _ σ a b
    intro n m hnm
    change w (θ.symm ((n : VFType (M := U)) - (m : VFType (M := U)))) = 1
    rw [map_sub, map_natCast, map_natCast]
    exact nat_sub_value_one w n m hnm
  have himage : j '' Y = (X : Set M) := by
    ext t
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro ht
      rcases TypedModelMap.sort_cover t with h | h
      · let a : K := ⟨⟨t, h⟩, (hK ⟨t, h⟩).mpr ht⟩
        have hj : j (baseMap a).val = t := by simp only [hj_vf, hbase, a]
        exact ⟨(baseMap a).val, by change j (baseMap a).val ∈ X; rwa [hj], hj⟩
      · obtain ⟨a, ha⟩ := hRV t ht h
        have hj : j (iRv (baseMap a).val) = t := by rw [hj_rv, hbase, ha]
        exact ⟨iRv (baseMap a).val, by change j (iRv (baseMap a).val) ∈ X; rwa [hj], hj⟩
  have hY := lemma_6_2_in_algebraic_envelope_pure W hW hU F Y hF hYRV hYrv hFH hEP
  have hI := @FunctionallyClosed.image LRV U M
    (CanonicalStructure.normalize (M := U)) (CanonicalStructure.normalize (M := M)) Y hY j
  exact himage ▸ hI

end SpecialTransformations.Section6.Paper
