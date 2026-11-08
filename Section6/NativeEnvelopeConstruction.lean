import Section6.ConcreteACVF
import Section6.ConcreteExtension
import Section6.NativeHenselian
import Section6.NativePresentation
import Section6.PureHenselianInputs
import Section6.UniformNormalizedElimination
import Section6.HenselianInvariance
import JohnsonAmalgamation
import Mathlib.FieldTheory.AlgebraicClosure

/-! Construction of the algebraic envelope from the native henselian
axioms, using the proved pure-characteristic-zero invariance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section6.UniformNormalizedElimination

open ConcreteValued NativeValuation

private def concreteFieldEquiv {L Δ : Type} [Field L] [LinearOrderedCommGroupWithZero Δ]
    (w : Valuation L Δ) [@Theory.Model LRV (Carrier w) (nativeStructure w) Axioms.ACVF] :
    letI := nativeStructure w
    L ≃+* VFType (M := Carrier w) := by
  letI := nativeStructure w
  let f : L →+* VFType (M := Carrier w) :=
    { toFun := fun x => ⟨.inl x, vf_inl w x⟩
      map_zero' := Subtype.ext (vfZero_eq w).symm
      map_one' := Subtype.ext (vfOne_eq w).symm
      map_add' := fun x y => Subtype.ext (vfAdd_eq w x y).symm
      map_mul' := fun x y => Subtype.ext (vfMul_eq w x y).symm }
  apply RingEquiv.ofBijective f
  refine ⟨f.injective, fun x => ?_⟩
  obtain ⟨y, hy⟩ := of_vf w x.val x.property
  exact ⟨y, Subtype.ext hy.symm⟩

theorem nativeEnvelope
    {M : Type} [LRV.Structure M] (h : M ⊨ HenselianTheory.canonicalHen00) :
    NativeEnvelope M := by
  have h00 : M ⊨ HenselianTheory.hen00 := h.mono (fun _ hσ => Or.inl hσ)
  have hc : M ⊨ HenselianTheory.canonicalNative := h.mono (fun _ hσ => Or.inr hσ)
  letI := valuedField_of_hen00 h00
  obtain ⟨Γ, sΓ, v, hv⟩ := exists_valuation_predV (M := M)
  letI := sΓ
  let K := NativeField.VF M
  letI : CharZero K := NativeValuation.charZero v hv h00
  letI : CharZero (ConcreteRV.Residue v) := NativeValuation.residueCharZero v hv h00
  letI : HenselianLocalRing v.valuationSubring := NativeValuation.henselian v hv h00
  let L := AlgebraicClosure K
  obtain ⟨Δ, sΔ, w, hw⟩ := Johnson22.valExtension_of_fieldExtension (L := L) v
  letI := sΔ
  letI := hw
  let ι := algebraMap K L
  letI : CharZero (ConcreteRV.Residue w) :=
    charZero_of_injective_algebraMap (algebraMap (ConcreteRV.Residue v) (ConcreteRV.Residue w)).injective
  obtain ⟨x, hx, hxv⟩ := NativeValuation.nontrivial v hv
  have hwnt : ∃ y : L, y ≠ 0 ∧ w y < 1 :=
    ⟨ι x, (map_ne_zero ι).mpr hx, (Valuation.HasExtension.val_map_lt_one_iff v w x).mpr hxv⟩
  let U := Carrier w
  letI : LRV.Structure U := nativeStructure w
  have hU : U ⊨ Axioms.ACVF00 := model_ACVF00 w hwnt
  letI : U ⊨ Axioms.ACVF := hU.mono (fun _ hσ => Or.inl (Or.inl hσ))
  letI : LRV.Structure (Carrier v) := nativeStructure v
  let P := NativePresentation.presentation v hv hc
  let f : M ↪[LRV] U := (extension v w).comp P.symm.toEmbedding
  let Y := ExpandedImages.Image f
  let θ := concreteFieldEquiv w
  let baseMap := θ.toRingHom.comp ι
  let F := baseMap.fieldRange
  let μ : K →+* F :=
    { toFun := fun x => ⟨baseMap x, baseMap.mem_fieldRange_self x⟩
      map_zero' := Subtype.ext baseMap.map_zero
      map_one' := Subtype.ext baseMap.map_one
      map_add' := fun x y => Subtype.ext (baseMap.map_add x y)
      map_mul' := fun x y => Subtype.ext (baseMap.map_mul x y) }
  let e : K ≃+* F := RingEquiv.ofBijective μ
    ⟨μ.injective, fun x => by
      obtain ⟨y, hy⟩ := x.property
      exact ⟨y, Subtype.ext hy⟩⟩
  letI : IsGalois K L := inferInstance
  letI : IsGalois F (VFType (M := U)) :=
    IsGalois.of_equiv_equiv (f := e) (g := θ) (RingHom.ext fun _ => rfl)
  let W := w.comap θ.symm.toRingHom
  have hW (x y : VFType (M := U)) : VFValued.predV x y ↔ W x ≤ W y := by
    obtain ⟨x, rfl⟩ := θ.surjective x
    obtain ⟨y, rfl⟩ := θ.surjective y
    change iLe (iRv (Sum.inl y : U)) (iRv (.inl x)) ↔
      w (θ.symm (θ x)) ≤ w (θ.symm (θ y))
    rw [rvMap_eq, rvMap_eq, le_inr, RVCalc.vrv_rv, RVCalc.vrv_rv,
      θ.symm_apply_apply, θ.symm_apply_apply]
  have hH : HenselianLocalRing (W.comap F.subtype).valuationSubring := by
    apply HenselianTheory.henselian_of_compatible_equiv v _ e
    intro x y
    change w (θ.symm (θ (ι x))) ≤ w (θ.symm (θ (ι y))) ↔ _
    rw [θ.symm_apply_apply, θ.symm_apply_apply, Valuation.HasExtension.val_map_le_iff v w]
  have hEP : HenselianAutomorphismInvariance W F := by
    intro hring σ a b
    letI := hring
    apply henselian_automorphism_invariance W _ σ a b
    intro n m hnm
    change w (θ.symm ((n : VFType (M := U)) - (m : VFType (M := U)))) = 1
    rw [map_sub, map_natCast, map_natCast]
    exact nat_sub_value_one w n m hnm
  have hext (z : Carrier v) : f (P z) = extension v w z := by
    change extension v w (P.symm (P z)) = _
    rw [FirstOrder.Language.Equiv.symm_apply_apply]
  have hY (t : U) : t ∈ Y ↔ ∃ z : Carrier v, extension v w z = t := by
    change (∃ m : M, f m = t) ↔ _
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨P.symm m, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨P z, hext z⟩
  have hF (a : VFType (M := U)) : a ∈ F ↔ a.val ∈ Y := by
    rw [RingHom.mem_fieldRange, hY]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Sum.inl x, rfl⟩
    · rintro ⟨z, hz⟩
      cases z with
      | inl x => exact ⟨x, Subtype.ext hz⟩
      | inr q => exact ((not_vf_inr w _) (hz.symm ▸ a.property)).elim
  have hRV (t : U) (ht : t ∈ Y) (hr : iRV t) : ∃ a : F, iRv a.val.val = t := by
    obtain ⟨z, rfl⟩ := (hY t).mp ht
    cases z with
    | inl x => exact (not_rv_inl w _ hr).elim
    | inr q =>
      obtain ⟨x, rfl⟩ := ConcreteValued.rv_surjective v q
      refine ⟨e x, ?_⟩
      change iRv (Sum.inl (ι x) : U) = Sum.inr (extensionRV v w (RVCalc.rv v x))
      rw [rvMap_eq, extensionRV_rv]
  refine NativeEnvelope.in_model hU (canonical w) f ?_
  let j : @ElementaryEmbedding LRV U U
      (CanonicalStructure.normalize (M := U)) (CanonicalStructure.normalize (M := U)) :=
    @ElementaryEmbedding.refl LRV U (CanonicalStructure.normalize (M := U))
  have himage : j '' (Y : Set U) = (Y : Set U) := Set.image_id _
  refine HenselianInputs.of_pure_algebraic_envelope hU Y Y j himage W hW F hF hRV hH hEP ?_
  intro t ht
  obtain ⟨a, ha⟩ := hRV t.val ht t.property
  exact ⟨a.val, (hF a.val).mp a.property, Subtype.ext ha⟩

theorem nativeEnvelopes (E : FirstOrder.Language.{0, 0}) : NativeEnvelopes E := by
  intro M _ h
  let i : LRV →ᴸ RVTermSupport.Expanded E := LHom.sumInl
  letI := i.reduct M
  apply nativeEnvelope
  apply (LHom.onTheory_model i HenselianTheory.canonicalHen00).mp
  exact h.mono (fun _ hσ => Or.inl hσ)

end SpecialTransformations.Section6.UniformNormalizedElimination
