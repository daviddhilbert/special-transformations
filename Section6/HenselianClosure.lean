import Section6.FunctionalClosure
import ValuedModelMap
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Henselian

/-!
# The henselian fixed-field argument in Lemma 6.2

The ambient field in this module is the algebraic envelope from the accepted
Corollary 3.14. Its Galois property and the RV-centre input from Lemma 3.13
are visible hypotheses. The one standard valuation-theory input is the
invariance of the extension of a henselian valuation under field
automorphisms. The fixed-field theorem itself is imported from Mathlib.

All raw definability uses the canonical normalization of the released LRV
structure, as in Sections 4 and 5. No conclusion of Section 6 is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section6

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev NormalizedDclClosed (X : Set M) : Prop :=
  @DclClosed LRV M (CanonicalStructure.normalize (M := M)) X

abbrev NormalizedFunctionallyClosed (X : Set M) : Prop :=
  @FunctionallyClosed LRV M (CanonicalStructure.normalize (M := M)) X

/-- The exact earlier centre input (Lemma 3.13) needed here: an RV point
definable over the VF-generated base has a VF representative definable
over that same base. The absorbing element is included. -/
def DefinableRVLifting (X : Set M) : Prop :=
  ∀ t : M, iRV t →
    @Set.Definable₁ M X LRV (CanonicalStructure.normalize (M := M)) {t} →
    ∃ a : VFType (M := M), iRv a.val = t ∧
      @Set.Definable₁ M X LRV (CanonicalStructure.normalize (M := M)) {a.val}

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

/-- Standard henselian uniqueness of the extension of a valuation to an
algebraic closure (Engler--Prestel, Valued Fields, henselian valuations).
Only preservation of the valuation preorder is required: the chosen value
group need not be fixed pointwise. This is an explicitly authorized
standard input, separate from the paper-specific closure theorem. -/
def HenselianAutomorphismInvariance (v : Valuation (VFType (M := M)) Γ)
    (K : Subfield (VFType (M := M))) : Prop :=
  HenselianLocalRing (v.comap K.subtype).valuationSubring →
    ∀ σ : VFType (M := M) ≃ₐ[K] VFType (M := M),
      ∀ a b, v (σ a) ≤ v (σ b) ↔ v a ≤ v b

private theorem valuedEmbedding_vf
    (F : VFType (M := M) →+* VFType (M := M))
    (hF : ∀ a b, VFValued.predV (F a) (F b) ↔ VFValued.predV a b)
    (a : VFType (M := M)) :
    ValuedModelMap.toCanonicalEmbedding F hF a.val = (F a).val := by
  change (ValuedModelMap.components F hF).carrierMap a.val = (F a).val
  exact (ValuedModelMap.components F hF).carrierMap_vf a.property

private theorem valuedEmbedding_rv
    (F : VFType (M := M) →+* VFType (M := M))
    (hF : ∀ a b, VFValued.predV (F a) (F b) ↔ VFValued.predV a b)
    (a : VFType (M := M)) :
    ValuedModelMap.toCanonicalEmbedding F hF (iRv a.val) = iRv (F a).val := by
  change (ValuedModelMap.components F hF).carrierMap (iRv a.val) = iRv (F a).val
  rw [(ValuedModelMap.components F hF).carrierMap_rv_map a.property,
    (ValuedModelMap.components F hF).carrierMap_vf a.property]
  rfl

/-- The released valued-model map gives the actual LRV automorphism of
the normalized algebraic envelope. The correspondence is constructed here,
rather than postulated as a definable-closure premise. -/
def valuedAutomorphism (σ : VFType (M := M) ≃+* VFType (M := M))
    (hσ : ∀ a b, VFValued.predV (σ a) (σ b) ↔ VFValued.predV a b) :
    @FirstOrder.Language.Equiv LRV M M
      (CanonicalStructure.normalize (M := M)) (CanonicalStructure.normalize (M := M)) := by
  let e := ValuedModelMap.toCanonicalEmbedding σ.toRingHom hσ
  have hs : Function.Surjective e := by
    intro b
    rcases TypedModelMap.sort_cover b with hb | hb
    · refine ⟨(σ.symm ⟨b, hb⟩).val, ?_⟩
      exact (valuedEmbedding_vf σ.toRingHom hσ _).trans
        (congrArg Subtype.val (σ.apply_symm_apply ⟨b, hb⟩))
    · obtain ⟨a, ha⟩ := CanonicalRV.encodedRv_surjective ⟨b, hb⟩
      refine ⟨iRv (σ.symm a).val, ?_⟩
      rw [valuedEmbedding_rv σ.toRingHom hσ]
      change iRv (σ (σ.symm a)).val = b
      rw [σ.apply_symm_apply]
      exact congrArg Subtype.val ha
  letI := CanonicalStructure.normalize (M := M)
  exact { toEquiv := _root_.Equiv.ofBijective (e : M → M) ⟨e.injective, hs⟩
          map_fun' := e.map_fun
          map_rel' := e.map_rel }

@[simp] theorem valuedAutomorphism_vf
    (σ : VFType (M := M) ≃+* VFType (M := M))
    (hσ : ∀ a b, VFValued.predV (σ a) (σ b) ↔ VFValued.predV a b)
    (a : VFType (M := M)) : valuedAutomorphism σ hσ a.val = (σ a).val :=
  valuedEmbedding_vf σ.toRingHom hσ a

@[simp] theorem valuedAutomorphism_rv
    (σ : VFType (M := M) ≃+* VFType (M := M))
    (hσ : ∀ a b, VFValued.predV (σ a) (σ b) ↔ VFValued.predV a b)
    (a : VFType (M := M)) :
    valuedAutomorphism σ hσ (iRv a.val) = iRv (σ a).val :=
  valuedEmbedding_rv σ.toRingHom hσ a

/-- All base RV elements are fixed because each is represented by a base
VF element. Surjectivity on the subfield, including zero, is essential. -/
theorem valuedAutomorphism_fixes_base
    (K : Subfield (VFType (M := M))) (X : Set M)
    (hK : ∀ a : VFType (M := M), a ∈ K ↔ a.val ∈ X)
    (hRV : ∀ t ∈ X, iRV t → ∃ a : K, iRv a.val.val = t)
    (σ : VFType (M := M) ≃ₐ[K] VFType (M := M))
    (hσ : ∀ a b, VFValued.predV (σ a) (σ b) ↔ VFValued.predV a b) :
    ∀ x ∈ X, valuedAutomorphism σ.toRingEquiv hσ x = x := by
  intro x hx
  rcases TypedModelMap.sort_cover x with hv | hr
  · let a : K := ⟨⟨x, hv⟩, (hK ⟨x, hv⟩).mpr hx⟩
    have ha : σ (a.val) = a.val := σ.commutes a
    exact (valuedAutomorphism_vf σ.toRingEquiv hσ ⟨x, hv⟩).trans
      (congrArg Subtype.val ha)
  · obtain ⟨a, rfl⟩ := hRV x hx hr
    rw [valuedAutomorphism_rv]
    exact congrArg (fun y : VFType (M := M) => iRv y.val) (σ.commutes a)

/-- The VF part of Lemma 6.2 in the algebraic envelope. Henselianity is
an actual `HenselianLocalRing` hypothesis; the permitted standard quotation
only supplies valuation invariance. Mathlib discharges the fixed-field step. -/
theorem henselian_vf_dcl
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (K : Subfield (VFType (M := M))) [IsGalois K (VFType (M := M))]
    (X : Set M) (hK : ∀ a : VFType (M := M), a ∈ K ↔ a.val ∈ X)
    (hRV : ∀ t ∈ X, iRV t → ∃ a : K, iRv a.val.val = t)
    (hH : HenselianLocalRing (v.comap K.subtype).valuationSubring)
    (hEP : HenselianAutomorphismInvariance v K)
    (a : VFType (M := M))
    (ha : @Set.Definable₁ M X LRV (CanonicalStructure.normalize (M := M)) {a.val}) :
    a.val ∈ X := by
  apply (hK a).mp
  have hf : ∀ σ : VFType (M := M) ≃ₐ[K] VFType (M := M), σ a = a := by
    intro σ
    have hp : ∀ x y, VFValued.predV (σ x) (σ y) ↔ VFValued.predV x y :=
      fun x y => (hv _ _).trans ((hEP hH σ x y).trans (hv _ _).symm)
    have hfix := valuedAutomorphism_fixes_base K X hK hRV σ hp
    let e := valuedAutomorphism σ.toRingEquiv hp
    let ee := @FirstOrder.Language.Equiv.toElementaryEmbedding LRV M M
      (CanonicalStructure.normalize (M := M)) (CanonicalStructure.normalize (M := M)) e
    have he := @definable_singleton_fixed LRV M (CanonicalStructure.normalize (M := M))
      X a.val ha ee hfix
    exact Subtype.ext ((valuedAutomorphism_vf σ.toRingEquiv hp a).symm.trans he)
  obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed a).mpr hf
  exact hc ▸ c.property

/-- Lemma 6.2 in the accepted algebraic envelope. Earlier Lemma 3.13
handles RV singleton lifting. In particular `VF(dcl X)=VF(X)` is proved,
not an input as in the legacy snapshot. -/
theorem lemma_6_2_in_algebraic_envelope
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (K : Subfield (VFType (M := M))) [IsGalois K (VFType (M := M))]
    (X : Set M) (hK : ∀ a : VFType (M := M), a ∈ K ↔ a.val ∈ X)
    (hRV : ∀ t ∈ X, iRV t → ∃ a : K, iRv a.val.val = t)
    (hrv : ∀ a : VFType (M := M), a.val ∈ X → iRv a.val ∈ X)
    (hH : HenselianLocalRing (v.comap K.subtype).valuationSubring)
    (hEP : HenselianAutomorphismInvariance v K)
    (hCenters : DefinableRVLifting X) : NormalizedFunctionallyClosed X := by
  apply @functionallyClosed_of_dclClosed LRV M (CanonicalStructure.normalize (M := M)) X
  intro b hb
  rcases TypedModelMap.sort_cover b with hvb | hrb
  · exact henselian_vf_dcl v hv K X hK hRV hH hEP ⟨b, hvb⟩ hb
  · obtain ⟨a, ha, had⟩ := hCenters b hrb hb
    rw [← ha]
    exact hrv a (henselian_vf_dcl v hv K X hK hRV hH hEP a had)

end SpecialTransformations.Section6
