module

public import Section3.AclModelGeometry
public import Section3.AlgebraicClosure
public import Section3.CanonicalContext
public import Section3.CanonicalParameters
public import Section3.ModelContext

@[expose] public section

/- Component: CanonicalAclModel -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem algebraicClosureSet_definableClosure (S : Set M) :
    algebraicClosureSet (definableClosure S) = algebraicClosureSet S := by
  ext x
  exact exists_congr (fun σ => algebraicAt_definableClosure_iff S σ x)

theorem canonical_vfGenerated_acl_meetsDefinable
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hS : VFGenerated S) (hvalues : NontrivialFiniteValues (algebraicClosureSet S)) :
    LRV.MeetsDefinable (algebraicClosureSet S) := by
  obtain ⟨A,hA,hS⟩ := hS
  have he : algebraicClosureSet S = algebraicClosureSet A := by
    rw [hS]
    exact algebraicClosureSet_definableClosure A
  have hvaluesA : NontrivialFiniteValues (algebraicClosureSet A) := he ▸ hvalues
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  have hnt := acl_field_nontrivial_valuation h00 A hA hvaluesA v hv
  rw [he]
  exact canonical_acl_meetsDefinable v hv hc h00 A hA hnt

theorem canonical_vfGenerated_acl_elementary
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hS : VFGenerated S) (hvalues : NontrivialFiniteValues (algebraicClosureSet S)) :
    (algebraicClosureSubstructure hc S).IsElementary := by
  have hm := canonical_vfGenerated_acl_meetsDefinable hc h00 S hS hvalues
  have he : Substructure.closure LRV (algebraicClosureSet S) = algebraicClosureSubstructure hc S := by
    apply SetLike.coe_injective
    exact hm.closure_eq_self
  rw [← he]
  exact hm.isElementary_closure

theorem canonical_corollary_3_14_model
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hS : VFGenerated S) (hvalues : NontrivialFiniteValues (algebraicClosureSet S)) :
    (algebraicClosureSubstructure hc S) ⊨ Axioms.ACVF00 := by
  let E : LRV.ElementarySubstructure M :=
    ⟨algebraicClosureSubstructure hc S,canonical_vfGenerated_acl_elementary hc h00 S hS hvalues⟩
  exact (E.theory_model_iff Axioms.ACVF00).mpr h00

end SpecialTransformations.Section3

/- Component: NamedAclModel -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.ModelTheory

/-- Adapted from Mathlib/ModelTheory/ElementaryMaps.lean,
ElementaryEmbedding.liftWithConstants (Apache-2.0, Aaron Anderson), allowing
an arbitrary type of original names instead of a subset of the source. -/
def elementaryEmbeddingWithNames {L : FirstOrder.Language} {M N α : Type}
    [L.Structure M] [L.Structure N] (f : M ↪ₑ[L] N) (u : α → M) :
    letI := Language.constantsOn.structure u
    letI := Language.constantsOn.structure (f ∘ u)
    M ↪ₑ[L[[α]]] N := by
  letI := Language.constantsOn.structure u
  letI := Language.constantsOn.structure (f ∘ u)
  refine ⟨f,?_⟩
  intro n φ x
  have hMnames : (fun a : α => (L.con a : M)) = u := rfl
  have hNnames : (fun a : α => (L.con a : N)) = f ∘ u := rfl
  have h : Sum.elim (f ∘ u) (f ∘ x) = f ∘ Sum.elim u x := (Sum.comp_elim _ _ _).symm
  simpa only [Formula.Realize,← BoundedFormula.realize_constantsVarsEquiv,hMnames,hNnames,h] using
    f.map_formula (BoundedFormula.constantsVarsEquiv φ) (Sum.elim u x)

end SpecialTransformations.ModelTheory

open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem ambient_named_model00 (h00 : M ⊨ Axioms.ACVF00) (S : LRV.Substructure M) :
    M ⊨ SubstructureTheory.ACVF_S S := by
  haveI := h00
  refine ⟨fun φ hφ => ?_⟩
  rcases hφ with htheory | hdiagram
  · obtain ⟨ψ,hψ,rfl⟩ := htheory
    exact (LRV.lhomWithConstants (S : Set M)).realize_onSentence (M := M) ψ
      |>.mpr (Axioms.ACVF00.realize_sentence_of_mem hψ)
  · rcases hdiagram with hpos | hneg
    · exact hpos.2
    · obtain ⟨ψ,_,rfl,hψ⟩ := hneg
      exact hψ

/-- The full named-base modelhood conclusion on the canonical
representation. Constants are the actual inclusion of S into acl(S). -/
theorem canonical_corollary_3_14_named
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (S : LRV.Substructure M) (hS : VFGenerated (S : Set M))
    (hvalues : NontrivialFiniteValues (algebraicClosureSet (S : Set M))) :
    let T := algebraicClosureSubstructure hc (S : Set M)
    letI := Language.constantsOn.structure
      (fun a : S => (⟨a.val,subset_algebraicClosureSet (S : Set M) a.property⟩ : T))
    T ⊨ SubstructureTheory.ACVF_S S := by
  let T := algebraicClosureSubstructure hc (S : Set M)
  let E : LRV.ElementarySubstructure M :=
    ⟨T,canonical_vfGenerated_acl_elementary hc h00 (S : Set M) hS hvalues⟩
  let u : S → T := fun a => ⟨a.val,subset_algebraicClosureSet (S : Set M) a.property⟩
  letI := Language.constantsOn.structure u
  letI := Language.constantsOn.structure (E.subtype ∘ u)
  have f := ModelTheory.elementaryEmbeddingWithNames E.subtype u
  exact (f.theory_model_iff (SubstructureTheory.ACVF_S S)).mpr (ambient_named_model00 h00 S)

end SpecialTransformations.Section3

/- Component: NormalizedAclModel -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem definableClosure_normalize_eq (S : Set M) :
    @definableClosure M (CanonicalStructure.normalize (M := M)) S = definableClosure S := by
  ext x
  exact exists_congr (fun σ => definableClosureAt_normalize_iff S σ x)

theorem algebraicClosureSet_normalize_eq (S : Set M) :
    @algebraicClosureSet M (CanonicalStructure.normalize (M := M)) S = algebraicClosureSet S := by
  ext x
  exact exists_congr (fun σ => algebraicAt_normalize_iff S σ x)

theorem vfGenerated_normalize_iff (S : Set M) :
    @VFGenerated M (CanonicalStructure.normalize (M := M)) S ↔ VFGenerated S := by
  constructor
  · rintro ⟨A,hA,he⟩
    exact ⟨A,(fun a ha => (CanonicalStructure.sortEval_normalize .vf a).mp (hA a ha)),
      he.trans (definableClosure_normalize_eq A)⟩
  · rintro ⟨A,hA,he⟩
    exact ⟨A,(fun a ha => (CanonicalStructure.sortEval_normalize .vf a).mpr (hA a ha)),
      he.trans (definableClosure_normalize_eq A).symm⟩

/-- The actual acl carrier with canonical interpretations of all symbols.
On every correctly sorted application these are the original operations. -/
noncomputable def normalizedAlgebraicClosureSubstructure (S : Set M) :
    @Language.Substructure LRV M (CanonicalStructure.normalize (M := M)) :=
  @algebraicClosureSubstructure M (CanonicalStructure.normalize (M := M))
    (CanonicalStructure.normalized_model hM) CanonicalStructure.normalize_isCanonical S

theorem mem_normalizedAlgebraicClosureSubstructure (S : Set M) (x : M) :
    x ∈ normalizedAlgebraicClosureSubstructure S ↔ x ∈ algebraicClosureSet S :=
  Set.ext_iff.mp (algebraicClosureSet_normalize_eq S) x

theorem normalized_acl_elementary (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hS : VFGenerated S) (hvalues : NontrivialFiniteValues (algebraicClosureSet S)) :
    @Substructure.IsElementary LRV M (CanonicalStructure.normalize (M := M))
      (normalizedAlgebraicClosureSubstructure S) := by
  have hN := CanonicalStructure.normalized_model hM
  have h00N := normalized_model00 h00
  have hSN := (vfGenerated_normalize_iff S).mpr hS
  have hVN := (nontrivialFiniteValues_normalize_iff (algebraicClosureSet S)).mpr hvalues
  rw [← algebraicClosureSet_normalize_eq S] at hVN
  exact @canonical_vfGenerated_acl_elementary M (CanonicalStructure.normalize (M := M)) hN
    CanonicalStructure.normalize_isCanonical h00N S hSN hVN

theorem normalized_acl_model (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hS : VFGenerated S) (hvalues : NontrivialFiniteValues (algebraicClosureSet S)) :
    @Theory.Model LRV (normalizedAlgebraicClosureSubstructure S)
      (@Substructure.inducedStructure LRV M (CanonicalStructure.normalize (M := M))
        (normalizedAlgebraicClosureSubstructure S)) Axioms.ACVF00 := by
  have hN := CanonicalStructure.normalized_model hM
  have h00N := normalized_model00 h00
  have hSN := (vfGenerated_normalize_iff S).mpr hS
  have hVN := (nontrivialFiniteValues_normalize_iff (algebraicClosureSet S)).mpr hvalues
  rw [← algebraicClosureSet_normalize_eq S] at hVN
  exact @canonical_corollary_3_14_model M (CanonicalStructure.normalize (M := M)) hN
    CanonicalStructure.normalize_isCanonical h00N S hSN hVN

/-- Corollary 3.14 for the full VF/RV acl, with its actual named-base
atomic diagram. Canonical normalization is explicit and internal: there is
no canonical-model premise, and the original acl carrier is unchanged. -/
theorem corollary_3_14 (h00 : M ⊨ Axioms.ACVF00)
    (S : LRV.Substructure M) (hS : VFGenerated (S : Set M))
    (hvalues : NontrivialFiniteValues (algebraicClosureSet (S : Set M))) :
    let T := normalizedAlgebraicClosureSubstructure (S : Set M)
    letI : LRV.Structure T := @Substructure.inducedStructure LRV M
      (CanonicalStructure.normalize (M := M)) T
    letI := Language.constantsOn.structure
      (fun a : normalizeSubstructure S => (⟨a.val,
        (mem_normalizedAlgebraicClosureSubstructure (S : Set M) a.val).mpr
          (subset_algebraicClosureSet (S : Set M) a.property)⟩ : T))
    T ⊨ @SubstructureTheory.ACVF_S M (CanonicalStructure.normalize (M := M)) (normalizeSubstructure S) := by
  have hN := CanonicalStructure.normalized_model hM
  have h00N := normalized_model00 h00
  have hSN := (vfGenerated_normalize_iff (S : Set M)).mpr hS
  have hVN := (nontrivialFiniteValues_normalize_iff (algebraicClosureSet (S : Set M))).mpr hvalues
  rw [← algebraicClosureSet_normalize_eq (S : Set M)] at hVN
  exact @canonical_corollary_3_14_named M (CanonicalStructure.normalize (M := M)) hN
    CanonicalStructure.normalize_isCanonical h00N (normalizeSubstructure S) hSN hVN

end SpecialTransformations.Section3
