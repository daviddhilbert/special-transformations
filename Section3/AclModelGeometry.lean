module

public import Section3.AclFieldImages
public import Section3.AlgebraicClosure
public import Section3.AlgebraicRVLifting
public import Section3.AlgebraicSubfieldModel
public import Section3.GammaCodeDefinability
public import Section3.TranscendenceDegrees

@[expose] public section

/- Component: AclModelGeometry -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def vfFieldNames (F : Subfield (VFType (M := M))) : Set M :=
  Subtype.val '' (F : Set (VFType (M := M)))

theorem rv_definable_over_field_names (F : Subfield (VFType (M := M))) (x : F) :
    DefinableClosureAt (vfFieldNames F) .rv (CanonicalRV.encodedRv x.val).val := by
  have hx : x.val.val ∈ vfFieldNames F := ⟨x.val,x.property,rfl⟩
  exact definableClosureAt_function_symbol (vfFieldNames F) Fn.rvMap (![x.val.val] : Fin 1 → M)
    (fun i => by fin_cases i; exact x.val.property)
    (fun i => by fin_cases i; exact definableClosureAt_of_mem hx x.val.property)

theorem acl_definable_over_field_names (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hS : ∀ a ∈ S, iVF a) :
    ∀ b ∈ algebraicClosureSet S, ∃ σ,
      DefinableClosureAt (vfFieldNames (vfAlgebraicClosureField S)) σ b := by
  rintro b ⟨σ,hb⟩
  cases σ with
  | vf =>
    let x : VFType (M := M) := ⟨b,hb.sorted⟩
    have hx : x ∈ vfAlgebraicClosureField S := (mem_vfAlgebraicClosureField S x).mpr hb
    exact ⟨.vf,definableClosureAt_of_mem ⟨x,hx,rfl⟩ hb.sorted⟩
  | rv =>
    let t : CanonicalRV.RVSort M := ⟨b,hb.sorted⟩
    obtain ⟨x,hx⟩ := (rv_algebraicClosure_iff_lift h00 S hS t).mp hb
    have hd := rv_definable_over_field_names (vfAlgebraicClosureField S) x
    refine ⟨.rv,?_⟩
    change DefinableClosureAt (vfFieldNames (vfAlgebraicClosureField S)) .rv t.val
    rw [← hx]
    exact hd

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

include hv in
theorem acl_meets_sorted_definable (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hS : ∀ a ∈ S, iVF a)
    (hnt : ∃ x : vfAlgebraicClosureField S, x ≠ 0 ∧ v x.val ≠ 1)
    (σ : SortTag) (A : Set M) (hA : DefinableAt (algebraicClosureSet S) σ A)
    (hne : A.Nonempty) : (A ∩ algebraicClosureSet S).Nonempty := by
  let F := vfAlgebraicClosureField S
  let T := vfFieldNames F
  have hd : DefinableAt T σ A := hA.eliminate_sorted_definable_params
    (acl_definable_over_field_names h00 S hS)
  obtain ⟨x,hx⟩ := sorted_definable_nonempty_meets_subfield v hv F hnt T A
    (Set.Subset.refl _) σ hd hne
  refine ⟨RVRepresentatives.decode σ x.val,hx,σ,?_⟩
  have hAlg : AlgebraicAt S .vf x.val.val := (mem_vfAlgebraicClosureField S x.val).mp x.property
  cases σ with
  | vf => exact hAlg
  | rv => exact rv_algebraic_of_algebraic_lift S x.val hAlg

include hv in
/-- Raw Tarski-Vaught witness property on the canonical representation.
The actual full LRV elementary substructure follows from Mathlib's
MeetsDefinable criterion; this is not only a VF-field assertion. -/
theorem canonical_acl_meetsDefinable (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (S : Set M) (hS : ∀ a ∈ S, iVF a)
    (hnt : ∃ x : vfAlgebraicClosureField S, x ≠ 0 ∧ v x.val ≠ 1) :
    LRV.MeetsDefinable (algebraicClosureSet S) := by
  intro A hne hA
  obtain ⟨a,ha⟩ := hne
  obtain ⟨σ,hσ⟩ : ∃ σ, sortEval σ a := by
    rcases TypedModelMap.sort_cover (M := M) a with h | h
    · exact ⟨.vf,h⟩
    · exact ⟨.rv,h⟩
  let C : Set M := A ∩ {x | sortEval σ x}
  have hCn : C.Nonempty := ⟨a,ha,hσ⟩
  have hCs : DefinableAt (algebraicClosureSet S) σ C :=
    raw_definable_sorted hc (algebraicClosureSet S) C σ
      (hA.inter (definableAt_sort (algebraicClosureSet S) σ).raw_definable) (fun x hx => hx.2)
  obtain ⟨b,hbC,hbAlg⟩ := acl_meets_sorted_definable v hv h00 S hS hnt σ C hCs hCn
  exact ⟨b,hbC.1,hbAlg⟩

include hv in
theorem canonical_algebraicClosureSubstructure_elementary
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hS : ∀ a ∈ S, iVF a)
    (hnt : ∃ x : vfAlgebraicClosureField S, x ≠ 0 ∧ v x.val ≠ 1) :
    (algebraicClosureSubstructure hc S).IsElementary := by
  have hm := canonical_acl_meetsDefinable v hv hc h00 S hS hnt
  have he : Substructure.closure LRV (algebraicClosureSet S) = algebraicClosureSubstructure hc S := by
    apply SetLike.coe_injective
    exact hm.closure_eq_self
  rw [← he]
  exact hm.isElementary_closure

include hv in
theorem canonical_algebraicClosureSubstructure_model
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hS : ∀ a ∈ S, iVF a)
    (hnt : ∃ x : vfAlgebraicClosureField S, x ≠ 0 ∧ v x.val ≠ 1) :
    (algebraicClosureSubstructure hc S) ⊨ Axioms.ACVF00 := by
  let E : LRV.ElementarySubstructure M :=
    ⟨algebraicClosureSubstructure hc S,
      canonical_algebraicClosureSubstructure_elementary v hv hc h00 S hS hnt⟩
  exact (E.theory_model_iff Axioms.ACVF00).mpr h00

end SpecialTransformations.Section3

/- Component: AclNontrivialValues -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Nontriviality of the actual finite value quotient of a real set.
This is a pair of RV elements with distinct values, not distinct RV points
and not algebraicity in a separate imaginary Gamma closure. -/
def NontrivialFiniteValues (A : Set M) : Prop :=
  ∃ a b : M, a ∈ A ∧ b ∈ A ∧ GammaParameters.NonzeroRV a ∧
    GammaParameters.NonzeroRV b ∧ ¬ GammaParameters.SameScalar a b

theorem nontrivialFiniteValues_normalize_iff (A : Set M) :
    @NontrivialFiniteValues M (CanonicalStructure.normalize (M := M)) A ↔ NontrivialFiniteValues A := by
  unfold NontrivialFiniteValues
  exact exists_congr (fun a => exists_congr (fun b => and_congr Iff.rfl
    (and_congr Iff.rfl (and_congr (GammaParameters.nonzero_rv_normalize a)
      (and_congr (GammaParameters.nonzero_rv_normalize b)
        (not_congr (GammaParameters.same_scalar_normalize a b)))))))

theorem algebraicAt_rv_of_mem_acl (S : Set M) (t : CanonicalRV.RVSort M)
    (ht : t.val ∈ algebraicClosureSet S) : AlgebraicAt S .rv t.val := by
  obtain ⟨σ,hσ⟩ := ht
  cases σ with
  | vf => exact (TypedModelMap.not_rv_of_vf hσ.sorted t.property).elim
  | rv => exact hσ

theorem acl_field_nontrivial_valuation (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hS : ∀ a ∈ S, iVF a)
    (hvalues : NontrivialFiniteValues (algebraicClosureSet S))
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y) :
    ∃ x : vfAlgebraicClosureField S, x ≠ 0 ∧ v x.val ≠ 1 := by
  obtain ⟨a,b,ha,hb,haNZ,hbNZ,hne⟩ := hvalues
  let t : CanonicalRV.RVSort M := ⟨a,haNZ.1⟩
  let u : CanonicalRV.RVSort M := ⟨b,hbNZ.1⟩
  obtain ⟨x,hx⟩ := (rv_algebraicClosure_iff_lift h00 S hS t).mp (algebraicAt_rv_of_mem_acl S t ha)
  obtain ⟨y,hy⟩ := (rv_algebraicClosure_iff_lift h00 S hS u).mp (algebraicAt_rv_of_mem_acl S u hb)
  have hxNZ : x ≠ 0 := by
    intro h0
    have hx0 : x.val = 0 := congrArg Subtype.val h0
    exact haNZ.2 ((congrArg Subtype.val hx).symm.trans ((CanonicalRV.encodedRv_zero_iff x.val).mpr hx0))
  have hyNZ : y ≠ 0 := by
    intro h0
    have hy0 : y.val = 0 := congrArg Subtype.val h0
    exact hbNZ.2 ((congrArg Subtype.val hy).symm.trans ((CanonicalRV.encodedRv_zero_iff y.val).mpr hy0))
  have hvne : v x.val ≠ v y.val := by
    intro he
    have he' := (Values.vf_value_eq_iff v hv x.val y.val).mpr he
    rw [hx,hy] at he'
    exact hne ⟨haNZ,hbNZ,(Values.vrv_eq_iff t u).mp he'⟩
  by_cases hx1 : v x.val = 1
  · exact ⟨y,hyNZ,fun hy1 => hvne (hx1.trans hy1.symm)⟩
  · exact ⟨x,hxNZ,hx1⟩

end SpecialTransformations.Section3
