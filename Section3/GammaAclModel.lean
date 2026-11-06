import Section3.AclModel
import Section3.CanonicalParameters
import Section3.GammaClosureElimination
import Section3.GammaParameterBridge
import Section3.GammaSupport

/- Component: GammaAclModel -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A genuinely VF-generated imaginary base has its real part generated
by the same VF parameters. No Gamma representatives enter this equality. -/
theorem VFGeneratedBase.real_vfGenerated {B : Base (M := M)} (hB : VFGeneratedBase B) :
    VFGenerated B.real := by
  obtain ⟨A,hAB,hA,hB⟩ := hB
  refine ⟨A,hA,?_⟩
  rw [← hB]
  ext x
  exact exists_congr (fun σ => dcl_base_empty_iff A σ x)

/-- Definable Gamma names in a VF-generated base add no real definable
sets. This is elimination of complete invariant fibres, without saturation. -/
theorem VFGeneratedBase.definableOver_iff_real {B : Base (M := M)}
    (hB : VFGeneratedBase B) {n : ℕ} (sn : Fin n → SortTag) (U : Set (Fin n → M)) :
    DefinableOverBase B sn U ↔ SpecialTransformations.Section3.DefinableOver B.real sn U := by
  constructor
  · intro hU
    obtain ⟨A,hAB,hA,hgen⟩ := hB
    have hreal (b : M) (hb : b ∈ B.real) : ∃ σ, DefinableClosureAt A σ b := by
      rw [← hgen] at hb
      obtain ⟨σ,hb⟩ := hb
      exact ⟨σ,(dcl_base_empty_iff A σ b).mp hb⟩
    have hgamma (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) :
        DefinableAt A .rv (Values.gammaPullback {γ}) := by
      rw [← hgen] at hγ
      exact (at_base_empty_iff A .rv _).mp hγ
    exact (hU.eliminate_to_real_base hreal hgamma).mono hAB
  · intro hU
    exact ((base_empty_iff B.real sn U).mpr hU).mono (Set.Subset.refl _) (Set.empty_subset _)

theorem VFGeneratedBase.definableAt_iff_real {B : Base (M := M)}
    (hB : VFGeneratedBase B) (σ : SortTag) (U : Set M) :
    DefinableAtBase B σ U ↔ DefinableAt B.real σ U := by
  constructor
  · intro hU
    have h := (hB.definableOver_iff_real (fun _ : Fin 1 => σ) {z | z 0 ∈ U}).mp hU
    exact ⟨h,fun u hu => ((definableOver_iff_normalized_raw B.real _ _).mp h).2 ![u] hu 0⟩
  · intro hU
    exact (hB.definableOver_iff_real (fun _ : Fin 1 => σ) {z | z 0 ∈ U}).mpr hU.1

theorem VFGeneratedBase.algebraic_iff_real {B : Base (M := M)}
    (hB : VFGeneratedBase B) (σ : SortTag) (b : M) :
    AlgebraicAtBase B σ b ↔ AlgebraicAt B.real σ b := by
  constructor
  · rintro ⟨U,hU,hfin,hb⟩
    exact ⟨U,(hB.definableAt_iff_real σ U).mp hU,hfin,hb⟩
  · rintro ⟨U,hU,hfin,hb⟩
    exact ⟨U,(hB.definableAt_iff_real σ U).mpr hU,hfin,hb⟩

theorem VFGeneratedBase.real_acl_eq {B : Base (M := M)} (hB : VFGeneratedBase B) :
    {b | ∃ σ, AlgebraicAtBase B σ b} = algebraicClosureSet B.real := by
  ext b
  exact exists_congr (fun σ => hB.algebraic_iff_real σ b)

/-- All Gamma names of a VF-generated base have actual nonzero RV
representatives in its real acl. The witness is obtained by elementarity
from the full invariant value fibre, never by naming a chosen section. -/
theorem VFGeneratedBase.gamma_names_lift_into_acl
    (h00 : M ⊨ Axioms.ACVF00) {B : Base (M := M)} (hB : VFGeneratedBase B)
    (hvalues : NontrivialFiniteValues (algebraicClosureSet B.real))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) :
    ∃ t : Code (M := M), raw t ∈ algebraicClosureSet B.real ∧ value t = γ := by
  have hVF := hB.real_vfGenerated
  obtain ⟨A,hAB,hA,hgen⟩ := hB
  have hγA : GammaDefinableClosureAtBase (⟨A,∅⟩ : Base (M := M)) γ := by
    rw [← hgen] at hγ
    exact hγ
  let U := Values.gammaPullback ({γ} : Set (Values.Gamma (M := M)))
  have hU : DefinableAt A .rv U := (at_base_empty_iff A .rv U).mp hγA
  have hUne : U.Nonempty := by
    let t := representative γ
    exact ⟨raw t,raw_rv t,raw_ne_zero t,representative_value γ⟩
  have hUN := (definableAt_iff_normalized_raw A .rv U).mp hU
  let T := normalizedAlgebraicClosureSubstructure B.real
  have he := normalized_acl_elementary h00 B.real hVF hvalues
  have hmem := mem_normalizedAlgebraicClosureSubstructure B.real
  have hAT : A ⊆ (T : Set M) := by
    intro a ha
    exact (hmem a).mpr
      (subset_algebraicClosureSet B.real (hAB ha))
  letI := CanonicalStructure.normalize (M := M)
  let E : LRV.ElementarySubstructure M := ⟨T,he⟩
  have hUE := hUN.1.mono hAT
  obtain ⟨t,htU,htE⟩ := E.meetsDefinable U hUne hUE
  obtain ⟨htRV,ht0,htγ⟩ := htU
  exact ⟨⟨⟨t,htRV⟩,ht0⟩,
    (hmem t).mp htE,htγ⟩

/-- Corollary 3.14 with a genuine VF-generated Gamma base. The full
VF/RV structure is a model, its carrier is exactly real algebraic closure
over that base, and every existing imaginary name is represented inside.
Real atomic-diagram naming is provided separately by `corollary_3_14`. -/
theorem corollary_3_14_gamma_base (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hB : VFGeneratedBase B)
    (hvalues : NontrivialFiniteValues {b | ∃ σ, AlgebraicAtBase B σ b}) :
    let T := normalizedAlgebraicClosureSubstructure B.real
    (@Theory.Model LRV T (@Substructure.inducedStructure LRV M
      (CanonicalStructure.normalize (M := M)) T) Axioms.ACVF00) ∧
    (∀ b : M, b ∈ T ↔ ∃ σ, AlgebraicAtBase B σ b) ∧
    (∀ γ ∈ B.gamma, ∃ t : Code (M := M), raw t ∈ T ∧ value t = γ) := by
  have hvalues' : NontrivialFiniteValues (algebraicClosureSet B.real) := by
    rwa [hB.real_acl_eq] at hvalues
  refine ⟨normalized_acl_model h00 B.real hB.real_vfGenerated hvalues',?_,?_⟩
  · intro b
    rw [mem_normalizedAlgebraicClosureSubstructure B.real b,← hB.real_acl_eq]
    rfl
  · intro γ hγ
    obtain ⟨t,ht,hv⟩ := hB.gamma_names_lift_into_acl h00 hvalues' γ hγ
    exact ⟨t,(mem_normalizedAlgebraicClosureSubstructure B.real (raw t)).mpr ht,hv⟩

end SpecialTransformations.Section3.GammaParameters
