module

public import Section9.ResidueCoefficientBase
public import Section4.SmallGeneratedBase
public import Section4.CanonicalLift

@[expose] public section

/-! Choose small auxiliary bases for a fixed value fibre. The first
names the scales. The VF coefficient enlargement contains its residue
parameters, and the last substructure names that enlarged residue
field for the generic-point argument. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language IsLocalRing
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "VF" => VFType (M := M)
local notation "v" => Values.presentationValuation (M := M)

theorem exists_normalization_bases {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    (a b : Fin n → VF) :
    ∃ (B₀ B₁ : LRV.Substructure M) (T : Set M),
      B ≤ B₀ ∧ (B₀ : Set M) ⊆ T ∧ T ⊆ (B₁ : Set M) ∧
      Cardinal.mk B₀ < κ ∧ Cardinal.mk B₁ < κ ∧ Cardinal.mk T < κ ∧
      IsAlgClosed (vfParameterField T) ∧
      residueParameterField B₀ ≤ residueCoefficientField (vfParameterField T) ∧
      residueCoefficientField (vfParameterField T) ≤ residueParameterField B₁ ∧
      (∀ i, (tupleRV a i).val ∈ B₀) ∧ (∀ i, (tupleRV b i).val ∈ B₀) ∧
      (∀ i, ((a i)⁻¹).val ∈ T) ∧ (∀ i, ((b i)⁻¹).val ∈ T) ∧ (0 : VF).val ∈ T := by
  let sa := rvValues (tupleRV a)
  let sb := rvValues (tupleRV b)
  let ia (i : Fin n) := ((a i)⁻¹).val
  let ib (i : Fin n) := ((b i)⁻¹).val
  let F : Set M := (Set.range sa ∪ Set.range sb) ∪ ((Set.range ia ∪ Set.range ib) ∪ {(0 : VF).val})
  have hF : F.Finite := ((Set.finite_range _).union (Set.finite_range _)).union
    (((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_singleton _))
  let B₀ := Substructure.closure LRV ((B : Set M) ∪ F)
  have hB₀ : Cardinal.mk B₀ < κ := small_generated_finite_extension hκ B hB F hF
  obtain ⟨T, hB₀T, hT, hET, hclosed, hres₀⟩ := exists_residueCoefficient_extension hκ B₀ hB₀
  let E := vfParameterField T
  let R := ((v).comap E.subtype).valuationSubring
  let k₀ := residueCoefficientField E
  have he : Cardinal.mk k₀ = Cardinal.mk (ResidueField R) :=
    Cardinal.mk_congr (residueFieldInclusion v E).rangeRestrictFieldEquiv.symm.toEquiv
  have hres : Cardinal.mk (ResidueField R) ≤ Cardinal.mk R :=
    Cardinal.mk_le_of_surjective (f := residue R) residue_surjective
  have hR : Cardinal.mk R ≤ Cardinal.mk E := Cardinal.mk_subtype_le _
  have hk₀ : Cardinal.mk k₀ < κ := he.le.trans_lt ((hres.trans hR).trans_lt hET)
  let X := Set.range (fun c : k₀ => residueRaw c.val)
  let B₁ := Substructure.closure LRV (T ∪ X)
  have hB₁ : Cardinal.mk B₁ < κ := small_generated_substructure hκ _
    ((Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt hκ.le hT (Cardinal.mk_range_le.trans_lt hk₀)))
  have hFB : F ⊆ (B₀ : Set M) := fun _ h => Substructure.subset_closure (Or.inr h)
  refine ⟨B₀, B₁, T, (fun _ h => Substructure.subset_closure (Or.inl h)), hB₀T,
    (fun _ h => Substructure.subset_closure (Or.inl h)), hB₀, hB₁, hT, hclosed, hres₀, ?_,
    (fun i => hFB (Or.inl (Or.inl (Set.mem_range_self i)))),
    (fun i => hFB (Or.inl (Or.inr (Set.mem_range_self i)))),
    (fun i => hB₀T (hFB (Or.inr (Or.inl (Or.inl (Set.mem_range_self i)))))),
    (fun i => hB₀T (hFB (Or.inr (Or.inl (Or.inr (Set.mem_range_self i)))))),
    hB₀T (hFB (Or.inr (Or.inr rfl)))⟩
  intro c hc
  exact Substructure.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)

end SpecialTransformations.Section9
