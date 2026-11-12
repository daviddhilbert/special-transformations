module

public import Section4.ResidueZariskiComparison
public import Section4.RVNamedDivision
public import Section4.EarlierRVInputs

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem normalizedResidueSet_definable_base
    (hcan : CanonicalStructure.IsCanonical (M := M))
    (B : LRV.Substructure M) {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) (B : Set M))
    (s : Fin n → CanonicalRV.RVSort M) (hs : ∀ i, (s i).val ∈ B) :
    Relative.Def (residueParameterField B) (normalizedResidueSet A s) := by
  let E := residueParameterField B
  exact normalizedResidueSet_definable hcan B E le_rfl
    (A.extend Set.subset_union_left) s (fun i => extendedCoefficients_base B E (hs i))

theorem residue_comparison_named
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hsat : Saturated M κ)
    (hh : StronglyHomogeneous M κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) (B : Set M))
    (s : Fin n → CanonicalRV.RVSort M) (hs : ∀ i, (s i).val ∈ B)
    (hval : ∀ t ∈ A.carrier, ∀ i, Values.vrv (t i) = Values.vrv (s i))
    (hne : A.carrier.Nonempty) :
    ringKrullDim (MvPolynomial (Fin n) (ModelResidue M) ⧸
      residueVanishingIdeal (normalizedResidueSet A s)) = rvDim A := by
  have hD := normalizedResidueSet_definable_base hcan B A s hs
  have hDne : (normalizedResidueSet A s).Nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨residueNormalize s a, residueNormalize_mem A s hval ⟨a, ha⟩⟩
  have he : residueRVSet hcan (residueParameterField B) (B : Set M)
      (residueParameterField_le_definableField B) (normalizedResidueSet A s) hD =
      (rvNamedDivision A s hs).image :=
    DefSet.eq_of_carrier_eq (rvNamedDivision_image_eq A s hs hval).symm
  rw [residue_dimension_eq_Zariski hcan hex hκ hsat hh B hB _ hD hDne,
    he, rvNamedDivision_dimension A s hs hval]

/-- Lemma 4.10: the actual Krull dimension of the normalized residue
set's Zariski closure is the RV dimension of the original fixed-value
set. The normalizing tuple is arbitrary; it is not assumed to be named
over the original base. Empty coordinates use the existing RV zero. -/
theorem lemma_4_10 (hcan : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) (C.base : Set M))
    (s : Fin n → CanonicalRV.RVSort M)
    (hval : ∀ t ∈ A.carrier, ∀ i, Values.vrv (t i) = Values.vrv (s i))
    (hne : A.carrier.Nonempty) :
    ringKrullDim (MvPolynomial (Fin n) (ModelResidue M) ⧸
      residueVanishingIdeal (normalizedResidueSet A s)) = rvDim A := by
  let B := Substructure.closure LRV ((C.base : Set M) ∪ Set.range (rvValues s))
  have hCB : (C.base : Set M) ⊆ (B : Set M) :=
    fun _ hx => Substructure.subset_closure (Or.inl hx)
  have hB : Cardinal.mk B < C.κ := small_generated_finite_extension C.uncountable
    C.base C.small _ (Set.finite_range (rvValues s))
  have hs : ∀ i, (s i).val ∈ B := fun i =>
    Substructure.subset_closure (Or.inr ⟨i, rfl⟩)
  let hex := rvExchangeInput_of_earlier C.uncountable.le C.saturated C.model00
  have h := residue_comparison_named hcan hex C.uncountable C.saturated C.homogeneous
    B hB (A.extend hCB) s hs hval hne
  have hinv := rvDim_parameter_invariant hcan hex C.uncountable.le C.saturated
    C.homogeneous hCB C.small hB A
  exact h.trans (congrArg (fun k : ℕ => (k : WithBot ℕ∞)) hinv)

theorem lemma_4_10_closure (hcan : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} (A : DefSet (rawRVSpace (M := M) n) (C.base : Set M))
    (s : Fin n → CanonicalRV.RVSort M)
    (hval : ∀ t ∈ A.carrier, ∀ i, Values.vrv (t i) = Values.vrv (s i))
    (hne : A.carrier.Nonempty) :
    ringKrullDim (MvPolynomial (Fin n) (ModelResidue M) ⧸
      MvPolynomial.vanishingIdeal (ModelResidue M)
        (residueZariskiClosure (normalizedResidueSet A s))) = rvDim A := by
  rw [residueZariskiClosure_vanishingIdeal]
  exact lemma_4_10 hcan C A s hval hne

end SpecialTransformations.Section4.ResiduePurity

end
