module

public import Section4.RVValuePatternFamily
public import Section4.GammaDefinableFibres
public import Section4.RVInfiniteIteration
public import Section4.RVSequenceBounds
public import Section4.RVDimensionRank

@[expose] public section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n k : ℕ}

theorem mem_projected_rvPatternRelation_fibre
    (hcan : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawRVSpace (M := M) n) S) (ε : Fin n → Bool) (v : Fin k → Fin n)
    (γ : Fin n → Values.Gamma (M := M)) (t : Fin k → CanonicalRV.RVSort M) :
    rvValues t ∈ ((rvPatternRelation hcan A ε).imageReal v).fibre γ ↔
      ∃ a ∈ A.carrier, RVValuePattern ε γ a ∧ a ∘ v = t := by
  rw [Relation.imageReal_fibre]
  constructor
  · rintro ⟨b, hb, hbt⟩
    let a (i : Fin n) : CanonicalRV.RVSort M :=
      ⟨b i, (rvPatternRelation hcan A ε).fibre_proper γ b hb i⟩
    have ha := (mem_rvPatternRelation_fibre hcan A ε γ a).mp hb
    refine ⟨a, ha.1, ha.2, ?_⟩
    apply rvValues_injective
    exact hbt
  · rintro ⟨a, ha, hp, he⟩
    refine ⟨rvValues a, (mem_rvPatternRelation_fibre hcan A ε γ a).mpr ⟨ha, hp⟩, ?_⟩
    exact congrArg rvValues he

theorem rvPatternFibre_subset
    (hcan : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawRVSpace (M := M) n) S) (ε : Fin n → Bool)
    (γ : Fin n → Values.Gamma (M := M)) (hγ : ∀ i, Values.GammaDefinable S {γ i}) :
    (rvGammaFibre hcan (rvPatternRelation hcan A ε) γ hγ).carrier ⊆ A.carrier :=
  fun a ha => ((mem_rvPatternRelation_fibre hcan A ε γ a).mp ha).1

theorem rvDim_rvPatternFibre_le
    (hcan : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawRVSpace (M := M) n) S) (ε : Fin n → Bool)
    (γ : Fin n → Values.Gamma (M := M)) (hγ : ∀ i, Values.GammaDefinable S {γ i}) :
    rvDim (rvGammaFibre hcan (rvPatternRelation hcan A ε) γ hγ) ≤ rvDim A := by
  apply rvDim_le_of_finite_map (Map.inclusion (rvPatternFibre_subset hcan A ε γ hγ))
  apply Map.finiteFibres_of_injective
  intro a b h
  exact Subtype.ext (congrArg (fun x : A => x.val) h)

theorem rvDim_rvPatternFibre_ge_of_iterate
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (A : DefSet (rawRVSpace (M := M) n) S) (ε : Fin n → Bool) (v : Fin k → Fin n)
    (γ : Fin n → Values.Gamma (M := M)) (hγ : ∀ i, Values.GammaDefinable S {γ i})
    (hmem : Fin.elim0 ∈ (rvInfiniteIterate hcan h00 hs hsmall
      ((rvPatternRelation hcan A ε).imageReal v) v).fibre γ) :
    k ≤ rvDim (rvGammaFibre hcan (rvPatternRelation hcan A ε) γ hγ) := by
  obtain ⟨t, ht, hti, _⟩ := rvInfiniteIterate_exists_independent hcan h00 hκ hs hsmall
    ((rvPatternRelation hcan A ε).imageReal v) v γ hmem
  obtain ⟨a, ha, hp, he⟩ := (mem_projected_rvPatternRelation_fibre hcan A ε v γ t).mp ht
  have htiS : RVSequenceIndependent S t := hti.mono_base Set.subset_union_left
  have hka : k ≤ rvTupleRank hcan hex S a := by
    rw [← rvTupleRank_eq_arity_of_sequence hcan hex S t htiS, ← he]
    exact rvTupleRank_subsequence_le hcan hex S a v
  let F := rvGammaFibre hcan (rvPatternRelation hcan A ε) γ hγ
  have haF : a ∈ F.carrier := (mem_rvPatternRelation_fibre hcan A ε γ a).mpr ⟨ha, hp⟩
  exact hka.trans (rvTupleRank_le_rvDim hcan hex F ⟨a, haF⟩)

end SpecialTransformations.Section4

end
