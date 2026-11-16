module

public import Section4.RVPatternProjection
public import Section4.EarlierRVInputs
public import Section4.GammaNamedValue

@[expose] public section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem exists_maximum_rv_pattern_fibre_nonempty
    (hcan : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : DefSet (rawRVSpace (M := M) n) (C.base : Set M)) (hne : A.carrier.Nonempty) :
    ∃ ε : Fin n → Bool, ∃ γ : Fin n → Values.Gamma (M := M),
      ∃ hγ : ∀ i, Values.GammaDefinable (C.base : Set M) {γ i},
        rvDim (rvGammaFibre hcan (rvPatternRelation hcan A ε) γ hγ) = rvDim A := by
  let S := (C.base : Set M)
  have hκ : Cardinal.aleph0 ≤ C.κ := C.uncountable.le
  let hex := rvExchangeInput_of_earlier hκ C.saturated C.model00
  let hΓ := gammaRVAlgebraicityInput_of_earlier hκ C.saturated C.model00
  obtain ⟨a, d, hd, v, hind⟩ := exists_maximum_rv_sequence_independent_gamma hcan hex
    hκ C.saturated hΓ C.small A hne
  let ε (i : Fin n) : Bool := decide ((a.val i).val = iRVZero)
  let γ0 (i : Fin n) : Values.Gamma (M := M) :=
    if h : (a.val i).val = iRVZero then 1 else Values.gammaOf (a.val i) h
  have hp : RVValuePattern ε γ0 a.val := by
    intro i
    by_cases hz : (a.val i).val = iRVZero
    · simp [ε, hz]
    · simp [ε, γ0, hz, Values.gammaOf]
  let Q := (rvPatternRelation hcan A ε).imageReal v
  have haQ : rvValues (a.val ∘ v) ∈ Q.fibre γ0 :=
    (mem_projected_rvPatternRelation_fibre hcan A ε v γ0 (a.val ∘ v)).mpr
      ⟨a.val, a.property, hp, rfl⟩
  have hseq : RVSequenceIndependent S (a.val ∘ v) :=
    (gammaRVSequenceIndependent_iff hκ hΓ ⟨S, Set.range γ0⟩ C.small _).mp (hind _)
  have hval : ∀ i, Values.vrv (a.val (v i)) = (γ0 (v i)).val := by
    intro i
    have hz : (a.val (v i)).val ≠ iRVZero := hseq.nonzero i
    simp only [γ0, dif_neg hz]
    rfl
  let D : Set (Fin n → Values.Gamma (M := M)) :=
    {γ | Fin.elim0 ∈ (rvInfiniteIterate hcan C.model00 C.saturated C.small Q v).fibre γ}
  have hDd : GammaSyntax.Definable S (fun γ => γ ∈ D) :=
    gamma_zero_relation_definable (rvInfiniteIterate hcan C.model00 C.saturated C.small Q v)
  have hDne : D.Nonempty := ⟨γ0, independent_mem_rvInfiniteIterate hcan C.model00 C.saturated
    C.small Q v γ0 (a.val ∘ v) haQ hval (hind _)⟩
  obtain ⟨γ, hγD, hγ⟩ := gamma_tuple_definable_point_base_context C D hDd hDne
  refine ⟨ε, γ, hγ, Nat.le_antisymm (rvDim_rvPatternFibre_le hcan A ε γ hγ) ?_⟩
  rw [← hd]
  exact rvDim_rvPatternFibre_ge_of_iterate hcan hex C.model00 hκ C.saturated C.small
    A ε v γ hγ hγD

/-- Maximal dimension is attained on an original-base definable value
fibre. The Boolean pattern accounts for the single absorbing RV value. -/
theorem exists_maximum_rv_pattern_fibre
    (hcan : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : DefSet (rawRVSpace (M := M) n) (C.base : Set M)) :
    ∃ ε : Fin n → Bool, ∃ γ : Fin n → Values.Gamma (M := M),
      ∃ hγ : ∀ i, Values.GammaDefinable (C.base : Set M) {γ i},
        rvDim (rvGammaFibre hcan (rvPatternRelation hcan A ε) γ hγ) = rvDim A := by
  by_cases hne : A.carrier.Nonempty
  · exact exists_maximum_rv_pattern_fibre_nonempty hcan C A hne
  · let ε : Fin n → Bool := fun _ => false
    let γ : Fin n → Values.Gamma (M := M) := fun _ => 1
    have hγ : ∀ i, Values.GammaDefinable (C.base : Set M) {γ i} :=
      fun _ => GammaSyntax.one_definable _
    refine ⟨ε, γ, hγ, ?_⟩
    have hAf : A.carrier.Finite := by
      rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact Set.finite_empty
    have hFf := hAf.subset (rvPatternFibre_subset hcan A ε γ hγ)
    rw [(rvDim_eq_zero_iff_finite _).mpr hFf, (rvDim_eq_zero_iff_finite _).mpr hAf]

end SpecialTransformations.Section4

end
