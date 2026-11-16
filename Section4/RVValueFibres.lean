module

public import Section4.RVMaximumValueFibre
public import Section4.MapParameters

@[expose] public section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

def rvValuePullback (γ : Values.GammaTop (M := M)) : Set M :=
  {a | ∃ ha : iRV a, Values.vrv ⟨a, ha⟩ = γ}

def RVValueDefinable (S : Set M) (γ : Values.GammaTop (M := M)) : Prop :=
  DefinableAt S .rv (rvValuePullback γ)

theorem mem_rvValuePullback (t : CanonicalRV.RVSort M) (γ : Values.GammaTop (M := M)) :
    t.val ∈ rvValuePullback γ ↔ Values.vrv t = γ := by
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨t.property, h⟩⟩

theorem infinity_value_definable (S : Set M) : RVValueDefinable S (Values.infinity (M := M)) := by
  have hz := definableClosureAt_function_symbol S Fn.rvZero Fin.elim0
    (fun i => i.elim0) (fun i => i.elim0)
  have he : rvValuePullback (Values.infinity (M := M)) = {iRVZero} := by
    ext a
    constructor
    · rintro ⟨ha, he⟩
      exact (Values.vrv_eq_infinity_iff ⟨a, ha⟩).mp he
    · intro he
      subst a
      exact ⟨Transfer.rv_zero_mem hM, (Values.vrv_eq_infinity_iff _).mpr rfl⟩
  change DefinableAt S .rv (rvValuePullback Values.infinity)
  rw [he]
  exact hz

theorem gamma_value_definable (γ : Values.Gamma (M := M))
    (hγ : Values.GammaDefinable S {γ}) : RVValueDefinable S γ.val := by
  have he : rvValuePullback γ.val = Values.gammaPullback {γ} := by
    ext a
    constructor
    · rintro ⟨ha, he⟩
      have h0 : a ≠ iRVZero := by
        intro hz
        exact γ.property (he.symm.trans ((Values.vrv_eq_infinity_iff _).mpr hz))
      exact ⟨ha, h0, Subtype.ext he⟩
    · rintro ⟨ha, h0, he⟩
      exact ⟨ha, congrArg Subtype.val he⟩
  change DefinableAt S .rv (rvValuePullback γ.val)
  rw [he]
  exact hγ

def rvPatternValues (ε : Fin n → Bool) (γ : Fin n → Values.Gamma (M := M)) :
    Fin n → Values.GammaTop (M := M) := fun i => if ε i then Values.infinity else (γ i).val

theorem rvValuePattern_iff (ε : Fin n → Bool) (γ : Fin n → Values.Gamma (M := M))
    (t : Fin n → CanonicalRV.RVSort M) :
    RVValuePattern ε γ t ↔ ∀ i, Values.vrv (t i) = rvPatternValues ε γ i := by
  apply forall_congr'
  intro i
  change (if ε i then (t i).val = iRVZero else Values.vrv (t i) = (γ i).val) ↔
    Values.vrv (t i) = (if ε i then Values.infinity else (γ i).val)
  cases ε i
  · exact Iff.rfl
  · exact (Values.vrv_eq_infinity_iff (t i)).symm

def rvValueFibre (A : DefSet (rawRVSpace (M := M) n) S)
    (γ : Fin n → Values.GammaTop (M := M)) (hγ : ∀ i, RVValueDefinable S (γ i)) :
    DefSet (rawRVSpace (M := M) n) S where
  carrier := {t | t ∈ A.carrier ∧ ∀ i, Values.vrv (t i) = γ i}
  definable := by
    have hp (i : Fin n) : S.Definable LRV {a : Fin n → M | a i ∈ rvValuePullback (γ i)} :=
      (hγ i).raw_definable.preimage_comp (fun _ : Fin 1 => i)
    have hall : S.Definable LRV {a : Fin n → M | ∀ i, a i ∈ rvValuePullback (γ i)} := by
      rw [Set.ofPred_forall]
      exact Set.definable_iInter_of_finite hp
    have hdA : @Set.Definable M S LRV sM (Fin n) ((rawRVSpace n).preimage A.carrier) := A.definable
    change @Set.Definable M S LRV sM (Fin n) _
    have he : (rawRVSpace n).preimage {t | t ∈ A.carrier ∧ ∀ i, Values.vrv (t i) = γ i} =
        (rawRVSpace n).preimage A.carrier ∩ {a | ∀ i, a i ∈ rvValuePullback (γ i)} := by
      ext a
      constructor
      · rintro ⟨ha, hA, hv⟩
        refine ⟨⟨ha, hA⟩, ?_⟩
        intro i
        have he := congrFun (rvValues_decode (M := M) ⟨a, ha⟩) i
        change ((rawRVSpace n).decode ⟨a, ha⟩ i).val = a i at he
        exact he ▸ (mem_rvValuePullback _ _).mpr (hv i)
      · rintro ⟨⟨ha, hA⟩, hv⟩
        refine ⟨ha, hA, ?_⟩
        intro i
        apply (mem_rvValuePullback _ _).mp
        have he := congrFun (rvValues_decode (M := M) ⟨a, ha⟩) i
        change ((rawRVSpace n).decode ⟨a, ha⟩ i).val = a i at he
        rw [he]
        exact hv i
    rw [he]
    exact hdA.inter hall

/-- Lemma 4.11, with the full value carrier retaining the one absorbing
value at zero coordinates. The value tuple and its fibre use exactly the
standing base; no independent-sequence or infinity-elimination conclusion
is a theorem hypothesis. -/
theorem lemma_4_11 (hcan : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : DefSet (rawRVSpace (M := M) n) (C.base : Set M)) :
    ∃ γ : Fin n → Values.GammaTop (M := M),
      ∃ hγ : ∀ i, RVValueDefinable (C.base : Set M) (γ i), rvDim (rvValueFibre A γ hγ) = rvDim A := by
  obtain ⟨ε, γ, hγ, hd⟩ := exists_maximum_rv_pattern_fibre hcan C A
  let δ := rvPatternValues ε γ
  have hδ : ∀ i, RVValueDefinable (C.base : Set M) (δ i) := by
    intro i
    change RVValueDefinable (C.base : Set M) (if ε i then Values.infinity else (γ i).val)
    cases hε : ε i
    · exact gamma_value_definable (γ i) (hγ i)
    · exact infinity_value_definable _
  refine ⟨δ, hδ, ?_⟩
  have he : rvValueFibre A δ hδ = rvGammaFibre hcan (rvPatternRelation hcan A ε) γ hγ := by
    have hc : (rvValueFibre A δ hδ).carrier =
        (rvGammaFibre hcan (rvPatternRelation hcan A ε) γ hγ).carrier := by
      ext t
      exact and_congr Iff.rfl (rvValuePattern_iff ε γ t).symm |>.trans
        (mem_rvPatternRelation_fibre hcan A ε γ t).symm
    exact DefSet.eq_of_carrier_eq hc
  rw [he]
  exact hd

end SpecialTransformations.Section4

end
