import Section4.RVMaximumValueFibre

/-! Choose a nonempty full-dimensional fixed-value fibre and take
its own point as the scale tuple. No section of RV to VF is chosen
definably over the original base. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem exists_full_nonzero_rvValueFibre
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : BaseContext M)
    (A : DefSet (rawRVSpace (M := M) n) (B.base : Set M))
    (hA : ∀ t ∈ A.carrier, ∀ i, (t i).val ≠ iRVZero) (hd : 0 < rvDim A) :
    ∃ F : DefSet (rawRVSpace (M := M) n) (B.base : Set M), ∃ s : F,
      F.carrier ⊆ A.carrier ∧ rvDim F = rvDim A ∧
      ∀ t ∈ F.carrier, ∀ i, Values.vrv (t i) = Values.vrv (s.val i) := by
  obtain ⟨ε, γ, hγ, hdim⟩ := exists_maximum_rv_pattern_fibre hc B A
  let F := rvGammaFibre hc (rvPatternRelation hc A ε) γ hγ
  have hsub : F.carrier ⊆ A.carrier := rvPatternFibre_subset hc A ε γ hγ
  have hne : F.carrier.Nonempty := by
    by_contra h
    have hfin : F.carrier.Finite := by
      rw [Set.not_nonempty_iff_eq_empty.mp h]
      exact Set.finite_empty
    exact (Nat.ne_of_gt hd) (hdim.symm.trans ((rvDim_eq_zero_iff_finite F).mpr hfin))
  obtain ⟨s, hs⟩ := hne
  refine ⟨F, ⟨s, hs⟩, hsub, hdim, ?_⟩
  intro t ht i
  have hs' := ((mem_rvPatternRelation_fibre hc A ε γ s).mp hs).2 i
  have ht' := ((mem_rvPatternRelation_fibre hc A ε γ t).mp ht).2 i
  cases h : ε i
  · simp only [h, Bool.false_eq_true, if_false] at hs' ht'
    exact ht'.trans hs'.symm
  · simp only [h, if_true] at hs'
    exact (hA s (hsub hs) i hs').elim

end SpecialTransformations.Section9
