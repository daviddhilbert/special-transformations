import Section4.GammaPredicates
import Mathlib.Data.Finset.Max

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

theorem gammaDefinable_sdiff {A B : Set (Values.Gamma (M := M))}
    (hA : Values.GammaDefinable S A) (hB : Values.GammaDefinable S B) :
    Values.GammaDefinable S (A \ B) :=
  (GammaSyntax.scalar_definable_iff (A \ B)).mp
    (((GammaSyntax.scalar_definable_iff A).mpr hA).and
      ((GammaSyntax.scalar_definable_iff B).mpr hB).not)

theorem gamma_finset_min_definable (F : Finset (Values.Gamma (M := M)))
    (hF : Values.GammaDefinable S (F : Set (Values.Gamma (M := M))))
    (hne : F.Nonempty) : Values.GammaDefinable S {F.min' hne} := by
  let ι := Fin 1 ⊕ Fin 1
  have hl := (GammaSyntax.unary_at hF (Sum.inr (0 : Fin 1) : ι)).and
    (GammaSyntax.lt_definable S (Sum.inr (0 : Fin 1) : ι) (Sum.inl 0))
  have h := ((GammaSyntax.scalar_definable_iff (F : Set (Values.Gamma (M := M)))).mpr hF).and
    hl.exists_block.not
  apply (GammaSyntax.scalar_definable_iff {F.min' hne}).mp
  exact h.congr (fun a => by
    change (a 0 ∈ F ∧ ¬ ∃ b : Fin 1 → Values.Gamma (M := M),
      b 0 ∈ F ∧ b 0 < a 0) ↔ a 0 = F.min' hne
    constructor
    · rintro ⟨ha, hb⟩
      exact le_antisymm (le_of_not_gt (fun he => hb ⟨![F.min' hne], F.min'_mem hne, he⟩))
        (F.min'_le _ ha)
    · intro he
      refine ⟨he.symm ▸ F.min'_mem hne, ?_⟩
      rintro ⟨b, hb, hba⟩
      rw [he] at hba
      exact not_lt_of_ge (F.min'_le _ hb) hba)

/-- Finite ordered imaginary sets have individually definable elements.
Iteratively removing the definable minimum retains the original base. -/
theorem gamma_finset_element_definable (F : Finset (Values.Gamma (M := M)))
    (hF : Values.GammaDefinable S (F : Set (Values.Gamma (M := M))))
    (c : Values.Gamma (M := M)) (hc : c ∈ F) : Values.GammaDefinable S {c} := by
  revert hF c
  induction F using Finset.strongInductionOn
  rename_i F ih
  intro hF c hc
  have hne : F.Nonempty := ⟨c, hc⟩
  let m := F.min' hne
  have hm : Values.GammaDefinable S {m} := gamma_finset_min_definable F hF hne
  by_cases he : c = m
  · exact he.symm ▸ hm
  · have hE : Values.GammaDefinable S ((F.erase m : Finset _) : Set (Values.Gamma (M := M))) := by
      simpa only [Finset.coe_erase] using gammaDefinable_sdiff hF hm
    exact ih (F.erase m) (Finset.erase_ssubset (F.min'_mem hne)) hE c
      (Finset.mem_erase.mpr ⟨he, hc⟩)

end SpecialTransformations.Section4

end
