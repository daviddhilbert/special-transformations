import Section4.GammaRVIndependence
import Section3.RVExchange

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The actual earlier-section Gamma theorem supplies the named input.
No earlier-section proof is rebuilt in the Section 4 workflow. -/
theorem gammaRVAlgebraicityInput_of_earlier {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) : GammaRVAlgebraicityInput (M := M) κ :=
  fun B hsmall b => algebraic_rv_gamma_base_iff hκ hs h00 B hsmall b

/-- Finite formula support extends the given small-base RV exchange
theorem to every parameter set used by the matroid closure construction. -/
theorem rvExchangeInput_of_earlier {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) : RVExchangeInput (M := M) := by
  intro B x y hx hx0
  obtain ⟨C, hCf, hC, hxC⟩ := hx.finite_character
  let D := C \ {y.val}
  have hDf : D.Finite := hCf.subset (fun _ h => h.1)
  have hDB : D ⊆ B := by
    rintro a ⟨haC, hay⟩
    rcases hC haC with he | haB
    · exact (hay he).elim
    · exact haB
  have hCD : C ⊆ insert y.val D := by
    intro a ha
    by_cases he : a = y.val
    · exact Or.inl he
    · exact Or.inr ⟨ha, he⟩
  have hsmall : Cardinal.mk D < κ :=
    hDf.lt_aleph0.trans_le hκ
  have he := lemma_3_6_rv hκ hs h00 D hsmall y x (hxC.mono hCD)
    (fun h => hx0 (h.mono hDB))
  exact he.mono (Set.insert_subset_insert hDB)

end SpecialTransformations.Section4

end
