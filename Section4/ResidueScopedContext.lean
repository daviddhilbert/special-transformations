import Section4.ResidueRelativeTerms
import TypedModelMap

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def residueFieldNames (E : Subfield (ModelResidue M)) : Set M :=
  {x | ∃ u : E, (residueRV u.val).val = x}

def residueExtendedBase (B : LRV.Substructure M) (E : Subfield (ModelResidue M)) : Set M :=
  (B : Set M) ∪ residueFieldNames E

/-- Adjoining residue elements introduces their ordinary field operations
into the coefficient field, while the original VF constants stay in B. -/
def scopedContextOfSubstructure (B : LRV.Substructure M) (E : Subfield (ModelResidue M))
    (hE : residueParameterField B ≤ E) {n : ℕ}
    (p : Parameters (residueExtendedBase B E)) (s : Fin n → CanonicalRV.RVSort M)
    (hs : ∀ i, s i ∈ extendedCoefficients B E) : Scoped.TermContext p s where
  vfBase := B
  coefficients := coefficientContextOfSubstructure B E hE
  vf_parameters i hi := by
    rcases p.mem_base i with hb | ⟨u, hu⟩
    · exact hb
    · have hr : iRV (p.values i) := hu ▸ (residueRV u.val).property
      exact (TypedModelMap.not_vf_of_rv hr hi).elim
  rv_parameters i hi := by
    rcases p.mem_base i with hb | ⟨u, hu⟩
    · exact extendedCoefficients_base B E hb
    · have he : (⟨p.values i, hi⟩ : CanonicalRV.RVSort M) = residueRV u.val :=
        Subtype.ext hu.symm
      change (⟨p.values i, hi⟩ : CanonicalRV.RVSort M) ∈ extendedCoefficients B E
      rw [he]
      exact extendedCoefficients_residue B E u.property
  rv_of_vf a ha := extendedCoefficients_base B E
    (B.fun_mem Fn.rvMap ![a.val] (by intro i; fin_cases i; exact ha))
  scales := hs

end SpecialTransformations.Section4.ResiduePurity

end
