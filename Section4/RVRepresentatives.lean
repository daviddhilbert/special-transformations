module

public import Section4.PositiveAdditiveRepresentatives
public import Section4.RVScissorCoproduct

@[expose] public section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

/-- Each element of the actual fixed-degree positive RV quotient has a
single genuine definable RV object as representative. -/
theorem rvClass_surjective : Function.Surjective (rvClass (M := M) (S := S) (k := k)) :=
  PositiveAdditiveGrothendieck.of_surjective (rvScissorPresentation S k)
    rvCoprodObject rvClass_coprod

end SpecialTransformations.Section4

end
