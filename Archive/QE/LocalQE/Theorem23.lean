import LocalAssembly
import SubstructureRVPreparation
import SubstructureRVGraph
import ProvedResidueClosure
import ProvedACFExtension
import CountableQECriterion
import CanonicalCountable

/-! Quantifier elimination in the author's RV language, with named inversion.

The paper-specific preparation and extension arguments are proved here.
Residue-field algebraic closedness and both ACF and ordinary ACVF embedding
extension are supplied by the repository's checked proofs. The generic QE
criterion for this countable language follows from the proved ultrapower
construction, downward Löwenheim–Skolem, and compactness.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace LocalAssembly

/-- Construct the preparation data from the actual language substructure.
There is no remaining paper-specific extension hypothesis. -/
theorem preparation_of_standard_results
    (hEP : ResidueEmbeddingExtension.EPAlgebraicallyClosedResidue)
    (hACF : ResidueEmbeddingExtension.MarkerACFSaturatedEmbeddingExtension) :
    Preparation := by
  intro M N sM sN hM hN hcM hcN hSat S f Γ Δ hΓ hΔ v w hv hw
  obtain ⟨ρ, R, hR, hfun, hgroup⟩ :=
    SubstructureRVPreparation.exists_frame v w hv hw S f hEP hACF hSat
  have hOld := SubstructureRVGraph.oldRV_of_contains_group v w hv hw S f R hR.zero hgroup
  exact ⟨{
    sourceComparison := hv
    targetComparison := hw
    residueMap := ρ
    graph := R
    laws := hR
    functional := hfun
    baseCompatibility :=
      SubstructureRVCompatibility.field_compat v w hv hw S f R hR.mul hR.inv hOld
    oldRV := hOld
  }⟩

/-- All algebraic preparation inputs are now supplied by checked proofs. -/
theorem preparation : Preparation :=
  preparation_of_standard_results ProvedResidueClosure.provedResidueClosure
    ProvedACFExtension.markerACFSaturatedEmbeddingExtension

/-- Full QE on canonical tagged structures, with every input proved. -/
theorem fullQE : MarkerBridge.FullQE CanonicalTheory.CanonicalACVF :=
  CountableQECriterion.fullQE_of_saturatedExtension ⟨Fn.vfZero⟩
    (canonicalExtension_of_preparation preparation)

theorem quantifier_elimination : HasQE Axioms.ACVF :=
  CanonicalStructure.hasQE_of_raw_canonical
    (MarkerBridge.rawCanonicalQE_of_fullQE fullQE)

end LocalAssembly

namespace SpecialTransformations.Milestone0

/-- Theorem 2.3, with no additional mathematical hypotheses.
The RV inverse is a named function, as in the author's group-language convention.
All paper-specific substructure preparation and RV extension steps are proved.
The ACF and ordinary valued-field QE steps are supplied by the checked Johnson
proofs, and residue-field algebraic closedness is also proved. -/
theorem theorem_2_3_quantifier_elimination : HasQE Axioms.ACVF :=
  LocalAssembly.quantifier_elimination

end SpecialTransformations.Milestone0

#print axioms LocalAssembly.preparation_of_standard_results
#print axioms LocalAssembly.preparation
#print axioms LocalAssembly.fullQE
#print axioms LocalAssembly.quantifier_elimination
#print axioms SpecialTransformations.Milestone0.theorem_2_3_quantifier_elimination
