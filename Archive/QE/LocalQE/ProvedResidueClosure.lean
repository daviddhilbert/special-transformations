import JohnsonGeometry
import ResidueEmbeddingExtension

/-!
The algebraic-closedness hypothesis for the actual residue field is discharged
by the residue-root argument already proved in the repository's Johnson
development. The two residue-field types are definitionally identical.
No valuation, model-theoretic, or QE result is assumed here.
-/

namespace ProvedResidueClosure

/-- The former Engler–Prestel residue-field input, now supplied by the existing
proof: the residue field of any valuation on an algebraically closed field is
algebraically closed. Nontriviality of the valuation is not required. -/
theorem provedResidueClosure : ResidueEmbeddingExtension.EPAlgebraicallyClosedResidue := by
  intro K Γ hK hKac hΓ v
  exact ValOneEC.Johnson.isAlgClosed_residueField v

end ProvedResidueClosure

#print axioms ProvedResidueClosure.provedResidueClosure
