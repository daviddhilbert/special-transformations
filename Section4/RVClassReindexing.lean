import Section4.RVReindexing
import Section4.RVPositiveIsoComparison

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k l : ℕ}

theorem rvClass_reindexVolume (U : RVObject (M := M) S k) (e : Equiv.Perm (Fin k)) :
    rvClass (U.reindexVolume e) = rvClass U := (rvClass_iso (rvReindexVolumeIso U e)).symm

/-- Transport in the degree agrees with any finite-coordinate
identification, because permutations of labels are actual RV isomorphisms. -/
theorem rvClass_cast_reindex (h : k = l) (U : RVObject (M := M) S k) (e : Fin l ≃ Fin k) :
    (h ▸ rvClass U) = rvClass (U.reindexVolume e) := by
  subst l
  exact (rvClass_reindexVolume U e).symm

end SpecialTransformations.Section4

end
