/-
# m8 / d7 (u8, consolidation) — the machine-check behind `QE/FRONTIER.md` and `QE/HANDOFF.md`

Nothing here is new mathematics.  This file exists so that every structural claim the two
documents make is checked against the tree rather than asserted:

* §0 `#check` of the six named parts of the frontier (`QE/RouteLedger.lean`) and of the three
  route theorems the documents call equivalent (`paper_theorem_rel_two`,
  `paper_theorem_rel_of_qffinsat`, `paper_theorem_2_3_of_five_rel`), plus the frozen-gate and
  hull-form endgames;
* §1 the reduction the documents rely on: the four case parts are jointly implied by **one**
  gate-free residual, `Case35Hull.RootHullRealisation` (`QE/RootHull.lean`);
* §2 the u6 matrix rows: `QFFinSat` at `relGate` implies all five non-quoted parts (hence the
  canonical single-hypothesis form is `G3.paper_theorem_rel_of_qffinsat`, recovered here through
  the six-part list);
* §3 the stress tests: the `QFFinSat` hypothesis of §2 is *not* a theorem at every `relGate` pair
  (`G3.not_forall_qffinsat_at_relGate`), and the parts are false at an Archimedean configuration
  (`G3.not_extendsAt_rel_of_archimedean_config`, `NewRVGlue.not_cases_of_infinitesimal`), so the
  frontier is conditional on the target's value group and is not a restatement of the target;
* §4 axiom audit.

Compile (from the repository root `$R`):

    LEAN_PATH=$R/QE:$R/.scratch2/sec3:$LEAN_PATH lean .ultramath/smw2qpqe7/m8/Probe.lean

No `sorry`, no `axiom`, no `native_decide`.
-/
import RouteLedger
import RootHull
import NewRVGlue
import NonVacuity2
import FinalAudit

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.Consolidation

/-! ## 0. The frontier as the tree states it -/

#check @RouteLedger.RelHull
#check @RouteLedger.RelSeparated
#check @RouteLedger.RelUnit
#check @RouteLedger.RelNonUnit
#check @RouteLedger.RelNewRV
#check @RouteLedger.relCases_of_parts
#check @RouteLedger.paper_theorem_2_3_of_five_rel
#check @G3.paper_theorem_rel_two
#check @G3.paper_theorem_rel_of_qffinsat
#check @RouteLedger.paper_theorem_2_3_of_five
#check @RouteLedger.paper_theorem_2_3_of_hull_and_cases
#check @RouteLedger.hull_and_cases_iff_satReal
#check @RouteLedger.relHull_and_cases_iff_input5R
#check @RouteLedger.RootData
#check @RouteLedger.AlgebraicUnitSlot
#check @RouteLedger.TranscendentalUnitSlot
#check @RouteLedger.RVTransVF
#check @RouteLedger.lemma36Hyp_false
#check @RouteLedger.not_exists_lemma36Hyp
#check @Case35Hull.RootHullRealisation
#check @Case35Hull.oneStepVFP_of_rootHullEmbedding
#check @Case35Hull.standing_rootHull

/-! ## 1. The four case parts come from one gate-free residual -/

/-- `QE/RootHull.lean`'s `RootHullRealisation` gives the whole case ledger at `relGate`; the gate is
not even consulted, because the residual carries no hypothesis of its own. -/
theorem relCases_of_rootHullRealisation (h : Case35Hull.RootHullRealisation) :
    RouteLedger.RelCases :=
  fun M N _ _ _ _ _ => Case35Hull.cases_of_rootHullEmbedding (h M N)

/-- Consequently the honest-gate endgame runs on **two** parts plus the quotation: the hull form
Lemma 3.3 and the root-hull realisation residual. -/
theorem paper_theorem_2_3_of_relHull_rootHull (hQ : M5Shoenfield.ShoenfieldTestRel)
    (hH : RouteLedger.RelHull) (h : Case35Hull.RootHullRealisation) : HasQE Axioms.ACVF :=
  RouteLedger.paper_theorem_2_3_of_relHull_relCases hQ hH
    (relCases_of_rootHullRealisation h)

/-! ## 2. The u6 matrix: `QFFinSat` at `relGate` implies all five non-quoted parts -/

section FinSat

/-- The `QFFinSat`-at-`relGate` input, named (it is the hypothesis of
`G3.paper_theorem_rel_of_qffinsat`). -/
def FinSatRelGate : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → M2Saturation.QFFinSat M N

/-- `QFFinSat` at the honest gate gives Marker's saturated realisation there. -/
theorem input5R_of_qffinsat (hfin : FinSatRelGate) : M5Shoenfield.Input5R :=
  G3.input5R_of_relGate_finSat hfin

/-- Row 1 of the matrix: the hull form (Lemma 3.3) and the case ledger, together. -/
theorem relHull_and_relCases_of_qffinsat (hfin : FinSatRelGate) :
    RouteLedger.RelHull ∧ RouteLedger.RelCases :=
  (RouteLedger.relHull_and_cases_iff_input5R).mpr (input5R_of_qffinsat hfin)

theorem relHull_of_qffinsat (hfin : FinSatRelGate) : RouteLedger.RelHull :=
  (relHull_and_relCases_of_qffinsat hfin).1

theorem relCases_of_qffinsat (hfin : FinSatRelGate) : RouteLedger.RelCases :=
  (relHull_and_relCases_of_qffinsat hfin).2

/-- Row 2 (3.7): the separated slot. -/
theorem relSeparated_of_qffinsat (hfin : FinSatRelGate) : RouteLedger.RelSeparated :=
  fun M N _ _ _ _ hR => (relCases_of_qffinsat hfin M N hR).separated

/-- Row 3 (3.4 / 3.6): the unit half of the not-separated slot. -/
theorem relUnit_of_qffinsat (hfin : FinSatRelGate) : RouteLedger.RelUnit :=
  fun M N _ _ _ _ hR =>
    (M5P1.caseNotSeparated_iff_unit_and_nonunit (M := M) (N := N)).mp
      (relCases_of_qffinsat hfin M N hR).notSeparated |>.1

/-- Row 4 (3.5): the non-unit half of the not-separated slot. -/
theorem relNonUnit_of_qffinsat (hfin : FinSatRelGate) : RouteLedger.RelNonUnit :=
  fun M N _ _ _ _ hR =>
    (M5P1.caseNotSeparated_iff_unit_and_nonunit (M := M) (N := N)).mp
      (relCases_of_qffinsat hfin M N hR).notSeparated |>.2

/-- Row 5 (3.8): the new-`rv` slot. -/
theorem relNewRV_of_qffinsat (hfin : FinSatRelGate) : RouteLedger.RelNewRV :=
  fun M N _ _ _ _ hR => (relCases_of_qffinsat hfin M N hR).newRV

/-- All five parts at once. -/
theorem relParts_of_qffinsat (hfin : FinSatRelGate) :
    RouteLedger.RelHull ∧ RouteLedger.RelSeparated ∧ RouteLedger.RelUnit ∧
      RouteLedger.RelNonUnit ∧ RouteLedger.RelNewRV :=
  ⟨relHull_of_qffinsat hfin, relSeparated_of_qffinsat hfin, relUnit_of_qffinsat hfin,
    relNonUnit_of_qffinsat hfin, relNewRV_of_qffinsat hfin⟩

/-- **The canonical single-hypothesis form, recovered through the six-part list**: the endgame of
`QE/RouteLedger.lean` with all five parts discharged by `QFFinSat` at `relGate` is the statement of
`G3.paper_theorem_rel_of_qffinsat`.  So the six-part route and the one-hypothesis route are the same
theorem. -/
theorem paper_theorem_2_3_of_qffinsat_via_parts (hfin : FinSatRelGate)
    (hQ : M5Shoenfield.ShoenfieldTestRel) : HasQE Axioms.ACVF :=
  RouteLedger.paper_theorem_2_3_of_five_rel hQ (relHull_of_qffinsat hfin)
    (relSeparated_of_qffinsat hfin) (relUnit_of_qffinsat hfin) (relNonUnit_of_qffinsat hfin)
    (relNewRV_of_qffinsat hfin)

end FinSat

/-! ## 3. The stress tests the documents quote -/

-- The `QFFinSat`-at-`relGate` hypothesis of §2 is not a theorem at every honest-gate pair.
#check @G3.not_forall_qffinsat_at_relGate
-- The parts themselves fail at an Archimedean configuration, so the frontier is conditional on
-- the target's value group and is not the target in disguise.
#check @G3.not_extendsAt_rel_of_archimedean_config
#check @G3.not_prop39Sat_of_archimedean_config
#check @NewRVGlue.not_cases_of_infinitesimal
#check @NewRVGlue.not_caseNewRV_of_infinitesimal
#check @M8NV.input5R_of_finSat_split
#check @M8NV.refutingConfig_not_input5R
-- The hull form forces only the units' size, so `RelHull` is strictly weaker than the target.
#check @RouteLedger.gatedHull_forces_units_size

/-! ## 4. Axiom audit -/

#print axioms SpecialTransformations.Milestone0.Consolidation.relCases_of_rootHullRealisation
#print axioms SpecialTransformations.Milestone0.Consolidation.paper_theorem_2_3_of_relHull_rootHull
#print axioms SpecialTransformations.Milestone0.Consolidation.input5R_of_qffinsat
#print axioms SpecialTransformations.Milestone0.Consolidation.relHull_and_relCases_of_qffinsat
#print axioms SpecialTransformations.Milestone0.Consolidation.relHull_of_qffinsat
#print axioms SpecialTransformations.Milestone0.Consolidation.relCases_of_qffinsat
#print axioms SpecialTransformations.Milestone0.Consolidation.relSeparated_of_qffinsat
#print axioms SpecialTransformations.Milestone0.Consolidation.relUnit_of_qffinsat
#print axioms SpecialTransformations.Milestone0.Consolidation.relNonUnit_of_qffinsat
#print axioms SpecialTransformations.Milestone0.Consolidation.relNewRV_of_qffinsat
#print axioms SpecialTransformations.Milestone0.Consolidation.relParts_of_qffinsat
#print axioms SpecialTransformations.Milestone0.Consolidation.paper_theorem_2_3_of_qffinsat_via_parts

end SpecialTransformations.Milestone0.Consolidation
