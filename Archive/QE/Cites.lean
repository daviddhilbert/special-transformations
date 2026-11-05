/-
m8 / d7 (u8 consolidation): the citation check behind `QE/FRONTIER.md` and `QE/HANDOFF.md`.

Every declaration those two documents name is `#check`ed here.  A document that cites a name this
file cannot check is a defect; the file is the guard.

    cd $R && LEAN_PATH=$R/QE:$R/.scratch2/sec3:$LEAN_PATH lean .ultramath/smw2qpqe7/m8/Cites.lean

No `sorry`, no `axiom`, no `native_decide`.
-/
import RouteLedger
import RootHull
import RelUnit
import NonUnitAssembly
import Matrix
import Shrink
import NewRVGlue
import NonVacuity2
import Gate
import FinalAudit
import Bookkeeping
import SlotWire
import HullAudit
import UnitSharpness

set_option autoImplicit false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

/-! ## The frozen target and the theory -/

#check @HasQE
#check @Axioms.ACVF

/-! ## The six-part frontier and its endgame (`QE/RouteLedger.lean`) -/

#check @RouteLedger.RelHull
#check @RouteLedger.RelSeparated
#check @RouteLedger.RelUnit
#check @RouteLedger.RelNonUnit
#check @RouteLedger.RelNewRV
#check @RouteLedger.RelCases
#check @RouteLedger.UnitSlot
#check @RouteLedger.NonUnitSlot
#check @RouteLedger.AlgebraicUnitSlot
#check @RouteLedger.TranscendentalUnitSlot
#check @RouteLedger.RootData
#check @RouteLedger.RVTransVF
#check @RouteLedger.relCases_of_parts
#check @RouteLedger.paper_theorem_2_3_of_five_rel
#check @RouteLedger.paper_theorem_2_3_of_relHull_relCases
#check @RouteLedger.input5R_of_relHull_relCases
#check @RouteLedger.hull_and_cases_iff_satReal
#check @RouteLedger.relHull_and_cases_iff_input5R
#check @RouteLedger.gatedHull_and_cases_iff_ledgerInput5P
#check @RouteLedger.gatedHull_forces_units_size
#check @RouteLedger.paper_theorem_2_3_of_five
#check @RouteLedger.GatedHull
#check @RouteLedger.GatedSeparated
#check @RouteLedger.GatedUnit
#check @RouteLedger.GatedNonUnit
#check @RouteLedger.GatedNewRV
#check @RouteLedger.paper_theorem_2_3_of_hull_and_cases
#check @RouteLedger.prop39Sat_of_hull_and_cases
#check @RouteLedger.lemma36Hyp_false
#check @RouteLedger.not_exists_lemma36Hyp
#check @RouteLedger.not_rvTrans_of_units
#check @RouteLedger.GatedCases

/-! ## The gates and the quotation (`QE/ShoenfieldQuote.lean`, `QE/PaperRoute.lean`) -/

#check @M5Shoenfield.relGate
#check @M5Shoenfield.ShoenfieldTestRel
#check @M5Shoenfield.ShoenfieldTestSaturated
#check @M5Shoenfield.Input5R
#check @M5Shoenfield.SatBridge
#check @M5Shoenfield.ExtendsAt
#check @M5Shoenfield.paperGate_le_relGate
#check @M5Shoenfield.shoenfieldTestSaturated_of_rel
#check @M7Paper.PaperHyp
#check @M7Paper.SizeHyp
#check @M7Paper.Prop39Sat
#check @M7Paper.ShoenfieldTestSat

/-! ## The three routes -/

#check @G3.paper_theorem_rel_two
#check @G3.paper_theorem_rel_of_qffinsat
#check @G3.input5R_of_relGate_finSat
#check @G3.extendsAt_rel_of_finSat
#check @G3.qfsat_of_satRel_of_qffinsat
#check @G3.extendsAt_rel_iff_input5R
#check @G3.satReal_iff_hullExtension_and_oneStep
#check @G3.satReal_iff_hullExtension_and_cases
#check @G3.ledgerInput5P_iff_gated_hullExtension_and_oneStep
#check @G3.input5R_iff_gated_hullExtension_and_oneStep
#check @G3.hullExtension_of_satReal
#check @G3.not_prop39Sat_of_archimedean_config
#check @G3.not_extendsAt_rel_of_archimedean_config
#check @G3.not_forall_qffinsat_at_relGate
#check @G3.not_finSat_of_satRel_of_archimedean
#check @G3.not_ledgerInput5P_of_config
#check @FinalAudit.paper_theorem_FINAL2
#check @FinalAudit.paper_theorem_FINAL3
#check @FinalAudit.FINAL2_iff_FINAL3
#check @FinalAudit.ledgerInput5P_iff_prop39Sat
#check @FinalAudit.not_saturationRealization_of_lt
#check @FinalAudit.reduced_final_is_the_criterion
#check @FinalAudit.paper_theorem_FINAL_of_input5

/-! ## The matrix (`QE/Matrix.lean`, u6) and the shrink (`QE/Shrink.lean`, d8) -/

#check @M6Matrix.relHull_of_finSat
#check @M6Matrix.relSeparated_of_finSat
#check @M6Matrix.relUnit_of_finSat
#check @M6Matrix.relNonUnit_of_finSat
#check @M6Matrix.relNewRV_of_finSat
#check @M6Matrix.fiveParts_of_finSat
#check @M6Matrix.fiveParts_iff_input5R
#check @M6Matrix.fiveParts_pair_iff_satReal
#check @M6Matrix.relCases_iff_parts
#check @M6Matrix.unit_nonunit_iff_notSeparated
#check @M6Matrix.separated_and_notSeparated_iff_oneStepRVOld
#check @M6Matrix.relHull_iff_prepStepP
#check @M6Matrix.relUnit_of_rootData_slot34_transcendental
#check @M6Matrix.relNonUnit_of_branch
#check @M6Matrix.relNewRV_iff_oneStepRVNew
#check @M6Matrix.not_finSatAtRelGate_of_config
#check @M6Matrix.not_finSat_of_config
#check @M6Matrix.paper_theorem_rel_of_finSat_split
#check @M6Matrix.no_refutingConfig_of_arch_half
#check @M6Matrix.finSatAtRelGate_of_split
#check @M6Matrix.two_routes_agree
#check @M6Matrix.paper_theorem_rel_of_finSat_via_parts
#check @M5Shrink.input5R_iff_relHull_and_fourParts
#check @M5Shrink.hullExtension_iff_nonStanding
#check @M5Shrink.relHull_iff_baseRootResidual
#check @M5Shrink.rootStepResidual_of_hullRootStep
#check @M5Shrink.relGate_units_card
#check @M5Shrink.relGate_no_card_obstruction
#check @M5Shrink.paper_theorem_2_3_of_six_rel

/-! ## The four case slots' own notes -/

-- 3.4 — `QE/Case34Slot.lean`
#check @M5P1.MonicO
#check @M5P1.IsRootOf
#check @M5P1.LiftAllRoot
#check @M5P1.Slot34
#check @M5P1.slot_of_liftAllRoot
#check @M5P1.not_separated_of_units
#check @M5P1.separated_of_pow_notin
#check @M5P1.separated_imp_pow_not_cls_one
#check @M5P1.caseNotSeparated_iff_unit_and_nonunit
#check @M5P1.unit_class_in_S
-- 3.4/3.6 attribution — `QE/Lemma36Audit.lean`
#check @Lemma36AuditACVF.separated_not_units
#check @Lemma36AuditACVF.not_separated_of_vfgen
#check @Lemma36AuditACVF.caseSeparated_empty_of_vfgen
#check @Lemma36AuditACVF.caseNotSeparated_hyp_satisfiable
#check @Lemma36AuditACVF.not_separated_of_vpow_mem
-- 3.6 — `QE/Lemma36Statement.lean` (merged form) and `QE/RelUnit.lean` (corrected form)
#check @M8.Lemma36Hyp
#check @M8.ClaimStar
#check @M8.lemma36_claim_star
#check @RelUnit.merged_lemma36_hyp_no_instances
#check @RelUnit.transcendentalUnitSlot_iff_paperClaimStar
#check @RelUnit.residualClasses_closure_of_residueTranscendental
#check @RelUnit.transcendentalClaimStar_of_residueTranscendental
#check @RelUnit.slot34_holds
#check @RelUnit.rootData_iff_rootData'
#check @RelUnit.unitSlot_iff_no_separated
#check @RelUnit.slotConcl_iff_closureEmbedding
#check @RelUnit.unitSlot_of_34_and_36
#check @RelUnit.relUnit_of_gated_parts
#check @RelUnit.relUnit_of_rootHullRealisation
#check @RelUnit.paper_theorem_2_3_of_parts
#check @RelUnit.paper_theorem_2_3_of_parts_rootHull
#check @M7.gamma_step
#check @M7.val_sum_eq_one
#check @M7.unit_hypothesis_essential
-- 3.5 — `QE/Case35Slot.lean`, `QE/D7Hull.lean`, `QE/NonUnitAssembly.lean`
#check @Case35.NotSeparatedBranch
#check @Case35.caseNotSeparated_of_branch
#check @Case35.not_residualClasses_of_perturbation
#check @Case35.not_rootStepHyp_of_standing
#check @Case35.RVOldClass
#check @D7.HullBaseStep
#check @D7.RootStepResidual
#check @D7.extendsHere_iff_steps_and_oneStep
#check @D7.not_hullBaseStep_of_cardinality
#check @D7.hullBaseStep_KEqTop_trivial
#check @D7.rootStepResidual_standing_trivial
#check @NonUnitAssembly.nonUnitSlot_of_extAlongStanding
#check @NonUnitAssembly.nonUnitHull_holds
#check @NonUnitAssembly.SlotTotalExt
#check @NonUnitAssembly.SlotAtomic
#check @NonUnitAssembly.relNonUnit_of_qffinsat
#check @NonUnitAssembly.paper_theorem_2_3_of_rel_parts_no_nonunit
#check @NonUnitAssembly.exists_nonunit
#check @NonUnitAssembly.ClampedNonUnitHull
-- 3.7 — `QE/Bookkeeping.lean`, `QE/SlotWire.lean`, `QE/HullAudit.lean`
#check @Bookkeeping.bookkeeping_half
#check @Bookkeeping.caseSeparated_of_structuralResidual
#check @Bookkeeping.gammaEqQ_of_residualClasses
#check @Bookkeeping.rvGenCover_iff_residualClasses
#check @HullAudit.divisibilityStep_pins_hull
#check @HullAudit.hull_clamp_not_pinning
#check @HullAudit.gammaHullInitial_imp_mem_divHull
#check @HullAudit.divisibleHullExists_at_gammaMk_surjective
-- 3.8 — `QE/NewRVClaim.lean`, `QE/NewRVGlue.lean`
#check @M5LNewRV.ResidualClassesNew
#check @M5LNewRV.ResidualClassesNew_of_VFGen
#check @M5LNewRV.claimStarNewRV_holds
#check @NewRVGlue.oneStepRVNew_of_total_extension
#check @NewRVGlue.not_caseNewRV_of_infinitesimal
#check @NewRVGlue.not_cases_of_infinitesimal
#check @NewRVGlue.hull_demand_of_standing
#check @NewRVGlue.hull_demand_of_oneStepRVNew
#check @NewRVGlue.oneStepRVNew_iff_gammaDivisible
#check @NewRVGlue.not_stepObligation_of_newRV
#check @NewRVGlue.cases_at_relGate_of_input5R

/-! ## The hull form (Lemma 3.3) -/

#check @M8Hull.standingHull
#check @M8Hull.standing_standingHull
#check @M8Hull.standingHull_le
#check @M8Hull.exists_standing_superset
#check @M8Hull.standingHull_eq_self_iff
#check @M8Hull.units_of_pow_units
#check @M5Ledger.SaturationRealization
#check @M5Ledger.LedgerInput5P
#check @M5Ledger.PrepStepPaper
#check @M5Ledger.GammaHullInitial
#check @M5Ledger.prepStepPaper_of_ledger
#check @M5Ledger.saturationRealization_forces_size
#check @M2Saturation.QFSat
#check @M2Saturation.QFFinSat
#check @M2Saturation.satReal_iff_qfsat
#check @M2Saturation.ledgerInput5P_of_saturatedFS_finSat

/-! ## The root-hull residual and its reductions -/

#check @Case35Hull.RootHullRealisation
#check @Case35Hull.RootHullEmbedding
#check @Case35Hull.standing_rootHull
#check @Case35Hull.rootClosedOn_rootHull
#check @Case35Hull.cases_of_rootHullEmbedding
#check @Case35Hull.oneStepVFP_of_rootHullEmbedding
#check @Case35Hull.oneStepVFP_iff_rootClosed
#check @Case35Hull.standing_iff_rootClosedOn
#check @Case35Hull.oneStepPaper_of_rootHullRealisation
#check @Case35Hull.paper_theorem_2_3_of_rootHullRealisation
#check @Case35Hull.rootHullEmbedding_self
#check @Case35Hull.rootHullEmbedding_top
#check @Case35Hull.rootHullEmbedding_of_global
#check @Case35Hull.perturbation_notSeparated_without_classControl
#check @Case35Hull.lemma35_hyp_is_newRV

/-! ## The Archimedean configuration (`QE/NonVacuity2.lean`, `QE/Gate.lean`) -/

#check @M8NV.FinSatAtArchimedean
#check @M8NV.RefutingConfig
#check @M8NV.input5R_of_finSat_split
#check @M8NV.refutingConfig_not_input5R
#check @M8NV.refutingConfig_not_finsat
#check @M8NV.refutingConfig_not_archimedean_source
#check @M8NV.no_refutingConfig_of_finSat
#check @M8NV.no_archimedean_refutation_of_finSat
#check @M8NV.huge_ordinal_atoms_realizable
#check @M5Gate.NoSatModel
#check @M5Gate.shoenfieldTestSat_iff_hasQE_of_noSatModel
#check @M5Gate.not_forall_not_saturatedFS
#check @M5Gate.satBridge_dichotomy
-- the pushed types and the saturated-realisation interface
#check @M1Fix.SatRel
#check @M1Fix.saturatedFS_iff
#check @Assembly.Standing
#check @Assembly.KEqTop
#check @Assembly.GammaDivisible
#check @Assembly.IsVFGen
#check @Assembly.OneStepVFP
#check @Assembly.PrepStepP
#check @M4Cases.Cases
#check @M4Cases.CaseSeparated
#check @M4Cases.CaseNotSeparated
#check @M4Cases.CaseNewRV
#check @M4Cases.OneStepPaper
#check @M4Cases.cases_of_global_extension
#check @M4Cases.oneStepVFP_of_cases
#check @M5.OneStepRVNew
#check @M5L.Separated
#check @M5L.VFInvClosedOn
#check @M5L.ResidualClasses

/-! ## The named residuals, as `FRONTIER.md` / `HANDOFF.md` name them -/

#check @RelUnit.TranscendentalClaimStar
#check @RelUnit.TranscendentalRealisation
#check @RelUnit.PaperClaimStar
#check @M8.AlgebraicOverVF
#check @M5P1.vfInvClosedOn_top
#check @M5P1.divHullCover_refuted
#check @FinalRoute.FinalHyp
#check @M4Cases.paper_theorem_2_3_sat_of_cases
#check @M5Shrink.relHull_iff_nonStanding
#check @M5Ledger.KEqTop_mono
#check @M5L.QuotExpansions
#check @M5L.OneStepSeparatedP
#check @Case35Hull.rootHull
#check @M6Matrix.FinSatAtRelGate
#check @M6Matrix.relCases_of_finSat
#check @M6Matrix.input5R_of_finSat
#check @M6Matrix.fiveParts_of_input5R
#check @M6Matrix.cases_of_satRel_qffinsat
#check @M6Matrix.gatedUnit_of_finSat
#check @M6Matrix.paper_theorem_sat_of_finSat
#check @M6Matrix.separated_and_notSeparated_iff_oneStepRVOld
