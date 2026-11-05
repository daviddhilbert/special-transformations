# u1 — `RelUnit` (the unit half of the six-part frontier): status

Member `m1`, swarm `smw2qpqe7`, direction `d1`.  Deliverable: `RelUnit.lean` (801 lines, green).

## Verdict

`RelUnit` (`QE/RouteLedger.lean`: `∀ M N, relGate M N → UnitSlot M N`) is **assembled** and reduced
to exactly two independent pieces of mathematics plus one bookkeeping package:

| piece | what it is | status |
|---|---|---|
| 3.4 | `RouteLedger.RootData` (monic `F` over `O(Ŝ)` with irreducible projection; henselianity step; class control) | residual — no merged asset |
| 3.6 class half | `TranscendentalClaimStar`, or (§3b) the paper's cone: residue transcendence + `QuotExpansions` + `IsVFGen (Closure S m)` + `VFInvClosedOn S` | **proved from the paper's hypotheses** through `QE/UnitCase.lean` (`ResidualClasses_of_VFGen_unit_min`), no EP 3.4.3, no `RVTrans`; the abstract form is a residual |
| realisation | `TranscendentalRealisation`: `f ↾ S` extends to `⟨Ŝ,m⟩ = closure (S ∪ {m})` — the paper's `f^*`, the half of Claim (⋆) the frozen `M8.ClaimStar` omits | residual — model-theoretic (saturation), the only place `N` is used |

Nothing else: `¬ M5L.Separated` is derivable at a unit (`unitSlot_iff_no_separated`), the `T` /
`m ∈ T` / `Standing T` conjuncts collapse into the closure embedding (`slotConcl_iff_closureEmbedding`,
no `ACVF`, no gate), `M5P1.Slot34` is a theorem (`slot34_holds`), `RootData`'s `iRv m ∈ S` row is
redundant (`rootData_iff_rootData'`), and `relGate` is never consumed.

## Main machine-checked statements

* `slotConcl_iff_closureEmbedding`, `closureEmbedding_of_slotConcl` — §0, structural, ACVF-free.
* `unitSlot_iff_no_separated`, `unitSlot_of_closure_parts`, `closureEmbedding_of_unitSlot`,
  `unitClosureStanding_of_residualClasses` — §1 (the equivalence, no weakening).
* `rootData_iff`, `rootData_iff_rootData'`, `slot34_holds`, `algebraicUnitSlot_of_rootData`,
  `closureEmbedding_of_liftAllRoot`, `algebraicClosureEmbedding_of_rootData` — §2 (3.4 = `RootData`).
* `claimStar_iff_residualClasses`, `transcendentalUnitSlot_iff_of_claimStar`,
  `transcendentalUnitSlot_iff_paperClaimStar`, `merged_lemma36_hyp_no_instances` — §3 (3.6 exactness).
* `residualClasses_closure_of_residueTranscendental`, `transcendentalClaimStar_of_residueTranscendental`
  — §3b (class half from the paper's hypotheses, no EP 3.4.3).
* `unitSlot_of_rootHullEmbedding`, `closureEmbedding_of_rootHullEmbedding` — §4 (repair-free form).
* `unitSlot_of_34_and_36`, `unitSlot_of_34_and_36_paper`, `relUnit_of_parts`,
  `relUnit_of_gated_parts`, `relUnit_of_rootHull`, `relUnit_of_rootHullRealisation`,
  `relUnit_of_ungated` — §5.
* `paper_theorem_2_3_of_parts`, `paper_theorem_2_3_of_parts_rootHull` — §5c: the five-part endgame
  with `RelUnit` replaced by its residuals.
* `unitHyp_at_keqTop`, `slotConcl_of_mem`, `closureEmbedding_of_mem`, `closureEmbedding_of_global`,
  `closure_top`, `unitClosureStanding_top`, `unitSlot_of_extendsHere`, `relUnit_of_qffinsat` — §6.

## Real outputs

    $ cd $R && LEAN_PATH=$R/.scratch2/sec3:$LEAN_PATH lean .ultramath/smw2qpqe7/m1/RelUnit.lean
    EXIT=0
    errors: 0
    warnings: 0
    sorryAx: 0
    audited: 42 lines of "#print axioms"
    every one of the 42: [propext, Classical.choice, Quot.sound]  (or a subset)

`grep -n "sorry\|admit\|native_decide" RelUnit.lean` returns only the docstring line that says there
are none.

## What a successor should do with this

1. To *use* the unit half: supply `RootData` + `TranscendentalRealisation` (+ optionally 3.6's class
   half) to `relUnit_of_gated_parts`, or the whole thing to `paper_theorem_2_3_of_five_rel`.
2. To *shrink* the residual further, the target is the realisation `f^* : ⟨Ŝ,m⟩ → N`.  It is
   model-theoretic: at `relGate`, `QFFinSat` at the pair gives it through
   `G3.extendsAt_rel_of_finSat` (`relUnit_of_qffinsat` records this consistency check).  It is *not*
   class bookkeeping, and no residue/`Γ` argument can produce it.
3. Do not try to repair `M8.Lemma36Hyp` by weakening `RVTrans` to `RVTransVF` and calling it done:
   `RVTransVF` is closer, but §3 shows that even with the class half in hand the slot needs the
   realisation, so a repaired 3.6 alone does not close the unit half.
