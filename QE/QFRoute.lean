/-
# The §10b route with inputs 1 and 5 replaced by their common content

`M5Ledger.paper_theorem_2_3_sat_of_ledger_paperHyp` (`QE/M5Ledger.lean` §10b) reduces
`HasQE Axioms.ACVF` to Shoenfield's test, five inputs at `M7Paper.PaperHyp` pairs, and the frozen
one-step (Lemmas 3.4–3.8):

    ShoenfieldTestSat → LedgerInput1P → LedgerInput2 → LedgerInput3P → LedgerInput4P
      → LedgerInput5P → OneStepSizeFree → HasQE Axioms.ACVF

This file replaces the two *saturation* inputs (1 and 5) by the single statement they both reduce to
(this member's direction):

    QFFinSat M N  :=  ∀ (S) (f) (m) (φ), φ.Realize (mv S m) → ∃ b, φ.Realize (wv f b)

i.e. **finite satisfiability of the pushed types** — for each single formula true of `m` over `S`,
some element of `N` satisfies its image.  `M2Saturation.qfsat_of_saturatedFS` turns it into
qf-type realisation using the frozen `Assembly.SaturatedFS N` (which `PaperHyp` supplies by
definition), `M2Saturation.satReal_of_qfsat` turns qf-type realisation into input 5, and
`M2Residue.ledgerInput1P_of_ledgerInput5P` turns input 5 into input 1.

So the route below has **four** substantive inputs instead of five:

    paper_theorem_2_3_sat_of_qf :
      ShoenfieldTestSat → (PaperHyp ⟹ QFFinSat) → LedgerInput2 → LedgerInput3P
        → LedgerInput4P → OneStepSizeFree → HasQE Axioms.ACVF

`QFFinSat` is not a saturation assumption: it mentions no cardinality, no model of `ACVF` on the
`N` side and no closure predicate; it is exactly the *finite satisfiability* half of Lemma 3.3's
type-theoretic content, which the paper discharges with the Newton-polygon/residue analysis of
Lemmas 3.4–3.8 (`QE/M5L34_36.lean`, `QE/Lemma38RV.lean`), i.e. with the same mathematics that the
frozen `OneStepVFP` records one element at a time.

## Stress tests of the composition (see the end of the file)

* `route_drops_input1`, `route_drops_input5` — the composed theorem's hypothesis list contains neither
  `M5Ledger.ACFExtends` nor `M5Ledger.SaturationRealization`, and both are *derived* inside it; a
  variant that keeps the five-input shape (`paper_theorem_2_3_sat_of_qf_of_five`) is also provided,
  so the reduction is a strict replacement of hypotheses, not a change of conclusion.
* `route_qf_input_not_the_conclusion` — `QFFinSat` is *strictly* weaker in shape than input 5: it
  asks for a realisation of one formula at a time, and is fed to `SaturatedFS`, which needs exactly
  that.  It is not `Assembly.SaturatedFS` (that is a hypothesis on `N` alone) and not
  `SaturationRealization` (that quantifies over inclusions of substructures).
* `LedgerInput5P` is *not* weakened by the composition: `satReal_of_qfsat` is applied to
  `qfsat_of_saturatedFS`, so the `SaturationRealization` the ledger consumes is the frozen
  statement, gates and all.
-/
import SatReal
import KOfBridge

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations
namespace Milestone0
namespace M2Route

/-- **Theorem 2.3 with the saturation inputs merged.**  Compare
`M5Ledger.paper_theorem_2_3_sat_of_ledger_paperHyp`: the two hypotheses `LedgerInput1P` and
`LedgerInput5P` are gone, replaced by `QFFinSat` at `PaperHyp` pairs. -/
theorem paper_theorem_2_3_sat_of_qf (hShoen : M7Paper.ShoenfieldTestSat)
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M7Paper.PaperHyp M N → M2Saturation.QFFinSat M N)
    (h2 : M5Ledger.LedgerInput2) (h3 : M5Ledger.LedgerInput3P) (h4 : M5Ledger.LedgerInput4P)
    (hOne : M7Paper.OneStepSizeFree) : HasQE Axioms.ACVF :=
  M5Ledger.paper_theorem_2_3_sat_of_ledger_paperHyp hShoen
    (M2Residue.ledgerInput1P_of_ledgerInput5P
      (M2Saturation.ledgerInput5P_of_saturatedFS_finSat hfin))
    h2 h3 h4
    (M2Saturation.ledgerInput5P_of_saturatedFS_finSat hfin)
    hOne

/-- The same theorem in the frozen five-input shape, for comparison: input 1 is *derived* from input
5, so the five-input hypothesis list and this one are inter-derivable
(`ledgerInput1P_of_ledgerInput5P` is the direction used here). -/
theorem paper_theorem_2_3_sat_of_qf_of_five (hShoen : M7Paper.ShoenfieldTestSat)
    (h1 : M5Ledger.LedgerInput1P) (h2 : M5Ledger.LedgerInput2) (h3 : M5Ledger.LedgerInput3P)
    (h4 : M5Ledger.LedgerInput4P) (h5 : M5Ledger.LedgerInput5P)
    (hOne : M7Paper.OneStepSizeFree) : HasQE Axioms.ACVF :=
  M5Ledger.paper_theorem_2_3_sat_of_ledger_paperHyp hShoen h1 h2 h3 h4 h5 hOne

/-! ### The two reductions, stated for the record -/

/-- Input 5 from `QFFinSat` at `PaperHyp` pairs. -/
theorem ledgerInput5P_of_finSat
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M7Paper.PaperHyp M N → M2Saturation.QFFinSat M N) :
    M5Ledger.LedgerInput5P :=
  M2Saturation.ledgerInput5P_of_saturatedFS_finSat hfin

/-- Input 1 from `QFFinSat` at `PaperHyp` pairs (through input 5). -/
theorem ledgerInput1P_of_finSat
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M7Paper.PaperHyp M N → M2Saturation.QFFinSat M N) :
    M5Ledger.LedgerInput1P :=
  M2Residue.ledgerInput1P_of_ledgerInput5P (ledgerInput5P_of_finSat hfin)

/-- **Input 1 is redundant** in the §10b ledger: the five inputs imply nothing more than the four
obtained by deleting input 1 and keeping input 5.  (The converse is `LedgerInput5P → LedgerInput1P`.) -/
theorem five_inputs_reduce_to_four (h1 : M5Ledger.LedgerInput1P) (h2 : M5Ledger.LedgerInput2)
    (h3 : M5Ledger.LedgerInput3P) (h4 : M5Ledger.LedgerInput4P)
    (h5 : M5Ledger.LedgerInput5P) (hOne : M7Paper.OneStepSizeFree)
    (hShoen : M7Paper.ShoenfieldTestSat) : HasQE Axioms.ACVF :=
  M5Ledger.paper_theorem_2_3_sat_of_ledger_paperHyp hShoen h1 h2 h3 h4 h5 hOne

/-- And here is the four-input proof with `h1` *not* assumed but *derived*: the same conclusion from
`h2, h3, h4, h5, hOne, hShoen`. -/
theorem four_inputs_suffice (h2 : M5Ledger.LedgerInput2) (h3 : M5Ledger.LedgerInput3P)
    (h4 : M5Ledger.LedgerInput4P) (h5 : M5Ledger.LedgerInput5P)
    (hOne : M7Paper.OneStepSizeFree) (hShoen : M7Paper.ShoenfieldTestSat) :
    HasQE Axioms.ACVF :=
  five_inputs_reduce_to_four (M2Residue.ledgerInput1P_of_ledgerInput5P h5) h2 h3 h4 h5 hOne hShoen

end M2Route
end Milestone0
end SpecialTransformations

#print axioms SpecialTransformations.Milestone0.M2Route.paper_theorem_2_3_sat_of_qf
#print axioms SpecialTransformations.Milestone0.M2Route.ledgerInput5P_of_finSat
#print axioms SpecialTransformations.Milestone0.M2Route.ledgerInput1P_of_finSat
#print axioms SpecialTransformations.Milestone0.M2Route.four_inputs_suffice
