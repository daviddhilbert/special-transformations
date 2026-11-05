# u6 — THE MASTER REDUCTION MATRIX

Swarm `smw2qpqe7`, member m6, direction u6. Files: `Matrix.lean` (machine-checked, green) and this
note. Everything below is stated at
`relGate M N = M1Fix.SatRel M N ∧ M7Paper.SizeHyp M N`, with the five endgame parts of
`QE/RouteLedger.lean` §6 (`RelHull`, `RelSeparated`, `RelUnit`, `RelNonUnit`, `RelNewRV`).

## The verdict in four lines

1. **All five parts are implied by `QFFinSat` at `relGate`** — every cell of the first matrix row is
   proved (`relHull_of_finSat`, `relSeparated_of_finSat`, `relUnit_of_finSat`,
   `relNonUnit_of_finSat`, `relNewRV_of_finSat`), and jointly as `fiveParts_of_finSat`.
2. **The five-part list is *equivalent* to Marker's `Input5R`** (`fiveParts_iff_input5R`; at a single
   pair, `fiveParts_pair_iff_satReal`: `HullExtension ∧ CaseSeparated ∧ UnitSlot ∧ NonUnitSlot ∧
   CaseNewRV ⟺ SaturationRealization`), so the parts carry no content beyond the saturation input:
   slicing §3 into the paper's four cases is a *rewriting* of input 5, not a way around it.
3. **`QFFinSat@relGate` is refutable** at the tree's own configuration family
   (`not_finSatAtRelGate_of_config`, `not_finSat_of_config`): at a `relGate` pair with an Archimedean
   target carrying an infinitesimal over an embeddable substructure, the pushed type is *not*
   finitely satisfiable. So `ShoenfieldTestRel → (∀ relGate, QFFinSat) → HasQE` is a **true theorem
   whose second hypothesis nobody can discharge** — it is not the canonical final.
4. **The canonical single-hypothesis final is the split form**
   `paper_theorem_rel_of_finSat_split : ShoenfieldTestRel → FinSatAtArchimedean →
   FinSatOffArchimedean → HasQE`. Its Archimedean half is *not* touched by the refutations
   (`no_refutingConfig_of_arch_half`: under it there is no `RefutingConfig` at all), and it *implies*
   the `relGate`-quantified form (`finSatAtRelGate_of_split`), so it is the stronger of the two.

## The matrix

Rows are hypotheses at a pair (or at the gate); columns are the five parts.
✅ = machine-checked in `Matrix.lean` (theorem named), ✗ = machine-checked *refutation*,
○ = open: nothing in the tree proves or refutes it (stated, not claimed).

| hypothesis | `RelHull` | `RelSeparated` | `RelUnit` | `RelNonUnit` | `RelNewRV` |
|---|---|---|---|---|---|
| `QFFinSat` @ `relGate` | ✅ `relHull_of_finSat` | ✅ `relSeparated_of_finSat` | ✅ `relUnit_of_finSat` | ✅ `relNonUnit_of_finSat` | ✅ `relNewRV_of_finSat` |
| `SatRel` + `QFFinSat` at one pair (no size) | ✅ `hullExtension_of_satRel_qffinsat` | ✅ `separated_of_satRel_qffinsat` | ✅ `unitSlot_of_satRel_qffinsat` | ✅ `nonUnitSlot_of_satRel_qffinsat` | ✅ `newRV_of_satRel_qffinsat` |
| `Input5R` / `SaturationRealization` | ✅ `fiveParts_of_input5R` | ✅ | ✅ | ✅ | ✅ |
| total extension `ExtendsHere` at the pair | ✅ `hullExtension_of_extendsHere` | ✅ `cases_of_extendsHere` | ✅ | ✅ | ✅ |
| tree's local interfaces | ✅ `relHull_iff_prepStepP` (＝ frozen `PrepStepP`) | ✅ `relSeparated_of_oneStepSeparatedP` (needs `VFInvClosedOn`) | ✅ `relUnit_of_rootData_slot34_transcendental`, `relUnit_of_branch` | ✅ `relNonUnit_of_branch` | ✅ `relNewRV_iff_oneStepRVNew` (definitional) |
| `SatRel` alone at a pair (no `QFFinSat`) | ○ | ○ | ○ | ○ | ○ |
| `QFFinSat` @ `relGate`, as a *theorem* | ✗ `not_finSatAtRelGate_of_config` (and per pair `not_finSat_of_config`) | | | | |
| five parts ⇒ `QFFinSat` | ○ — no proof in the tree, and no separation is available at a configuration pair (both sides fail there) | | | | |

Three equivalences make the table exact rather than merely one-directional:

* `relCases_iff_parts` — the four case parts are *exactly* `RelCases` (the converse of
  `RouteLedger.relCases_of_parts`), so the four-way split loses nothing;
* `unit_nonunit_iff_notSeparated` and `separated_and_notSeparated_iff_oneStepRVOld` — the u1/u2 split
  is lossless and the two `rv`-old branches are exactly `M5.OneStepRVOld`;
* `fiveParts_pair_iff_satReal` — at a *single pair*, the five parts are exactly the pair's
  `SaturationRealization` (= `QFSat`).  So the pair-level matrix's hypothesis cannot be weakened below
  input 5, and the parts' *conjunction* is input 5's instance, word for word.

Chain, all machine-checked:

    FinSatAtArchimedean ∧ FinSatOffArchimedean
      ⟹ FinSatAtRelGate                       finSatAtRelGate_of_split
      ⟹ RelHull ∧ RelSeparated ∧ RelUnit ∧ RelNonUnit ∧ RelNewRV   fiveParts_of_finSat
      ⟺ Input5R                                fiveParts_iff_input5R
      ⟹ HasQE Axioms.ACVF                      RouteLedger.paper_theorem_2_3_of_five_rel

and the two ends are also joined directly (`paper_theorem_rel_of_finSat_split`,
`paper_theorem_rel_of_finSat_via_parts`, `paper_theorem_sat_of_finSat` at the *frozen* gate), with
`two_routes_agree` recording that the case-lemma route and the direct route are the same theorem.

## Per part: what discharges it, what is left

| part | = which paper lemma | discharged by | residual if `QFFinSat` is not granted |
|---|---|---|---|
| `RelHull` | Lemma 3.3 | `G3.PrepStepP` pointwise (`relHull_iff_prepStepP`) — and `QFFinSat@relGate` via input 5 | the hull construction (`M5Ledger.prepStepPaper_of_ledger`: inputs 1–5) |
| `RelSeparated` | Lemma 3.7 | `M5L.OneStepSeparatedP` + `M5L.VFInvClosedOn` (`relSeparated_of_oneStepSeparatedP`); `VFInvClosedOn` is *not* derivable from `Standing` (`QE/OneStepCases.lean` §2) | that defect, or the dominant-term computation of `QE/Lemma37.lean` |
| `RelUnit` | Lemmas 3.4 + 3.6 | `RootData` + `M5P1.Slot34` + `TranscendentalUnitSlot` (`relUnit_of_rootData_slot34_transcendental`) | 3.4's r1/r2/r3 (`RootData`) and 3.6 — note `M8.Lemma36Hyp` is *inconsistent* (`RouteLedger.§1`), so merged 3.6 gives nothing |
| `RelNonUnit` | Lemma 3.5 | `Case35.NotSeparatedBranch` (`relNonUnit_of_branch`), exponent-one branch | `M5.ResidualClasses S T` + the realisation |
| `RelNewRV` | Lemma 3.8 | definitionally `M5.OneStepRVNew` (`relNewRV_iff_oneStepRVNew`); class half is a theorem (`M5LNewRV.ResidualClassesNew_of_VFGen`) | `Standing T` (the divisible hull) and the monomorphism |

## Why the single-hypothesis form is not canonical (the machine-checked obstruction)

`not_finSat_of_config` (per pair) and `not_finSatAtRelGate_of_config` (the `∀`-form): given
`SatRel M N`, `ArchimedeanRV N`, a substructure embedding `f : S ↪ N` and `s ∈ S`, `m ∈ M` with
`1 < v(s)`, `1 < v(m)`, `v(s)^n ≤ v(m)` for all `n`, the pushed type of `m` over `(S, f)` is not
finitely satisfiable. So `∀ relGate, QFFinSat` is false at any such pair that also carries
`SizeHyp`. The author ruling keeps `QFFinSat` out of the quotation list, so this hypothesis has to be
*proved*, and the tree's own refutations fire exactly there: no proof of it can exist at such a pair.
The split form moves exactly the failing half into a hypothesis whose
negation is what the tree's refutations produce (`not_finSat_of_refutingConfig`), and that half is
invisible to those refutations (`no_refutingConfig_of_arch_half`).

**Consequence for the frontier.** The five named parts cannot be discharged by first proving `QFFinSat`
at `relGate`; they must be proved directly (u1–u5), or `Input5R` must be granted, or the work must be
done on the non-Archimedean branch. Conversely, u1–u5 are *not* wasted work: their conjunction is
pointwise equivalent to `Input5R` (`fiveParts_iff_input5R`), i.e. to the paper's §3 in full.

## Verification (real output)

    $ cd $R && LEAN_PATH=$R/.scratch2/sec3:$LEAN_PATH lean .ultramath/smw2qpqe7/m6/Matrix.lean
    EXIT=0
    errors=0
    axiom lines printed: 39
    all 39 lines read "depends on axioms: [propext, Classical.choice, Quot.sound]"
    grep -c 'sorry|admit|native_decide' Matrix.lean  ->  0

(No `sorry`, no `admit`, no `native_decide`, no new axiom, no `QED`/`axiom` declaration; only the
three standard axioms, checked with `#print axioms` for all 39 theorems at the end of the file.)
