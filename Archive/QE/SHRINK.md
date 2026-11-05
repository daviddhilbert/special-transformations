# m5 / d8 — can the honest-gate endgame's hypothesis list be shortened?

Direction: **QUOTE-DISCHARGE / HYPOTHESIS-SHRINKING** — not a slot proof, not the implication
matrix (d4), not documentation (d7). The question: `QE/RouteLedger.lean`'s
`paper_theorem_2_3_of_five_rel` consumes six hypotheses

    ShoenfieldTestRel, RelHull, RelSeparated, RelUnit, RelNonUnit, RelNewRV.

Is any of them **redundant**, i.e. can the list be made strictly shorter?

Deliverable: [`Shrink.lean`](Shrink.lean) — 350 lines, machine-checked. Verification pasted in §4.

---

## 1. The answer, in three parts

### 1a. No formal shortening is available: the list is already at its floor

The tree already contains the shortest form that exists in its own vocabulary:

* `QE/Prop39Decomp.lean:294` — `paper_theorem_rel_two (hQ : ShoenfieldTestRel)
  (h5 : Input5R) : HasQE Axioms.ACVF`. **Two** hypotheses.
* `QE/RouteLedger.lean` — `relHull_and_cases_iff_input5R : (RelHull ∧ RelCases) ↔ Input5R`.

Composing them, and machine-checking the composition in `Shrink.lean` §4b:

    theorem input5R_iff_relHull_and_fourParts :
      M5Shoenfield.Input5R ↔
        RelHull ∧ RelSeparated ∧ RelUnit ∧ RelNonUnit ∧ RelNewRV

(via `relCases_iff_parts : RelCases ↔ RelSeparated ∧ RelUnit ∧ RelNonUnit ∧ RelNewRV`, whose
forward direction uses nothing but the projections and whose backward direction is the tree's
`relCases_of_parts`; the two halves being `caseNotSeparated_iff_halves`).  So the six-part list
asserts **exactly the same thing** as the two-hypothesis list.
The four-way split of `RelCases` into `RelSeparated`, `RelUnit`, `RelNonUnit`, `RelNewRV` is
`relCases_of_parts` in one direction and projection in the other, so it adds *attack surface*, not
hypothesis strength. Consequently: **removing a part from the frontier means proving that part.**
There is no restructuring that removes one. This is the honest answer to the direction's question,
and it is why I did not produce a "five-part endgame" of the cosmetic kind (replace
`RelUnit ∧ RelNonUnit` by `CaseNotSeparated`, or the four parts by `RelCases`): each such rewrite is
definitionally the same obligation, and the tree already records the collapsed form.

The only hypothesis that could be *discharged* rather than restructured is the quotation
`ShoenfieldTestRel = QEOfGate relGate = (ExtendsAt relGate → HasQE ACVF)`. Discharging it is
Shoenfield's test. Mathlib 4.33.1 has **no** general QE criterion to build on
(`grep -rn "HasQE" /opt/mathlib/Mathlib/` returns nothing; the only QE-adjacent file is
`ModelTheory/Arithmetic/Presburger/Basic.lean`), so this is a from-scratch back-and-forth argument
over `L_RV` — out of scope for this run, and it is quoted by author ruling in any case.

### 1b. The hull slot is the one part that is *content*-disjoint from the other four

Machine-checked in `Shrink.lean`, §2–§3. Every case slot's hypothesis list begins with
`Assembly.Standing S`:

| part | domain |
|---|---|
| `RelSeparated` (`M4Cases.CaseSeparated`) | `Assembly.Standing S` |
| `RelUnit` (`RouteLedger.UnitSlot`) | `Assembly.Standing S` |
| `RelNonUnit` (`RouteLedger.NonUnitSlot`) | `Assembly.Standing S` |
| `RelNewRV` (`M5.OneStepRVNew`) | `Assembly.Standing S` |
| `RelHull` (`G3.HullExtension`) | **all** `S` |

and on the `Standing` region the hull slot is *free*:

    theorem hullExtension_iff_nonStanding :
      G3.HullExtension M N ↔ ∀ S, ¬ Assembly.Standing S → D7.HullExtensionAt S

(`D7.hullExtensionAt_of_standing`, `D7.hullExtension_iff_forall_hullExtensionAt`, `by_cases` on
`Standing`). Lifted to the gate: `relHull_iff_nonStanding :
RouteLedger.RelHull ↔ RelHullNonStanding`. So **no case slot can ever discharge the hull slot**, and
the hull slot's obligation is confined to the complement of the four case slots' domain. This is the
sharpest "cannot be shortened" statement that is provable without a model: it does not say
`RelHull` is independent of the other five (that needs a countermodel), it says its content lives in
a region the other four never mention.

### 1c. Inside that region, the hull slot is exactly two further-confined steps

`D7.hullExtension_iff_base_root` (`G3.HullExtension ⟺ HullBaseStep ∧ HullRootStep`) lifted to the
gate, plus the new bridge `rootStepResidual_of_hullRootStep` (the missing converse of
`D7.hullRootStep_of_rootStepResidual`), gives

    relHull_iff_baseRootResidual : RouteLedger.RelHull ↔ RelHullBaseRootResidual

i.e. at every `relGate` pair: **the unit adjoinment** `D7.HullBaseStep` **and** the named root
residual `D7.RootStepResidual`. D7's own confinement lemmas then say where the content is:

* `D7.hullBaseStep_iff_nonKEqTop` — base step has content only at `¬ Assembly.KEqTop S`;
* `D7.rootStepResidual_iff` — root residual only at `KEqTop T ∧ ¬ Standing T`.

Both classes are outside the four case slots' region (`Standing ⟹ KEqTop`), which is the
gate-level proof that the frontier's five-way split of `L3x` can never absorb `L33`.

### 1d. The gate's size conjunct is exactly the hull slot's cardinality need

`D7.hullExtension_forces_units_size_restated` says `HullExtension` forces
`#Kˣ(M) ≤ #N` at every pair; `M7Paper.SizeHyp M N` is `#M ≤ #N`; units inject into the carrier. So

    relGate_units_card : relGate M N → #Kˣ(M) ≤ #N
    relGate_no_card_obstruction : relGate M N → ¬ (#N < #Kˣ(M))

Hence `relGate`'s second conjunct is not decoration: it is precisely the cardinality obstruction
that `L33` would otherwise hit (`D7.not_hullExtension_of_cardinality`). That also answers the
sub-question "is `SizeHyp` idle in the gate?" — for the hull slot, no: it is load-bearing.

---

## 2. What `Shrink.lean` contains

| # | name | statement |
|---|---|---|
| 1 | `units_card_le` | `#Kˣ(M) ≤ #M` |
| 2 | `relGate_units_card` | `relGate M N → #Kˣ(M) ≤ #N` |
| 3 | `relGate_no_card_obstruction` | `relGate M N → ¬ (#N < #Kˣ(M))` |
| 4 | `hullExtension_iff_nonStanding` | `G3.HullExtension M N ↔ ∀ S, ¬Standing S → HullExtensionAt S` |
| 5 | `hullExtension_iff_base_root` | `L33 ⟺ base ∧ root` (restated from D7) |
| 6 | `rootStepResidual_of_hullRootStep` | `HullRootStep → RootStepResidual` (**new**; D7 had only the converse) |
| 7 | `not_standing_of_missing_unit` | a unit outside `S` ⟹ `¬Standing S` |
| 8 | `not_standing_of_not_KEqTop` | `¬KEqTop S ⟹ ¬Standing S` |
| 9 | `hullExtensionAt_at_caseSlot_domain` | `Standing S ⟹ HullExtensionAt S` |
| 10 | `RelHullNonStanding`, `RelHullBaseRoot`, `RelHullBaseRootResidual` | the three reduced gate forms |
| 11 | `relHull_iff_nonStanding`, `relHull_iff_baseRoot`, `relHull_iff_baseRootResidual` | the three equivalences |
| 12 | `paper_theorem_2_3_of_five_rel_nonStanding`, `…_baseRoot`, `…_baseRootResidual` | the endgame re-run on each reduced form |
| 13 | `RelAlgebraicUnit`, `RelTranscendentalUnit`, `relUnit_of_algebraic_transcendental`, `paper_theorem_2_3_of_six_rel` | gate-level split of `RelUnit` into 3.4 and 3.6 (only the pair-level version existed, `RouteLedger.unitSlot_of_algebraic_transcendental`) |
| 14 | `unitSlot_of_caseNotSeparated`, `nonUnitSlot_of_caseNotSeparated`, `caseNotSeparated_iff_halves` | the unit/non-unit split is an **equivalence**, not a strengthening |
| 15 | `cases_iff_parts` | `M4Cases.Cases ⟺ CaseSeparated ∧ UnitSlot ∧ NonUnitSlot ∧ CaseNewRV` at a pair |
| 16 | `relCases_iff_parts` | the same at the gate |
| 17 | `input5R_iff_relHull_and_fourParts` | **the six-part list ⟺ `Input5R`** — §1a, machine-checked |

Item 13 is for u1/m1: the unit half can now be handed in as two separate frontier parts at the gate
(`RelAlgebraicUnit` = Lemma 3.4, `RelTranscendentalUnit` = Lemma 3.6), with the endgame
`paper_theorem_2_3_of_six_rel` consuming them instead of the combined `RelUnit`.

---

## 3. What this does *not* establish (honest limits)

* It does **not** prove any of the six parts, and §1a's equivalence is an equivalence of
  *statements*; it does not show that any part is easier than another. The only part I attempt to place is `RelHull`, and
  only by confinement (1b/1c), not by proof.
* It does **not** prove `RelHull` independent of the other five. That needs a countermodel, and none
  is constructible in this tree. The confinement statement is strictly weaker than independence and
  is what is machine-checked here.
* **Non-vacuity of the confinement is not machine-checked.** `hullExtension_iff_nonStanding` would be
  vacuous if every substructure were `Standing`. `not_standing_of_missing_unit` characterises when a
  substructure is outside the region (some unit of `M` outside `S`), but producing such an `S`
  unconditionally needs a cardinality fact (`⊥` is at most countable while an uncountable model has
  uncountably many units) that I did not formalise. In the limiting case where every `S` is
  `Standing`, `RelHull` becomes a *theorem* (`hullExtensionAt_of_standing`) — so either the region is
  non-empty, or the hull slot is free; both readings are covered by the equivalence.
* The `SizeHyp` question is settled only for the hull slot. Whether `RelSeparated`, `RelUnit`,
  `RelNonUnit`, `RelNewRV` need `#M ≤ #N` is not addressed here.

---

## 4. Verification (real output)

```
$ cd $R && LEAN_PATH=$R/.scratch2/sec3:$LEAN_PATH lean .ultramath/smw2qpqe7/m5/Shrink.lean
lean-status=0
48 lines of output
errors=0  sorryAx=0  audits=18
```

`#print axioms` on all eighteen audited declarations, verbatim from the run:

```
'...M5Shrink.relGate_units_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'...M5Shrink.relGate_no_card_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
'...M5Shrink.hullExtension_iff_nonStanding' depends on axioms: [propext, Classical.choice, Quot.sound]
'...M5Shrink.rootStepResidual_of_hullRootStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'...M5Shrink.not_standing_of_missing_unit' depends on axioms: [propext, Quot.sound]
'...M5Shrink.not_standing_of_not_KEqTop' depends on axioms: [propext, Quot.sound]
'...M5Shrink.hullExtensionAt_at_caseSlot_domain' depends on axioms: [propext, Classical.choice, Quot.sound]
'...M5Shrink.relHull_iff_nonStanding' depends on axioms: [propext, Classical.choice, Quot.sound]
'...M5Shrink.relHull_iff_baseRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'...M5Shrink.relHull_iff_baseRootResidual' depends on axioms: [propext, Classical.choice, Quot.sound]
'...M5Shrink.paper_theorem_2_3_of_five_rel_nonStanding' depends on axioms: [propext, Classical.choice, Quot.sound]
'...M5Shrink.paper_theorem_2_3_of_five_rel_baseRootResidual' depends on axioms: [propext, Classical.choice, Quot.sound]
'...M5Shrink.caseNotSeparated_iff_halves' depends on axioms: [propext, Classical.choice, Quot.sound]
'...M5Shrink.cases_iff_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'...M5Shrink.relCases_iff_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'...M5Shrink.input5R_iff_relHull_and_fourParts' depends on axioms: [propext, Classical.choice, Quot.sound]
'...M5Shrink.relUnit_of_algebraic_transcendental' depends on axioms: [propext, Classical.choice, Quot.sound]
'...M5Shrink.paper_theorem_2_3_of_six_rel' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `admit`, no `native_decide`, no new `axiom`; `set_option autoImplicit false`; the only
imports are the merged `RouteLedger` and `D7Hull` (so `QE/Assembly_val.lean` and the `Pre_*`/`AV`
files are not imported).

---

## 5. What a successor on this direction should do

1. **Do not try to shrink the list by restructuring.** It is at the floor (§1a); the only shrink is a
   proof. Attacking a part directly is strictly more valuable than any rewriting.
2. **For `RelHull` (u5-class work), use `RelHullBaseRootResidual`.** The half of the paper's Lemma 3.3
   left in the tree is: `HullBaseStep` at `¬ KEqTop` domains (adjoin all residue units and extend the
   map) and `RootStepResidual` at `KEqTop ∧ ¬ Standing` domains (one root adjoinment). Both are
   *outside* the `Standing` region, so no case-lemma proof will ever close them.
3. **The saturation interface is the likely stumbling block for the base step.** The single-element
   engine *exists*: `QE/Assembly_frozen.lean`'s `Realize.exists_oneStep` (with `Realize.gEmb`,
   `realize_eq`, `realize_eq'`) extends an embedding by one element whose atomic type is realised,
   and `QE/InterfaceClosure.lean`'s `SlotRealization` / `SlotFieldData` / `exists_oneStep_closure`
   already package that for the case slots. What does **not** exist is a set-valued version: the base
   step adjoins `Kˣ(M)` — a whole residue field — in one step, and
   `D7.hullBaseStep_forces_units_size` shows it is cardinality sensitive. So either restate the base
   step one element at a time (which puts the `ω`-iteration back into the hull construction and needs
   a chain argument over a possibly uncountable index), or add a partial-embedding (tuple) form of
   `Realize.RealizesAtomic`. Do not assume the existing single-element interface closes the base step.
4. **For u1/m1**, hand in `RelAlgebraicUnit` and `RelTranscendentalUnit` separately and consume
   `paper_theorem_2_3_of_six_rel`; nothing else in the endgame changes.
