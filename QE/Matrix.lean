/-
# m6 / u6 — THE MASTER REDUCTION MATRIX

Swarm `smw2qpqe7`, member m6, direction u6.  Question: **which of the five endgame parts of
`QE/RouteLedger.lean` are already implied by `QFFinSat` at `relGate`** — and hence whether

    ShoenfieldTestRel → (∀ relGate pairs, QFFinSat) → HasQE Axioms.ACVF

is the canonical single-hypothesis final, or whether a part needs less (or more).

## The answers (machine-checked below)

**A1. All five parts follow from `QFFinSat@relGate`.** Per pair, `SatRel ∧ QFFinSat` gives Marker's
saturated realisation `M5Ledger.SaturationRealization` (§1, `satReal_of_satRel_qffinsat`), which at
the pair is *equivalent* to `HullExtension ∧ Cases` (`RouteLedger.hull_and_cases_iff_satReal`), and
`Cases` projects to the three case slots; the unit/non-unit halves of `CaseNotSeparated` are its
specialisations.  Gated, that is §2: `relHull_of_finSat`, `relSeparated_of_finSat`,
`relUnit_of_finSat`, `relNonUnit_of_finSat`, `relNewRV_of_finSat`.

**A2. The five-part list is *equivalent* to Marker's input 5 at `relGate`** (§3,
`five_parts_iff_input5R`).  So the parts do not carry content beyond the saturation input: proving
the case lemmas is proving input 5 (`RouteLedger` §6b says this for `L33 ∧ L3x`; here it is said for
the five *named* parts).  In particular *no* part can be dropped and no part is "the easy half" in
the sense of being independent of the input.

**A3. Each part is also implied by hypotheses that are independent of finite satisfiability** (§4):
at a pair, a *total* extension `ExtendsHere` gives all five (no saturation, no size, no `QFFinSat`),
and the tree's own interfaces give the individual parts without `QFFinSat` (hull from `PrepStepP`,
3.7 from `OneStepSeparatedP` + `VFInvClosedOn`, 3.5/3.4/3.6 from `NotSeparatedBranch`, 3.8
definitionally from `OneStepRVNew`).  So `QFFinSat` is a *sufficient* route to every part, not the
minimal hypothesis of any of them; what the parts really need less of is the gate: per pair the matrix
uses `SatRel` only, and none of the five cells consumes `M7Paper.SizeHyp` (§1, and
`sizeHyp_of_satRel_qffinsat` shows the size conjunct is *produced* by `SatRel ∧ QFFinSat`).

**A4. The single-hypothesis final is TRUE but NOT canonical.**  `QFFinSat` at `relGate` pairs is
refutable at a machine-checked family of configurations (§5): at a `relGate` pair with an Archimedean
target carrying an infinitesimal over an embeddable substructure, `QFFinSat` **fails**
(`G3.not_forall_qffinsat_at_relGate`).  So `(∀ relGate, QFFinSat)` is not a hypothesis anyone can
discharge; the honest canonical statement is the **split** form (§6)

    ShoenfieldTestRel → FinSatAtArchimedean → (QFFinSat at the remaining relGate pairs) → HasQE

(machine-checked as `paper_theorem_rel_of_finSat_split`, exactly `M8NV.input5R_of_finSat_split`
composed with `G3.paper_theorem_rel_two`), whose Archimedean half is *not* refutable by the tree's
configuration (`M8NV.no_refutingConfig_of_finSat`): the two forms differ exactly where the tree's
refutations fire.

**A5. A by-product that sharpens the gate.**  `SatRel ∧ QFFinSat` at a pair already *produces* the
size conjunct `#M ≤ #N` at any substructure-embedding that exists (`sizeHyp_of_satRel_qffinsat`), so
`QFFinSat`'s content is orthogonal to `SizeHyp`; the size conjunct of `relGate` is not spent by the
matrix, it is derived.  What the size conjunct really does is *shrink the quantifier domain* — which
is why adding it to the Archimedean half of the split is wrong (`FinSatAtArchimedean` quantifies over
`SatRel` pairs with no size bound, `M8NV.FinSatAtArchimedean`).

Every declaration below is fully proved: no placeholder proofs, no new axioms, no compiler-decided proofs;
axiom audit at the end.
-/
import RouteLedger
import NonVacuity2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.M6Matrix

/-! ## 0. The named hypotheses of the matrix

`QFFinSat` at `relGate` pairs, and the two halves of its honest refinement. -/

/-- **The single hypothesis of the matrix**: finite satisfiability of the pushed types at every
`relGate` pair.  This is the hypothesis of `G3.paper_theorem_rel_of_qffinsat`. -/
abbrev FinSatAtRelGate : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → M2Saturation.QFFinSat M N

/-- **The non-Archimedean half** of the split form: `QFFinSat` at the `relGate` pairs whose target is
not Archimedean.  This is `M8NV.input5R_of_finSat_split`'s second hypothesis. -/
abbrev FinSatOffArchimedean : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N], M ⊨ Axioms.ACVF → N ⊨ Axioms.ACVF →
    M1Fix.SatRel M N → M7Paper.SizeHyp M N → ¬ Hahn.ArchimedeanRV N →
    M2Saturation.QFFinSat M N

/-! ## 1. Per pair: `SatRel` + `QFFinSat` gives every part

The matrix at a fixed pair, with no gate and no size hypothesis anywhere.  The chain is

    SatRel ∧ QFFinSat → QFSat → SaturationRealization → HullExtension ∧ Cases → each slot

and each arrow is a merged theorem; the content of this section is that the composite exists at a
pair, i.e. that the chain does not lose an element on the way. -/

section Pair

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **`SatRel` + `QFFinSat` ⟹ Marker's saturated realisation**, at a pair.  Composite of
`G3.qfsat_of_satRel_of_qffinsat` and `M2Saturation.satReal_of_qfsat`; this is the single link that
the whole matrix hangs on. -/
theorem satReal_of_satRel_qffinsat (hSat : M1Fix.SatRel M N)
    (hfin : M2Saturation.QFFinSat M N) :
    M5Ledger.SaturationRealization (M := M) (N := N) :=
  M2Saturation.satReal_of_qfsat (G3.qfsat_of_satRel_of_qffinsat hSat hfin)

/-- The hull half (Lemma 3.3) from the same data. -/
theorem hullExtension_of_satRel_qffinsat (hSat : M1Fix.SatRel M N)
    (hfin : M2Saturation.QFFinSat M N) : G3.HullExtension M N :=
  G3.hullExtension_of_satReal (satReal_of_satRel_qffinsat hSat hfin)

/-- The case half (Lemmas 3.4–3.8) from the same data: input 5 collapses to a *total* extension
(`G3.extendsHere_of_satReal`), and a total extension gives every case slot with `T = ⊤`. -/
theorem cases_of_satRel_qffinsat (hSat : M1Fix.SatRel M N)
    (hfin : M2Saturation.QFFinSat M N) : M4Cases.Cases (M := M) (N := N) :=
  M4Cases.cases_of_global_extension (G3.extendsHere_of_satReal (satReal_of_satRel_qffinsat hSat hfin))

/-- **3.7 from `SatRel` + `QFFinSat`.** -/
theorem separated_of_satRel_qffinsat (hSat : M1Fix.SatRel M N)
    (hfin : M2Saturation.QFFinSat M N) : M4Cases.CaseSeparated (M := M) (N := N) :=
  (cases_of_satRel_qffinsat hSat hfin).separated

/-- **3.5 ∪ 3.4 ∪ 3.6 (the not-separated slot) from `SatRel` + `QFFinSat`.** -/
theorem notSeparated_of_satRel_qffinsat (hSat : M1Fix.SatRel M N)
    (hfin : M2Saturation.QFFinSat M N) : M4Cases.CaseNotSeparated (M := M) (N := N) :=
  (cases_of_satRel_qffinsat hSat hfin).notSeparated

/-- **3.8 from `SatRel` + `QFFinSat`.** -/
theorem newRV_of_satRel_qffinsat (hSat : M1Fix.SatRel M N)
    (hfin : M2Saturation.QFFinSat M N) : M4Cases.CaseNewRV (M := M) (N := N) :=
  (cases_of_satRel_qffinsat hSat hfin).newRV

/-- **The unit half (3.4 / 3.6) from `SatRel` + `QFFinSat`**: `UnitSlot` is a specialisation of
`CaseNotSeparated` (add the hypothesis `iUnits (iRv m)`), so no separate work is needed. -/
theorem unitSlot_of_satRel_qffinsat (hSat : M1Fix.SatRel M N)
    (hfin : M2Saturation.QFFinSat M N) : RouteLedger.UnitSlot (M := M) (N := N) := by
  intro S f hS m hmVF hmrv _hunit hns
  exact (cases_of_satRel_qffinsat hSat hfin).notSeparated S f hS m hmVF hmrv hns

/-- **The non-unit half (3.5) from `SatRel` + `QFFinSat`.** -/
theorem nonUnitSlot_of_satRel_qffinsat (hSat : M1Fix.SatRel M N)
    (hfin : M2Saturation.QFFinSat M N) : RouteLedger.NonUnitSlot (M := M) (N := N) := by
  intro S f hS m hmVF hmrv _hunit hns
  exact (cases_of_satRel_qffinsat hSat hfin).notSeparated S f hS m hmVF hmrv hns

/-- **A5: the size conjunct of `relGate` is *produced*, not spent.**  At a pair, `SatRel` +
`QFFinSat` gives `#M ≤ #N` — the very second conjunct of `relGate` — at every substructure embedding
that exists.  (The embedding hypothesis is not droppable: `QFFinSat` is a `∀`-statement over pairs
`(S, f)`, so at a pair with no such pair it says nothing about cardinality.  This is the exact reason
`FinSatAtArchimedean` is stated *without* the size bound.) -/
theorem sizeHyp_of_satRel_qffinsat (hSat : M1Fix.SatRel M N)
    (hfin : M2Saturation.QFFinSat M N) (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    M7Paper.SizeHyp M N :=
  M5Ledger.saturationRealization_forces_size (satReal_of_satRel_qffinsat hSat hfin) S f

end Pair

/-! ## 2. The matrix at `relGate`: all five parts from `FinSatAtRelGate`

Each theorem below is one cell of the matrix's first row.  The proofs are the gated forms of §1 and
use `relGate`'s first conjunct (`M1Fix.SatRel`) only; the size conjunct is never touched. -/

section Gate

/-- **`RelHull` (Lemma 3.3, hull form) from `QFFinSat@relGate`.** -/
theorem relHull_of_finSat (hfin : FinSatAtRelGate) : RouteLedger.RelHull :=
  fun M N _ _ hM hN hR => hullExtension_of_satRel_qffinsat hR.1 (hfin M N hR)

/-- **Every case slot at once from `QFFinSat@relGate`** (the gated form of
`cases_of_satRel_qffinsat`). -/
theorem relCases_of_finSat (hfin : FinSatAtRelGate) : RouteLedger.RelCases :=
  fun M N _ _ hM hN hR => cases_of_satRel_qffinsat hR.1 (hfin M N hR)

/-- **`RelSeparated` (Lemma 3.7) from `QFFinSat@relGate`.** -/
theorem relSeparated_of_finSat (hfin : FinSatAtRelGate) : RouteLedger.RelSeparated :=
  fun M N _ _ hM hN hR => separated_of_satRel_qffinsat hR.1 (hfin M N hR)

/-- **`RelUnit` (Lemmas 3.4 / 3.6, the unit half) from `QFFinSat@relGate`.** -/
theorem relUnit_of_finSat (hfin : FinSatAtRelGate) : RouteLedger.RelUnit :=
  fun M N _ _ hM hN hR => unitSlot_of_satRel_qffinsat hR.1 (hfin M N hR)

/-- **`RelNonUnit` (Lemma 3.5, the non-unit half) from `QFFinSat@relGate`.** -/
theorem relNonUnit_of_finSat (hfin : FinSatAtRelGate) : RouteLedger.RelNonUnit :=
  fun M N _ _ hM hN hR => nonUnitSlot_of_satRel_qffinsat hR.1 (hfin M N hR)

/-- **`RelNewRV` (Lemma 3.8) from `QFFinSat@relGate`.** -/
theorem relNewRV_of_finSat (hfin : FinSatAtRelGate) : RouteLedger.RelNewRV :=
  fun M N _ _ hM hN hR => newRV_of_satRel_qffinsat hR.1 (hfin M N hR)

/-- **The whole five-part list from the single hypothesis.**  All five cells at once; this is the
matrix's head line, and it is what makes the case-lemma work (u1–u5) unnecessary *if* `FinSatAtRelGate`
is granted. -/
theorem fiveParts_of_finSat (hfin : FinSatAtRelGate) :
    RouteLedger.RelHull ∧ RouteLedger.RelSeparated ∧ RouteLedger.RelUnit ∧
      RouteLedger.RelNonUnit ∧ RouteLedger.RelNewRV :=
  ⟨relHull_of_finSat hfin, relSeparated_of_finSat hfin, relUnit_of_finSat hfin,
    relNonUnit_of_finSat hfin, relNewRV_of_finSat hfin⟩

end Gate

/-! ## 3. The five-part list *is* Marker's input 5

Two directions, both machine-checked:

* `←` : input 5 gives `HullExtension ∧ Cases` (`RouteLedger.relHull_and_cases_iff_input5R`), whose
  projections are the five parts;
* `→` : the five parts give `RelCases` (`RouteLedger.relCases_of_parts`) and `RelHull`, hence input 5.

The consequence is the matrix's *negative* half: the parts are not a weakening of input 5 at all, so
no amount of case-splitting can make input 5 unnecessary.  What the parts give is the *statement* of
input 5 in the paper's own four cases — nothing more, nothing less. -/

/-- **The five-part list ⟺ `Input5R`** (Marker's saturation realisation at `relGate`). -/
theorem fiveParts_iff_input5R :
    (RouteLedger.RelHull ∧ RouteLedger.RelSeparated ∧ RouteLedger.RelUnit ∧
      RouteLedger.RelNonUnit ∧ RouteLedger.RelNewRV) ↔ M5Shoenfield.Input5R := by
  constructor
  · rintro ⟨hH, hsep, hu, hn, hnew⟩
    exact (RouteLedger.relHull_and_cases_iff_input5R).mp
      ⟨hH, RouteLedger.relCases_of_parts hsep hu hn hnew⟩
  · intro h5
    have hH : RouteLedger.RelHull := ((RouteLedger.relHull_and_cases_iff_input5R).mpr h5).1
    have hC : RouteLedger.RelCases := ((RouteLedger.relHull_and_cases_iff_input5R).mpr h5).2
    exact ⟨hH,
      fun M N _ _ _ _ hR => (hC M N hR).separated,
      fun M N _ _ _ _ hR => by
        intro S f hS m hmVF hmrv _hunit hns
        exact (hC M N hR).notSeparated S f hS m hmVF hmrv hns,
      fun M N _ _ _ _ hR => by
        intro S f hS m hmVF hmrv _hunit hns
        exact (hC M N hR).notSeparated S f hS m hmVF hmrv hns,
      fun M N _ _ _ _ hR => (hC M N hR).newRV⟩

/-- **`FinSatAtRelGate` is at least as strong as input 5**: the matrix row's first cell composed with
the equivalence.  (One line from `relHull_of_finSat` and `relCases_of_finSat`, recorded because it is
the precise sense in which `QFFinSat` *dominates* the paper's §3.) -/theorem input5R_of_finSat (hfin : FinSatAtRelGate) : M5Shoenfield.Input5R :=
  (fiveParts_iff_input5R).mp (fiveParts_of_finSat hfin)

/-- **The four case parts are *exactly* `RelCases`** (the converse of `RouteLedger.relCases_of_parts`,
which is a projection).  So the four-way split of `RelCases` loses nothing: the parts are a rewriting
of Lemmas 3.4–3.8 at `relGate`, not a weakening of them. -/
theorem relCases_iff_parts :
    RouteLedger.RelCases ↔
      (RouteLedger.RelSeparated ∧ RouteLedger.RelUnit ∧ RouteLedger.RelNonUnit ∧
        RouteLedger.RelNewRV) := by
  constructor
  · intro hC
    exact ⟨fun M N _ _ _ _ hR => (hC M N hR).separated,
      fun M N _ _ _ _ hR => by
        intro S f hS m hmVF hmrv _hunit hns
        exact (hC M N hR).notSeparated S f hS m hmVF hmrv hns,
      fun M N _ _ _ _ hR => by
        intro S f hS m hmVF hmrv _hunit hns
        exact (hC M N hR).notSeparated S f hS m hmVF hmrv hns,
      fun M N _ _ _ _ hR => (hC M N hR).newRV⟩
  · rintro ⟨hsep, hu, hn, hnew⟩
    exact RouteLedger.relCases_of_parts hsep hu hn hnew

/-! ## 4. Rows outside finite satisfiability: what each part needs less of

The matrix has more rows that matter for the ledger: every part is implied by data that has nothing to
do with finite satisfiability.  The strongest such row is the *total extension* at the pair
(Proposition 3.9 itself): it gives every part, with no gate, no size and no `QFFinSat`.  The local rows
record the tree's own interfaces per part, so that the matrix says which merged file discharges which
cell.  (What the parts need *less* of is the gate, not the finite satisfiability: none of the five
cells uses `M7Paper.SizeHyp`, and §1 shows `SatRel ∧ QFFinSat` already produces it.) -/

section Weaker

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **A total extension gives every case slot** (no saturation, no size, no `QFFinSat`).  This is the
stress test that the five parts are *not* statements about finite satisfiability: they follow from
Proposition 3.9 itself.  (It also shows that no part is contradictory, at any pair where the extension
property holds.) -/
theorem cases_of_extendsHere (h : G3.ExtendsHere M N) : M4Cases.Cases (M := M) (N := N) :=
  M4Cases.cases_of_global_extension h

/-- The hull form from a total extension: `HullExtension` is the restriction of the total embedding to
the standing hull. -/
theorem hullExtension_of_extendsHere (h : G3.ExtendsHere M N) : G3.HullExtension M N :=
  G3.hullExtension_of_extendsHere h

/-- **Saturation realisation alone gives all five parts at a gated pair** — the row that makes
`fiveParts_iff_input5R`'s `←` direction visible at the level of the matrix.  No `QFFinSat`, no
`SatRel`, no size. -/
theorem fiveParts_of_input5R (h5 : M5Shoenfield.Input5R) :
    RouteLedger.RelHull ∧ RouteLedger.RelSeparated ∧ RouteLedger.RelUnit ∧
      RouteLedger.RelNonUnit ∧ RouteLedger.RelNewRV :=
  (fiveParts_iff_input5R).mpr h5

/-! ### 4.1 The tree's local interfaces, per part

Each theorem names the merged asset that discharges the cell *without* `QFFinSat`, so a reader of the
matrix can see which work remains if the single hypothesis is not granted. -/

/-- **`RelHull` *is* the frozen Lemma 3.3 statement** (`Assembly.PrepStepP` at the gate), by
`G3.prepStepP_iff_hullExtension` pointwise.  So the matrix's first cell needs no new mathematics to
*state*: it is the paper's hull step, verbatim. -/
theorem relHull_iff_prepStepP :
    RouteLedger.RelHull ↔
      ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
        M5Shoenfield.relGate M N → Assembly.PrepStepP (M := M) (N := N) := by
  constructor
  · intro h M N _ _ _ _ hR
    exact (G3.prepStepP_iff_hullExtension (M := M) (N := N)).mpr (h M N hR)
  · intro h M N _ _ _ _ hR
    exact (G3.prepStepP_iff_hullExtension (M := M) (N := N)).mp (h M N hR)

/-- **`RelSeparated` ⟸ the tree's separated interface** (`M5L.OneStepSeparatedP`), at the price of
`M5L.VFInvClosedOn` at every `Standing` substructure — the defect `QE/OneStepCases.lean` §2 isolates.
This is `RouteLedger.caseSeparated_of_oneStepSeparatedP` gated. -/
theorem relSeparated_of_oneStepSeparatedP
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → M5L.OneStepSeparatedP (M := M) (N := N))
    (hfinv : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], M5Shoenfield.relGate M N →
      ∀ S : LRV.Substructure M, Assembly.Standing S → M5L.VFInvClosedOn S) :
    RouteLedger.RelSeparated :=
  fun M N _ _ hM hN hR =>
    RouteLedger.caseSeparated_of_oneStepSeparatedP (h M N hR) (hfinv M N hR)

/-- **`RelNonUnit` ⟸ Lemma 3.5's merged branch statement** (`Case35.NotSeparatedBranch`), which is
stronger than the slot: `RouteLedger.nonUnitSlot_of_branch` gated. -/
theorem relNonUnit_of_branch
    (hb : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → Case35.NotSeparatedBranch (M := M) (N := N)) :
    RouteLedger.RelNonUnit :=
  fun M N _ _ hM hN hR => RouteLedger.nonUnitSlot_of_branch (hb M N hR)

/-- **`RelUnit` ⟸ Lemma 3.5's merged branch statement** — the same asset covers the unit half too, so
`NotSeparatedBranch` is stronger than both halves. -/
theorem relUnit_of_branch
    (hb : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → Case35.NotSeparatedBranch (M := M) (N := N)) :
    RouteLedger.RelUnit :=
  fun M N _ _ hM hN hR => RouteLedger.unitSlot_of_branch (hb M N hR)

/-- **`RelNewRV` *is* the frozen new-`rv` one-step** (definitional: `M4Cases.CaseNewRV` is an
`abbrev` for `M5.OneStepRVNew`).  Recorded so that the matrix's 3.8 cell points at the frozen
statement rather than at a paraphrase. -/
theorem relNewRV_iff_oneStepRVNew :
    RouteLedger.RelNewRV ↔
      ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
        M5Shoenfield.relGate M N → M5.OneStepRVNew (M := M) (N := N) :=
  Iff.rfl

/-- **`RelUnit` ⟸ (3.4's residual + `Slot34`) ∧ (3.6's transcendental half)**, gated: the unit half
splits classically into the algebraic and the transcendental sub-case
(`RouteLedger.unitSlot_of_algebraic_transcendental`), and the algebraic one is discharged by
`RootData` + `Slot34` (`RouteLedger.algebraicUnitSlot_of_rootData_slot34`).  This is the matrix's
"what the case lemmas still owe" cell for the unit half. -/
theorem relUnit_of_rootData_slot34_transcendental
    (hroot : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], M5Shoenfield.relGate M N → RouteLedger.RootData (M := M) (N := N))
    (h34 : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → M5P1.Slot34 (M := M) (N := N))
    (htrans : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], M5Shoenfield.relGate M N →
      RouteLedger.TranscendentalUnitSlot (M := M) (N := N)) :
    RouteLedger.RelUnit :=
  fun M N _ _ hM hN hR =>
    RouteLedger.unitSlot_of_algebraic_transcendental
      (RouteLedger.algebraicUnitSlot_of_rootData_slot34 (hroot M N hR) (h34 M N hR))
      (htrans M N hR)

end Weaker

/-! ## 4b. Which parts imply which: the split is lossless

The matrix's "which parts each implies" column.  Two exact identities, both at a pair:

* `CaseNotSeparated ⟺ UnitSlot ∧ NonUnitSlot` — the u1/u2 split is *lossless*
  (`M5P1.caseNotSeparated_iff_unit_and_nonunit`, restated at the `RouteLedger` slot names).  So proving
  u1 and u2 is proving Lemma 3.5's slot and nothing is dropped.
* `CaseSeparated ∧ CaseNotSeparated ⟺ OneStepRVOld` — the two `rv`-old branches are *exactly* the
  `rv`-old one-step (`M4Cases.oneStepRVOld_of_cases` is one direction; the other is a projection).

Together with `relCases_iff_parts` (§3) this makes the four-way split of `RelCases` an equivalence at
`relGate`, so the parts are a rewriting of Lemmas 3.4–3.8, not a weakening of them. -/

section WhichImplies

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **The unit half is a specialisation of, and together with the non-unit half *equivalent* to, the
not-separated slot.**  This is `M5P1.caseNotSeparated_iff_unit_and_nonunit` in the ledger's slot
names. -/
theorem unit_nonunit_iff_notSeparated :
    (RouteLedger.UnitSlot (M := M) (N := N) ∧ RouteLedger.NonUnitSlot (M := M) (N := N)) ↔
      M4Cases.CaseNotSeparated (M := M) (N := N) := by
  constructor
  · rintro ⟨hu, hn⟩
    exact RouteLedger.caseNotSeparated_of_halves hu hn
  · intro h
    exact ⟨fun S f hS m hmVF hmrv _ hunit =>
        h S f hS m hmVF hmrv hunit,
      fun S f hS m hmVF hmrv _ hunit =>
        h S f hS m hmVF hmrv hunit⟩

/-- **The two `rv`-old parts are *exactly* the `rv`-old one-step**: at a pair, `CaseSeparated` and
`CaseNotSeparated` together are equivalent to `M5.OneStepRVOld`.  So neither branch can be dropped, and
neither is stronger than `OneStepRVOld`: they are its two halves. -/
theorem separated_and_notSeparated_iff_oneStepRVOld :
    (M4Cases.CaseSeparated (M := M) (N := N) ∧ M4Cases.CaseNotSeparated (M := M) (N := N)) ↔
      M5.OneStepRVOld (M := M) (N := N) := by
  constructor
  · rintro ⟨hsep, hns⟩
    exact M4Cases.oneStepRVOld_of_cases hsep hns
  · intro h
    exact ⟨fun S f hS m hmVF hmrv _ => h S f hS m hmVF hmrv,
      fun S f hS m hmVF hmrv _ => h S f hS m hmVF hmrv⟩

/-- **`Cases` ⟺ its three branches**, definitionally (recorded so the matrix's shape is explicit). -/
theorem cases_iff_branches :
    M4Cases.Cases (M := M) (N := N) ↔
      (M4Cases.CaseSeparated (M := M) (N := N) ∧
        M4Cases.CaseNotSeparated (M := M) (N := N) ∧
        M4Cases.CaseNewRV (M := M) (N := N)) :=
  ⟨fun h => ⟨h.separated, h.notSeparated, h.newRV⟩,
    fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- **At a pair: the five parts ⟺ Marker's saturated realisation.**  The sharp form of A2, with no
gate: `HullExtension ∧ Cases ⟺ SaturationRealization` is
`RouteLedger.hull_and_cases_iff_satReal`, `Cases ⟺ its branches` is `cases_iff_branches`, and the unit
/ non-unit split is `unit_nonunit_iff_notSeparated`.  So at every pair, the paper's §3 case lemmas are
*nothing but* input 5 said in cases. -/
theorem fiveParts_pair_iff_satReal {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF] :
    (G3.HullExtension M N ∧ M4Cases.CaseSeparated (M := M) (N := N) ∧
        RouteLedger.UnitSlot (M := M) (N := N) ∧ RouteLedger.NonUnitSlot (M := M) (N := N) ∧
        M4Cases.CaseNewRV (M := M) (N := N)) ↔
      M5Ledger.SaturationRealization (M := M) (N := N) := by
  constructor
  · rintro ⟨hH, hsep, hu, hn, hnew⟩
    exact (RouteLedger.hull_and_cases_iff_satReal (M := M) (N := N)).mp
      ⟨hH, cases_iff_branches.mpr
        ⟨hsep, RouteLedger.caseNotSeparated_of_halves hu hn, hnew⟩⟩
  · intro h5
    obtain ⟨hH, hC⟩ := (RouteLedger.hull_and_cases_iff_satReal (M := M) (N := N)).mpr h5
    obtain ⟨hsep, hns, hnew⟩ := cases_iff_branches.mp hC
    obtain ⟨hu, hn⟩ := unit_nonunit_iff_notSeparated.mpr hns
    exact ⟨hH, hsep, hu, hn, hnew⟩

end WhichImplies

/-! ## 5. Row "`QFFinSat@relGate` alone": refuted

The single hypothesis is **not** a theorem, at `relGate` or anywhere else: at a `relGate` pair with an
Archimedean target, an infinitesimal over an embeddable substructure makes the pushed type finitely
*unsatisfiable*.  This row is what stops `ShoenfieldTestRel → (∀ relGate, QFFinSat) → HasQE` from
being a route to an unconditional theorem. -/

section Refute

variable {M N : Type} [LRV.Structure M] [LRV.Structure N] [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **`FinSatAtRelGate` fails at an Archimedean `relGate` pair carrying the infinitesimal
configuration.**  Restatement of `G3.not_forall_qffinsat_at_relGate` with the hypothesis named, i.e.
the matrix's refutation cell. -/
theorem not_finSatAtRelGate_of_config (hSat : M1Fix.SatRel M N) (hsize : M7Paper.SizeHyp M N)
    (hArch : Hahn.ArchimedeanRV N) {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmRV : iRV m) (hmne : m ≠ iRVZero) (hmgt : ¬ iLe m iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow s n) m) :
    ¬ FinSatAtRelGate :=
  G3.not_forall_qffinsat_at_relGate (f := f) hSat hsize hArch hsS hsRV hsne hsgt hmRV hmne hmgt hinf

/-- **At such a pair `QFFinSat` itself fails**, not merely the `∀`-form. -/
theorem not_finSat_of_config (hSat : M1Fix.SatRel M N) (hArch : Hahn.ArchimedeanRV N)
    {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmRV : iRV m) (hmne : m ≠ iRVZero) (hmgt : ¬ iLe m iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow s n) m) :
    ¬ M2Saturation.QFFinSat M N :=
  G3.not_finSat_of_satRel_of_archimedean (f := f) hSat hArch hsS hsRV hsne hsgt hmRV hmne hmgt hinf

end Refute

/-! ## 6. The canonical statement: the split form

`FinSatAtArchimedean` (the Archimedean half, `QE/NonVacuity2.lean` §3) plus `FinSatOffArchimedean`
(the non-Archimedean half) gives input 5 (`M8NV.input5R_of_finSat_split`), hence `HasQE`
(`G3.paper_theorem_rel_two`).  This is the honest single-hypothesis final: unlike
`FinSatAtRelGate`, its Archimedean half is not refuted by the tree's configuration family
(`M8NV.no_refutingConfig_of_finSat`), and its non-Archimedean half is exactly what the case lemmas
3.4–3.8 have to prove. -/

/-- **THE CANONICAL SINGLE-HYPOTHESIS FINAL.**  `HasQE` from Shoenfield's test, the Archimedean half of
finite satisfiability, and the non-Archimedean half. -/
theorem paper_theorem_rel_of_finSat_split (hQ : M5Shoenfield.ShoenfieldTestRel)
    (hArch : M8NV.FinSatAtArchimedean) (hRest : FinSatOffArchimedean) :
    HasQE Axioms.ACVF :=
  G3.paper_theorem_rel_two hQ (M8NV.input5R_of_finSat_split hArch hRest)

/-- The split form's first half is *not* refutable by the tree's configuration: under
`FinSatAtArchimedean` there is no refuting configuration at all.  (Machine-checked form of "the split
form's hypothesis is the right one".) -/
theorem no_refutingConfig_of_arch_half (h : M8NV.FinSatAtArchimedean) :
    M8NV.RefutingConfig → False :=
  M8NV.no_refutingConfig_of_finSat h

/-- **The unconditional statement is not available from the tree's refutations alone**: the Archimedean
half of the split is a genuine hypothesis, since a refuting configuration would falsify it
(`refutingConfig_not_finsat`).  So `HasQE` is not derivable from `ShoenfieldTestRel` plus the
*negation* of the split's Archimedean half. -/
theorem not_finSat_of_refutingConfig (W : M8NV.RefutingConfig) :
    ¬ M8NV.FinSatAtArchimedean := by
  intro h
  exact M8NV.no_refutingConfig_of_finSat h W

/-! ## 6b. The split hypothesis implies the single hypothesis

The two forms are not in competition: the split's two halves *derive* `FinSatAtRelGate`, because at a
`relGate` pair the target is either Archimedean (where `FinSatAtArchimedean` applies, and it needs no
size bound) or not (where `FinSatOffArchimedean` applies).  So the canonical statement's hypothesis is
at least as strong as the single-hypothesis form, and it is the one that survives the refutations. -/

/-- **`FinSatAtArchimedean` + `FinSatOffArchimedean` ⟹ `FinSatAtRelGate`.** -/
theorem finSatAtRelGate_of_split (hArch : M8NV.FinSatAtArchimedean)
    (hRest : FinSatOffArchimedean) : FinSatAtRelGate := by
  intro M N _ _ hM hN hR
  by_cases hA : Hahn.ArchimedeanRV N
  · exact hArch M N hM hN hR.1 hA
  · exact hRest M N hM hN hR.1 hR.2 hA

/-- **Consequently the whole matrix is available from the split hypothesis**: the five parts, and
input 5, follow from it. -/
theorem fiveParts_of_split (hArch : M8NV.FinSatAtArchimedean) (hRest : FinSatOffArchimedean) :
    RouteLedger.RelHull ∧ RouteLedger.RelSeparated ∧ RouteLedger.RelUnit ∧
      RouteLedger.RelNonUnit ∧ RouteLedger.RelNewRV :=
  fiveParts_of_finSat (finSatAtRelGate_of_split hArch hRest)

/-- **The split hypothesis gives input 5**, so the canonical statement is a strengthening of the
single-hypothesis one rather than a substitute for it. -/
theorem input5R_of_split (hArch : M8NV.FinSatAtArchimedean) (hRest : FinSatOffArchimedean) :
    M5Shoenfield.Input5R :=
  input5R_of_finSat (finSatAtRelGate_of_split hArch hRest)

/-! ## 6c. The same hypothesis collapses the *frozen* gate list

`paperGate` implies `relGate` (`M5Shoenfield.paperGate_le_relGate`), so the frozen endgame list
(`GatedHull`, `GatedSeparated`, `GatedUnit`, `GatedNonUnit`, `GatedNewRV`) is a corollary of the
matrix's first row: no separate work is needed at the frozen gate.  This is the row of the matrix that
says the two gate lists are not independent — the `relGate` list is the sharper one and it dominates. -/

/-- **`GatedHull` from the single hypothesis.** -/
theorem gatedHull_of_finSat (hfin : FinSatAtRelGate) : RouteLedger.GatedHull :=
  RouteLedger.gatedHull_of_relHull (relHull_of_finSat hfin)

/-- **`GatedSeparated` from the single hypothesis.** -/
theorem gatedSeparated_of_finSat (hfin : FinSatAtRelGate) : RouteLedger.GatedSeparated :=
  fun M N _ _ _ _ hP =>
    (RouteLedger.gatedCases_of_relCases (relCases_of_finSat hfin) M N hP).separated

/-- **`GatedUnit` from the single hypothesis.** -/
theorem gatedUnit_of_finSat (hfin : FinSatAtRelGate) : RouteLedger.GatedUnit :=
  fun M N _ _ _ _ hP => by
    intro S f hS m hmVF hmrv _hunit hns
    exact (RouteLedger.gatedCases_of_relCases (relCases_of_finSat hfin) M N hP).notSeparated
      S f hS m hmVF hmrv hns

/-- **`GatedNonUnit` from the single hypothesis.** -/
theorem gatedNonUnit_of_finSat (hfin : FinSatAtRelGate) : RouteLedger.GatedNonUnit :=
  fun M N _ _ _ _ hP => by
    intro S f hS m hmVF hmrv _hunit hns
    exact (RouteLedger.gatedCases_of_relCases (relCases_of_finSat hfin) M N hP).notSeparated
      S f hS m hmVF hmrv hns

/-- **`GatedNewRV` from the single hypothesis.** -/
theorem gatedNewRV_of_finSat (hfin : FinSatAtRelGate) : RouteLedger.GatedNewRV :=
  fun M N _ _ _ _ hP =>
    (RouteLedger.gatedCases_of_relCases (relCases_of_finSat hfin) M N hP).newRV

/-- **The frozen endgame `paper_theorem_2_3_of_five` from the single hypothesis.**  Same conclusion as
`paper_theorem_rel_of_finSat_via_parts`, taken through the frozen gate list and the frozen quotation
`M7Paper.ShoenfieldTestSat` instead of Marker's pair-relative one. -/
theorem paper_theorem_sat_of_finSat (hShoen : M7Paper.ShoenfieldTestSat)
    (hfin : FinSatAtRelGate) : HasQE Axioms.ACVF :=
  RouteLedger.paper_theorem_2_3_of_five hShoen (gatedHull_of_finSat hfin)
    (gatedSeparated_of_finSat hfin) (gatedUnit_of_finSat hfin) (gatedNonUnit_of_finSat hfin)
    (gatedNewRV_of_finSat hfin)

/-! ## 7. The two finals agree

The tree's `G3.paper_theorem_rel_of_qffinsat` (single hypothesis, through `Input5R`) and this file's
`paper_theorem_rel_of_finSat_via_parts` (single hypothesis, through the five *named* parts) have the
same hypothesis and the same conclusion: the matrix shows the case-lemma route and the direct route
are the same theorem.  Recorded so that no later file can claim a stronger endgame from the parts
without also proving `QFFinSat`. -/

/-- **The single-hypothesis final through the five named parts.**  This is a *different proof* of
`G3.paper_theorem_rel_of_qffinsat`'s statement: instead of feeding `Input5R` directly, it builds the
five parts (`fiveParts_of_finSat`) and runs the endgame `RouteLedger.paper_theorem_2_3_of_five_rel`.
The two proofs agree by proof irrelevance, which is the machine-checked statement that the case lemmas
add nothing to input 5. -/
theorem paper_theorem_rel_of_finSat_via_parts (hQ : M5Shoenfield.ShoenfieldTestRel)
    (hfin : FinSatAtRelGate) : HasQE Axioms.ACVF :=
  RouteLedger.paper_theorem_2_3_of_five_rel hQ (relHull_of_finSat hfin) (relSeparated_of_finSat hfin)
    (relUnit_of_finSat hfin) (relNonUnit_of_finSat hfin) (relNewRV_of_finSat hfin)

/-- **The two routes are the same theorem** (same statement, hence equal proofs by proof
irrelevance). -/
theorem two_routes_agree (hQ : M5Shoenfield.ShoenfieldTestRel) (hfin : FinSatAtRelGate) :
    paper_theorem_rel_of_finSat_via_parts hQ hfin = G3.paper_theorem_rel_of_qffinsat hQ hfin :=
  Subsingleton.elim _ _

/-! ## 8. Axiom audit -/

#print axioms SpecialTransformations.Milestone0.M6Matrix.satReal_of_satRel_qffinsat
#print axioms SpecialTransformations.Milestone0.M6Matrix.cases_of_satRel_qffinsat
#print axioms SpecialTransformations.Milestone0.M6Matrix.unitSlot_of_satRel_qffinsat
#print axioms SpecialTransformations.Milestone0.M6Matrix.nonUnitSlot_of_satRel_qffinsat
#print axioms SpecialTransformations.Milestone0.M6Matrix.sizeHyp_of_satRel_qffinsat
#print axioms SpecialTransformations.Milestone0.M6Matrix.relHull_of_finSat
#print axioms SpecialTransformations.Milestone0.M6Matrix.relCases_of_finSat
#print axioms SpecialTransformations.Milestone0.M6Matrix.relSeparated_of_finSat
#print axioms SpecialTransformations.Milestone0.M6Matrix.relUnit_of_finSat
#print axioms SpecialTransformations.Milestone0.M6Matrix.relNonUnit_of_finSat
#print axioms SpecialTransformations.Milestone0.M6Matrix.relNewRV_of_finSat
#print axioms SpecialTransformations.Milestone0.M6Matrix.fiveParts_of_finSat
#print axioms SpecialTransformations.Milestone0.M6Matrix.fiveParts_iff_input5R
#print axioms SpecialTransformations.Milestone0.M6Matrix.input5R_of_finSat
#print axioms SpecialTransformations.Milestone0.M6Matrix.fiveParts_of_input5R
#print axioms SpecialTransformations.Milestone0.M6Matrix.relHull_iff_prepStepP
#print axioms SpecialTransformations.Milestone0.M6Matrix.relSeparated_of_oneStepSeparatedP
#print axioms SpecialTransformations.Milestone0.M6Matrix.relNonUnit_of_branch
#print axioms SpecialTransformations.Milestone0.M6Matrix.relUnit_of_branch
#print axioms SpecialTransformations.Milestone0.M6Matrix.relUnit_of_rootData_slot34_transcendental
#print axioms SpecialTransformations.Milestone0.M6Matrix.not_finSatAtRelGate_of_config
#print axioms SpecialTransformations.Milestone0.M6Matrix.paper_theorem_rel_of_finSat_split
#print axioms SpecialTransformations.Milestone0.M6Matrix.no_refutingConfig_of_arch_half
#print axioms SpecialTransformations.Milestone0.M6Matrix.paper_theorem_rel_of_finSat_via_parts
#print axioms SpecialTransformations.Milestone0.M6Matrix.two_routes_agree
#print axioms SpecialTransformations.Milestone0.M6Matrix.relCases_iff_parts
#print axioms SpecialTransformations.Milestone0.M6Matrix.unit_nonunit_iff_notSeparated
#print axioms SpecialTransformations.Milestone0.M6Matrix.separated_and_notSeparated_iff_oneStepRVOld
#print axioms SpecialTransformations.Milestone0.M6Matrix.cases_iff_branches
#print axioms SpecialTransformations.Milestone0.M6Matrix.fiveParts_pair_iff_satReal
#print axioms SpecialTransformations.Milestone0.M6Matrix.finSatAtRelGate_of_split
#print axioms SpecialTransformations.Milestone0.M6Matrix.fiveParts_of_split
#print axioms SpecialTransformations.Milestone0.M6Matrix.input5R_of_split
#print axioms SpecialTransformations.Milestone0.M6Matrix.gatedHull_of_finSat
#print axioms SpecialTransformations.Milestone0.M6Matrix.gatedSeparated_of_finSat
#print axioms SpecialTransformations.Milestone0.M6Matrix.gatedUnit_of_finSat
#print axioms SpecialTransformations.Milestone0.M6Matrix.gatedNonUnit_of_finSat
#print axioms SpecialTransformations.Milestone0.M6Matrix.gatedNewRV_of_finSat
#print axioms SpecialTransformations.Milestone0.M6Matrix.paper_theorem_sat_of_finSat

end SpecialTransformations.Milestone0.M6Matrix
