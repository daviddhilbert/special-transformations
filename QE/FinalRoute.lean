/-
# FINAL ROUTE: Theorem 2.3 (`qe:acvf`) from the seven hypotheses, at the paper's own pair

Direction **e8** of swarm `smw2jkpn4` (member `m8`).  *No new mathematics*: this file is the
composition of the tree's §10b ledger (`QE/M5Ledger.lean`, author-ruled canonical route shape) with
m7's repaired one-step gate (`OneStepPaper`, from swarm `smw2ioy2w`, file
`.ultramath/smw2ioy2w/m7/HahnObstruction.lean`), plus the audit that the composition introduces no
hypothesis of its own.

The single theorem:

    paper_theorem_FINAL :
      M7Paper.ShoenfieldTestSat → LedgerInput1P → LedgerInput2 → LedgerInput3P →
      LedgerInput4P → LedgerInput5P → M7OneStepPaper → HasQE Axioms.ACVF

and `HasQE Axioms.ACVF` **is** the frozen target: `Milestone0/Encoding.lean:1884`,
`theorem theorem_2_3_quantifier_elimination : HasQE ACVF` (`ACVF` is `Axioms.ACVF`,
`Milestone0/Encoding.lean:1472`), whose proof is still `sorry`.  Discharging the seven hypotheses
would discharge that `sorry` with no change of statement.

## The two halves, and what each replaces

1. **Lemma 3.3 (the prep step) at the paper's pair** — `M5Ledger.prepStepPaper_of_ledger`:
   `LedgerInput1P → LedgerInput2 → LedgerInput3P → LedgerInput4P → LedgerInput5P →
   PrepStepPaper`, i.e. the five steps of `MILESTONES.md` (Marker's ACF extension, Prestel–Engler's
   henselization, and the paper's two construction steps plus Marker's saturation realisation) give
   `Assembly.PrepStepP` at pairs with `M7Paper.PaperHyp M N = SaturatedFS N ∧ #M ≤ #N`.
2. **Lemmas 3.4–3.8 (the one-element step)** — m7's `Hahn.OneStepPaper`, which is
   `Assembly.OneStepVFP` at the same `PaperHyp` pairs and **not** at all pairs: m7 machine-refuted
   the frozen `M7Paper.OneStepSizeFree` (`∀ M N, OneStepVFP`) and the size-only repair
   `∀ M N, SizeHyp M N → OneStepVFP` (`Hahn.not_oneStepSizeFree`, `Hahn.not_oneStepSizeBounded`, at
   any pair carrying `Hahn.RoomObstruction` whose target is `Hahn.ArchimedeanRV`).  So the FINAL uses
   `OneStepPaper`, and this is the *only* difference from `M5Ledger.paper_theorem_2_3_sat_of_ledger_paperHyp`,
   which is recovered from it below (`paper_theorem_2_3_sat_of_ledger_paperHyp_recovered`,
   `Hahn.oneStepPaper_of_free`).

The join is `Assembly.prop39P_noVFGen` (`QE/Prop39Two.lean`): `PrepStepP` + `OneStepVFP` at a fixed
pair give Proposition 3.9 there, and `M7Paper.ShoenfieldTestSat` is exactly
`M7Paper.Prop39Sat → HasQE Axioms.ACVF`.  One instantiation per `PaperHyp` pair — nothing else.

## Hypothesis / owner table (the seven hypotheses of `paper_theorem_FINAL`)

| # | hypothesis (as in the signature) | content | status | owner / route |
|---|---|---|---|---|
| 1 | `M7Paper.ShoenfieldTestSat` | Shoenfield's test *at the paper's pairs*: `Prop39Sat → HasQE Axioms.ACVF`, i.e. "the substructure-extension property (Proposition 3.9) at every `PaperHyp` pair implies quantifier elimination" | **quotable-missing** | direction **e1** (Marker, *Model Theory*, Shoenfield's test): transcribe as a `ClassicalProps`-style `Prop` and prove `quote → ShoenfieldTestSat`.  Note the shape is not Marker's QE criterion out of the box: the hypothesis is *substructure*-extension at every `S ⊆ M`, not "every formula is equivalent to a QF one"; e1 must enumerate what is definitional and what needs a named statement. |
| 2 | `M5Ledger.LedgerInput1P` | `ACFExtends` at `PaperHyp`: for every `S ⊆ M`, `f : S ↪ N` there is a **field** embedding `K(M) → K(N)` agreeing with `f` on `Kˣ(S)` | **half quoting, half missing** | the *algebraic* half is done and consumed: `ClassicalProps.ACFExtendsAlgebraicEmbeddings` via `QE/KAlgClosedQuote.lean` / `KAlgClosed.lean`; the *transcendental* half needs saturated-field universality at `K(N)` — direction **e2(i)**.  This is a *saturation* statement, not ACF model completeness (see `M5Ledger.ACFExtends`'s docstring and the `FINDING` in `M5Ledger`'s header stress test (b)). |
| 3 | `M5Ledger.LedgerInput2` | `M7Hens.HenselizationExists M`: every substructure has an **immediate henselian** extension (`QE/M7Hensel.lean:209`) | **quoted-done** (as a `Prop` def, consumed, never proved) | Prestel–Engler, *Valued Fields* Ch. 5.  Already the tree's own vocabulary; no transcription left.  Used here exactly once (`prepStepPaper_of_ledger`); unlike §10 it is *not* shared with the one-step. |
| 4 | `M5Ledger.LedgerInput3P` | `ResidueStep` at `PaperHyp`: adjoining representatives of all residue classes — `KEqTop T`, `Γ(T) = Γ(S)`, `VF(T) = VF(S)`, and `γ` realised by the extended monomorphism | **real work** | paper Lemma 3.3(2), construction.  In swarm `smw2ioy2w` member m8 showed the *closure* half (`KEqTop`, `Γ`-divisibility, directed unions) is a theorem (`exists_standing_superset`); the remaining content is the **embedding extension**.  Hypothesis-light case analysis: direction **e3**'s ledger feeds here. |
| 5 | `M5Ledger.LedgerInput4P` | `DivisibilityStep` at `PaperHyp`: the divisible hull — `GammaDivisible T` plus `GammaHullInitial S T` (the clamp that forbids `T = ⊤`, `bare_gammaDivisible_trivial`) | **real work** | paper Lemma 3.3(3) + Prestel–Engler divisible hull.  Needs case Lemmas 3.4/3.6 (e3), 3.8 (e4), and the `Γ`-divisibility API (direction **e7**). |
| 6 | `M5Ledger.LedgerInput5P` | `SaturationRealization` at `PaperHyp`: saturated ⟹ homogeneous, so a partial isomorphism of size `< ‖M‖⁺` extends to a bigger domain | **quotable-missing** | direction **e2(ii)** (Marker, saturation/homogeneity).  Note: `LedgerInput5P` is not vacuous (`saturationRealization_refl`) and forces exactly `#M ≤ #N`, the size half of `PaperHyp` (`M5Ledger.saturationRealization_forces_size`). |
| 7 | `M7OneStepPaper` | Lemmas 3.4–3.8 at `PaperHyp` = `Assembly.OneStepVFP` restricted to the paper's pairs (`Hahn.OneStepPaper`, abbrev'd here) | **real work** (the paper's §3.2–§3.3) | 3.2 is in the tree (`QE/Lemma32_at_model`, `M6Wire`), 3.7 is in the tree (`QE/Lemma37`), the separated case is `QE/M5L34_36`; the open case lemmas 3.4/3.6 are direction **e3** and 3.8 + the combinator `oneStepVFP_of_cases` is direction **e4**.  m7's `M7Hens.oneStepVFP_of_hens` already reduces `OneStepSizeFree` to `HenselizationExists` + `ImmediateLift` + the case lemmas at henselian domains. |

So: **1, part of 2, 6 are quotation work**; **3 is already quoted-and-consumed**; **4, 5, 7 are the
paper's real content**.  Nothing in the FINAL is new mathematics: it is `M5Ledger` §10b plus m7's
gate, glued at `Assembly.prop39P_noVFGen`.

### Is hypothesis 1 circular?

No more than in any other route in the tree.  `hShoen` is applied **once**, to
`prop39Sat_FINAL`'s output, and `M7Paper.ShoenfieldTestSat` is a statement about the *theory*
`ACVF` — Shoenfield's criterion, "the substructure-extension property at every `PaperHyp` pair
implies quantifier elimination" — not a restatement of `HasQE`.  It is consumed exactly as in
`M7Paper.paper_theorem_2_3_sat` (`QE/PaperRoute.lean`) and `M7PaperHyp.paper_theorem_2_3_FS`.  What
e1 must supply is the transcription of Marker's criterion plus the proof that `Prop39Sat` is the
hypothesis that criterion needs; the FINAL neither proves it nor strengthens it.  Its two halves —
`PrepStepPaper` (Lemma 3.3) and `M7OneStepPaper` (Lemmas 3.4–3.8) — are the paper's Section 3
content and contain no `HasQE`.

## The import obstacle this file had to solve (machine-reproduced, please read)

m7's `HahnObstruction.lean` starts `import PRCopy`, where `.ultramath/smw2ioy2w/m7/PRCopy.lean` is a
**byte-identical copy** of `QE/PaperRoute.lean` (sha256 `98360e92…5fd1`, checked in this directory).
`PRCopy` and `PaperRoute` *declare the same constants*, so Lean rejects both in one environment:

    $ cat clashprobe.lean
    import HahnObstruction
    import M5Ledger
    $ LEAN_PATH=… lean clashprobe.lean
    clashprobe.lean:1:0: error: import PaperRoute failed, environment already contains
    'SpecialTransformations.Milestone0.M7Paper.Prop39Size' from PRCopy

`M5Ledger` imports `PaperRoute`.  Any member composing m7's file with the tree's ledger hits this.
Fix used here: build m7's file against a one-line **shim** `m7route/PRCopy.lean` = `import PaperRoute`,
i.e. the module `PRCopy` reduced to the import of the canonical tree module.  m7's `Transport.lean`
and `HahnObstruction.lean` are compiled in `m7route/` as **byte-identical copies** of m7's text
(sha256 recorded in `VERIFICATION.md`), so the verification is of m7's file, with the stronger side
condition that it must also elaborate against the tree's own `PaperRoute` rather than against a copy.
The standalone route (`m7verify/`, m7's own copy) is verified too; both are green.

## Stress tests run below

* (a) *Conclusion is the frozen target*, not a variant: `frozen_conclusion_shape`.
* (b) *The `PaperHyp` gates are strictly weaker than the frozen §9 gates*:
  `ledgerInput{1,3,4,5}P_of_ledgerInput{1,3,4,5}` — every `P`-input follows from its `SizeHyp`
  version, so the FINAL assumes no more than the tree's §9 ledger at each of the five.
* (c) *No hidden stronger gate on the one-step*: `oneStepPaper_of_free` (m7) shows the gate is
  weaker than the frozen `OneStepSizeFree`; `oneStepSizeBounded_of_free` + `oneStepPaper_of_sizeBounded`
  show the three shapes are nested; `oneStepSizeFree_refutable` / `oneStepSizeBounded_refutable`
  (m7, conditional on an infinitesimal configuration) show the two stronger shapes are *false*, so
  the restriction to `PaperHyp` is not cosmetic.
* (d) *The FINAL recovers the documented routes*: `paper_theorem_2_3_sat_of_ledger_paperHyp_recovered`
  is `M5Ledger` §10b verbatim (`OneStepSizeFree` in place of the gate), and
  `paper_theorem_2_3_sat_of_ledger_drops_two` is `M5Ledger` §10's route **with its `ImmediateLift`
  and one-step-at-henselian-domains hypotheses discarded** — those two are not needed here.
* (e) *The gate is exactly `PaperHyp`, and it is not cardinally refutable*: `paperHyp_unfold`
  (`SaturatedFS N ∧ #M ≤ #N`), `final_gate_supplies_units_size` (what `PrepStepP`'s `KEqTop`
  forces, `M7Paper.prepStepP_forces_units_size`), `final_input1_forces_residue_size`,
  `final_input3_forces_units_size`, `final_input5_forces_size` (each input's own cardinality
  content; input 4 forces nothing, see `final_input3_forces_units_size`'s docstring).
* (f) *No duplicated hypothesis*: `FinalHyp` packages the seven as a 7-fold conjunction with a
  round-trip (`parts_of_finalHyp`, `finalHyp_of_parts`), so the hypothesis set is counted, not
  prose: each conjunct is consumed **once** (`h2` once by `prepStepPaper_of_ledger`, whereas §10's
  chain consumes it twice, ledger + one-step).  This is a counting statement, **not** an
  independence statement: nothing here shows that `OneStepPaper` is not derivable from
  `h1`–`h5`; refuting that would need the concrete models direction e6 does not yet have.

## What the FINAL does *not* do (read this before quoting it)

* It does **not** discharge any of the seven hypotheses; it is a conditional theorem, exactly like
  every other route in the tree.  What it establishes is that the seven are *enough*, and that no
  eighth is needed.
* It does **not** prove that the seven are jointly satisfiable: the tree still has no model of
  `Axioms.ACVF` (`axNontrivialRV` excludes the trivial valuation), so `Assembly.SaturatedFS N` is
  not known to be inhabited at any `N ⊨ Axioms.ACVF`.  That is direction **e6**, and until it lands
  the FINAL is a reduction, not a proof of consistency.  (This is *not* a defect of the composition:
  the same gap sits under every earlier route, including the frozen `Assembly` chain.)
* It does **not** prove `SaturatedFS N → #K(M) ≤ #K(N)` (input 1's own size content, see
  `final_input1_forces_residue_size` and `M5Ledger`'s header `FINDING`).  So the residual on input 1
  is exactly: at a `PaperHyp` pair, saturated-field universality/homogeneity must supply the
  residue-field embedding — direction **e2(i)**.  Nothing in this file hides that.
* It does **not** reprove `M5Ledger` §10b, m7's `HahnObstruction`, or `Assembly.prop39P_noVFGen`:
  those are imported.  What is new here is only the join (`prop39Sat_FINAL`), the gate audit, and
  the import fix below.

## Verification

`lean` exit 0, 0 `error` lines, no `sorry`/`admit`/`native_decide`/new `axiom`,
`#print axioms` of every head theorem ⊆ `{propext, Classical.choice, Quot.sound}` — real outputs at
the end of the file.  Build command (from the repository root):

    cd .ultramath/smw2jkpn4/m8
    export LEAN_PATH="$PWD/m7route:$PWD:$R/.scratch2/sec3:$LEAN_PATH"
    lean -o m7route/PRCopy.olean m7route/PRCopy.lean      # shim
    lean -o m7route/Transport.olean m7route/Transport.lean
    lean -o m7route/HahnObstruction.olean m7route/HahnObstruction.lean
    lean FinalRoute.lean

(`$R` = the repository root; the shared oleans live in `$R/.scratch2/sec3`.)
-/
import HahnObstruction
import M5Ledger

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations
namespace Milestone0
namespace FinalRoute

/-! ### 0. m7's gate, re-exported under the name the FINAL uses

`Hahn.OneStepPaper` is *literally* `Assembly.OneStepVFP` restricted to `M7Paper.PaperHyp` pairs
(`HahnObstruction.lean` §5).  The `abbrev` is only a renaming; `M7OneStepPaper_eq` is the
machine-checked statement that no definition is hidden behind it. -/

/-- **m7's repaired one-step gate** (`Hahn.OneStepPaper`): Lemmas 3.4–3.8 at the paper's pairs. -/
abbrev M7OneStepPaper : Prop := Hahn.OneStepPaper

/-- The renaming hides no definition: `M7OneStepPaper` *is* m7's `OneStepPaper`. -/
theorem M7OneStepPaper_eq : M7OneStepPaper = Hahn.OneStepPaper := rfl

/-- And its gate is exactly the paper's: unfolding the gate gives `SaturatedFS N ∧ #M ≤ #N`. -/
theorem oneStepPaper_gate_shape :
    M7OneStepPaper =
      (∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
        M7Paper.PaperHyp M N → Assembly.OneStepVFP (M := M) (N := N)) := rfl

/-! ### 1. Proposition 3.9 at the paper's pair, from the prep step and the one-step

This is the whole join: `Assembly.prop39P_noVFGen` at a pair where *both* halves are available.
It is m7's `Hahn.prop39Sat_of_paper` with `M7Paper.PrepStepSize` (Lemma 3.3 gated at `SizeHyp`)
replaced by `M5Ledger.PrepStepPaper` (the same lemma gated at `PaperHyp`, produced by the five
inputs).  The gate is the same in both halves, which is why no hypothesis has to be moved. -/

/-- **Proposition 3.9 (`lrv:mono:lift`) at the paper's pairs**, from Lemma 3.3 there and
Lemmas 3.4–3.8 there. -/
theorem prop39Sat_FINAL (hPrep : M5Ledger.PrepStepPaper) (hOne : M7OneStepPaper) :
    M7Paper.Prop39Sat :=
  fun M N _ _ _ _ hP S f =>
    Assembly.prop39P_noVFGen (hPrep M N hP) (hOne M N hP) S f

/-! ### 2. The FINAL theorem -/

/-- **Theorem 2.3 (`qe:acvf`) — the FINAL ROUTE.**

Shoenfield's test at the paper's pairs, plus the five inputs of `M5Ledger` §10b (Lemma 3.3
decomposed) and the one-step gate, give `HasQE Axioms.ACVF` — the statement of the frozen
`theorem_2_3_quantifier_elimination` (`Milestone0/Encoding.lean:1884`).

The proof is three lines because the content is in the two halves: the §10b ledger turns the five
inputs into `PrepStepPaper`, `prop39Sat_FINAL` joins it with the one-step into `Prop39Sat`, and
Shoenfield's test closes.  No saturation, size or henselization hypothesis is introduced here. -/
theorem paper_theorem_FINAL (hShoen : M7Paper.ShoenfieldTestSat)
    (h1 : M5Ledger.LedgerInput1P) (h2 : M5Ledger.LedgerInput2)
    (h3 : M5Ledger.LedgerInput3P) (h4 : M5Ledger.LedgerInput4P)
    (h5 : M5Ledger.LedgerInput5P) (hOne : M7OneStepPaper) :
    HasQE Axioms.ACVF :=
  hShoen (prop39Sat_FINAL (M5Ledger.prepStepPaper_of_ledger h1 h2 h3 h4 h5) hOne)

/-! ### 3. Stress test (a): the conclusion is the frozen target's statement -/

/-- The FINAL's conclusion is the frozen file's conclusion: `HasQE Axioms.ACVF`, `Axioms.ACVF`
being the theory of `Milestone0/Encoding.lean:1472` and `HasQE` its `Milestone0/Encoding.lean:1793`.
Fully qualified on both sides so that an accidental shadowing of `HasQE`/`Axioms.ACVF` would be
caught by the `rfl`. -/
theorem frozen_conclusion_shape :
    (HasQE Axioms.ACVF) =
      (SpecialTransformations.Milestone0.HasQE
        SpecialTransformations.Milestone0.Axioms.ACVF) := rfl

/-! ### 4. Stress test (b): each `P`-input is *weaker* than the tree's §9 input

`M5Ledger` §9 states the five inputs at the frozen guard `SizeHyp`; §10b at `PaperHyp`, which
contains it.  So each §9 input implies its §10b version — the FINAL never assumes more than the
ledger at the frozen guard would.  (The converse fails, and that failure is the point of §10b:
`M5Ledger`'s header stress test (b) shows `SizeHyp` does not imply `#K(M) ≤ #K(N)`, which input 1
forces.) -/

theorem ledgerInput1P_of_ledgerInput1 (h : M5Ledger.LedgerInput1) : M5Ledger.LedgerInput1P :=
  fun M N _ _ _ _ hP => h M N hP.2

theorem ledgerInput3P_of_ledgerInput3 (h : M5Ledger.LedgerInput3) : M5Ledger.LedgerInput3P :=
  fun M N _ _ _ _ hP => h M N hP.2

theorem ledgerInput4P_of_ledgerInput4 (h : M5Ledger.LedgerInput4) : M5Ledger.LedgerInput4P :=
  fun M N _ _ _ _ hP => h M N hP.2

theorem ledgerInput5P_of_ledgerInput5 (h : M5Ledger.LedgerInput5) : M5Ledger.LedgerInput5P :=
  fun M N _ _ _ _ hP => h M N hP.2

/-- The same on the *prep-step* half: `M5Ledger.PrepStepPaper` (Lemma 3.3 at `PaperHyp`) follows
from `M7Paper.PrepStepSize` (Lemma 3.3 at the frozen `SizeHyp`).  So both halves of the FINAL are
weaker than the corresponding frozen obligations, and the FINAL assumes nothing the merged tree did
not already assume. -/
theorem prepStepPaper_of_prepStepSize (h : M7Paper.PrepStepSize) : M5Ledger.PrepStepPaper :=
  fun M N _ _ _ _ hP => h M N hP.2

/-! ### 5. Stress test (c): the one-step gates are nested, and the two stronger ones are false -/

/-- The frozen shape implies the size-bounded shape (m7). -/
theorem oneStepSizeBounded_of_free (h : M7Paper.OneStepSizeFree) : Hahn.OneStepSizeBounded :=
  Hahn.oneStepSizeBounded_of_free h

/-- The size-bounded shape implies the paper-pair shape (m7). -/
theorem oneStepPaper_of_sizeBounded (h : Hahn.OneStepSizeBounded) : M7OneStepPaper :=
  Hahn.oneStepPaper_of_sizeBounded h

/-- **The FINAL's gate is weaker than the frozen one** — so replacing `OneStepSizeFree` by
`M7OneStepPaper` in the FINAL is a weakening, not a strengthening. -/
theorem oneStepPaper_of_free (h : M7Paper.OneStepSizeFree) : M7OneStepPaper :=
  Hahn.oneStepPaper_of_free h

/-- **The frozen `OneStepSizeFree` is false** at any pair carrying m7's infinitesimal
configuration whose target is Archimedean.  (Conditional: the tree has no concrete model of
`Axioms.ACVF`, so the Hahn-field pair is a citation — see m7's module docstring, stress test (e);
this is the reason the FINAL cannot use the frozen gate.) -/
theorem oneStepSizeFree_refutable {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : Hahn.RoomObstruction M N) (hArch : Hahn.ArchimedeanRV N) :
    ¬ M7Paper.OneStepSizeFree :=
  Hahn.not_oneStepSizeFree h hArch

/-- The size-bounded repair is false too, so it is **not** the size half of `PaperHyp` that repairs
the one-step: only the saturation half can. -/
theorem oneStepSizeBounded_refutable {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : Hahn.RoomObstruction M N) (hArch : Hahn.ArchimedeanRV N) (hSize : M7Paper.SizeHyp M N) :
    ¬ Hahn.OneStepSizeBounded :=
  Hahn.not_oneStepSizeBounded h hArch hSize

/-! ### 6. Stress test (d): the FINAL recovers the documented routes

Two recoveries, each with *fewer* hypotheses than the theorem it reproduces. -/

/-- **`M5Ledger` §10b recovered** (`paper_theorem_2_3_sat_of_ledger_paperHyp`): with the frozen
`OneStepSizeFree` in place of the paper-pair gate, the FINAL is literally the §10b theorem.  So the
only difference between the FINAL and the merged route is the one-step gate. -/
theorem paper_theorem_2_3_sat_of_ledger_paperHyp_recovered
    (hShoen : M7Paper.ShoenfieldTestSat)
    (h1 : M5Ledger.LedgerInput1P) (h2 : M5Ledger.LedgerInput2)
    (h3 : M5Ledger.LedgerInput3P) (h4 : M5Ledger.LedgerInput4P)
    (h5 : M5Ledger.LedgerInput5P) (hOne : M7Paper.OneStepSizeFree) :
    HasQE Axioms.ACVF :=
  paper_theorem_FINAL hShoen h1 h2 h3 h4 h5 (oneStepPaper_of_free hOne)

/-- **`M5Ledger` §9–§10's route recovered from the §9 inputs**: the five inputs at the frozen
`SizeHyp` guard and the frozen one-step already give `HasQE`. -/
theorem paper_theorem_2_3_sat_of_ledger_recovered
    (hShoen : M7Paper.ShoenfieldTestSat)
    (h1 : M5Ledger.LedgerInput1) (h2 : M5Ledger.LedgerInput2)
    (h3 : M5Ledger.LedgerInput3) (h4 : M5Ledger.LedgerInput4)
    (h5 : M5Ledger.LedgerInput5) (hOne : M7Paper.OneStepSizeFree) :
    HasQE Axioms.ACVF :=
  paper_theorem_2_3_sat_of_ledger_paperHyp_recovered hShoen
    (ledgerInput1P_of_ledgerInput1 h1) h2 (ledgerInput3P_of_ledgerInput3 h3)
    (ledgerInput4P_of_ledgerInput4 h4) (ledgerInput5P_of_ledgerInput5 h5) hOne

/-- **The two extra hypotheses of `M5Ledger.paper_theorem_2_3_sat_of_ledger` are not needed.**
This is that theorem's exact hypothesis list — `ImmediateLift` and Lemmas 3.4–3.8 *at henselian
domains* included — with the two passed to the FINAL route as `_hL`, `_hOneHens` and **ignored**.
Hence the FINAL's hypothesis set is not stronger than the documented §10 route's: it is that set
with two elements deleted and nothing added. -/
theorem paper_theorem_2_3_sat_of_ledger_drops_two
    (hShoen : M7Paper.ShoenfieldTestSat)
    (h1 : M5Ledger.LedgerInput1) (h2 : M5Ledger.LedgerInput2)
    (h3 : M5Ledger.LedgerInput3) (h4 : M5Ledger.LedgerInput4)
    (h5 : M5Ledger.LedgerInput5)
    (_hL : M7Hens.ImmediateLift)
    (_hOneHens : ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF]
      [Q ⊨ Axioms.ACVF] (S : LRV.Substructure P) (f : S ↪[LRV] Q),
      Assembly.Standing S → M7Hens.IsHenselianVF S → ∀ m : P, iVF m →
        ∃ (T : LRV.Substructure P) (g : T ↪[LRV] Q) (hST : S ≤ T),
          (∀ x : S, g ⟨(x : P), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T)
    (hOne : M7Paper.OneStepSizeFree) :
    HasQE Axioms.ACVF :=
  paper_theorem_2_3_sat_of_ledger_recovered hShoen h1 h2 h3 h4 h5 hOne

/-- **Agreement with m7's own route** (`Hahn.paper_theorem_2_3_sat_of_paper`): Lemma 3.3 at the
frozen `SizeHyp` plus the paper-pair one-step also gives `HasQE` through the FINAL's join, so the two
compositions of the same two halves agree — the FINAL adds no strength to m7's statement, it only
re-gates the prep half at the paper's pair. -/
theorem m7_route_recovered (hShoen : M7Paper.ShoenfieldTestSat) (hPrep : M7Paper.PrepStepSize)
    (hOne : M7OneStepPaper) : HasQE Axioms.ACVF :=
  hShoen (prop39Sat_FINAL (prepStepPaper_of_prepStepSize hPrep) hOne)

/-! ### 7. Stress test (e): the gate is exactly `PaperHyp`, and it is not cardinally refutable -/

/-- The gate of every `P`-input and of the one-step is the paper's own: `SaturatedFS N ∧ #M ≤ #N`. -/
theorem paperHyp_unfold {M N : Type} [LRV.Structure M] [LRV.Structure N] :
    (M7Paper.PaperHyp M N ↔ Assembly.SaturatedFS N ∧ Cardinal.mk M ≤ Cardinal.mk N) :=
  Iff.rfl

/-- **The gate supplies the size content that `PrepStepP` forces.**  `Assembly.PrepStepP`'s
`Standing` conclusion puts every unit of `M` into `T` and embeds `T` into `N`, so it forces
`#Kˣ(M) ≤ #N` (`M7Paper.prepStepP_forces_units_size`); `PaperHyp` supplies exactly that.  Same for
the one-step, whose `Standing S` hypothesis forces the same bound
(`M7Paper.standing_forces_units_size`). -/
theorem final_gate_supplies_units_size {M N : Type} [LRV.Structure M] [LRV.Structure N]
    (h : M7Paper.PaperHyp M N) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N :=
  M7Paper.paperHyp_supplies_units_size h

/-- What input 1 forces: `#K(M) ≤ #K(N)` (an injective ring hom out of a field).  At `PaperHyp`
this is *not* supplied by the size half alone — it is what saturated-field universality must give
(e2(i)); recorded here so the residual is visible, not hidden. -/
theorem final_input1_forces_residue_size {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : M5Ledger.ACFExtends (M := M) (N := N)) (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    Cardinal.mk (StandingField.KOf M) ≤ Cardinal.mk (StandingField.KOf N) :=
  M5Ledger.acfExtends_field_size h S f

/-- What input 5 forces: `#M ≤ #N`, the size half of `PaperHyp` — the frozen `SizeHyp`, so the
saturation input cannot be applied at a pair where the gate fails. -/
theorem final_input5_forces_size {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : M5Ledger.SaturationRealization (M := M) (N := N)) (S : LRV.Substructure M)
    (f : S ↪[LRV] N) : Cardinal.mk M ≤ Cardinal.mk N :=
  M5Ledger.saturationRealization_forces_size h S f

/-- What input 3 forces, and that the gate supplies it: `ResidueStep`'s conclusion carries
`Assembly.KEqTop T` (every unit of `M` is in `T`) and an embedding `g : T ↪[LRV] N`, so it forces
`#Kˣ(M) ≤ #N` — the same bound `Assembly.PrepStepP` forces
(`M7Paper.prepStepP_forces_units_size`) and the bound `final_gate_supplies_units_size` extracts from
`PaperHyp`.  (Input 4's conclusion forces nothing: its `T ⊇ S` starts from an arbitrary `S`, and the
only `S` that would force `#M ≤ #N` is `⊤`, for which the tree does not derive `IsHenselianVF ⊤`.
So no cardinality audit is available for input 4 and none is needed.) -/
theorem final_input3_forces_units_size {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : M5Ledger.ResidueStep (M := M) (N := N)) (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (γ : StandingField.KOf M →+* StandingField.KOf N)
    (hagree : ∀ (x : S) (hx : iUnits (x : M)),
      (γ ⟨(x : M), Or.inl hx⟩ : StandingField.KOf N).1 = f x)
    (hhen : M7Hens.IsHenselianVF S) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N := by
  obtain ⟨T, g, _hST, _hag, hKEq, _hΓ, _hVF, _hγ⟩ := h S f γ hagree hhen
  refine Cardinal.mk_le_of_injective (f := fun x : {x : M // iUnits x} =>
    g ⟨x.1, hKEq x.1 x.2⟩) ?_
  intro a b hab
  have h2 : (⟨a.1, hKEq a.1 a.2⟩ : T) = ⟨b.1, hKEq b.1 b.2⟩ := Embedding.injective g hab
  exact Subtype.ext (congrArg (fun y : T => (y : M)) h2)

/-! ### 8. Stress test (f): the seven hypotheses are counted, not prose

`FinalHyp` is the seven-fold conjunction.  The round-trip below shows the packaging neither drops
nor duplicates a conjunct, and `paper_theorem_FINAL_flat` is the FINAL at the packaged form (the
shape in which the swarm's remaining obligations can be listed one by one). -/

/-- The FINAL's hypothesis set, packaged. -/
def FinalHyp : Prop :=
  M7Paper.ShoenfieldTestSat ∧ M5Ledger.LedgerInput1P ∧ M5Ledger.LedgerInput2 ∧
    M5Ledger.LedgerInput3P ∧ M5Ledger.LedgerInput4P ∧ M5Ledger.LedgerInput5P ∧ M7OneStepPaper

/-- Projection: the seven parts of `FinalHyp`, each recoverable. -/
theorem parts_of_finalHyp (h : FinalHyp) :
    M7Paper.ShoenfieldTestSat ∧ M5Ledger.LedgerInput1P ∧ M5Ledger.LedgerInput2 ∧
      M5Ledger.LedgerInput3P ∧ M5Ledger.LedgerInput4P ∧ M5Ledger.LedgerInput5P ∧
        M7OneStepPaper :=
  h

/-- Grouping: the seven parts give back `FinalHyp`, so no conjunct is lost in the packaging. -/
theorem finalHyp_of_parts
    (h0 : M7Paper.ShoenfieldTestSat) (h1 : M5Ledger.LedgerInput1P)
    (h2 : M5Ledger.LedgerInput2) (h3 : M5Ledger.LedgerInput3P)
    (h4 : M5Ledger.LedgerInput4P) (h5 : M5Ledger.LedgerInput5P) (h6 : M7OneStepPaper) :
    FinalHyp :=
  ⟨h0, h1, h2, h3, h4, h5, h6⟩

/-- The FINAL at the packaged hypothesis set. -/
theorem paper_theorem_FINAL_flat (h : FinalHyp) : HasQE Axioms.ACVF :=
  paper_theorem_FINAL h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2

end FinalRoute
end Milestone0
end SpecialTransformations

#print axioms SpecialTransformations.Milestone0.FinalRoute.M7OneStepPaper_eq
#print axioms SpecialTransformations.Milestone0.FinalRoute.oneStepPaper_gate_shape
#print axioms SpecialTransformations.Milestone0.FinalRoute.prop39Sat_FINAL
#print axioms SpecialTransformations.Milestone0.FinalRoute.paper_theorem_FINAL
#print axioms SpecialTransformations.Milestone0.FinalRoute.frozen_conclusion_shape
#print axioms SpecialTransformations.Milestone0.FinalRoute.ledgerInput1P_of_ledgerInput1
#print axioms SpecialTransformations.Milestone0.FinalRoute.ledgerInput3P_of_ledgerInput3
#print axioms SpecialTransformations.Milestone0.FinalRoute.ledgerInput4P_of_ledgerInput4
#print axioms SpecialTransformations.Milestone0.FinalRoute.ledgerInput5P_of_ledgerInput5
#print axioms SpecialTransformations.Milestone0.FinalRoute.prepStepPaper_of_prepStepSize
#print axioms SpecialTransformations.Milestone0.FinalRoute.oneStepSizeBounded_of_free
#print axioms SpecialTransformations.Milestone0.FinalRoute.oneStepPaper_of_sizeBounded
#print axioms SpecialTransformations.Milestone0.FinalRoute.oneStepPaper_of_free
#print axioms SpecialTransformations.Milestone0.FinalRoute.oneStepSizeFree_refutable
#print axioms SpecialTransformations.Milestone0.FinalRoute.oneStepSizeBounded_refutable
#print axioms SpecialTransformations.Milestone0.FinalRoute.paper_theorem_2_3_sat_of_ledger_paperHyp_recovered
#print axioms SpecialTransformations.Milestone0.FinalRoute.paper_theorem_2_3_sat_of_ledger_recovered
#print axioms SpecialTransformations.Milestone0.FinalRoute.paper_theorem_2_3_sat_of_ledger_drops_two
#print axioms SpecialTransformations.Milestone0.FinalRoute.m7_route_recovered
#print axioms SpecialTransformations.Milestone0.FinalRoute.paperHyp_unfold
#print axioms SpecialTransformations.Milestone0.FinalRoute.final_gate_supplies_units_size
#print axioms SpecialTransformations.Milestone0.FinalRoute.final_input1_forces_residue_size
#print axioms SpecialTransformations.Milestone0.FinalRoute.final_input5_forces_size
#print axioms SpecialTransformations.Milestone0.FinalRoute.final_input3_forces_units_size
#print axioms SpecialTransformations.Milestone0.FinalRoute.parts_of_finalHyp
#print axioms SpecialTransformations.Milestone0.FinalRoute.finalHyp_of_parts
#print axioms SpecialTransformations.Milestone0.FinalRoute.paper_theorem_FINAL_flat
#print SpecialTransformations.Milestone0.FinalRoute.paper_theorem_FINAL
