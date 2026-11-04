# Handoff: the QE thread (state at the Γ(M) completion + §10b adoption + second swarm launch, 2026-11-04)

Read this first if you are picking up Theorem 2.3. Deliberately short; the detail is in
`QE-PLAN.md` (chronology), `Milestone0/DECISION.md` (rulings), `MILESTONES.md` (ledger).

## The route, exactly as it stands

**Frontier (after `QE/FinalRoute.lean`, smw2jkpn4 e8 accepted):** the reduction layer is
COMPLETE — `QE/FinalRoute.lean`'s `paper_theorem_FINAL` proves

```
ShoenfieldTestSat → LedgerInput1P → LedgerInput2 → LedgerInput3P → LedgerInput4P
                  → LedgerInput5P → Hahn.OneStepPaper → HasQE Axioms.ACVF
```

where the conclusion is machine-identified with the frozen target
(`frozen_conclusion_shape`, by `rfl`). Everything on the line to Theorem 2.3 is therefore
exactly these seven hypotheses, each gated at `PaperHyp` (`SaturatedFS N ∧ #M ≤ #N`). The
ledger road here: §10b of `QE/M5Ledger.lean` (adopted by author ruling) — hypotheses 1–5 are the
ledger's five inputs at the paper's pair, plus Shoenfield's test and the `OneStepPaper` gate (the
only one-step shape that survives: `QE/HahnObstruction.lean` machine-refutes both stronger
shapes):

```
ShoenfieldTestSat    RESOLVED as transcription + gate audit (`QE/ShoenfieldQuote.lean`, e1):
                     the book quote is `ShoenfieldTestRel` at `relGate` (pair-relative
                     ‖M‖⁺-saturation); the frozen gate's ∀M `SaturatedFS` is the wrong quantifier
                     order (`SatBridge` = `SatRel → SaturatedFS`, no book supplies it; and if
                     `SaturatedFS` is uninhabited the frozen input 1 IS the target —
                     `shoenfieldTestSat_iff_hasQE_of_no_saturatedFS`, machine-checked). Canonical
                     discharge route is `paper_theorem_2_3_rel` at `relGate`; FINAL's input 1 is
                     DERIVED there (`shoenfieldTestSat_of_relLedger_gated`), and route assembly is
                     gate-polymorphic (`paper_theorem_2_3_of_gate H`)
LedgerInput1P        ACFExtends at PaperHyp (Marker quote; algebraic half consumable
                     via QE/KAlgClosedQuote.lean; universality half: smw2jkpn4 e2)
LedgerInput2         HenselizationExists ∀ M — QUOTED, done (QE/M7Hensel.lean) ✓
LedgerInput3P        ResidueStep at PaperHyp — REAL WORK (inputs 3; m8's exists_standing_superset
                     reduces its closure half to a theorem; embedding extension remains)
LedgerInput4P        DivisibilityStep at PaperHyp — REAL WORK (input 4; PE DivisibleHullExists
                     quoted in ClassicalProps; Γ-divisibility API: smw2jkpn4 e7)
LedgerInput5P        SaturationRealization at PaperHyp (Marker quote: smw2jkpn4 e2)
Hahn.OneStepPaper  ∀∀ PaperHyp → OneStepVFP — the ONLY surviving gate (QE/HahnObstruction.lean
                     machine-refutes `OneStepSizeFree`, and `OneStepSizeBounded` too: size cannot
                     repair the one-step, only saturation can); case-lemmas state: 3.2 ✓,
                     3.7 ✓, separated ✓, atomic transport ✓; assembly combinator + 3.8 value side
                     LANDED (`QE/OneStepCases.lean` `oneStepVFP_of_cases`: three slots — separated /
                     not-separated / new-rv — `caseSeparated_of_RVControl`/`_of_ResidualClasses`
                     discharge forms; `QE/Case38Value.lean`; caveat recorded: `M5L.VFInvClosedOn` is
                     NOT Standing-derivable — no VF-inverse symbol — so the slots omit it);
                     3.4 `lift:all:root` and 3.6 `lift:divisible:hull` open — smw2k0btg f1/f2
```

The join is `prop39Sat_FINAL` + `hShoen`, three lines; the audit also proves each SizeHyp-gated
input implies its PaperHyp form, so the FINAL assumes strictly less than the old frozen shape.
The earlier frozen
`paper_theorem_2_3` route (`ShoenfieldTestSize → PrepStepSize → OneStepSizeFree`) still compiles
but its gates are refuted or under-powered (`QE/M5Ledger.lean` finding: `SizeHyp` does not supply
`#K(M) ≤ #K(N)` that input 1 forces; m7's `HahnObstruction.lean`: size cannot repair the
one-step, only saturation can).

**Why not the older statements:**

* Universally-quantified `∀ M N, PrepStepP` is **refutable as stated** — machine-checked three
  independent ways (`QE/M5OneStep.lean` `units_le_of_prepStepP`, `QE/PaperRoute.lean`
  `prepStepP_forces_units_size` + `prop39FS_forces_size`, and m1's `card_le_of_prop39FS`):
  `KEqTop T` places every unit of M in the embedded substructure, forcing `#Kˣ(M) ≤ #N` at
  arbitrary pairs, which false model pairs violate. The paper fixes `N` `‖M‖⁺`-saturated
  (qe.tex:578) before Lemmas 3.3–3.8; only Lemma 3.3 needs the size hypothesis;
  `OneStepVFP`'s `Standing S` already carries it.
* `QE/Prop39Two.lean` (**valid implication, refuted hypotheses** — header says so, do not treat
  its two hypotheses as open lemmas): Weispfenning is *redundant* on this route — exhausting
  the VF elements exhausts the model (`Assembly.eq_top_of_vf_all`), since the tagged encoding
  has no junk elements in models (`QE/SortCover.lean`, from `sdCover`/`sdDisjoint`), so the
  `VFGenCaseP` instance is proved outright (`Assembly.VFGenCaseP_top`).
* Flagged caveat not machine-checked (would need a concrete model of `Axioms.ACVF`, which the
  tree does not have): m5's AUDIT argues `OneStepVFP` also fails at equal cardinality for
  value-group-dimension reasons (`v(m)/2` must exist in Γ(N)).

## Ingredients state (Lemmas 3.2-3.8)

| item | state |
|---|---|
| 3.2 `rv:root:lift:vf` | Mathlib-level proof done (`QE/Lemma32_root_lifting.lean`); instantiated at a model (`QE/Lemma32_at_model.lean`); **syntactic transport done** (`QE/M6Syntactic.lean`); consumption shape done (`QE/M6Wire*.lean`, chain form `hred` automatic at a root) |
| 3.3 `PrepStepSize` | **assembly ledger landed** (`QE/M5Ledger.lean`, smw2ioy2w m5): five inputs → `Assembly.PrepStepP`; **FINDING: the frozen `SizeHyp` guard is under-powered** — input 1 forces `#K(M) ≤ #K(N)`, which `#M ≤ #N` does not imply (paper gets it from `‖M‖⁺`-saturation). Recommended shape is §10b: `PrepStepPaper` at `PaperHyp`, and `paper_theorem_2_3_sat_of_ledger_paperHyp : ShoenfieldTestSat → five inputs → OneStepSizeFree → HasQE Axioms.ACVF` is proved end-to-end. Inputs now dischargeable: (i) `ACFExtends` — Marker quote consumable (`QE/KAlgClosedQuote.lean`); (ii) henselization quoted (`QE/M7Hensel.lean`). Still to discharge: inputs 3/4 (paper constructions, d6/d7 territory) and 5 (Marker saturation) |
| 3.4/3.6/3.8 | **open** as tagged case lemmas; one-step skeleton in `QE/M5OneStep.lean` (`RVStepP`, `OneStepRV*`, `oneStepVFP_of_two_steps`, `standing_of_RV_le`) |
| 3.5 `lift:divisible:hull` | **open**; the old base had a *vacuous* hypothesis, machine-checked and now fixed (`QE/M8Stars.lean`: `hne`, `exists_rv_vfSum'`) |
| 3.7 `e:transc` | **proved** in the frozen encoding, both former hypotheses discharged (`QE/Lemma37.lean`) |
| Remark 3.1 + Weispfenning | **not needed on this route** (see above) |
| `ShoenfieldTestSize` | **open**; m1 reduced it to classical statements: `QE/M1Fix.lean` (`hasQE_of_qfEAmalg`, `hasQE_of_modelComplete_monoAmalg`); an embedding transfers only QF truth (`qf_realize_embedding`), so Prop39-style monomorphisms alone can never prove QE |

## The frozen target and its integrity

- `Milestone0/Encoding.lean` carries the two frozen `sorry`s: `theorem_2_3_quantifier_elimination`,
  `theorem_2_8_c_minimal`. Everything else in `Milestone0/`, `Milestone0/accepted/`, `QE/` compiles
  green (`make milestones`, full pass). (The one earlier exception, `QE/ValBridge.lean`, was
  removed at `009a684`.)
- The guard repair is **applied** (`86d7ea7e…`): `Occurs := InAntecedent`, `GuardTrue` inductive,
  `junkFalse`/`junkTrue` semantics in `QE/JunkTrue.lean`. Anything copied from
  `QE/Reduction_assembly.lean` (or from `Assembly_val`) is a **pre-repair snapshot** that omits
  the nine `repairRV` axioms and has the old unrestricted `HasQE` — re-check everything compiled
  against it (m6's RVCalc established: `rv(-x)=rv(x)` fails there, works over the frozen axioms).
- `Assembly.PrepStep`/`OneStepVF`/`VFGenCase` bodies never mention the saturation argument
  (`Iff.rfl` against every saturation notion), and `Assembly.Saturated` is too strong to be
  meaningful (it proves Prop 3.9's conclusion outright). Those facts are recorded with
  `Assembly.prepStep_iff` etc. in `QE/Assembly_frozen.lean`.
- Saturation (Frank: `SaturatedFS`) is *not* where the size bound lives, and a pure size bound is
  not sufficient either (value-group dimension). Correct route quantifiers are the paper's own.

## Sections of the paper: what is in the tree

* §3: all 17 items in the tree (`QE/Sec3*`, `Exchange`, `M3AclField`, `M8*`, `BallSec3`,
  `M7Centres`, `AclFibres`, `UniformCover`, `Sec3Corrected`, `Sec3Count`, `Sec3Fibre`). Notable
  hazards recorded there: frozen `IsSetOfCenters` was wrong (function form repaired), frozen
  `SP.AclConstOfFibres` was false (repaired with `A.Nonempty`), `average:0:rv:not:constant`'s
  frozen form is refuted (char-0 needed), `finite:VF:project:RV` now proved at finite `A` with
  target `RV^{n·k}`, and `alg:ind:imag` stands on `M5.ExchangeVF` alone (rv-fibres infinite).
  `QE/Exchange.lean`'s `SwapFinite` is exactly Yin's C-minimality content still owed.
* §4: merged (`Sec4Rename`, `Sec4FibreDim`, `Sec42Morphism`, `M6Polydisc`, `Sec4EK`,
  `Sec4DimACFModel`, plus the breakthrough: **`QE/Compose.lean` — the `DefinableFun` composition
  wall is down**, `comp`/`comp_of_mapsTo`, and `QE/Fibre.lean` first applications, e.g.
  `dimVF_fibre_le`; `QE/Proj.lean` projection lemma). The td non-vacuity model is in.
* §5: `QE/Sec5.lean`.
* §6: `QE/HenS.lean`, `QE/Sec6QE.lean`, `QE/Sec6.lean` (HenS(0,0) + `cut:to:hensel:substru` +
  `hasVFQE_of_step`).
* §7: `QE/Sec7Gamma.lean` (Def 7.1, "some (hence all)" proved), `QE/Sec7GammaHensel.lean`
  (hensel:lemma's proof body), `QE/Sec7Lift.lean`, `QE/Sec7Cor77.lean`.
* §8: `QE/Sec8Points.lean`, `QE/Sec8AlmostCont.lean` + `QE/Sec8Top.lean`
  (`fun:almost:cont` at `closure (DiscSet f)`), `QE/Sec8ValCons.lean`.
* §9: `QE/Sec9Limits.lean`, `QE/Sec9AE.lean`.
* §10: `QE/Sec10.lean`, `QE/Sec10RVVol.lean` (hreduce disclosure kept visible).

## Build/check discipline that has already cost a day, now codified

* `lean FILE.lean` **does not write an olean** in this environment; `lean -o FILE.olean FILE.lean`
  does. A stale olean silently *removes* declarations; build your own constants before judging.
* Run counts with `grep -c ': error'`, never `'error('`.
* Never report a theorem proved without `lean` on the actual file + `#print axioms` ⊆
  {propext, Classical.choice, Quot.sound}. A reminder-trigger retry may re-verify outdated work.
* Do not `import QE/Assembly_val.lean` together with `Enc` (module-name collision: it embeds its
  own copy of the encoding). Port constructions the way `QE/VFField.lean`/`QE/VFValued.lean` did.
* A hypothesis that is its own conclusion is worse than an open lemma. This project has been
  refuted-by-itself at least seven times (`VFGenCase`-sans-saturation, `Saturated`,
  `CoverVF`/`AtomCover`, `IsSetOfCenters`, `SP.AclConstOfFibres`,
  `swl_algebraic_balls_definable_centers`, the unrestricted `HasQE`); every new hypothesis gets the
  cardinality/vacuity stress test BEFORE the verdict, and any "ingredient" file being accepted is
  itself machine-checked for a hidden restatement of its target.
* `.ultramath/<swarm>/` files are unvetted until compiled in the current tree. Oleans for
  `Enc` + the main `QE/` modules live in `.scratch2/sec3/`; work there:
  `cd .scratch2/sec3 && LEAN_PATH=$PWD:$LEAN_PATH lean [-o X.olean] X.lean`.

## smw2ioy2w (2026-11-04, ENDED solved: 5 accepted + 1 salvaged): Γ/K infrastructure and the frontier

Accepted and merged this session: **d1** (`QE/GammaGroup.lean`: `commGroupRVStar`,
`KStar : Subgroup (RVStar M)`, quotient `CommGroup (RVStar ⧸ KStar)` — the paper's Γ(M) as a
group, zero added hypotheses) **plus the order half** (m2's direction was abandoned on budget
*after* delivering: file verified judge-side and merged — `Cls` setoid, `GammaOf M` with
`CommGroup` + `LinearOrder` + `IsOrderedMonoid`, `gamma_isLinearOrderedAbelianGroup`,
`gammaMk_eq_one_iff_units`; **Γ(M) is now a full linearly-ordered abelian group in the tree**),
**d4** (`QE/KAlgClosed.lean` + `QE/KAlgClosedQuote.lean`:
`IsAlgClosed (KOf M)` extracted from the frozen `Axioms.kAlgClosed`; `exists_pow_kOf`;
`ACFExtendsAlgebraicEmbeddings` instantiated at the residue fields) and **d5**
(`QE/M5Ledger.lean`: the complete formal skeleton of Lemma 3.3 — five inputs → `PrepStepP`,
the §10b `PaperHyp` route to `HasQE`, machine-checked vacuity and cardinality audits, and the
Finding that the frozen `SizeHyp` guard is under-powered: input 1 forces a residue-field size
inequality it does not supply; corrected shapes `PrepStepSizeK` and `PrepStepPaper` are in the
file). Judge-verified: exit 0, 0 errors, all `#print axioms` ⊆ {propext, Classical.choice,
Quot.sound}. Oleans `ClassicalProps`, `GammaGroup`, `KAlgClosed`, `M5Ledger` are built into
`.scratch2/sec3/`. Also accepted: **d7/d-ADD** (`QE/RVAdd.lean`, m3 — self-scoped direction): the
valuation-ring layer, hypothesis-free from `Axioms.ACVF` (`O = {1 ≤ rv x}` subring, `m` ideal =
non-units, `rv_inv`, `isInt_or_inv`, equality-form strict triangle `rv_add_eq_of_lt'`, ball
congruences); removed the `w`/`hw` hypotheses `M6Syntactic`/`M6Wire` carried; its item (i) was
machine-checked FALSE (vacuous at VF-elements, value 0 not preserved by `+`) and the corrected
forms were delivered — credited. Hazard note recorded (shared board f9): `VFType M` lacks
`LeftDistribClass`/`RightDistribClass` instances, so `ring`/`mul_sub` fail there — prove
multiplicative facts at the `M` level and transport by `Subtype.ext`. Also accepted: **d6**
(`QE/StandingHull.lean` + `QE/StandingHullRoute.lean`, m8): `standingHull S` — the LEAST
`Standing` superset, built outright in M (closure-operator API, rigidity `units_of_pow_units`),
and `prepStepP_iff_hullExtension`: frozen Lemma 3.3 ⟺ extending monomorphisms to the fixed hull;
its VF/Γ-equality clauses of paper Lemma 3.3 are explicitly NOT claimed. Swarm end state: d2's
order half salvaged and merged (see above); d8 consistency witness abandoned with no output
(relaunched as smw2jkpn4 e6); m7's OneStep-shape files (`Transport.lean`,
`HahnObstruction.lean`) delivered as findings, judge-verification assigned to smw2jkpn4 e8.
Also re-verified: `QE/Assembly_val.lean` green and `hasQE_ACVF_val` axiom-clean — the L_val QE
theorem stands. Author ruling 2026-11-04: Marker/Prestel–Engler quotations remain HYPOTHESES
of the final theorem (the standing convention; the author notes they are 100% reliable math).

## What a new session should do first

1. `git log --oneline -15` and read `MILESTONES.md`'s last two sections (the route diagram).
2. Check running swarms (`ultramath_status`) before starting any: judge any `waiting_for_verdict`
   first. Do not start a fresh swarm over directions with `state: active` unless they are stuck.
3. The QE-critical three: `PrepStepSize` (Lemma 3.3, biggest open), the 3.4/3.5/3.6/3.8 case
   lemmas (skeleton in `QE/M5OneStep.lean`, fixed RV algebra in `QE/M8Stars.lean`), and
   `ShoenfieldTestSize` / `QFEAmalg` / `ModelCompleteRV + MonoAmalg` (form in `QE/M1Fix.lean`).
