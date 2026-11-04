# Milestone check (verified, not quoted from the plan)

Every number below was produced in this session by running `lean` on the file, counting **all**
error lines (`grep -c error`, which catches Lean's uncoded errors) and warning lines
`declaration uses 'sorry'`.  Re-run with `make milestones` (see the Makefile).

## The milestone list

From `HANDOFF.md` — Milestones 0–5 cover the paper's Sections 4–10; Theorem 2.3 (QE) and Theorem 2.8
(C-minimality) are **cross-cutting** and tracked in `QE-PLAN.md`.

| # | milestone | paper | state |
| --- | --- | --- | --- |
| 0 | language and syntax | §2 | **done** (statements frozen) |
| 1 | algebraic layer: `vrv`, exact sequence, balls, polydiscs, valuative centre | §3–§4 | **done for the intended model**; the abstract route from `gammaAxioms` is blocked (see below) |
| 2 | definable sets and dimensions: `acl`/`dcl`, `dimVF`/`dimRV`/`dimfib`, 4.2/4.4/4.6, `VF[k,·]`/`RV[k,·]`, `L`, Grothendieck semigroups | §4 | **most of it, in the tree** (`QE/Sec4Dim.lean`, `Sec4Categories.lean`, `Sec4Polydisc.lean`, `Sec4Pair.lean`): `dimVF` with its layer, `dim:RV:fibers` proved from Yin 4.10 + compactness, the categories `VF[k,·]`/`RV[k,·]` with weight and `E_k`, `full:dim:open:poly`'s two directions at the base.  Absent: the lift `L`, the Grothendieck semigroups, `dimfib`, and the general "only if" of `full:dim:open:poly` |
| 3 | special bijections: 5.1, 5.4, 5.5, 5.6, 5.7 | §5 | **scaffold green and now in the tree** (`QE/Sec5.lean`); 5.2/5.4/5.5 are statements |
| 4 | lifting functions: Hensel 7.2, Thm 7.6, Cor 7.7 | §7 | **nothing** |
| 5 | differentiation and volume forms: 9.1–9.14, 9.16, 10.4, 10.5, 10.6 | §9–§10 | **nothing** |
| — | **Theorem 2.3 (QE)** | §2 | the bulk of the work; see the last section |
| — | Theorem 2.8 (C-minimality) | §2 | statement only |

## What was measured

| directory | files | green | errors | `sorry` warnings |
| --- | --- | --- | --- | --- |
| `Milestone0/*.lean` | 6 | **6** | 0 | 3 (`Encoding` 2 — the two frozen targets; `Balls` 1) |
| `Milestone0/accepted/*.lean` | 10 | **10** | 0 | 0 |
| `QE/*.lean` | 47 | **47** | 0 | 16 |
| `SpecialTransformations/*.lean` | 11 | — | — | stubs, 221 lines in total; `Main.lean`'s table is honest: every paper item "not started" |

Two claims in the repository were **false** and are corrected in the commit that adds this file:

* `HANDOFF.md` and `README.md` said "Everything compiles; no theorem is proved yet".  The second half
  is plainly false (`Milestone0/accepted/` is ~19 000 lines of model-building with no `sorry`, and
  `QE/` has 45 green files), and the first half was false in the sense that `make milestone0` and
  `make qe` did not run at all: `Milestone0/Saturation.lean` and most of `QE/` import `Enc`, and the
  Makefile called `lean` with no search path, so the `Enc` olean was never in scope.  Both targets
  now build `Enc` first and pass `LEAN_PATH`; `make qe` also picks up the `QE/Sec3_draft.lean` that
  had silently stopped compiling (missing `open LRV` after `WellSorted` moved into `LRV`).
* `SpecialTransformations/Main.lean` said Theorem 2.3 "not started".  It is stated and half reduced —
  see below.

## Milestone by milestone

**Milestone 0 — done, and better than "statements frozen".**  `Milestone0/Encoding.lean` (2468 lines)
has `L_RV`, `ACVF`, `ACVF_S(0,0)`, the two target statements, and the audit that `ACVF`'s axioms are
well-sorted; the two `sorry`s are exactly `theorem_2_3_quantifier_elimination` and
`theorem_2_8_c_minimal`.  `Tagging`, `RVModel`, `Partiality`, `Saturation` add the tagging
convention, the intended model, the partiality/junk conventions and the saturation interface, all
green with no `sorry`.  `Balls.lean` has the C-relation and one `sorry`
(`infinite_boolComb_contains_openBall`, which Theorem 2.8 needs and Theorem 2.3 does not).
`Milestone0/accepted/` is ten standalone model-building snapshots (≈19 000 lines): `ACVFModel`,
`ACVF_general_model`, `ACVF_residue_ops`, `IntendedModel`, `Obstruction`, `RepairedTheory`, … — the
models that make the axiom checks non-vacuous.

**Milestone 1 — the exact sequence IS proved, and this row of the check was wrong the first time.**
`Milestone0/accepted/IntendedModel.lean` (green, no `sorry`) *is* the exact sequence, for the intended
model built from a Mathlib `Valuation`:

| what | where |
| --- | --- |
| `vrv : RV v → Γ₀`, `vrv_none`, `vrv_some`, `vrv_mk`, `vrv_rv` | `IntendedModel.lean:701-726` |
| `vrv_mul : vrv (rvMul t s) = vrv t * vrv s` | `:728` |
| `vrv_range : (∃ t, vrv t = γ) ↔ ∃ x, v x = γ` — `vrv` is onto | `:737` |
| `vrv_kernel : vrv t = 1 ↔ t` is a residue unit | `:752` |
| `rvLe` induced by `vrv`, `le_iff`, `lt_iff`, `le_class_of_one_iff` | `:778-798` |

and the same four facts are proved in `ACVF_fragment`, `ACVF_gamma_padic`, `ACVF_general_model`,
`ACVF_general_model_gamma`, `ACVF_residue_ops` — six independent snapshots, all green.

**What is *not* available is the abstract version**, and it cannot be, from the frozen `gammaAxioms`:
they link `Γ` to `RV` only by units-multiplicativity (`gVrvMul`, guarded by `uUnits ⊓ uUnits`), the
kernel criterion (`gVrvEq`), and the order (`gLeVrv`).  There is **no** axiom making `vrv` additive on
all of `RV ∖ {0}`, **no** axiom `vrv u = ⊤ → u = 0`, and **no** surjectivity axiom onto `Γ`.  So a
theorem "the exact sequence holds in every model of `ACVF00Γ`" is not derivable; the concrete route
above is the content, and if the abstract version is wanted the axiomatisation has to grow.  (This is
the same species as the two earlier encoding defects: the axioms are weaker than the paper's item 5,
which says `Γ` *is* the quotient.)

Part 4 of
`Encoding.lean` has the expansion `LRVΓ = LRV.sum LΓ`, `gVrv`, `pMemGamma`, and the `Γ` axioms
(`gammaAxioms`), which is the vocabulary `vrv` needs; balls are `IsBall`/`IsClosedBall`/`IsOpenBall`
in Part 7 and the C-relation in `Balls.lean`; the `rv`-ball is `Sec3.rvBall`; a centre is
`Sec3.IsCentreOf`; polydiscs and `rv`-hulls exist only in the §5 scaffold (Milestone 3 below).
**Missing:** `vrv` as a function with its exact sequence `1 → Kˣ/(1+M) → RV → Γ → 0`, and the
valuative-centre theory as statements.

**Milestone 2 — only `acl`/`dcl`.**  `QE/Sec3_frozen.lean` defines `SP` (sorted parameter pairs),
`acl`, `dcl`, `DefinableVF`, `DefinableRV`, `DefinableFun` and freezes §3's closure-theoretic items
(5 `sorry`s, statements checked against `paper.tex` and corrected in this session — three of the
first transcriptions were false).  Proved: `dcl_subset_acl`, `acl_self`.  **Missing:** `dimVF`,
`dimRV`, `dimfib` (they exist only in the swarm artifact `.ultramath/smw16q93m/m3/Model.lean`, where
they are `def … := n`, i.e. definitional dimensions with no theorems), Lemmas 4.2/4.4/4.6, the
categories `VF[k,·]`/`RV[k,·]`, the lift `L`, and the Grothendieck semigroups —
`SpecialTransformations/{Dimension,Categories}.lean` are 17-line stubs.

**Milestone 3 — the scaffold is in the tree now, as `QE/Sec5.lean`.**
`QE/Sec5.lean` (1110 lines, standalone `import Mathlib`, compiled: exit 0, 0 errors, **no `sorry`**)
is the file the swarm left at `.ultramath/smw18ygko/m1/Sec5.lean`, moved in verbatim after the
header; it cannot be the library module `SpecialTransformations/SpecialBijection.lean` because its own
copy of `RV` clashes with `Basic.lean`'s in one `lake build` (`environment already contains
'SpecialTransformations.RV'` — measured), and unifying the two copies is Milestone 1–2 work.  55
theorems: `Pt`, `key`, `SamePD`, `polydisc`, `rvHull`,
`IsRVPullback`, `Csharp`, `rvHullSharp`, the focus map, `eta`, `SpecialBijection` (a structure with
`image`, `invMap`, `lh`, `refl`, `comp`), `IsDeformedRVPullback`, `eta_wellPosed` derived from its
hypotheses, `etaInv ∘ eta = id`, and `exists_unique_contractionVF`.  The paper's 5.2/5.4/5.5 are
frozen as `def … : Prop`, so **no** paper-numbered theorem of §5 is proved yet.  Merging this file
into the tree (`QE/` or `SpecialTransformations/`) is a mechanical step nobody has done.

**Milestone 4 — nothing.**  `SpecialTransformations/Hensel.lean` is a stub; no Hensel, no lifting
function, no §7 statement.

**Milestone 5 — nothing.**  `Differentiation.lean` and `VolumeForms.lean` are stubs; none of
9.1–9.14, 9.16, 10.4, 10.5, 10.6 exists.

## The cross-cutting item, Theorem 2.3, which is where the work went

Statements: `Milestone0/Encoding.lean` (frozen, 2 `sorry`s).  Supporting structure, all green:
`QE/JunkTrue.lean` (the junk-truth semantics of the repaired guard, plus a machine-checked proof
that the repair rejects the junk-sensitivity witness), `QE/FragmentTransfer.lean` (the fragment
transfer reduced to one hypothesis, `QFStep`), `QE/ParamBridge*.lean` (the parameter bridge:
`hasQE_of_hasQE_empty`), `QE/MulNormalForm.lean` (`mul` cancellation off `Kˣ`), `QE/QF2Fragment.lean`
(the sorted-context fragment), `QE/QF2Cover.lean` (**`qf2_cover` proved**, no `sorry`: the
quantifier-free fragment over a sorted context is covered by `QF2`),
`QE/TransferWS.lean` (the frozen fragment statement), `QE/Assembly_val.lean` (the assembly; still
carries a copy of the encoding, hence the same 2 `sorry`s), `QE/{Sec3_frozen,Sec3_sat}.lean` (§3
over parameter pairs and over the monster model), `QE/{FailProbe}.lean` (the located obstruction).

**The route is the paper's, and it goes through Weispfenning.**  `QE/Reduction_assembly.lean` has
`theorem_2_3_of_hypotheses (hShoen : ShoenfieldTest) (hAlg : AlgIngredients)`, where `AlgIngredients`
is `prep` (Lemma 3.3 + henselization), `one` (Lemmas 3.4–3.8) and `vfgen` — *"Remark 3.1 +
Weispfenning's QE theorem for `L_v`"*.  So `L_v` QE is a load-bearing input of the one route
(`qe.tex:549-552`), the `L_RV`-specific content is the non-VF-generated case (Remark `L:v:and:L:RV`),
and the QF-type/criterion family below is an equivalent *check*, not a second route.

Open, in the paper's order:

0. **`ShoenfieldTest`, `AlgIngredients.prep`, `.one`, `.vfgen`** — the four hypotheses of
   `theorem_2_3_of_hypotheses`; `.rv` is already discharged (`theorem_2_3_of_three`).
1. **`QFStep IsNontrivialVF Axioms.ACVF`** (criterion side, i.e. the check) — the one-element back-and-forth step.  With it,
   `NontrivialTransferWS Axioms.ACVF` follows, and `AllNontrivial Axioms.ACVF` is already proved.
2. ~~**`QFRes2.qf2_cover`**~~ — **done**: extraction, soundness and the formula induction are all
   proved in `QE/QF2Cover.lean`, no `sorry`.
3. **OFF THE QE PATH** (source-checked): `alg:ind:imag`, `exchange` and `aclS:model` are in
   `qe.tex` Section 4 (`\section{Minimality in ACVF}` starts at line 879; `exchange` is 918,
   `aclS:model` 1177), i.e. *downstream* of quantifier elimination. The QE section is 547–878 and
   its content is Lemmas 3.2–3.8, Remark 3.1 and Proposition 3.9. So the item below is a §4 result,
   not progress on Theorem 2.3; the earlier claim that "`aclS:model` is what `prep` consumes" was
   wrong. Recorded in `QE-PLAN.md`.
   ~~The remaining §3 item with a printed proof, `alg:ind:imag`~~ — **proved for every `t ∈ RV`**
   (`QE/AclZero.lean`, green, axioms clean). `M5.acl_singleRV_zero` covers `t = rv 0` — the closed
   term `rv 0` is substituted for the single `RV` parameter, since a term of the language is not an
   `acl`-generator — and `M5.alg_ind_imag_all` is the case split against `M5.alg_ind_imag`. The one
   input still owed is geometric, not algebraic: `t ≠ rv 0 → ¬ Small (rv⁻¹ t)`, i.e. the fibre of
   `rv` over `t ≠ ∞` is a coset of the unit ball and so is not small. It is carried as a hypothesis
   about cardinalities, never as a statement about `acl`. `exchange` (Yin 4.3) remains a frozen
   hypothesis, carried as `M5.ExchangeVF`.

## The reduction's three defects, and `QE/Assembly_frozen.lean`

Found in one pass while judging the QE swarm; all three are machine-checkable and all three are in
`QE/Reduction_assembly.lean`.

1. **Pre-repair snapshot.** Its header dates the encoding copy to `Milestone0/Encoding.lean` commit
   `d608de6` (sha `78607b94…`); the frozen file is `86d7ea7e…` (`f18b6f5`). Its `ACVFpaper` therefore
   omits the nine `repairRV` axioms, and its `HasQE` is the old unrestricted form while the frozen one
   is well-sorted-guarded. `theorem_2_3_of_three` is a theorem about that snapshot.
2. **`VFGenCase` without saturation is false** — repaired in `40abb97` by adding
   `(hSat : Saturated N)`, which `prop39` already had in scope. With `S = ⊥` it asserted an injection
   from an uncountable model of `ACVF` into a countable one.
3. **`Assembly.Saturated` is too strong, so the main route is vacuous.**
   `Assembly.extensionProperty_of_saturated` derives Proposition 3.9's conclusion from `Saturated`
   alone, with no `hPrep`/`hOne`/`hVFGen`; `Assembly.shoenfieldTest_iff_hasQE` makes `ShoenfieldTest`
   equivalent to the conclusion. `Saturated` must quantify over *finitely satisfiable* formula sets,
   leaving Lemmas 3.3–3.8 to produce finite satisfiability. The repair is sketched in
   `Assembly.SaturatedFS`/`saturatedFS_of_saturated`/`Prop39FS`/`ShoenfieldTestFS`/`theorem_2_3_of_fs`.

Defect 1 is closed by construction in **`QE/Assembly_frozen.lean`** (green, no `sorry`, axioms
`{propext, Classical.choice, Quot.sound}`): it is `import Enc` plus Parts B and C of
`Reduction_assembly.lean`, so it states

```
theorem theorem_2_3_quantifier_elimination_of_ingredients
    (hShoen : Assembly.ShoenfieldTest) (hPrep) (hOne) (hVFGen) : HasQE Axioms.ACVF
```

over the frozen `HasQE` and `Axioms.ACVF` with no copy to drift. (The frozen name itself is still the
`sorry`-ed target, so the assembly cannot take it.) Note that this proves the *implication*, and at
the present `Saturated` the implication is vacuous — defects 2 and 3 are what make its hypotheses
mean something.

Consequence for the campaign: everything the QE swarms proved for `prep`/`one`/`vfgen` survives as
mathematics, but any file proved against `Reduction_assembly`'s axiom set has to be re-checked against
the frozen one. `QE/ValBridge.lean` is the intended route for the Lemma 3.2/3.5/3.7 ports: they are
instantiations at `K := VFType M`, not re-proofs.

## The route compressed (member m7, accepted): two ingredients, no Weispfenning

`.ultramath/smw1rx5g2/m7/M7_vfgen.lean` (green):

* `eq_top_of_vf_all` — a substructure containing every `VF` element of a model of `ACVF` is `⊤`,
  because every element is `VF` or `RV` (`Axioms.sdCover`, now also `QE/SortCover.lean`'s
  `iVF_or_iRV`), every `RV` element is `rv` of a `VF` element or `rv 0` (`RVeqRvVF_of_model`), and
  substructures are closed under `Fn.rvMap`.
* `VFGenCaseP_top`, `prop39P_noVFGen`, `Prop39FS_of_two`, `theorem_2_3_of_two` —
  the entire Proposition 3.9 follows from `PrepStepP` + `OneStepVFP`; `VFGenCaseP` is never
  exercised, so Weispfenning's `L_v` QE is **not** on this route any more.

The frontier is now exactly three hypotheses: `PrepStepP` (Lemma 3.3, henselization),
`OneStepVFP` (Lemmas 3.4–3.8), `ShoenfieldTestFS`. In `QE/Assembly_frozen.lean` as
`Assembly.theorem_2_3_of_fs`; member m7's `theorem_2_3_of_two` is the two-ingredient form.

## Lemma 3.7 (`e:transc`) — done in the frozen encoding

`.ultramath/smw1rx5g2/m5/Lemma37_frozen.lean` (green, accepted): `Transc.e_transc_of_gamma` with
both former hypotheses discharged — `vsum_exists_min` (every nonempty partial sum has a
minimal-term class, hence is nonzero) and `hdis_of_gamma` (the paper's cancellation by a power of
`e`, from `leMulCompatFull` calculus). Lemma 3.2's syntactic half is also done (green):
`.ultramath/smw1rx5g2/m6/M6Syntactic.lean` (`rv_root_lift_encoding`, `huniv_of_units`,
`hred_of_residue_sum_zero`).

## The tagged encoding has no junk elements (only junk terms)

`QE/SortCover.lean` (green, axiom-clean): `iVF_or_iRV`, `not_both`, `sorted_exclusive` — every
element of a model of `ACVF` is in exactly one of the two sorts, from `sdCover`/`sdDisjoint`, which
are sentences of `Axioms.ACVF`. Consequences: the "(T2) prime-models junk" worry does not apply to
elements; the junk in this encoding is a property of **ill-sorted terms** (`rv (rv x)`, `kAdd` at
junk arguments), whose values no axiom constrains. The Johnson swarm confirmed the same from the
other side: `M5OneEC.sorted_exclusive`, and the argument that the *unrestricted* frozen 1-ec is very
likely false (`rv` at an `RV`-sorted element is unconstrained), so Johnson's route to the frozen
target must use well-sorted 1-ec — if it is used at all (the main route no longer needs it).

## Sections 3 and 4 of the paper — swarms ended solved

`smw1qqehg` (§3) 8/8 accepted; `smw1qqem3` (§4) 6/6 accepted. Notable, beyond what the notes above
already record: `acl(S)` closed under field operations (`M3AclField`); item 716 PROVED at finite `A`
with the corrected target `RV^{n·k}` (M8); `average:0:rv:not:constant` settled plus a refutation of
the frozen form (709); the centres statements refuted-as-frozen and repaired with Definition 4.14's
function form (M7Centres); §4's renaming/Boolean-algebra layer (`Sec4Rename`), coordinate-map
dimension bounds without the composition wall (M6Polydisc), §4.2's `RVMap` category isolating the
composition wall to one definability field (Sec42Morphism), and the td non-vacuity model for the
dimension axioms (Sec4DimACFModel).

## `QE/Standing.lean` — every model is `Standing` at `⊤`

Green, axiom-clean: `rv_one_units`, `vfPow`, `vfType_root` (n-th roots via
`IsAlgClosed.exists_pow_nat_eq`), `gammaDivisible_top` (Γ(M) divisible), `standing_top`.

## The `DefinableFun` composition wall is down

`QE/Compose.lean` (green, axiom-clean): `Sec4FunComp.DefinableFun.comp` and
`DefinableFun.comp_of_mapsTo` — the composition of definable functions is definable. The guarded
iterated existential `exsG` (the only shape `WellSorted` admits for eliminating the composite's
intermediate tuple) with `wellSorted_exsG`, plus non-degeneracy (`compForm_idForm`). First
applications in `QE/Fibre.lean`: `dimVF_fibre_le` (the "other direction is trivial" of
`dim:VF:pullback`, paper.tex:842), `dimVF_le_of_finFib'`, and the unconditional
`dimVF_fibre_le_zero`, with the parameter discipline (`τ` naming `t̄`) carried explicitly and shown
strictly weaker than the old `hcomp`. This was the wall recorded as blocking six items across
Sections 4, 7, 8, 9 and 10; `QE/Proj.lean` supplies the matching projection lemma
(`Definable.exists_snocRV`).

## Everything else the shared ledger should know right now

* The route to Theorem 2.3 is exactly three hypotheses: `PrepStepP`, `OneStepVFP`,
  `ShoenfieldTestFS` (`QE/Prop39Two.lean`, `Assembly.theorem_2_3_of_two`). Weispfenning is not on
  it.
* `QE/Lemma37.lean` — Lemma 3.7 proved in the frozen encoding with both former hypotheses
  discharged.
* `QE/M6Syntactic.lean` — Lemma 3.2's syntactic transport (`rv_root_lift_encoding`).
* `QE/Jm2T1.lean` — every `RV`-sorted quantifier is a `VF`-sorted one substituted by `rv`
  (`exSorted_rv_iff_vf`); the `L_val → L_RV` QF translation preserves well-sortedness and truth;
  `L_val` QE + the named residual `RVAtomElim` would yield `HasQE` at the all-VF context.
* `QE/Standing.lean` — every model is `Standing` at `⊤`; `rv_one_units`, n-th roots,
  `gammaDivisible_top`.
* `QE/SortCover.lean` — no junk elements in any model; junk is a property of ill-sorted terms only.
* §3 of the paper fully merged (`QE/Sec3*`, `QE/Acl*`, `QE/UniformCover`, `QE/Exchange`,
  `QE/M3AclField`, `QE/M8*`, `QE/BallSec3`, `QE/M7Centres`): 670 repaired, 709 settled, 716 proved
  at finite A, the centre statements refuted-as-frozen and repaired with the function form, and
  `alg:ind:imag` stands on `M5.ExchangeVF` alone (fibres infinite).
* §4 of the paper fully merged (`QE/Sec4Rename`, `QE/Sec4FibreDim`, `QE/Sec42Morphism`,
  `QE/M6Polydisc`, `QE/Sec4EK`, `QE/Sec4DimACFModel`) plus the composition wall above and the td
  non-vacuity model.

## The cardinality objection is the defect that matters (two members, two ways, machine-checked)

The tree's universally-quantified two-ingredient route is implicationally valid but **refutable as
stated**, and this is now machine-checked, independent×2:

* `smw1tqlqv` **m5** (`M5_OneStep.lean`): `units_le_of_prepStepP` —
  `PrepStepP (M := M) (N := N)` forces `Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N`, because
  `KEqTop T` puts every unit of `M` in the substructure `T ↪[LRV] N`. Contrapositive in-file.
* `smw1tqlqv` **m7** (`PaperRoute.lean`, merged as `QE/PaperRoute.lean`): the paper fixes
  `N` `‖M‖⁺`-saturated before Lemmas 3.3–3.8 (qe.tex:578, whose first step is `#K(M) ≤ #K(N)`);
  `prepStepP_forces_units_size`, `prop39FS_forces_size`, `vfGenCaseP_forces_size`,
  `standing_forces_units_size`, and the repair (below).
* m5's AUDIT adds the independently-argued point (labelled as argument, to be machine-checked
  before reliance): `OneStepVFP` appears to fail also at equal cardinality — Hahn fields
  `M = ℂ((t^{ℚ²}))`, `N = ℂ((t^ℚ))` — because divisibility at `rv(m)`, n=2, creates
  `v(m)/2 ∈ Γ(T)`, i.e. the value group of `N` must have room. That failure is what saturation is
  actually for, and a pure size bound will not repair it.

**The repair, already in the tree** (`QE/PaperRoute.lean`): only Lemma 3.3 changes —

```
PrepStepSize       ∀ M N models, SizeHyp M N → PrepStepP           (SizeHyp M N := #M ≤ #N)
OneStepSizeFree    ∀ M N models, OneStepVFP                        (unchanged -- Standing S carries it)
Prop39Size/Sat, prop39Size_of_two, prop39Sat_of_size,
paper_theorem_2_3, paper_theorem_2_3_sat, shoenfieldTestFS_of_sat
```

`paperHyp_supplies_units_size` shows the repair is not itself refutable in the same way.

**Live frontier (now)**: `ShoenfieldTestSize` (or `ShoenfieldTestSat`), `PrepStepSize`, and
`OneStepSizeFree` — with the caveat that, if m5's OneStepVFP counterexample machine-checks,
`OneStepSizeFree`'s quantification also moves onto the saturated-with-room half of `PaperHyp`.
`QE/Prop39Two.lean`'s header now records the vacuity explicitly; the file stays because the
implication is what the repaired inputs plug into.

## Gap 2 as it actually is (member m1, accepted; merged as `QE/M1Fix.lean`)

The Shoenfield half of the theorem is now reduced to classical model theory, honestly named:

* `card_le_of_prop39FS` — a third independent machine-check that frozen `Prop39FS` forces size
  at every partial embedding, so it is no evidence for Theorem 2.3 at the frozen quantifier.
* `hasQE_of_qfEAmalg` — elementary amalgamation at QF-well-sorted-identical tuples alone gives
  `HasQE Axioms.ACVF`; `qfEAmalg_model` shows the amalgam is automatically an `ACVF` model.
* `hasQE_of_modelComplete_monoAmalg` — Robinson's route: model completeness of `ACVF` in
  `L_RV` (embeddings between models are well-sorted-elementary, `WellSortedElem`) + common-model
  amalgamation at QF-identical tuples.
* `qf_realize_embedding` — an `L_RV` embedding transfers *only* quantifier-free truth, which is
  precisely why a `Prop39FS`-style monomorphism can never by itself be a proof of QE; the
  elementary amalgam replaces it.

So **Gap 2 = one of `QFEAmalg` or (`ModelCompleteRV` + `MonoAmalg`)**, both classical statements
Mathlib does not have, and both of which the §3.1 route (into saturated models) is designed to
supply.

## Frontier, current form

```
ShoenfieldTestSize  (or QFEAmalg / ModelCompleteRV + MonoAmalg)
PrepStepSize        Lemma 3.3 at pairs with Card M <= Card N
OneStepSizeFree     Lemmas 3.4-3.8 (unchanged; Standing carries the size)
```

plus the flagged caveat that `OneStepVFP` may also fail at equal cardinality for
value-group-dimension reasons (m5's Hahn-field argument; realizing it needs a concrete model of
`Axioms.ACVF` in Lean, which the tree does not yet have).

## Tree-wide compile state (`make milestones`, full pass, 2026-11-04)

Every file in `Milestone0/`, `Milestone0/accepted/`, and `QE/` (116 files) compiles with
`exit=0, errors=0`, with **one exception: `QE/ValBridge.lean` (exit 1, one error)** — my own
superseded file from before the `VFField`/`VF policy` overhaul (it was written against
`Assembly_val`'s `M4ValueOnly` before the bare-`Enc` port existed; `QE/VFField.lean` +
`QE/VFValued.lean` replace it). Nothing in the tree imports it. It should be deleted; the
deletion needs a person to approve it and nobody is currently at the desk, so it is recorded
here instead — do not build on it, and do not let a future session "Exc: 1 error" claim the tree
is green without quoting this line.

## Author ruling (2026-11-04): Marker model theory is quotable, never proved

**Model theory in Dave Marker's book may be taken as given — transcribe the statement as a named
Prop, with the book's content in its docstring — never attempt a proof.** Concretely, for this
project: Shoenfield's test, Robinson's model-completeness criterion, ACF model completeness,
Löwenheim–Skolem–Tarski, elementary amalgamation, saturated-model existence/universality/
homogeneity, compactness. `ShoenfieldTestSize`/`ShoenfieldTestSat`, `QFEAmalg`,
`ModelCompleteRV`, `MonoAmalg` are thereby **given classical statements**, and the remaining
content of Theorem 2.3 is exactly:

```
PrepStepSize      Lemma 3.3 + henselization at pairs with Card M <= Card N  + Γ divisible
OneStepSizeFree   Lemmas 3.4-3.8 (3.7 proved; 3.2 transported and wired; 3.4/3.5/3.6/3.8 open)
```

Both live at `PaperHyp = SaturatedFS N ∧ SizeHyp` pairs (the existence half of the one-step needs
type realization; saturation itself is now quoted). `QE/PaperRoute.lean`'几乎是 calibrated route is
therefore a proof of Theorem 2.3 modulo exactly those two algebra bundles (and the classical
statements it consumes). Swarm `smw1v42vv` was stopped and replaced by `smw1vehvn`, whose
directions are algebra/encoding-only (3.3, Γ-room, 3.8, WS-bridge, residue-extension).

## The one-element step is now a two-halves decomposition (both in the tree)

`smw1ukwfb` ended solved (3 accepted, all merged):

* **Algebraic half** (`QE/M5L34_36.lean`, m5): the paper's Claim (⋆) as a Γ-statement.
  `cls_ratio_units` + `mem_of_cls_mem` bridge the gap the paper leaves implicit — Γ-class
  identities become `RV`-membership through `KEqTop S`; the polynomial half
  (`cls_vsum_monomial`, separated case `OneStepSeparatedP`), the quotient step
  (qe.tex:645), and Standing for free once class control is exhibited.
* **Semantic half** (`QE/M1QFStep.lean`, m1): atomic-type agreement over `S` already produces
  the `LRV`-embedding of `closure (S ∪ range a)` into `N` (saturation realization is Marker
  content, quoted). `Frozen.StepObligation` records exactly what each case lemma owes:
  (i) an atomic match `m ↦ n` in `N`, (ii) `RV(closure(S,m)) ⊆ S`.

Two negative facts both parts record, kept visible: `RV(closure (S ∪ {m})) ⊆ S` is NOT
derivable from `Axioms.ACVF` at a general `S` (junk-term values are unconstrained), so the
case lemmas need the `IsVFGen` restriction on the target; and the divisible hull
`Γ(S) + ℤ·v(m)` is exactly what `Standing T` forces when `iRv m ∉ S` (where the Γ-room of
`smw1vehvn`'s Hahn direction lands).

## Ruling applied to both routes (2026-11-04, author)

* **Shoenfield's test**: statement-given (Marker). Nothing in the tree proves the test itself;
  `ShoenfieldTestSat`/`ShoenfieldTestSize`/`Assembly.ShoenfieldTestFS` are consumed as named
  hypotheses, and `QE/ShoenfieldWS.lean`/`QE/M1Fix.lean` are encoding-specific derivations
  *from* classical statements, not proofs of them.
* **Johnson's approach**: the same rule applies. Marker covers model completeness of ACF,
  amalgamation, Robinson's criterion. It does NOT cover Johnson's specific machinery from
  *Fun with Fields* ch. 2 (the valuation-ring amalgamation construction 2.2.4–2.2.7, the 1-ec
  "cheese" lemmas 2.3.x) — and that machinery is exactly what is **already proved in this tree**
  (`QE/Amalgamation_reduced.lean`, `QE/CheeseMeetsBase.lean`, `QE/OneEC_val.lean`,
  `QE/Johnson23_valuation.lean`), completing `Assembly_val.hasQE_ACVF_val` for `L_val`. The
  tagged `L_RV` version (T2) stays dormant: 1-ec unrestricted is very likely false in the frozen
  encoding; it would need *well-sorted* 1-ec if ever used. The main route does not use it;
  keep it as the check, not the frontier.

## Second axiom-of-quotation (2026-11-04, author): Prestel-Engler valuation theory

**General valuation theory found in Prestel-Engler may be taken as given — statements only.**
Concretely for this project: henselization exists; the henselization has the same residue field
and the same value group; a valued-field embedding extends along the henselization on both
sides; the divisible hull of a value group exists and is initial; `Kˣ`/`O`/maximal-ideal algebra;
Newton-polygon facts. Folded into the second ruling's discipline: transcribe as named Prop with
the book statement in the docstring, never prove.

After both rulings, **Lemma 3.3 (`PrepStepP` at SizeHyp pairs) decomposes as**:

1. `g : K(M) → K(N)` extending `f ↾ K(S)` — Marker (ACF extension of embeddings), quoted.
2. henselization of `VF(Ŝ)` + `K` and `Γ` preserved — Prestel-Engler, quoted.
3. adjoining representatives of all residue classes gives `K(S*) = K(M)` — construction.
4. `Γ(S*)` divisible via the (Prestel-Engler) divisible hull — construction-meets-quote.
5. extending the monomorphism — Marker (saturation realization), quoted.

So what remains is the **assembly** of those five into the frozen `PrepStepP`/`PrepStepSize`
statement, which is Lean work, not mathematics. The KEqTop obligation is irreducible content
(`M5.units_le_of_prepStepP`), hence the size hypothesis stays; the rest is quoted or built.
Swarm `smw1vehvn` was already directed accordingly (henselization-existence as named Prop).

## smw2ioy2w (2026-11-04): Γ(M) and K(M) infrastructure landed — d1, d4 accepted and merged

* `QE/GammaGroup.lean` (m1, accepted): `RVStar M` is a `CommGroup` (`commGroupRVStar`); `Kˣ` is a
  subgroup (`KStar`); `RVStar M ⧸ KStar` — the paper's `Γ(M)` as a group — is a Mathlib
  `CommGroup` with no further congruence work. Zero hypotheses beyond the ambient model.
  (Order half is d2, running: value-class setoid `Cls`, `GammaOf`, `LinearOrder`,
  `CovariantClass` from `RVCalc.le_mul_iff`.)
* `QE/KAlgClosed.lean` (m4, accepted): `IsAlgClosed (KOf M)` — the residue field's algebraic
  closedness is the frozen `Axioms.kAlgClosed` scheme (Yin's Def. 2.2 item 3); the content was
  extraction (`acfSchemeK_realize`, `hornerPoly_realize_K`, `IsAlgClosed.of_exists_root`).
  Corollaries `exists_root_kOf`, `exists_pow_kOf` (`K(M)^×` divisible — the field-level
  `rvDivisible` at units), plus instance `instIsAlgClosedKOf`.
* `QE/KAlgClosedQuote.lean`: Marker's `ACFExtendsAlgebraicEmbeddings` (as transcribed in
  `QE/ClassicalProps.lean`) instantiates at `K(M) → K(N)` with `[IsAlgClosed (KOf N)]` discharged —
  Lemma 3.3 step (i) is now consumable by the PrepStep assembly (d5 ledger, m5 running).
* Re-verified this session: `QE/Assembly_val.lean` full elaboration green, `hasQE_ACVF_val`
  ⊆ {propext, Classical.choice, Quot.sound} — the QE-in-`L_val` theorem stands.
* Stale record closed: `QE/ValBridge.lean` was removed at `009a684`; the full pass has no known
  exception.

## smw2ioy2w (2026-11-04, continued): the Lemma 3.3 ledger landed — and a guard finding

* `QE/M5Ledger.lean` (m5, accepted): the complete formal skeleton of Lemma 3.3.
  `prepStepP_of_ledger : ACFExtends → HenselizationExists M → ResidueStep → DivisibilityStep →
  SaturationRealization → Assembly.PrepStepP` (#line ~407), via the tower
  `S → henselize → T₁ → residues → T₂ → divisible hull → T₃`; henselianity transported by the
  paper's `VF(T₂) = VF(T₁)` mechanism (`M7Hens.henselian_congr`), `KEqTop` by monotonicity.
  Prestel–Engler route (`ImmediateLift` for input 5) also proved (`prepStepP_of_ledger_hens`).
* **FINDING (route shape, recorded).** Input 1 (`ACFExtends`) forces `#K(M) ≤ #K(N)`; the frozen
  guard `SizeHyp := #M ≤ #N` does NOT imply it (K(M) can be as large as M while K(N) stays small).
  The paper supplies the inequality from `‖M‖⁺`-saturation (residue fields of saturated models are
  saturated, hence universal). So `M7Paper.PrepStepSize` (SizeHyp-only guard) is under-powered for
  the Marker discharge. Corrected shapes in the file: `PrepStepSizeK` (adds the K-inequality) and
  **§10b (recommended)**: `PrepStepPaper` at `PaperHyp`, with
  `paper_theorem_2_3_sat_of_ledger_paperHyp : ShoenfieldTestSat → LedgerInput1P → LedgerInput2 →
  LedgerInput3P → LedgerInput4P → LedgerInput5P → OneStepSizeFree → HasQE Axioms.ACVF` proved
  end-to-end — no `ImmediateLift`, no henselian one-step hypothesis.
* Stress tests machine-checked: the bare forms ARE vacuous (`bare_KEqTop_trivial`,
  `bare_gammaDivisible_trivial`, `standing_top_trivial`); the Γ-conjuncts (`GammaEq`,
  `GammaHullInitial`) are exactly what blocks `T = ⊤`; cardinality audit on all four inputs
  (`acfExtends_field_size`, `saturationRealization_forces_size`, `units_size_of_sizeHypK`).
* What remains to discharge for Lemma 3.3: inputs 3/4 (the paper's two constructions — d6/d7
  territory), input 5 (Marker saturation realization), and the ClassicalProps transcription of the
  saturated-field universality/homogeneity statements named in the `ACFExtends`/`SaturationRealization`
  docstrings.

## smw2ioy2w (2026-11-04, continued): the valuation-ring layer — d7 accepted

* `QE/RVAdd.lean` (m3, accepted, self-scoped direction d-ADD): `O = {x | 1 ≤ rv x}` is a subring
  (`isInt_zero/one/add/neg/mul/sub`), `m = {x | rv x < 1}` is an ideal and exactly the non-units
  (`iUnits_iff_isInt_and_not_isMax`), `rv_inv : rv (x⁻¹) = iRVInv (rv x)`,
  `isInt_or_inv : x ≠ 0 → x ∈ O ∨ x⁻¹ ∈ O`, the strict triangle as an EQUALITY
  (`rv_add_eq_of_lt'`), residue invariance (`rv_add_eq_of_isMax`), `1 + m ⊆ Kˣ`, and balls as
  cosets (`inBall_congr`, unit ball = O). All from `Axioms.ACVF` alone — no `w`, no `hw`, unlike
  the `M6Syntactic`/`M6Wire` versions it supersedes. This is the additive layer the ledger inputs
  3/4 and the case lemmas consume.
* Discipline note: the direction's own item (i), as registered, was false — vacuous at VF-elements
  (`sdUnits`/`sdDisjoint`: `iUnits` is ill-sorted there) and false on the intended reading (value 0
  is not preserved by `+`). The member machine-checked both failures and shipped the corrected
  `isInt_add`/`isMax_add`/`not_isMax_add_of_unit`; the falsification is recorded in the tree.
* Hazard recorded (board f9): `VFType M` has no `LeftDistribClass`/`RightDistribClass` instances
  (`Field.ofMinimalAxioms` does not register them), so `ring`/`mul_sub` fail at `VFType`; work at
  the `M` level and transport with `Subtype.ext`. Workaround lemmas `vf_mul_add_vf`/`vf_add_mul_vf`
  are in `QE/RVAdd.lean`.

## 2026-11-04 (later): Γ(M) completed; §10b ADOPTED by author ruling; second swarm launched

* **Γ(M) complete.** m2's order-half file (delivered at budget exhaustion as a finding, verified
  judge-side and merged into `QE/GammaGroup.lean`): `Cls` value-class setoid, `GammaOf M`,
  descended `CommGroup` + `LinearOrder` + `IsOrderedMonoid` + `CovariantClass`, the 10-conjunct
  `gamma_isLinearOrderedAbelianGroup`, `gammaMk_eq_one_iff_units`/`gammaMk_eq_iff_units_mul`
  (classes = Kˣ-cosets), `gammaVal_eq_iff_le`. All 22 audit heads axiom-clean.
* **Author ruling 2026-11-04: the canonical route is §10b** (`QE/M5Ledger.lean`'s
  `paper_theorem_2_3_sat_of_ledger_paperHyp`: ShoenfieldTestSat + five inputs at `PaperHyp` +
  OneStep gate → `HasQE Axioms.ACVF`). Decision on quote presentation left open by the author
  (quotations stay hypotheses by the standing convention unless he says otherwise).
* m7's machine-checked shape results (findings, files verified by smw2jkpn4 e8 during assembly):
  `OneStepSizeFree` is refuted both frozen and `SizeHyp`-gated (`ArchimedeanRV` obstruction,
  `not_oneStepVFP_of_infinitesimal`); the surviving gate is `OneStepPaper` (`∀∀ PaperHyp →`),
  which fits §10b by direct specialization.
* m8's machine-checked construction (finding): `exists_standing_superset` — every substructure
  has a `Standing` superset outright (residue + divisibility closure, directed union
  `standing_iSup`), so ledger inputs 3/4's closure side is a THEOREM; their remaining content is
  the embedding extension (saturation).
* **Second swarm `smw2jkpn4` (8 members, 360 min)** launched on the seven-hypothesis frontier:
  e1 Shoenfield transcription, e2 saturation transcriptions (LedgerInput1P/5P wiring), e3 case
  lemmas 3.4/3.6 ledger, e4 case 3.8 + `oneStepVFP_of_cases` combinator, e5 valuation bridge
  (`GammaOf` vs `VFValued`'s `w`), e6 consistency witness (scoped Hahn-series ledger), e7
  Γ-divisibility API, e8 final route document. Banned overlaps: m7's OneStep shape and m8's
  Standing-T construction (smw2ioy2w still running them).

## smw2ioy2w ENDED (2026-11-04, solved): 5 accepted + 1 salvaged; d6 anchored the Lemma 3.3 reduction

* `QE/StandingHull.lean` + `QE/StandingHullRoute.lean` (m8, accepted): `standingHull S` is the
  least, Zeroth-Order-constructible `Standing` superset — closure under Kˣ(M) and all n-th roots
  of stage elements (roots from `StandingTree.gammaDivisible_top`), ω-union (`standing_iSup`),
  minimality via `units_of_pow_units`; full closure-operator API (`standingHull_idem`,
  `standingHull_top`, `standingHull_eq_self_iff ↔ Standing`). Route file:
  **`prepStepP_iff_hullExtension`** — frozen Lemma 3.3 ⟺ every monomorphism `S ↪ N` extends to
  the FIXED hull; `PrepStepSize_iff_hullExtension`, `paper_theorem_2_3_sat_of_hullExtension`,
  and the cardinality stress test `hullExtension_forces_unitsN_size`. Explicitly NOT claimed
  (correct): paper Lemma 3.3's `VF(S*) = VF(S)` and Γ-hull clauses.
* Consequence for the route: `PrepStepPaper` (the §10b prep half) reduces to
  `HullExtension`-at-PaperHyp-pairs, which is exactly the shape `SaturationRealization` supplies
  (smw2jkpn4 e2) — the two may collapse into one transcription item; composition check pending.
* Author ruling 2026-11-04 (third): Marker/Prestel–Engler quotations REMAIN HYPOTHESES of the
  final theorem — "100% reliable math, harmless as axioms, but hypotheses they are if that is the
  convention." It is.
* Board leftovers: m7's `Transport.lean`/`HahnObstruction.lean` (OneStepPaper gate) delivered as
  findings but never submitted; first-hand verification assigned to smw2jkpn4 e8. d8 consistency
  witness abandoned empty; relaunched as smw2jkpn4 e6.

## 2026-11-04 (cont.): the reduction layer is COMPLETE — `QE/FinalRoute.lean` (smw2jkpn4 e8, accepted)

* `paper_theorem_FINAL : M7Paper.ShoenfieldTestSat → M5Ledger.LedgerInput1P → LedgerInput2 →
  LedgerInput3P → LedgerInput4P → LedgerInput5P → Hahn.OneStepPaper → HasQE Axioms.ACVF`
  (`QE/FinalRoute.lean`), with `frozen_conclusion_shape` machine-identifying the conclusion with
  the frozen target by `rfl`. The proof: §10b ledger → `PrepStepPaper`, `prop39Sat_FINAL` joins
  with the one-step gate, Shoenfield closes. No saturation/size/henselization hypothesis is
  introduced by the composition itself.
* Merged with it: m7's OneStep-shape work (finally first-hand verified):
  `QE/Transport.lean` (embedding reflection of `iLe`, infinitesimal transport) and
  `QE/HahnObstruction.lean` (`ArchimedeanRV`, `not_oneStepVFP_of_infinitesimal`,
  `OneStepPaper`, `paper_theorem_2_3_sat_of_paper`; the `PRCopy` byte-copy replaced by the
  canonical `import PaperRoute` — byte-identity of the rest sha256-checked).
* Audit: each SizeHyp-gated input implies its PaperHyp form, so FINAL assumes strictly less than
  the old frozen gates; `oneStepSizeFree_refutable`/`oneStepSizeBounded_refutable` re-exported.
* The campaign's open set is now exactly the FINAL's seven hypotheses + T4 contingency
  (SaturatedFS strength, e2) + e6 consistency (orthogonal). No more glue work on the route.

## smw2jkpn4 e1 (2026-11-04, accepted): Shoenfield transcribed — and the T4/gate question is settled

* `QE/ShoenfieldQuote.lean` (m5): the quote is `ShoenfieldTestRel := QEOfGate relGate` where
  `relGate M N := M1Fix.SatRel M N ∧ #M ≤ #N` — the paper's *pair-relative* `‖M‖⁺`-saturation.
  The frozen `ShoenfieldTestSat` is `QEOfGate paperGate` by `Iff.rfl`, and `paperGate ⊆ relGate`
  makes the frozen input strictly stronger: the fit is exact up to `SatBridge` = the quantifier-order
  upgrade `SatRel M N → Assembly.SaturatedFS N`, which NO book supplies (`satBridge_diagonal`).
* **Circularity check (machine-checked):** if `SaturatedFS` holds of no structure, the frozen gate
  is empty and `ShoenfieldTestSat ↔ HasQE Axioms.ACVF` — the frozen input 1 would BE the target.
  The paper's gate (`relGate`) is inhabited in the paper's setting; the frozen `∀ M` reading is
  the quantifier-order defect `QE/M1Fix.lean` §2 warned about. Discharge-side gates (e2's
  transcriptions, f1/f2 case lemmas, f6's adversarial audit) should all be stated at `relGate`.
* The repair: `paper_theorem_2_3_of_gate H` (gate-polymorphic route); `paper_theorem_2_3_rel`
  is the canonical discharge theorem at the book's gate; `shoenfieldTestSat_of_relLedger_gated`
  DERIVES the frozen input 1 from quote + five inputs at `relGate` + `relGate`-gated one-step, so
  the merged `QE/FinalRoute.lean` remains valid as the conservative (paperGate) form.

## smw2jkpn4 e4 (2026-11-04, accepted): the one-step case assembly + Lemma 3.8's value side

* `QE/OneStepCases.lean` (m4): the paper's 3.4–3.8 case split as three hypothesis-family slots —
  `CaseSeparated` (3.4/3.6), `CaseNotSeparated` (3.5), `CaseNewRV` = `M5.OneStepRVNew` (3.7/3.8) —
  with `oneStepVFP_of_cases : Cases → Assembly.OneStepVFP` at a fixed pair, NO gate/size/saturation,
  so m7's `OneStepPaper` gate applies by specialization (`oneStepPaper_of_cases`), and
  `paper_theorem_2_3_sat_of_cases` absorbs the five §10b inputs up to `HasQE`. Discharge interfaces:
  separated slot from `RVControl` or `ResidualClasses` (M5L34_36 vocabulary), plus
  `cases_of_oneStepRVOld`/`cases_of_stepObligation`/`cases_of_classStepP`/`cases_of_global_extension`.
* **Finding (recorded):** the tree's separated-case hypothesis `M5L.VFInvClosedOn` is NOT derivable
  from `Standing` — `L_RV` has no VF-inverse symbol, so `VF(S)` is only a subring. The slots omit it;
  the separated-case discharge must supply it by computation (`M5L.rvPoly_mem_of_separated` etc.),
  not by hypothesis inheritance.
* `QE/Case38Value.lean`: `lift:value:full`'s value side over genuine Mathlib valuations
  (`lemma38_transfer`: algebraically-closed-in-L subfields + divisible value group + isometry σ ⇒
  transcendence of e,d + value transfer across `K(e) → K'(d)`), with a concrete `RatFunc ℚ` stress
  model (`inftyVQ_two`, `sameRV_not_implied_by_value`).

## smw2jkpn4 e2 (2026-11-04, accepted): saturation transcribed — input 5 analyzed to its residual

* `QE/SatQuotes.lean` (m2): Marker's universality/homogeneity of κ-saturated algebraically closed
  fields transcribed (`SatAt`, `SatField`, `FieldUniversal`, `MarkerSaturatedFieldUniversal`,
  `SameType`); the paper's input-1 route factors as quote + `ResidueInduced` (the only missing
  piece, named) via `acfExtends_of_universal_induced`, the size side `#K(M) < κ` from `PaperHyp`.
* `QE/SatReal.lean`: `SaturationRealization ⟺ QFSat` (one-element atomic realization), and at
  `PaperHyp` pairs with `SaturatedFS` the ONLY residual is `QFFinSat` — finite satisfiability of
  the pushed type per formula — `ledgerInput5P_of_saturatedFS_finSat`. The case lemmas 3.2–3.8
  are precisely the QFFinSat-discharge mechanism: one-element steps iterated.
* `QE/KOfBridge.lean`: `kOfHom` — a total L_RV embedding induces the residue-field ring hom:
  `LedgerInput5P ⟹ LedgerInput1P`.
* `QE/QFAudit.lean`: `prop39Pair_iff_satReal` — input 5 IS the pair-level Proposition 3.9
  conclusion; `hasQE_of_ledgerInput5P` (Shoenfield + input 5 → HasQE). Combined with m8's
  `prepStepP_iff_hullExtension`: the prep side is all monomorphism extension.
* `QE/QFRoute.lean`: `paper_theorem_2_3_sat_of_qf` — the honest frontier:
  Shoenfield + `QFFinSat`-at-PaperHyp + inputs 2/3/4 + one-step. (Seam noted: it keeps the ungated
  `OneStepSizeFree`; the gated variant is one line via `ShoenfieldQuote.paper_theorem_2_3_of_gate`.)
* Frontier state after e1+e2+e4: the remaining irreducible content is `QFFinSat`-at-PaperHyp —
  i.e. case lemmas 3.4/3.6 + the separated-slot discharge (smw2k0btg f1/f2) — plus input 3/4
  half-content and quote transcription (smw2k0btg f3/f4 alternatives), gated at `relGate`
  per e1's resolution. Consistency (e6) runs orthogonal.

## smw2k0btg f3 (2026-11-04, accepted): Γ(M) divisible, hypothesis-free — one PE quote retired

* `QE/GammaDiv.lean` (m6): `gamma_divisible : ∀ n ≥ 1, ∀ a : GammaOf M, ∃ b, b ^ n = a` in EVERY
  model of `Axioms.ACVF`, from `StandingTree.gammaDivisible_top` alone (no saturation, no gate).
  `gammaDivisible_top_iff_forall_root` identifies the frozen `Assembly.GammaDivisible ⊤` with group
  divisibility exactly (residue factor killed by `gammaMk_unit_eq_one`); `RootableBy (GammaOf M) ℕ`
  and `ℤ` instances; `gamma_pow_inj`, `one_le_pow_iff`, `existsUnique_gamma_root`.
* Bridges for the ledger: `GammaEqQ`/`GammaHullInitialQ` (quotient forms) ⟺ `M5Ledger.GammaEq`/
  `GammaHullInitial` (`gammaEq_iff_gammaMk`, `gammaHullInitial_iff_gammaMk_pow`);
  `gammaHullInitial_of_gammaEq` (clamp strictly weaker than `GammaEq`).
* Stress tests: `forall_root_including_zero_subsingleton` (n = 0 excluded essentially — allowing it
  forces Γ trivial), `gamma_divisible_at_any_cardinality`.
* Negative, recorded: `Transfer.iRVInv` is a choice witness, not a term symbol — `Γ(S)` is only a
  submonoid of `Γ(M)`; use `GammaHullInitialQ`, not subgroup-valued lift lemmas.
* Consequence: input 4's divisibility half is a THEOREM of the frozen axioms (the value group of
  ACVF is divisible — as it should be); the anticipated Prestel–Engler divisibility quote is
  retired. What remains of input 4 (`DivisibilityStep`) is clamp + embedding content.
* Also recorded in the same merge: `QE/FinalAudit.lean` (f6, accepted earlier this session) — the
  seven-hypothesis collapse to `ShoenfieldTestSat + Prop39Sat`; `FinalRoute.olean` was missing from
  the shared chain (the audit exposed it) and is now built.

## 2026-11-04 (smw2jkpn4 ended solved; sentinels): HenselDefect + HahnAnatomy

* **smw2jkpn4 ended solved (4 accepted + 2 valuable abandoned-sentinel findings).** Accepted:
  e8 (`QE/FinalRoute.lean`), e1 (`QE/ShoenfieldQuote.lean`, T4 resolved at `relGate`), e4
  (`QE/OneStepCases.lean` + `QE/Case38Value.lean`), e2 (`QE/SatQuotes/SatReal/KOfBridge/QFRoute/
  QFAudit`, QFFinSat residual). Its member m1's abandoned direction left the defect below.
* **DEFECT FOUND + FIXED (m1's `HenselDefect`, sentinel).** `QE/M7Hensel.lean`'s `IsHenselianVF`
  was vacuous: its constant-term clause read `¬iLe (rv 1) (rv (a 0))` (contradicts the coefficient
  clause at `i = 0`); intended — and now restored — is `¬iLe (rv (a 0)) (rv 1)` (a₀ strictly below
  1 in the reversed-reading order; cf. `QE/RVAdd.lean`'s `IsMax`). Consequence before the fix:
  everything consuming the predicate was trivially satisfiable (including `HenselizationExists`),
  which mattered only for *honesty of the hypothesis* — no proof step was unsound. Fix = argument
  swap only; all 14 consumers (`M7Hensel`, `M5Ledger`, `FinalAudit`, `QFRoute`, `QFAudit`,
  `M7PaperHyp`, `HahnAnatomy`, `ShoenfieldQuote`, `SatReal`, `KOfBridge`, `SatQuotes`,
  `Case38Value`, `StandingHullRoute`) re-verified 0 errors after the patch.
* **`QE/HahnAnatomy.lean` (smw2k0btg m4, accepted).** The Hahn obstruction is EXACTLY at the
  embedding half (`EmbAt`: extension without `Standing`): `not_embAt_of_infinitesimal` excludes it
  with no Standing or size, `not_forall_embAt_of_infinitesimal` covers every domain class — no
  hull/KEqTop/GammaDiv strengthening repairs the one-step. `oneStepVFP_iff_gammaDivisible`:
  the frozen one-step is degenerate (GammaDivisible only, KEqTop free). The Prop39
  finite-satisfiability relation is pinned as the bifurcation locus: `embAt_of_finSat` (finite sat
  ⟹ embedding half) but `not_finSat_of_archimedean` at the configuration — so **`SaturatedFS` cannot
  imply `¬ArchimedeanRV`** (a saturated ACVF's Γ is divisible, hence Archimedean; the infinitesimal
  sits in M, its N-side iff is exactly finite satisfiability, i.e. `QFFinSat`).
  `not_oneStepPaper_of_config`: at a `PaperHyp` pair with an Archimedean-halved configuration, the
  `OneStepPaper` gate fails — so `OneStepPaper` (hypothesis 7 of `paper_theorem_FINAL`, used only by
  the intermediate forms) must rest on `¬ArchimedeanRV`, and the paper's route certainly did not
  fold through it. The canonical FINAL2 route (Shoenfield + Prop39Sat = QFFinSat at relGate) is
  untouched by all of this.
* Chain note: `FinalRoute.olean` had been missing from `.scratch2/sec3` (exposed by f6's build) —
  built alongside this batch; the chain is now current through `FinalAudit`.

## smw2k0btg ENDED (2026-11-04, solved: 3 accepted + 4 sentinels); smw2ku6gn launched on the two-hypothesis frontier

* smw2k0btg's accepted: f6 (`QE/FinalAudit.lean` — seven ⟹ two: Shoenfield + Prop39Sat), f3
  (`QE/GammaDiv.lean` — Γ divisible hypothesis-free, one PE quote retired), f4-revised
  (`QE/HahnAnatomy.lean` — obstruction at the embedding half, OneStepPaper needs ¬ArchimedeanRV,
  Prop39FS is the locus). Sentinel findings with no files: d2 hull-collapse composition, d4 case
  3.4, d5 case 3.6, d8 gate-demand table. Consistency (e6) produced nothing in either swarm.
* The canonical frontier is now exactly: `ShoenfieldTestRel + Prop39Sat ⟹ HasQE Axioms.ACVF`
  (`QE/FinalAudit.lean`'s FINAL2/3; e1's relGate resolves T4 and the disjoint question).
* **smw2ku6gn (8 members, 360 min)** re-briefed onto that frontier: g1 case 3.4 (`lift:all:root`),
  g2 case 3.6 (`lift:divisible:hull`), g3 hull-collapse composition, g4 gate-demand table,
  g5 two-value-groups, g6 Hahn-series consistency witness.
* Chain state: oleans for every merged file through `FinalAudit` are current in `.scratch2/sec3`
  (FinalRoute's missing olean was rebuilt when f6's build exposed it).

## smw2ku6gn sentinel salvage (2026-11-04): four deliverables verified judge-side and merged

Five of smw2ku6gn's eight members expired WITHOUT submitting; their four delivered files were
verified first-hand and merged (the two case-lemma directions produced nothing for the second
generation running; m4 residue-induction, m6 Hahn consistency, m8 non-vacuity still run):

* `QE/Prop39Decomp.lean` (m3/g3): Proposition 3.9 at a fixed pair ⟺ `HullExtension` ∧
  `OneStepVFP` (⟺ HullExtension ∧ `OneStepCases.Cases`) — `extendsHere_iff_hullExtension_and_oneStep`;
  `satReal_iff_hullExtension_and_oneStep` — Marker's saturation-realization input 5 IS the paper's
  §3 (3.3 + 3.4–3.8) EXACTLY, gate-free; `extendsAt_rel_iff_input5R` — at the paper's relGate,
  input 5 = Prop 3.9 (relGate form of FinalAudit §3); and `paper_theorem_rel_two :
  ShoenfieldTestRel → Input5R → HasQE Axioms.ACVF` (the two-quote final at the honest gate).
  REFUTATIONS: `not_extendsHere_of_archimedean`, `not_prop39Sat_of_archimedean_config`,
  `not_extendsAt_rel_of_archimedean_config`, `not_finSat_at_pair_of_archimedean` — the canonical
  frontier is vacuous at any PaperHyp pair carrying an Archimedean target + the Hahn
  configuration; the non-vacuity requirement (whether the paper's gate excludes it) is the open
  question handed to m8. GATE-MATCHING: pairing ShoenfieldTestRel with the frozen Prop39Sat
  silently needs `SatBridge`; only matched pairings are theorem-free.
* `QE/ValueGroupBridge.lean` + `QE/BridgeStress.lean` + `QE/WireIn.lean` (m7/g5): Γ(M) is
  literally a Mathlib value group — `vGammaValuation : Valuation (VFType M) (WithZero (GammaOf M))`
  (explicit, no choice); the `O`/`m` order characterizations; `gv_surjective` (axiom `rvSurj`).
  The brief's naive order-translation was machine-checked FALSE as written (`BridgeStress.wrong_direction`)
  — Mathlib's `Valuation` is the absolute-value convention, so the correct swapped form is
  `VGBridge.le_iff_gv_le_of_valuation` (w x ≤ w y ↔ gv y ≤ gv x); PE quotes instantiate at a model
  (`WireIn`: `HenselizationExists → Nonempty (HenselizationOf (vGammaValuation _))`, same Γ).
* `QE/HullAudit.lean` (m2/g2, audit rather than the 3.6 slot): `ClassicalProps.DivisibleHullExists`
  is an ISOMORPHISM at the only instantiable value group `Additive (GammaOf M)`
  (`divisibleHullExists_at_gammaMk_surjective` — Γ(M) already divisible, the quote adds nothing);
  it cannot instantiate at Γ(Ŝ) (submonoid only, no inverses — GammaDiv §9); the paper's
  Γ(S*) = hull Γ(S) IS proved from the two clamp conjuncts + initiality
  (`divisibilityStep_pins_hull`); zero prior consumers in the tree. Consequence: case 3.6's content
  is NOT the Prestel–Engler quote — it is the construction itself.
* Chain note: `Lifting_transcendental.olean` was missing from the shared chain (HullAudit exposed
  it); now built; the chain is current through every file above.

## 2026-11-04 (late): residue-induction gap CLOSED (m4 salvage); smw2mluv7 fully engaged

* `QE/ResidueInduction.lean` + `QE/ResidueInductionStress.lean` (smw2ku6gn m4, expired without
  submitting — verified judge-side and merged): **`ResidueInduced` is a theorem**, not a gap.
  Construction: the subring `RS S` of `KOf M` generated by the units of `S`; `tr : RS S →+* KOf N`
  induced by an embedding `f`; `ker_eq` — f preserves AND reflects the polynomial relations among
  the units (the L_RV-specific content; reflection needs injectivity); prime ideal `Ip`, domain
  `Qp`, fraction field `Fp`; embeddings `psiM`/`psiN`; `Ksub = (psiM).fieldRange` with
  `Ksub_eq`/`Ksub_minimal`; `jmap : Ksub →+* KOf N`; `residueInduced : SatQuotes.ResidueInduced`
  for every model pair. Consequences: `acfExtends_of_universal` (paper's step (i) with the gap
  closed), `ledgerInput1P_of_marker` (input 1 from Marker universality + size alone),
  `residueInduced_subtype` (non-vacuity at N = M). Stress: `inclusion_only_is_false` — dropping
  reflection is machine-refuted. All axiom-clean.
* Consequence: the input-1 route (`acfExtends`) has NO named missing piece left — its only
  hypotheses are Marker's quote and the size bound.
* Chain note: `SatQuotes.olean` had been missing from `.scratch2/sec3` (built without `-o` at its
  original merge) — exposed by this build; now built, chain current.
* smw2mluv7: all 8 members registered and running (p1/p2/p3 case 3.4; p4 case 3.6; p5 case 3.5;
  p6 separated-slot closure; p7 non-vacuity at relGate; p8 henselianity reconciliation; plus an
  m6-chosen direction assembling 3.7/3.8 into the CaseNewRV slot). No submissions yet.
* smw2ku6gn: m4 ended (salvaged above); m6 (Hahn-series consistency) still running.

## smw2ku6gn ENDED (exhausted, no accepted submissions) — salvage and the Hahn-model state

* Board: g1 (case 3.4) and g2 (3.6-as-audit) directions produced nothing beyond what was already
  merged; g3 (hull-collapse) delivered the Prop39Decomp refutations (merged); g5 (two value groups)
  delivered ValueGroupBridge/BridgeStress/WireIn (merged); g6 (Hahn consistency) was mid-work at the
  end; residue-induction direction delivered ResidueInduction (merged). All accepted artifacts were
  merged judge-side across this session; the swarm itself closed with 0 formal acceptances because
  its members expired without submitting — its output lives in the tree anyway.
* `QE/HahnModel.lean` (m6, salvage, verified 0 errors, no sorry): a concrete Hahn-series model of
  the frozen `L_RV` — carrier `VFT ⊕ RV` with `VFT = ℂ((t^ℚ))` (`HahnSeries ℚ ℂ`), `RV = Option (kfˣ × VG)`
  (`none` = 0 = ∞), `rv x = (leadingCoeff, order)`; **the sort axioms are proved**: `model_sdUnits`,
  `model_sdCover`, `model_sdDisjoint`, `model_sdKAdd`, `model_sdKNeg`, `model_sdKMul`,
  `model_sortClosure`, `model_sortAxioms`. This is part 1 of the consistency witness; part 2 (the
  algebraic axiom groups) is WIP — `.ultramath/smw2ku6gn/m6/F2.lean` (original, mid-edit) and
  `.scratch2/repair/F2_wip.lean` (partially repaired: 4 known errors, three at `pUnits`-unfolding
  sites) — NOT merged.
* FINDING recorded in HahnModel's header (encoding-level, worth remembering): the order on `RV`
  is forced by the frozen `rvUltrametric` to be `val t ≤ val s` with `val none = ⊤` (paper's ∞ on
  top); the alternative reading used by `Milestone0/RVModel.lean` (`t ≤ s ↔ vrv s ≤ vrv t`)
  satisfies `leTop`/`leClassOne` but FALSIFIES `rvUltrametric` — explicit counterexample
  `x = 1 + t`, `y = -1` in `ℂ((t))`. Any future model construction must use the forced reading.

## smw2mluv7 m1 (2026-11-04, accepted): the case-slot attribution is CORRECTED

* `QE/Case34Slot.lean` (m1, verified 0 errors, 22 axiom heads clean): **`M5L.Separated` is false at
  every unit** — `separated_imp_pow_not_cls_one` (test at x = y = 1: no positive power of `rv m`
  may have the class of 1) + `not_separated_of_units` (a unit has `Cls (rv m) 1` at k = 1 via
  `units_iff_le_one`). Consequences, all machine-checked:
  * Lemma 3.4's `e ∈ U(M)` and Lemma 3.6's `e ∈ U(M)` both refute `Separated`
    (`liftAllRoot_not_separated`, `liftTranscendental_not_separated`), so **3.4 and 3.6 are never
    `CaseSeparated` configurations** — carrying both is inconsistent:
    `slot34_at_caseSeparated_hypotheses_vacuous`;
  * `CaseSeparated` (with `Separated`) is the infinite-order configuration only (Lemma 3.7's
    hypothesis);
  * `caseNotSeparated_iff_unit_and_nonunit`: `CaseNotSeparated` = unit half (3.4/3.6) ∪ non-unit
    half (3.5) — a proof of only the `m^n = a` shape is provably incomplete;
  * `DivHullCover` (m4's proposal) is REFUTED: at `S = ⊤`, `m = 1` there is no `HasDivHullConfig`
    (the truncated separation fails at k = 1) — caveat: conditional on an embedding `⊤ ↪ N`.
* Deliverables besides the finding: `MonicO`/`IsRootOf`/`LiftAllRoot` (paper hypotheses +
  isolated residuals root_lift/embed/class_control), `Slot34` (the correct slot form, with
  `¬Separated`), `slot_of_liftAllRoot : Claim (⋆) ⇒ Slot34` (T = closure(S ∪ {m}), `Standing` via
  `standing_of_ClassControl`), `separated_of_pow_notin` (converse, pinned to `VFInvClosedOn`),
  `unit_class_in_S`. Stress tests: `MonicO`/`IsRootOf` inhabited by F = X − 1, e = 1; slot
  satisfiable at T = ⊤ (`slot_of_global_extension`).
* `QE/OneStepCases.lean`'s slot comments corrected in the same commit (the "separated = 3.4/3.6"
  attribution was rotated).
* Residuals named by the file: `root_lift` (needs the hred + Polynomial↔vfEval transport),
  `embed` (Engler–Prestel), `class_control` (fundamental inequality) — feeding 3.4's proof.

## smw2mluv7 salvage (2026-11-04): the separated-slot bookkeeping + the CaseNewRV analysis

Two members expired with green, unsubmitted files; verified judge-side and merged:

* `QE/Bookkeeping.lean` (m2, p2 — the Lemma 3.4 bookkeeping half). `bookkeeping_half`: for a
  separated step `S ≤ T` with `Standing S`, `VFInvClosedOn S`, `IsVFGen T`, `QuotExpansions S T e` —
  concludes `Standing T` ∧ `GammaEqQ S T` ∧ `gammaSub T = gammaSub S` ∧ `RVGenCover S T (rv e)` ∧
  `ResidualClasses S T`. Machinery: `RVNatSpanCls`/`RVIntSpanCls` (natural/integer monomial spans),
  `rvGenCover_iff_residualClasses`, `gammaEqQ_of_residualClasses`,
  `gammaHullInitial_of_residualClasses`, `divHull_gammaSub_of_gammaEqQ`. **Constraint recorded**: in
  the separated branch `IsVFGen S` is refuted (`not_separated_of_isVFGen`), so the group form needs
  `RVInvClosedOn S` as an extra hypothesis (not derivable from Γ-divisibility,
  `root_closed_not_neg_closed`); hence the `ℕ`-monomial form. Also `cls_one_of_iUnits`: `Cls` is
  Γ-equality, so the residue-field half is invisible to it.
* `QE/SlotWire.lean` (m2): `caseSeparated_of_structuralResidual` — `CaseSeparated` from the
  residual "(realisation of the extension) + `VFInvClosedOn S` + `IsVFGen T` + `QuotExpansions S T m`",
  with the Γ/RV content discharged by `bookkeeping_half`; `caseSeparated_bookkeeping` gives the extra
  conclusions at every separated step. **So the separated slot owes only realisation +
  field-generatedness, nothing about Γ/RV.**
* `QE/NewRVGlue.lean` (m6, d8 — the CaseNewRV analysis, machine-checked). §1–§2: `CaseNewRV`
  (= `M5.OneStepRVNew`) is a REALISATION statement — refutable at Hahn configurations
  (`not_oneStepRVNew_of_infinitesimal`), not repaired by Γ-divisibility
  (`oneStepRVNew_iff_gammaDivisible`, `not_oneStepRVNewGam_of_infinitesimal`); the tree's
  `ClassStepP`/`StepObligation` interfaces cannot even state the new-`rv` case
  (`not_classStepP_of_newRV`, `not_stepObligation_of_newRV`). §3: the slot's conclusion DEMANDS the
  divisible hull of `Γ(S) + ℤ·vv(m)` from any `Standing` witness (`hull_demand_of_standing`).
  §4: the one positive source is the total-extension property (`oneStepRVNew_of_total_extension`).
  Structural note: the fragments (`Lemma37`, `Lemma37_transcendental`, `Lemma38RV`, `Case38Value`)
  have NO consumer in the merged tree — the missing consumer is Remark 3.1's `L_v → L_RV`
  conversion, which the canonical route bypasses by taking realisation (`Input5R`) as hypothesis.

## smw2ngn1z m4 (2026-11-04, accepted): the slot attribution confirmed and sharpened; 3.6's Γ-step done

* `QE/Lemma36Audit.lean` (m4, d2; verified 0 errors, axioms clean): independent confirmation of the
  unit exclusion (`separated_not_units`, via `units_cls_one` from `Axioms.leClassOne` — a different
  route from m1's `not_separated_of_units`), and the SHARPENING: `not_separated_of_vpow_mem` — a root
  of `X^n − a` with `a ∈ S`, `a ≠ 0` is ¬Separated (test at k = n, x = 1, y = a), so **Lemma 3.5's
  element too is never `CaseSeparated`**. Net: `CaseSeparated` is the value-growth regime
  (Lemmas 3.7/3.8) ONLY, and `caseSeparated_empty_of_vfgen` shows it is EMPTY at `IsVFGen`
  substructures (e.g. Ŝ) — the slot is trivially true exactly where the paper's Lemma 3.3 leaves `S`
  VF-generated. Non-vacuity of the ¬Separated slot pinned by `lemma36UnitsHyp_satisfiable` (S = ⊤,
  e = 1) and `separated_top_forces_zero`.
* `QE/GroupCore.lean` (m4; Mathlib-only, no frozen imports): **3.6's Γ-unchanged step, modulo the
  quote**. `le_of_ratRankZeroIn` / `eq_top_of_ratRankZero` / `mem_of_ratRankZero`: a divisible
  subgroup with rational-rank-zero quotient contains everything; `EP343_ratRankZero` is EP 3.4.3
  transcribed as a hypothesis and `gamma_unchanged_of_EP343` is the wiring (qe.tex:762-765).
  Sharpness: `divisibility_necessary` (2ℤ) and `torsion_is_obstruction` (ZMod 2) — both inputs are
  needed.
* Remaining for 3.6 per this member: rv(e)-transcendence, the descent, the b/b* induction, EP
  3.3.4's residue half — the directions other q-members hold.

## smw2ngn1z m3 (2026-11-04, accepted): the EP quotes transcribed; DivisibilityStep's Γ-content done

* `QE/EPQuotes.lean` (m3): BOTH Engler–Prestel inequalities transcribed as quoted Props in the
  Mathlib valuation vocabulary the consumers use —
  `EP343_dimension_inequality` (e transcendental over K + residue-transcendental ⇒ the value group
  is torsion over Γ(K); the ratrank-0 form Lemma 3.6 consumes) and
  `EP334_fundamental_inequality` (residue degree ≤ field degree for a finite extension of valued
  fields, with the equality case giving value-group equality; the form Lemmas 3.4/3.8 consume) —
  with wiring and stress lemmas. Author ruling: quoted, not proved.
* `QE/EPAudit.lean` + `QE/EP_LEDGER.md` (m3): the Mathlib 4.33.1 inventory behind that decision —
  vocabulary present (`Valuation`, `IsLocalRing.ResidueField` as an algebra giving residue degrees,
  `Module.finrank`, `Transcendental`, `HasExtension`); the CONTENT absent (no Abhyankar, no rational
  rank, no dimension inequality, no residue-degree theorems). So both inequalities, and EP 3.2's
  residue facts, must stay hypotheses.
* `QE/GammaTorsion.lean` (m3): **DivisibilityStep's Γ-content, wired**: 
  `gammaEqQ_of_gammaDivisible_of_hullInitial : Assembly.GammaDivisible S → GammaHullInitialQ S T →
  GammaEqQ S T` — the ledger's input-4 conclusion from its two Γ-hypotheses; and
  `exists_vf_class_witness` — the paper's VF-sorted value normalization
  (∀ t ∈ T with iRV t, t ≠ 0, ∃ a ∈ VF(S) with class equality `gammaMk t = gammaMk (rv a)`, given
  `IsVFGen S`), which is exactly the shape Lemma 3.6's b/b* induction consumes. Sharpness: 
  divisibility is not removable (G = Multiplicative ℤ, K = {g + g}); the exponent must be positive.

## smw2ngn1z m1 (2026-11-04, accepted): Claim (⋆)'s RV-containment, both branches, inverse-free

* `QE/NewRVClaim.lean` (m1, d5): the new-`rv` branch's `RV`-containment (Lemma 3.7's second half /
  3.8's residue-side RV-containment — the part `QE/Lemma37.lean` left unformalized). The key device:
  `L_RV` has no RV-inverse, so membership in `⟨RV(S), rv e⟩` is written inverse-free with two
  witnesses — `StarMem S e y := ∃ s t j k, s,t ∈ S∩VF nonzero with rv s, rv t ∈ S ∧
  Cls (y·rv s·(rv e)^j) (rv t·(rv e)^k)`. `rvQuotExpansion_star` (the quotient step: pair the
  minimal monomials, multiply by rv x, transitivity) gives `ResidualClassesNew_of_VFGen`:
  `IsVFGen T + QuotExpansions S T e + Separated S e ⇒ every RV element of T is StarMem or rv 0`.
  No `rv e ∈ S`, no inverse closure.
* `QE/OldRVClaim.lean` (m1): the same "keep the factor" move for the old-`rv` branch:
  `RatioInS` (the ratio form), `rvQuotExpansion_ratio`, `ResidualClassesRatio_of_VFGen` — the
  RV-containment in ratio form with NO `VFInvClosedOn` and NO `KEqTop` — plus
  `ResidualClasses_of_VFGen'` re-deriving the tree's `ResidualClasses` while dropping `KEqTop`, and
  `ratio_of_residual` (the converse, at VF-generated `S`).
  **Caveat recorded**: converting the ratio form back to the tree's class form still consumes
  `VFInvClosedOn` (`ResidualClasses_of_Ratio` needs the inverse `s'` to eliminate the class
  representative), so the precise claim is "the ratio form is `VFInvClosedOn`-free", not its
  removal everywhere. A consumer that can accept the ratio form gets the hypothesis for free.
* Stress: `not_separated_top` makes the ⊤-witness test of these hypotheses necessarily negative
  (honestly so, not vacuously).

### Flagged discrepancy (unverified): which lemmas consume the EP inequalities

m1's report states "Lemma 3.8 does not consume EP 3.3.4/3.4.3; only 3.4 and 3.6 do", while
`QE/Lemma38RV.lean:71`'s comment says the converse for 3.8's `vv(e) ∉ Γ(Ŝ)` step. Neither has been
checked against the other by a judge; whoever next touches 3.8 should settle it in Lean (does
`lift:value:full`'s proof need the fundamental inequality, or only the residue-side algebra?).

## smw2mluv7 ended (solved; 1 formal acceptance) — its last five files salvaged and merged

The swarm dissolved with only m1's formal submission, but five members left green unsubmitted work;
all verified judge-side (exit 0, 0 errors, 0 sorryAx, axiom heads ⊆ {propext, Classical.choice,
Quot.sound}) and merged:

* `QE/NonVacuity.lean` (m7, p7 — the highest-stakes direction). §1 gate analysis:
  `relGate_of_saturatedFS`/`relGate_diag_of_saturatedFS` (SaturatedFS gives gate pairs; the diagonal
  gate is saturation-hard via `saturatedFS_of_relGate_diag`, i.e. `SatBridge`);
  `qeOfGate_iff_hasQE_of_empty` + `shoenfieldTestRel_iff_hasQE_of_no_relGate` (**empty gate ⇒ the
  quotation is equivalent to the target — circularity**); `shoenfieldTestRel_of_not_extendsAt`
  (failed extension ⇒ quotation trivially true); `hasQE_iff_qfTypeDetWS`; `input5R_implies_prop39Sat`.
  §2 the exact obligation: `not_finSatAt_iff` — failure of finite satisfiability at a triple is ONE
  formula of the pushed type with no realisation; and `configHuge_ordinal_core_finsat` /
  `configTiny_ordinal_core_finsat` — every finite piece of the configuration's **ordinal core** is
  realised in EVERY model of ACVF (c^{N₀+1}; (N₀+1)-th root via Γ-divisibility), so the failing
  formula must come from the **residue/quantifier part** of the pushed type. §3 (documented, not
  machine-checked, and correctly flagged as using QE-for-ACVF — an argument about the statement, not
  in its proof): the expected answer is that the type IS finitely satisfiable, `SatRel` then realises
  it, contradicting `ArchimedeanRV N` — so no gate pair carries the configuration and
  `Prop39Decomp`'s Archimedean refutations are vacuous rather than fatal. This narrows the open
  question to: finite satisfiability of the config's non-ordinal (residue/quantifier) part.
* `QE/Case35Slot.lean` (m5, p5 — 32 theorems): the exact slot statements and the obstruction.
  `SeparatedBelow` with `separated_iff_forall_separatedBelow` (Separated = all finite truncations),
  `exists_minimal_violation`/`separatedBelow_of_minimal`; the paper's branch hypothesis
  `RootStepHyp`; and the KEY finding — at `Standing S` (Γ(S) divisible) the `m^n = a` shape with
  separation-below-`n` (n ≥ 2) is **inconsistent**, so the paper's 3.5-shaped step belongs to the
  PREP (divisible-hull, Lemma 3.3) construction, not to the one-step slot at Standing S; the correct
  branch statement there is the exponent-one (`RVOldClass`) form. Wiring:
  `cases_of_branch`, `caseNotSeparated_of_paper_branch_and_global`; non-vacuity
  `caseNotSeparated_hyp_satisfiable`.
* `QE/HensDemand.lean` (m8, p8): the Polynomial↔vfEval bridge (`polyOf`, `eval_polyOf`,
  `monic_polyOf`) and the henselianity facts: `isHenselianVF_of_vf_full` (full-VF substructures are
  henselian) and `isHenselianVF_top` — so `IsHenselianVF ⊤` holds (the predicate is inhabited, not
  vacuous, after the erratum fix).
* `QE/InterfaceClosure.lean` (m3, p6): polynomial-expansion interface — `PolyExpansions`,
  `polyExpansions_quot`, `rv_mem_of_polyExpansions`, `ResidualClasses_of_poly`,
  `standing_of_poly_hypotheses`, `SlotRealization`, `SlotFieldData`.
* Chain note: `RV_henselian.olean` was missing from `.scratch2/sec3` (never built with `-o`); now
  built.

## smw2ngn1z m7 (2026-11-04, accepted): Lemma 3.6's Γ-step needs NO dimension inequality

* `QE/UnitTranscend.lean` (m7, d6): **`val_sum_eq_one`** — for a unit `e` (`v e = 1`) whose residue is
  transcendental over the base residue field (as the no-vanishing-residue-polynomial hypothesis),
  an expansion `Σ cᵢ e^mᵢ` with integral coefficients, one of value exactly 1, has value exactly 1:
  there is NO cancellation. Proof: ultrametric bound, then if the value is < 1 the residue vanishes,
  residue-linearity splits it into the residue polynomial, and transcendence forces the value-1
  coefficient's residue to 0 — contradiction. **`gamma_step`** then gives, for any quotient of
  expansions (i.e. any `b ∈ VF(⟨Ŝ,e⟩)`), a base element `a` with `v b = v a` and `v(b/a) = 1` — the
  paper's `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)` and value normalization (qe.tex:741-747) **without Engler–Prestel
  Thm 3.4.3**. So EP 3.4.3 can be DROPPED from Lemma 3.6's hypotheses: a strict reduction in
  quote-dependence. (Lifting to the frozen encoding still needs `iUnits`-form unit-ness and the
  `VFInvClosedOn`/`IsVFGen` fraction-field representation — the latter needed by 3.5 anyway.)
* `QE/UnitSharpness.lean`: the countermodel — `t` in `R[[Z]]` with `addVal` is transcendental over
  the constants, the base value group {0} is divisible, yet `addVal t = 1` is not a base value: the
  unit hypothesis is exactly what substitutes for the quote.
* `QE/EPQuotesGamma.lean`: `gamma_collapse` (torsion + divisible ⇒ equal, PROVED) — the only use of
  EP 3.4.3 at qe.tex:743, now a theorem; plus `RatRankZero`, `ResidueDegreeLeFieldDegree`.
  **Correction recorded**: EP 3.3.4 gives residue degree ≤ field degree; Lemma 3.4's *equality*
  needs defectless + unramified (the other half from `F` monic + `F̄` irreducible + `e` a unit) —
  so `EP334_fundamental_inequality` (QE/EPQuotes.lean) should not be read as supplying the equality
  half by itself.
* `QE/UnitTranscendWitness.lean`: a top-witness for `ResidueTranscendental` (trivial residue field)
  and the hypothesis repair (injective exponents), keeping the definition honest.

## smw2ngn1z m2 (2026-11-04, accepted): the value-group layer, general form with sharpness

* `QE/RatRank.lean` (m2, d3; Mathlib-only, at exactly `GammaOf M`'s instance signature):
  `RatRankZero H K := K ≤ divHull H` (`ratRankZero_iff_le_divHull`, `Iff.rfl`),
  `eq_of_divisible_of_ratRankZero` (H ≤ K → DivisibleSubgroup H → ratrank zero → K = H; uses
  torsion-freeness via `pow_right_injective`), and **`maximal_extension_iff`** — with a root-closed
  ambient G, the inference holds for EVERY K ≥ H iff H is divisible: divisibility is not a side
  condition but the exact content of the inference. `RootableBy` bridge to `GammaDiv`'s form.
* `QE/RatRankTensor.lean`: the canonical Mathlib rational rank, `Module.rank ℚ (ℚ ⊗[ℤ] A)`, with
  `rationalRank_eq_zero_iff_torsion` — a Prestel–Engel quote in rational-rank form now has a correct
  target statement, and `eq_of_divisible_of_rationalRank_eq_zero` consumes it.
* `QE/RatRankSharp.lean`: sharpness on the nose — divisibility necessary (ℤ in ℚ: ratrank zero, not
  divisible, hull = ⊤ ≠ ℤ), rational rank necessary (ℚ×ℚ vs ℚ×{0}), root-existence necessary;
  non-vacuity at ℚ and at `Γ(M)`.
* `QE/GammaInstantiation.lean`: the step applies verbatim at the tree's `GammaOf M`.
* Relation to the frontier: m7's `QE/UnitTranscend.lean` shows Lemma 3.6's Γ-step needs no dimension
  inequality at all, so this layer is not on the critical path — it is the correct general statement
  of the quote-based route plus the reusable tensor characterisation, and it pins (by sharpness)
  which hypotheses any future rational-rank argument must carry.

## smw2ngn1z m8 (2026-11-04, accepted): LEMMA 3.6 PROVED at the frozen level, modulo EP 3.4.3; swarm closed

* `QE/Lemma36Gamma.lean` (m8, d1, no residual): `gammaEq_of_gammaHullInitial` — **`GammaDivisible S` +
  `M5Ledger.GammaHullInitial S T ⇒ M5Ledger.GammaEq S T`** at the TREE's predicates (proof: root
  extraction `gamma_root_of_gammaDivisible` + torsion-free injectivity `gamma_pow_inj`); then
  `ResidualClasses S T` (Claim (⋆) in class form) and `Standing T`, with NO
  `VFInvClosedOn`/`QuotExpansions`/`IsVFGen`. See also `divisibility_essential` (Γ = ℤ, 2ℤ): the
  divisibility cannot be dropped — that branch is Lemma 3.8's.
* `QE/PEQuotes.lean`: both EP theorems as quoted Props, specialised and wired — EP 3.4.3 ⇒
  `GammaHullInitial` under `rv(e)` transcendental + `e ∈ U(M)`; EP 3.3.4 ⇒ `GammaBoundBy` (the
  value-group half) in the algebraic case; `RVTrans`, `AlgebraicOverVF` definitions; wired to
  `Standing ⟨Ŝ,e⟩`; stress tests.
* `QE/Lemma36Statement.lean`: `Lemma36Hyp` (pair-level named hypotheses, no ∀M∀N gate), `ClaimStar`
  (= `ResidualClasses` at `closure (S ∪ {e})` ∧ `Standing`), and
  **`lemma36_claim_star : EPDimensionInequality → Lemma36Hyp → ClaimStar`** — Lemma 3.6
  (`lift:transcendental`) PROVED modulo the single EP 3.4.3 quote, plus `exists_vf_of_rv` (the
  paper's `d ∈ VF(N)`). Stated-and-unused residuals: `TranscendenceDescent` (q1a),
  `RVTransImpliesSeparated`.
* Complementarity: this is the tree-vocabulary counterpart of m7's Mathlib-level `UnitTranscend`.
  Lemma 3.6 now has two routes: WITH the quote (m8, frozen level, fully wired) or WITHOUT
  (m7, Mathlib level; the lift of m7's `gamma_step` to `GammaDivisible`/`GammaHullInitial` is the
  remaining piece for a quote-free 3.6).
* **smw2ngn1z ended solved: 6 acceptances** (m4 audit+GroupCore, m3 GammaTorsion+EPQuotes, m1
  NewRVClaim/OldRVClaim, m7 UnitTranscend, m2 RatRank layer, m8 Lemma 3.6). Its board also carried
  the m6/m7 trdeg and 3.7 directions unfinished.

## TREE-WIDE AUDIT (2026-11-04, after ~45 merges): 196 files, 0 errors, 19 known sorries

`make milestones` over `Milestone0/*`, `Milestone0/accepted/*`, `QE/*` (196 files: 176 QE + 20
Milestone0) finished `EXIT=0`: **every file exit=0, errors=0**. Sorry counts — unchanged from the
recorded baseline, i.e. no new holes were introduced by today's merges:
`Milestone0/Balls.lean` 1, `Milestone0/Encoding.lean` 2 (the two frozen targets),
`QE/Assembly_val.lean` 2 (their copies), `QE/Sec3_frozen.lean` 4, `QE/Sec3_sat.lean` 8,
`QE/TransferWS.lean` 2 — 19 total in 6 files.

## smw2ox51x launched (2026-11-04, 8 members): the last case-lemma push

Directions r1–r3 (Lemma 3.4's residuals `root_lift`/`embed`/`class_control` + the `Slot34`
endgame), r4 (3.5's surviving exponent-one branch), r5 (the quote-free lift of `gamma_step` to the
frozen predicates — would eliminate EP 3.4.3 from 3.6), r6 (3.8's EP question + slot statement),
r7 (the final assembly ledger: what must be proved for `HasQE`, as named Props with status), r8
(non-vacuity / finite satisfiability of the Archimedean configuration's pushed type).

## smw2ox51x m8 (2026-11-04, accepted): the Archimedean question determined; the frontier SPLITS

* `QE/NonVacuity2.lean` (m8, r8; verified 0 errors, 24 axiom heads clean). The statement-level
  question is settled as far as the tree allows:
  1. **Both configurations contradict Archimedean-ness of their own SOURCE model**
     (`not_archimedean_of_configHuge`, `not_archimedean_of_configTiny`): every firing pair has a
     non-Archimedean source and an Archimedean target. Non-vacuity of the route therefore reduces to
     the existence of a `SatRel` pair with an **Archimedean target and non-Archimedean source** —
     not decidable in the tree (no ACVF model with non-Archimedean Γ; no `SatRel` pair at a model
     target).
  2. The configuration's **ordinal atoms are realised by ONE element in EVERY target**, Archimedean
     or not (`huge/tiny_ordinal_core_in_target`, `huge_ordinal_atoms_realizable`) — so the failing
     formula of `not_finSatAt_iff` is provably NOT ordinal; the value-group reading is refuted.
  3. The ledger, all machine-checked: `RefutingConfig → ¬Input5R`, `→ ¬ExtendsHere`,
     `→ ¬QFFinSat` (formula level), `→ ¬Archimedean source`. And the key refinement:
     **`input5R_of_finSat_split`**: `Input5R` = `FinSatAtArchimedean` + `QFFinSat` at
     **non-Archimedean targets**. So **the case lemmas 3.4–3.8 need be proved only at
     non-Archimedean targets**, where the tree's Archimedean refutations do not fire; conversely a
     `RefutingConfig` would falsify the whole input. `not_finSat_of_configTiny_gateFree`: the
     finite-satisfiability failure is gate-free.
  4. Honest residual: the residue/quantifier part of finite satisfiability is QE for ACVF itself —
     identified as such, not papered over.

## smw2ox51x m2 (2026-11-04, accepted): a tree `sorry` ELIMINATED; the gate hypothesis corrected

* **`Milestone0/Balls.lean` is now sorry-free** (applied in place and re-verified: exit 0, 0 errors,
  0 `uses .sorry`, `infinite_boolComb_contains_openBall` axiom-clean). `Milestone0/Balls.lean:499`'s
  frozen target — "an infinite Boolean combination of balls contains an open ball" — is PROVED
  (from swarm m2's `Balls_target.lean`, differing from the tree file by exactly the proof block and
  the theorem's proof; the STATEMENT is verbatim). Proof: normal forms (`rvBall_normal`: an
  `rv`-ball is an open ball or a point; `IsBallN`), atoms as fibres of the membership-pattern map, an
  infinite union of finitely many atoms has an infinite atom, and at a nonzero point every ball
  containing it is a point (finitely many) or contains an open ball at it.
  **Hypothesis finding**: `hne` is UNUSED (the theorem keeps its verbatim statement, so the
  redundancy is documented, not exercised); `s.Infinite` is essential.
  Tree sorry count: **19 → 18** (remaining: the 2 frozen Encoding targets, their 2 copies in
  `Assembly_val`, `Sec3_frozen` 4, `Sec3_sat` 8, `TransferWS` 2).
* `QE/Gate.lean` (m2, second file; 0 errors, axioms clean): `ShoenfieldQuote.lean` §5's hypothesis
  `∀ N, ¬ SaturatedFS N` is **FALSE as written** — `saturatedFS_of_subsingleton` +
  `paperGate_subsingleton_inhabited` show a subsingleton `LRV.Structure` satisfies `SaturatedFS`, so
  that conditional theorem is vacuous. Corrected form: `NoSatModel := ∀ N ⊨ ACVF, ¬ SaturatedFS N`,
  with `shoenfieldTestSat_iff_hasQE_of_noSatModel`, `noSatModel_of_forall_not`, and the dichotomy
  `saturatedFS_of_satBridge_of_satRel`: `SatBridge ⇒ (no ACVF model is diagonally SatRel) ∨ (some
  ACVF model is SaturatedFS)`. The §5 circularity route is therefore closed as stated and re-opened
  only under the correct `NoSatModel` hypothesis.

## smw2ox51x salvage (2026-11-04): six more files verified and merged (smarm ended solved, 2 acceptances)

The swarm's other six members expired without submitting but left green work; verified judge-side
and merged (one WIP left behind):

* `QE/Lemma38EP.lean` + `QE/Lemma38Frozen.lean` (m6, r6 — the 3.8 EP question): the algebraic content
  of Lemma 3.8 at genuine Mathlib valuations (`lemma38_algebraic_content`, `lemma38_of_rv_new`,
  `value_transfer_of_divisible`) plus the sharp group-theoretic fact
  `upgrade_needs_divisibility` and its realisation: in `Multiplicative ℤ` with `H = ⟨2⟩`, `g^2 ∈ H`
  but `g ∉ H` — the ramified instance `ℚ ⊆ ℚ(√2)` at the 2-adic place, where `v(√2)² = v(2) ∈ Γ(ℚ)`
  but `v(√2) ∉ Γ(ℚ)`. So 3.8's value-group upgrade NEEDS divisibility (which 3.6 has and 3.8 does
  not — consistent with `gammaDivisible_top` being about the ambient model, not the subfield).
  `Lemma38Frozen` states 3.8 at `CaseNewRV`'s hypotheses on the merged fragments.
* `QE/RootHull.lean` (m1, r1): the root-hull route for 3.4 — `standing_top_via_rootClosed`,
  `oneStepPaper_of_rootHullEmbedding`, `paper_theorem_2_3_sat_of_rootHullEmbedding`, and the
  packaged `RootHullRealisation` with `oneStepPaper_of_rootHullRealisation`
  (`paper_theorem_2_3_of_rootHullRealisation`): 3.4's content as ONE named realisation property of a
  root hull, wired to the route.
* `QE/D7Hull.lean` (m5, r4): the 3.5 step analysis — `not_hullBaseStep_of_cardinality`,
  `hullBaseStep_KEqTop_trivial`, `rootStepResidual_standing_trivial`,
  `hullBaseStep_iff_nonKEqTop`, `rootStepResidual_iff`, and
  `extendsHere_iff_steps_and_oneStep`: Proposition 3.9 decomposed into the hull base step + root-step
  residuals + the one-step, with the triviality tests showing which residuals are contentful.
* `QE/RouteLedger.lean` (m7, r7 — the final ledger): `relCases_of_parts` (the relative-gate case
  split: separated/unit/non-unit), **`paper_theorem_2_3_of_five_rel`**: Theorem 2.3 at the paper's
  `relGate` from five named parts + ShoenfieldTestRel; `hull_and_cases_iff_satReal`,
  `gatedHull_and_cases_iff_ledgerInput5P`, `relHull_and_cases_iff_input5R`,
  `gatedHull_forces_units_size`. This is the route's final edition at the honest gate.
* `QE/UnitCase.lean` (m3, r5): the unit-case analysis (namespace `M8`), merged after trimming three
  dangling `#print axioms` lines for theorems that were planned but not written (the rest of its
  audit is intact).
* WIP left behind: m4's `RootLift.lean` (39 KB, one parse error in a theorem statement at :748 —
  a mid-edit; kept at `.ultramath/smw2ox51x/m4/RootLift.lean` for the next 3.4 worker) and m3's
  missing `M8` companion file.

## smw2qpqe7 m6 (2026-11-04, accepted): THE MATRIX — the route's definitive accounting

* `QE/Matrix.lean` + `QE/MATRIX.md` (m6, u6; verified 0 errors, 39 axiom heads clean). The
  per-part matrix, machine-checked:
  - **per pair, no size needed**: `SatRel ∧ QFFinSat ⇒` hull, `CaseSeparated`, `UnitSlot`,
    `NonUnitSlot`, `CaseNewRV` — **and it produces `SizeHyp`**;
  - gated: `relHull/relSeparated/relUnit/relNonUnit/relNewRV_of_finSat`, jointly
    `fiveParts_of_finSat`;
  - **EXACTNESS**: `fiveParts_pair_iff_satReal`, **`fiveParts_iff_input5R`** (the five-part list IS
    Marker's saturated realisation — no part is slack), `relCases_iff_parts`,
    `unit_nonunit_iff_notSeparated`, `separated_and_notSeparated_iff_oneStepRVOld` (the u1/u2 split
    loses nothing);
  - weaker rows → tree interfaces: `relHull_iff_prepStepP`,
    `relUnit_of_rootData_slot34_transcendental`, `relNonUnit_of_branch`,
    `relNewRV_iff_oneStepRVNew`;
  - **REFUTATION row**: `not_finSatAtRelGate_of_config` (the ∀-form of `QFFinSat@relGate` dies at
    Archimedean-config pairs) and `not_finSat_of_config` (the pointwise form too) — consistent with
    `QE/NonVacuity2.lean`; the blanket `QFFinSat@relGate` route is therefore NOT usable as stated;
  - **CANONICAL form**: `paper_theorem_rel_of_finSat_split : ShoenfieldTestRel → FinSatAtArchimedean
    → FinSatOffArchimedean → HasQE`, with `no_refutingConfig_of_arch_half` (the Archimedean half is
    not refutable by the tree's configuration) and `two_routes_agree`.
* Verdict of the matrix (to be quoted): u1–u5 cannot be short-circuited by a blanket
  `QFFinSat@relGate`, but **their conjunction is exactly `Input5R`**; the canonical frontier is the
  split form, and the case lemmas are needed at the non-Archimedean targets.

## TREE BASELINE (2026-11-04, second full audit after the day's merges): 211 files, 0 errors, 18 sorries

`make milestones` over `Milestone0/*`, `Milestone0/accepted/*`, `QE/*`: **211 files** (191 `QE/` +
20 `Milestone0*`), `EXIT=0`, **0 errors and 0 non-zero exits**, **18 sorries in 5 files**:
`Milestone0/Encoding.lean` 2 (the frozen Theorem 2.3 and 2.8 targets), `QE/Assembly_val.lean` 2
(their copies), `QE/Sec3_frozen.lean` 4, `QE/Sec3_sat.lean` 8, `QE/TransferWS.lean` 2.
`Milestone0/Balls.lean` no longer appears — its sorry was eliminated in a clean build (the proof of
`infinite_boolComb_contains_openBall` holds from scratch, not just incrementally).

## smw2qpqe7 m2 (2026-11-04, accepted): RelNonUnit reduced; the slots' missing clamp diagnosed

* `QE/NonUnitAssembly.lean` + `QE/NonUnitNOTES.md` (m2, u2; verified 0 errors, 26 axiom heads
  clean):
  - `relNonUnit_of_qffinsat` — `QFFinSat@relGate ⇒ RelNonUnit`;
  - **`nonUnitSlot_of_extAlongStanding`** — the slot follows from monomorphism-extension along
    `Standing` inclusions, a hypothesis that never mentions `m`, `¬iUnits` or `¬Separated`: the
    non-unit slot has **no pure-`M` content**; the hull row is trivial (`nonUnitHull_holds`, `T = ⊤`,
    costing exactly relGate's `SizeHyp`); `SlotTotalExt` isolated as the weakest realisation row;
    sandwich with `SlotAtomic` (NonUnitSlot ⇒ SlotAtomic; SlotAtomic + `Standing (closure (S∪{m}))`
    ⇒ NonUnitSlot).
  - **THE DIAGNOSIS**: the `Γ`-clamp `M5Ledger.GammaHullInitial` (which `DivisibilityStep` uses to
    forbid `T = ⊤`) is ABSENT from all four `M4Cases` slots, so their hull rows are trivially
    satisfiable — the slot-level counterpart of `QE/FinalAudit.lean`'s ⊤-witness finding. Lemma 3.5's
    content therefore belongs to the hull/`QFFinSat` row, and `ClampedNonUnitHull` (with the clamp;
    satisfiable) is the paper-faithful restatement.
  - Honest dead-end checks: at perturbation points that ARE slot points, `ResidualClasses`/RV-control
    fail; `RVOldClass ⟺ ¬Separated`, so `Case35`'s branch restricts only by its conclusion;
    `Bookkeeping`/`InterfaceClosure` need `Separated` and are inapplicable here.
  - `paper_theorem_2_3_of_rel_parts_no_nonunit`: the other four parts + `QFFinSat@relGate` already
    give `HasQE` — so `RelNonUnit` is strictly weaker than the realisation row.
  - Non-vacuity: `exists_nonunit` (extracted from `axNontrivialRV`).

## smw2qpqe7 m5 (2026-11-04, accepted): the frontier's shape is FORCED, not chosen

* `QE/Shrink.lean` + `QE/SHRINK.md` (m5, d8; verified 0 errors, 18 axiom heads clean):
  - **`input5R_iff_relHull_and_fourParts`**: `Input5R ⟺ RelHull ∧ RelSeparated ∧ RelUnit ∧
    RelNonUnit ∧ RelNewRV` — the six-part list is the SAME assertion as the two-hypothesis endgame
    `paper_theorem_rel_two`. So no restructuring can shorten the list: a shorter list needs a part
    PROVED, and the only dischargeable hypothesis is the quote (Shoenfield's test), which Mathlib
    cannot supply. **The frontier's shape is machine-checked, not a choice of presentation.**
  - **`hullExtension_iff_nonStanding`**: `HullExtension ⟺ (∀ S, ¬Standing S → HullExtensionAt S)`.
    All four case slots carry `Standing S`, so **none of them can discharge `RelHull`** — the precise
    structural reason it must stay a separate hypothesis.
  - `relHull_iff_baseRootResidual`: `RelHull ⟺ D7Hull.HullBaseStep ∧ RootStepResidual` per relGate
    pair, with the converse `rootStepResidual_of_hullRootStep` that `QE/D7Hull.lean` lacked, and the
    content localized to the `¬KEqTop` and `KEqTop ∧ ¬Standing` domains.
  - `relGate_units_card` + `relGate_no_card_obstruction`: `relGate`'s size conjunct gives
    `#Kˣ(M) ≤ #N`, so the hull slot's cardinality obstruction never applies at `relGate` pairs — the
    gate is exactly the cardinality the construction forces.
  - Also a gate-level split of the unit slot (for u1's worker).

## smw2qpqe7 m1 (2026-11-04, accepted): RelUnit assembled; every slot is an EMBEDDING statement

* `QE/RelUnit.lean` + `QE/RELUNIT.md` (m1, u1; verified 0 errors, 42 axiom heads clean):
  - **§0 STRUCTURAL (no ACVF, no gate)**: for the slot conclusion shared by ALL five slots,
    `Standing (Closure S m) ⇒ (SlotConcl S f m ↔ ClosureEmbedding S f m)`. So the `T`, `m ∈ T` and
    `Standing T` conjuncts are NEVER extra content — **every slot's real content is the embedding
    statement**. This is the general form of the ⊤-witness/attribution observations.
  - `UnitSlot ⟺` the unit-cone implication (¬Separated is derivable at units — the hypothesis is
    redundant) and `UnitSlot ⟺ UnitClosureEmbedding ∧ UnitClosureStanding` with the realisation half
    NECESSARY (`closureEmbedding_of_unitSlot`).
  - `RootData` reduced: `rootData_iff_rootData'` (the `iRv m ∈ S` row is redundant);
    `slot34_holds` — **`M5P1.Slot34` is a theorem** (from `slot_of_liftAllRoot`);
    `algebraicUnitSlot_of_rootData_via_slot34` identifies **3.4's content with `RootData` exactly**.
  - Statement-level finding: the frozen `M8.ClaimStar` omits the paper's embedding half of
    Claim (⋆); the transcendental CLASS half is DERIVED from the paper's hypotheses (residue
    transcendence, `QuotExpansions`, `IsVFGen` closure, `VFInvClosedOn`) via `QE/UnitCase.lean` —
    **no EP 3.4.3, no RVTrans**.
  - Assembly: `unitSlot_of_34_and_36_paper`, `relUnit_of_parts`/`_gated_parts`/`_rootHull`/
    `_rootHullRealisation`, and `paper_theorem_2_3_of_parts` (the five-part endgame with `RelUnit`
    split). Residual named: `TranscendentalRealisation` (`f* : ⟨Ŝ,m⟩ → N`) + `RootData` + the
    closure VF-part rows. `relGate` is never consumed — the assembly is per-pair.
