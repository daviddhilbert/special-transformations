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
