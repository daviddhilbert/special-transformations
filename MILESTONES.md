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
| 1 | algebraic layer: `vrv`, exact sequence, balls, polydiscs, valuative centre | §3–§4 | **partly, inside the encoding**; nothing as a theorem |
| 2 | definable sets and dimensions: `acl`/`dcl`, `dimVF`/`dimRV`/`dimfib`, 4.2/4.4/4.6, `VF[k,·]`/`RV[k,·]`, `L`, Grothendieck semigroups | §4 | **`acl`/`dcl` only**; dimensions and categories absent |
| 3 | special bijections: 5.1, 5.4, 5.5, 5.6, 5.7 | §5 | **scaffold green, but only in `.ultramath/`**; 5.2/5.4/5.5 are statements |
| 4 | lifting functions: Hensel 7.2, Thm 7.6, Cor 7.7 | §7 | **nothing** |
| 5 | differentiation and volume forms: 9.1–9.14, 9.16, 10.4, 10.5, 10.6 | §9–§10 | **nothing** |
| — | **Theorem 2.3 (QE)** | §2 | the bulk of the work; see the last section |
| — | Theorem 2.8 (C-minimality) | §2 | statement only |

## What was measured

| directory | files | green | errors | `sorry` warnings |
| --- | --- | --- | --- | --- |
| `Milestone0/*.lean` | 6 | **6** | 0 | 3 (`Encoding` 2 — the two frozen targets; `Balls` 1) |
| `Milestone0/accepted/*.lean` | 10 | **10** | 0 | 0 |
| `QE/*.lean` | 45 | **45** | 0 | 19 |
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

**Milestone 1 — the `Γ` side exists inside the encoding, the exact sequence does not.**  Part 4 of
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

**Milestone 3 — the scaffold is green but it is not in the tree.**
`.ultramath/smw18ygko/m1/Sec5.lean`: 1122 lines, standalone (`import Mathlib`), compiled here —
exit 0, 0 errors, **no `sorry`** — with 55 theorems: `Pt`, `key`, `SamePD`, `polydisc`, `rvHull`,
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
(the sorted-context fragment), `QE/QF2Cover.lean` (`qf2_cover` stated, 2 `sorry`s),
`QE/TransferWS.lean` (the frozen fragment statement), `QE/Assembly_val.lean` (the assembly; still
carries a copy of the encoding, hence the same 2 `sorry`s), `QE/{Sec3_frozen,Sec3_sat}.lean` (§3
over parameter pairs and over the monster model), `QE/{FailProbe}.lean` (the located obstruction).

Open, in order of sharpness:

1. **`QFStep IsNontrivialVF Axioms.ACVF`** — the one-element back-and-forth step.  With it,
   `NontrivialTransferWS Axioms.ACVF` follows, and `AllNontrivial Axioms.ACVF` is already proved.
2. **`QFRes2.qf2_cover`** — stated; needs the `Option`-valued term extraction (`vfOpt`/`rvOpt`) and
   its soundness induction, then the formula induction.
3. The remaining §3 item with a printed proof, `alg:ind:imag` (needs exchange — frozen — plus the
   parameter transport `QE/ParamBridgeRelabel.lean` now supplies, plus the `rv`-fibre/countability
   argument).
