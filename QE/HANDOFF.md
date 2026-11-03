# Handoff: the QE thread (state at end of the long session)

Read this first if you are picking up Theorem 2.3. It is deliberately short; the detail is in
`QE-PLAN.md` (chronological record) and `Milestone0/DECISION.md` (rulings and specifications).

## What is green right now

| file | sha / status | what it is |
| --- | --- | --- |
| `Milestone0/Encoding.lean` | `851d6a98…`, 0 errors, 2 `sorry`s | the frozen target; the two `sorry`s are `theorem_2_3_quantifier_elimination`, `theorem_2_8_c_minimal` |
| `Milestone0/Saturation.lean` | green, no `sorry` | Marker-shaped `Saturated`/`MonsterModel`/`MonsterACVF` |
| `QE/Sec3_sat.lean` | green, 7 `sorry`s | §3 over the monster model: `alg:ind:imag`, `average`, `ball:proper:sub:center`, `dcl:to:ac`, `effectiveness`, `algebraic:balls:…`, `rv:effectiveness` |
| `QE/TransferWS.lean` | green, 2 `sorry`s | the QF-type assembly over the fragment: `TransferAtWS`, `NontrivialTransferWS`, `TrivialTransferWS`, `CaseSeparationWS`; targets `nontrivialTransferWS_ACVF`, `caseSplit_ACVF` |
| `QE/Assembly_val.lean` | green, 23 246 lines, **2 `sorry`s** (the embedded copy of the frozen targets) | the assembly; the QF balls bridge is merged in |
| `QE/Sec3_frozen.lean` | green, 5 `sorry`s | §3 over arbitrary models, `SP`/`acl`/`dcl` |

Build recipes: §3/Saturation/TransferWS files use `import Enc` (a compiled `Milestone0/Encoding.lean`);
see the header of `QE/Sec3_sat.lean` for the exact commands. `Assembly_val` and the swarm files are
standalone `import Mathlib`.

## The one thing being worked on: the guard repair

Author's ruling: keep the recursive `WellSorted`, add the junk-truth condition on the guard of
`.all`. The specification (in `DECISION.md`, section "`Occurs := InAntecedent`") is:

1. move `guardAtom`/`InAntecedent` above `Occurs` (done in the attempts, see below);
2. **define `Occurs i s η := InAntecedent s i η`** — replacing the compiled match, which cannot be
   bridged because its discriminator looks inside subterms;
3. delete `inAntecedent_of_occurs` (it becomes `id`);
4. restate `occurs_self` → `InAntecedent.atom`, `occurs_foldr_hyps`/`occurs_sortedHyps` →
   `.and_left`/`.and_right` chains;
5. `wellSorted_alls` keeps `(hj : ∀ d, GuardTrue (ss d) d χ)`; its four callers gain
   `fun d => GuardTrue.of_inAntecedent (occurs_sortedHyps ss d)`.

The attempt at exactly this produced **17 mechanical errors**; the inventory by line number is in
`DECISION.md` and the two working attempts are commits `604f968` and `35be8be` (both WIP, both
red). `git show 35be8be:Milestone0/Encoding.lean` is the base to continue from.

## After the repair

1. `nontrivialTransferWS_ACVF` (frozen in `QE/TransferWS.lean`) — the sharp test of the repaired
   predicate; expect the first failure in the `all`/`ex` cases.
2. `caseSplit_ACVF`, `trivialTransferWS_ACVF` (should follow from the unrestricted
   `trivialTransfer_ACVF` in `Assembly_val`), `CaseSeparationWS`.
3. The fragment compactness step (`QFTypeDeterminesWS → HasQEws WellSorted`), then the
   `sortEval`/`sortedHyps` bridge to the frozen `HasQE`.
4. Still open from the main route: the mixed-context elimination (needs the `mul`-cancellation
   normal form for elements off `K`) and the forward half of the parameter bridge
   (`hasQE_of_hasQE_empty`; shrink side is green in `.ultramath/smw19wtoj/m2/`).

## Assets from swarms worth reading before re-proving anything

* `.ultramath/smw19wtoj/m1/W1.lean` — `exists_toFrag_WSg` (all cases, both sorts), `WSg`, `JunkTrueAt`.
* `.ultramath/smw19wtoj/m4/SubstRv.lean` — `substLastRv`, `tmSort_substLastRv`, `wellSorted_substLastRv`.
* `.ultramath/smw19wtoj/m3/QF2.lean` — `QF2`/`QFq2` mixed-context fragment, image in `WellSorted`.
* `.ultramath/smw19wtoj/m5/Main.lean` — `qf_witness_of_exists_toFrag`, `hasQEws_of_exists_toFrag`.
* `.ultramath/smw19wtoj/m2/SortTransport.lean` — shrink side of the parameter bridge.
* `QE/Semantics_saturation.lean` (`QESat`) — QF-preservation under embeddings, the back-and-forth step.
* `QE/Sec3_sat.lean` and `Milestone0/DECISION.md` — the saturation interface and every ruling.

## Discipline that has cost time when skipped

* A file is green only if `lean FILE.lean` exits 0; `grep -c "error"`, never `grep "error("`.
* Stale oleans have caused four false alarms: always build your own `.olean` from the current file.
* `Assembly_val.lean` carries a copy of `Encoding.lean`; any change to the encoding must be
  re-synced into it in the same commit.
* Do not report a theorem as proved without `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.

## Update: the second route is closed as stated (read this before re-attempting it)

Two swarm results landed after the section above and both change the plan.

**1. `NontrivialTransfer Axioms.ACVF` is false, not merely unproved.**
`Missing.nontrivialTransfer_iff_hasQEb` (`.ultramath/smw1b0thh/m3/AvAudit.lean:264`, compiled,
axioms clean) proves

```
FinalAssembly.NontrivialTransfer Axioms.ACVF  ↔  QECriterion.HasQEb (L := LRV) Axioms.ACVF
```

i.e. the tree's one remaining hypothesis for the frozen target (`hasQE_ACVF_of_nontrivialTransfer`,
`Assembly_val:16347`) is equivalent to *unrestricted* QE, which is false — three refutations are in
`QE-PLAN.md`.  So that theorem is vacuous.  **Do not try to prove `NontrivialTransfer`.**  The live
form is `QE/TransferWS.lean`'s `NontrivialTransferWS`, which is the same assembly over the fragment.

Same audit, three recorded obligations: none of the seven criterion files proves a *relativised*
Shoenfield test; missing are the fragment transfer and a fragment compactness step
(`FragAudit.MissingFragmentCriterion`); and `hasQE_ACVF_val` + the ball dictionary does **not**
suffice — `Missing.HasQEb_ACVF_val`, `Missing.VFQ_to_QFq`, `Missing.MixedContextCover`.

**2. `L_val` reaches only a strict sub-fragment.**  `.ultramath/smw1b0thh/m2/W2.lean` proves
`wellSorted_valFormulaToRVvf` (the `L_val` image lies inside the frozen fragment — the tree's
transfer never said this) and `transfer_of_qfType_VF` (equal QF well-sorted `L_RV` type at
`VF`-tuples gives equal full `L_val` type, *without* a cover).  But the image contains only
`s = t`, `v s ≤ v t` and `VF`-guarded quantifiers: `rv s = rv t`, `kAdd`/`kNeg`/`rvMul`, `Kˣ` and
`RV`-quantifiers have no `L_val` preimage.  Two named gaps: no compiled bridge
`vfValStruct = vfStruct`; `hasQE_ACVF_val` is `HasQE` at `n = 0` while tuples need `HasQEb`.

**The one conclusion that has survived every direction: the residue-field and `RV`-side atoms are
the irreducible content.**  No translation to the valuation language reaches them; closing QE means
doing the `RV` work directly, which is what the paper's §4–§5 does.

## Swarms, and what happens to them when this session ends

* `smw1b0thh` (the Shoenfield/criterion route, 4 members, 120 min): w4 audit and w2 transfer
  **accepted and recorded above**; w1 (fragment Shoenfield criterion) and w3 (worked instance on
  two `C v` models) still running when this was written.
* Older swarms still listed as "running" (`smw17pts2`, `smw18pb0w`) have no working members; their
  accepted output is already merged or recorded in `QE-PLAN.md`.  Nothing is owed by them.
* **A swarm belongs to the session that started it.**  A new session cannot see, judge or resume
  these; `ultramath_status` only lists its own session's swarms.  So:
  - anything a member delivers lands as ordinary files under `.ultramath/<swarm>/m<k>/` — those
    survive, and the new session can use them as artifacts (the accepted ones are listed above);
  - anything not yet submitted will not be judged.  If w1 or w3 matters, wait for the reminder and
    judge it in this session before starting the new one; otherwise treat the files under
    `.ultramath/smw1b0thh/{m1,m3}/` as unvetted and re-check them with `lean` before relying on
    them.

## Recheck of the two unvetted swarm files (done here, as instructed)

Ran in each member's own directory with `LEAN_PATH=$PWD:$LEAN_PATH lean FILE.lean`:

| file | result |
| --- | --- |
| `.ultramath/smw1b0thh/m1/W1.lean` (w1, fragment Shoenfield criterion) | **green**: exit 0, 0 errors, no `sorry` warning. Usable, but read its statement before relying on it — in particular check whether it carries a saturation hypothesis, which would make it not a criterion. |
| `.ultramath/smw1b0thh/m4/Main.lean` (w3, the worked instance on two `C v` models) | **does not compile**: `Main.lean:89:40 error: Function expected at WellSorted` (name not in scope where applied). Nothing in `m4/` should be relied on; if the instance is wanted, rebuild it against a fresh `Enc.olean` from `Milestone0/Encoding.lean`. |

So of the two, only w1 is an artifact. w3 is not, and neither has been judged (a swarm belongs to the
session that started it), so treat both as *unvetted input* even where green: `lean` exit 0 says the
file elaborates, not that its statement is the one wanted.
