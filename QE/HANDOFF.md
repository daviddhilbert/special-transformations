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

## w1 judged (accepted): the fragment criterion exists, and it is sharp

`.ultramath/smw1b0thh/m1/W1.lean` (checked by compiling: exit 0, 0 errors, no `sorry`):

* `W1.QFTypeDetermines T` — two models, `∀ α sα n sn`, `sortEval` sortedness on *both* parameter
  tuples and *both* variable tuples, QF agreement restricted to well-sorted formulas.  **No
  saturation hypothesis**, so it is a criterion and not a step.
* `W1.hasQE_of_qfTypeDetermines : QFTypeDetermines T → HasQE T` with the frozen `HasQE` as
  conclusion; `W1.hasQE_iff_qfTypeDetermines` — the two are **equivalent**.
* `W1.hasQE_of_embedding` — the substructure-embedding shape is *strictly weaker* in this encoding
  (ill-sorted term values unconstrained), so a bridge `QFTypeEmbeddable` is genuinely needed.
* `W1.exists_list_of_models_bounded` — compactness with parameters, via `Formula.equivSentence`;
  sortedness must be named by sentences, else the extraction is over unsorted tuples.

**Consequence to keep in mind:** because of the equivalence, `QFTypeDetermines Axioms.ACVF` is
exactly as hard as Theorem 2.3.  The criterion *relocates* the content; it does not reduce it.
So the second route is now a sharp statement of where the work is, not a second proof.

## Sequencing decision: repair first, then use it as the probe of the `RV` work

Both routes now agree that the irreducible content is the residue-field/`RV` side
(`Missing.VFQ_to_QFq`, `Missing.MixedContextCover`, and `QFTypeDetermines Axioms.ACVF`, which by
`W1.hasQE_iff_qfTypeDetermines` is *equivalent* to the theorem).  So the `RV` work is the real
destination and everything else is either bounded bookkeeping or a probe.

Order, and why:

1. **The guard repair** — bounded (a 17-error inventory, one pass, spec in `DECISION.md`).  It is
   required by the translation route's soundness whether or not the criterion route needs it, and
   it is the only way to state `NontrivialTransferWS`.
2. **One cheap experiment *before* grinding the repair**, because it may change the order: check
   whether the *unrepaired* `WellSorted` already satisfies `QFTypeDetermines` at a single
   quantifier.  m1's criterion is compiled against the current predicate, so if junk elements can
   never influence a well-sorted formula *at sorted tuples*, the repair is unnecessary for the
   criterion route and is only needed for `exists_toFrag`'s induction.  The case to try:
   `∀x (pVF x ⟹ ((pVF x ⟹ ⊥) ⟹ ψ))` — at `x ∈ VF` the inner guard is false, so the body is `⊤`,
   which suggests junk-insensitivity, but that is one formula, not a proof.
3. **`nontrivialTransferWS_ACVF` far enough to locate its first failure** (frozen in
   `QE/TransferWS.lean`).  That failure point *is* the `RV`-side work stated minimally — it is the
   cheapest probe available, and it converts "do the `RV` work" from a direction into a lemma.
4. **Then the `RV`-side proper**, with the §5 skeleton already in hand:
   `.ultramath/smw18ygko/m1/Sec5.lean` (definition 5.1's apparatus, `eta_wellPosed`,
   `exists_unique_contractionVF`; statements 5.2/5.4/5.5 frozen).

Do **not** spend further effort on criterion variants: `hasQE_iff_qfTypeDetermines` makes them
sharply equivalent to the theorem, so a variant buys a reformulation, not progress.

## The junk-sensitivity experiment: answered (junk-sensitivity is real; repair still needed)

Question: can a formula that is `WellSorted` under the **unrepaired** predicate have its truth at
*sorted* tuples influenced by elements outside the sorts?  If not, the guard repair would be
unnecessary for the criterion route.

**Answer: yes, and here is the witness.**  Take `s = .vf` and

```
φ  =  ∀x ( ((x ∈ VF) ⟹ ⊥) ⟹ (x = 0_VF) )
```

* `WellSorted` holds: the body is `.imp η ψ` with `η = ((pVF x) ⟹ ⊥)`, and `GuardsLast` fires on
  `η` because `Occurs i .vf (pVF x)` holds (`pVF x` *is* `sortPredG .vf (var i)`); `ψ = (x = 0)` is
  a well-sorted atom at sort `.vf`; so `WellSorted.all` applies under the unrepaired predicate.
* **At `x ∈ VF` the body is `⊤`** (`x ∈ VF` is true, so `(x ∈ VF ⟹ ⊥)` is `⊥`, so the implication
  is `⊤`) — so on the `VF` sort `φ` is vacuous.
* **At `x` outside `VF`** — i.e. at an `RV`-element, which exists in every model by `sdCover` and
  `sdDisjoint` — the body is `x = 0_VF`, i.e. it asks whether that `RV`-element equals the `VF`
  zero.  So `φ` says "every element outside `VF` equals the `VF`-zero", which is a real condition
  on the junk part of the model.

So the unrepaired `WellSorted` admits formulas whose truth is decided entirely by junk elements,
while the *guards* in them look innocuous.  Consequences:

1. **The criterion's statement is unaffected** — `QFTypeDetermines` is equivalent to the target
   (`W1.hasQE_iff_qfTypeDetermines`), and the target is what it is.  Junk-sensitivity does not
   refute it, because such a `φ` must still have a QF equivalent if the theorem is true.
2. **The proof is affected.**  Any induction on `WellSorted` derivations that pushes an equivalence
   through `∀` must bound the body's truth at junk values, and this witness shows the unrepaired
   predicate gives no such bound.  So the guard repair (or the equivalent invariant `JunkTrueAt` on
   bodies) **is still needed for the criterion route's proof**, not for its statement.
3. Which is the useful form of the answer: the repair is not bookkeeping — it is the difference
   between a fragment whose formulas are controlled by their sorted part and one that is not.

## The criterion, in its smallest form (m4, accepted) — this is the target to attempt

`.ultramath/smw1b0thh/m4/` — all four files compiled here (exit 0, 0 errors, no `sorry`):

| file | what it gives |
| --- | --- |
| `FragQE.lean` | `FragmentQFTypeDetermines T` (QF-well-sorted type at sort-respecting tuples of two models determines the well-sorted type) → frozen `HasQE T`, plus the converse and the `iff` |
| `FragQE1.lean` | the **one-directional** hypothesis suffices (compactness needs no more) |
| `FragAtoms.lean` | the hypothesis **reduced to atoms** — term equations of one sort, `memVF`/`memRV`/`memUnits`/`rvLe` at their declared sorts; `qfType_iff_atoms` |
| `SortSound.lean` | sort-discipline helpers; term induction stated as `TermSortSound` |

**So the remaining mathematical obligation of the criterion route is one named statement:**

```
FragmentAtomQFTypeDetermines Axioms.ACVF        -- FragAtoms.lean:100
```

and by the proved equivalences it is iff `HasQE Axioms.ACVF` — the theorem in atom form, not a
shortcut.  It is nevertheless the smallest form of the obligation anyone has produced: the `RV`-side
work is now exactly "two models agreeing on the *atoms* agree on the atoms' Boolean combinations at
sorted tuples", which is where §4–§5's special transformations enter.

Two facts from its proof worth not rediscovering: the compactness set must include the sort
assertions (themselves QF and well-sorted) or the witness tuple is not sorted; and `WellSorted` must
survive the meet/join folds.  Also: the partial-isomorphism (Shoenfield-embedding) form is *unusable*
in this encoding, because junk values lie outside the fragment — the QF-type form is the only one
available.  That settles the comparison question: there is no second, independent formulation to
check against; there is the criterion, sharp, in atom form.

## State after the guard repair (this session)

| file | status |
| --- | --- |
| `Milestone0/Encoding.lean` | **repaired**, sha256 `86d7ea7e…`, `lean` exit 0, 0 errors, 2 frozen `sorry`s |
| `QE/Assembly_val.lean` | green, 0 errors, 2 frozen `sorry`s; embedded encoding re-spliced verbatim |
| `QE/TransferWS.lean` | green against the repaired encoding (2 `sorry`s, by design) |
| `QE/FailProbe.lean` | green; the transfer's first failure point, machine-checked |

The repair: `Occurs := InAntecedent`; `GuardTrue` is an inductive family with an `.all` clause;
`WellSorted.all`, `wellSorted_alls`, `wellSorted_allOne` carry it; every `wellSorted_allSorted*` /
`exSorted*` signature is unchanged.  Details and the reasons in `DECISION.md` §"The guard repair:
applied, green, and what it changed".

**The endgame lost three of its four hypotheses.**  `TrivialHalf.allNontrivial_ACVF` (every model of
`Axioms.ACVF` is `IsNontrivialVF`, from `Transfer.isNontrivialVF_of_model`, now checked) gives
`caseSplit_ACVF`, `caseSeparation_ACVF`, and

```
Transfer.hasQE_ACVF_of_nontrivialTransfer : FinalAssembly.NontrivialTransfer Axioms.ACVF
    → QECriterion.HasQE Axioms.ACVF
```

So there is **no two-case question for the frozen theory**, and `TrivCase.FineTriv` is empty over it
(`TrivialHalf.not_fineTriv`) — the trivially valued model of §10 above satisfies a weaker axiom set.

**The transfer's first failure is located** (`QE/FailProbe.lean`): the induction on `WellSorted` has
an immediate atom/`imp` case, and its `all` case splits on the bound element into (i) junk-truth of
the body — the repair's payload, now an unproved semantic lemma rather than an obstruction — and
(ii) for a *sorted* bound element, a sorted `a : M` with the same QF type over the parameters, i.e.
realization of a QF type in a fixed model, which `TransferAtWS`'s hypothesis does not supply.  This
is why the transfer is a reformulation of QE rather than a reduction, and why the atom form above is
the target.

## Two swarm files that must not be relied on as-is (one line each)

* **`W1.lean`** (fragment criterion, `.ultramath/smw1b0thh/m1/`) is **superseded** by
  `.ultramath/smw1b0thh/m4/{FragQE,FragQE1,FragAtoms}.lean`, which is stronger (hypothesis reduced
  to atoms) and imports only `Enc`, so it is immune to `Assembly_val` drift.  `W1.lean` is *not*
  current-prelude-green: rebuilt against the merged `Assembly_val` it fails at 272, 276 (`show`
  pattern) and 304 (`Type mismatch`).  Do not fix it unless the *embedding-form argument* is wanted
  — that lives in its `REPORT.md` prose and in `W1.hasQE_of_embedding` / `QFTypeEmbeddable` — or
  `W1.exists_list_of_models_bounded` (compactness with parameters).
* **`smw18pb0w` m4's `ValueOnly.lean`** is byte-identical to the already-merged
  `m1/ValueOnlyM4.lean`; nothing new in it.

**Rule.** `lean` against a member's own olean proves only "elaborates against that snapshot".
Rebuild the prelude before relying on a file importing `Pre_build`/`Pre2`/`PreC`/`AV`; files
importing only `Enc` or `Mathlib` are safe from `Assembly_val` drift.
