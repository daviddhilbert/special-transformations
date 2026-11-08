# Section 6: Henselian-field QE and descent

The active shared-language library is `Section6.Library`. It develops
functional closedness, the henselian fixed-field argument, transfer from
an elementary algebraic envelope, and geometric descent along the actual
Section 5 special bijections. Earlier sections are accepted as given under
the author's explicit instruction; they are not rederived.

[PaperResults.lean](PaperResults.lean) gives Proposition 6.4 over the
original named base and Corollary 6.5 for ordinary Denef–Pas structures.
The corollary retains arbitrary original free names, covers both
valuation branches, and produces a sorted formula with only RF/Gamma
quantifiers. The proofs supply the representation and saturation
interfaces used by the earlier helpers.

[STATUS.md](STATUS.md) records compiler and axiom evidence.
[TARGETS.md](TARGETS.md), [INPUTS.md](INPUTS.md), and
[STATEMENT-REVIEW.md](STATEMENT-REVIEW.md) give the theorem scopes and
the earlier results used.

Run `lake env python3 Section6/verify.py` in the pinned environment with the
accepted earlier compiled interfaces on the import path. Verification
records and temporary sources belong under `.scratch/`.

`Sec6.lean` and `Sec6QE.lean` are preserved legacy reference snapshots,
excluded from the active library. Their historical headers are not current
verification evidence. `../Archive/MOVE-INDEX.json` records their old paths.
