# Section 6: Henselian-field QE and descent

The active shared-language library is `Section6.Library`. It develops
functional closedness, the henselian fixed-field argument, transfer from
an elementary algebraic envelope, and geometric descent along the actual
Section 5 special bijections. Earlier sections are accepted as given under
the author's explicit instruction; they are not rederived.

The continuation constructs the actual formula in Lemma 6.3, the uniform
henselian elimination step, Proposition 6.4 over the original named base,
and the Denef-Pas translation for Corollary 6.5. The final checked
theorem, `DenefPasTheorem.corollary_6_5`, retains arbitrary original free
names, handles trivial and nontrivial valuations, and produces a properly
sorted formula with only RF/Gamma quantifiers. The explicit standard and
earlier inputs remain visible.

[STATUS.md](STATUS.md) records compiler and axiom evidence;
[TARGETS.md](TARGETS.md) distinguishes geometric descent from full
syntactic elimination; [INPUTS.md](INPUTS.md) displays the earlier and
standard-reference inputs; [STATEMENT-REVIEW.md](STATEMENT-REVIEW.md)
reviews the three requested headline scopes;
[HANDOFF.md](HANDOFF.md) records the next step.
The final pinned Lake check passed 78 modules, 444 full headline type/axiom
audits and the combined ACVF-QE + Section5 + Section6 import. Only the three
permitted Lean axioms occur. The final immutable evidence is under
`.scratch/section6-final78-444/`. Explicit theorem hypotheses remain;
INPUTS.md and STATEMENT-REVIEW.md give their scopes.

Run `lake env python3 Section6/verify.py` in the pinned environment with the
accepted earlier compiled interfaces on the import path. Verification
records and temporary sources belong under `.scratch/`.

`Sec6.lean` and `Sec6QE.lean` are preserved legacy reference snapshots,
excluded from the active library. Their historical headers are not current
verification evidence. `../Archive/MOVE-INDEX.json` records their old paths.
