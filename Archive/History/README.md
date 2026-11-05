# special-transformations

Lean 4 formalization of:

> Yimu Yin, **Special transformations in algebraically closed valued fields**,
> Annals of Pure and Applied Logic (2010). arXiv:1006.2467.

This is the **paper repository**. Reusable, paper-independent background belongs in
the separate foundation repository [`hilbert-mathlib`](https://github.com/daviddhilbert/hilbert-mathlib).

## Environment

- Lean 4.33.1, Mathlib prebuilt read-only at `/opt/mathlib`.
- `lakefile.toml` depends on Mathlib by path, so builds use the VM's prebuilt
  Mathlib and do not rebuild it.
- `.lake/packages` is populated on first build (about 400 MB of dependency
  sources; no Mathlib oleans are downloaded).

## Layout

| Path | Purpose |
| --- | --- |
| `SpecialTransformations.lean` | Library root, imports all paper modules |
| `SpecialTransformations/Basic.lean` | `RV = Kˣ/(1+M)`, `rv : K → RV` |
| `SpecialTransformations/Language.lean` | The language `L_RV`, theory `ACVF_S(0,0)` |
| `SpecialTransformations/Definable.lean` | Definable sets, balls, C-minimality |
| `SpecialTransformations/Dimension.lean` | `dimVF`, `dimRV`, `dimfib` |
| `SpecialTransformations/Categories.lean` | `VF[k,·]`, `RV[k,·]`, Grothendieck semigroups, `L` |
| `SpecialTransformations/SpecialBijection.lean` | RV-pullbacks, special bijections |
| `SpecialTransformations/Hensel.lean` | Hensel, lifting functions, Theorem 7.6 |
| `SpecialTransformations/Differentiation.lean` | Non-archimedean derivatives and Jacobians |
| `SpecialTransformations/VolumeForms.lean` | Volume-form categories, Section 10 |
| `SpecialTransformations/Main.lean` | Target theorem list and formal status |
| `Milestone0/` | Language decision and artifacts — start at `Milestone0/DECISION.md` |
| `QE/LocalQE/Theorem23.lean` | Verified RV QE with no extra mathematical hypotheses; dedicated verifier in `QE/LocalQE/verify.py` |
| `QE/LocalJohnson/JohnsonMain.lean` | Cleaned entry point for the existing ordinary valued-field QE proof through Johnson's Chapter 2; verification status in `QE/LocalJohnson/STATUS.txt` |

## Build

```bash
lake build
make check FILE=SpecialTransformations/Basic.lean
make sorry
make milestone0   # elaborate the standalone Milestone 0 artifacts
```

## Formalization status

The repository contains the **statement-level scaffold** in
`SpecialTransformations/` (target table, dependency order, the first algebraic
definition `RV`), and the real work in `Milestone0/` and `QE/`. The local RV QE
entry point is [`QE/LocalQE/Theorem23.lean`](QE/LocalQE/Theorem23.lean). The
latest integration removes all remaining mathematical hypotheses from its
statement. **All 86 modules and a fresh combined import passed verification
by 2026-11-05 at 05:45 UTC** (November 4 at 21:45 America/Los_Angeles).
The fresh check confirms the exact parameter-free theorem, and its axiom
audit lists only `propext`, `Classical.choice`, and `Quot.sound`.
The previous three-hypothesis version passed all 78 modules and a fresh
combined import on 2026-11-05 at 05:11 UTC, with only the standard Lean axioms
in the final audit. That result and the earlier four-hypothesis, 68-module
check remain verification history; the 86-module run verifies the latest sources.
The proof uses the corrected encoding with named RV inversion. C-minimality
remains a separate statement.
[`QE/LocalQE/STATUS.txt`](QE/LocalQE/STATUS.txt) records the proof, assumptions
and dedicated verification procedure; this proof is not imported by the default
scaffold library root. The earlier model-building and QE snapshots remain.

The repository also already contained an unconditional proof of **ordinary
valued-field QE** through Will Johnson's Chapter 2 argument. The original
`hasQE_ACVF_val` prefix of `QE/Assembly_val.lean` has now been checked with
exit code 0, no errors or `sorry`, and only the standard Lean axioms. Its
cleaned entry point is
[`QE/LocalJohnson/JohnsonMain.lean`](QE/LocalJohnson/JohnsonMain.lean), with
no additional mathematical hypotheses. All five extracted modules and a fresh
import of both QE theorems passed verification; the records are linked in
[`QE/LocalJohnson/STATUS.txt`](QE/LocalJohnson/STATUS.txt). This one-sorted
result supplies the ordinary valued-field step through
`JohnsonValuedExtension.markerNotesProposition45`. The latest integration
also supplies pure ACF QE from the repository's existing Johnson criterion
proof and residue-field algebraic closedness from its local Johnson proof.
The final countable-language QE criterion combines downward
Löwenheim–Skolem, the existing compactness proof, and an adapted
nonprincipal-ultrapower saturation proof from Elliot Glazer's
[`definable-saturated`](https://github.com/elliotglazer/definable-saturated),
located through Palomar. No continuum hypothesis is used. The current
integrated verification status is recorded in `QE/LocalQE/STATUS.txt`.

`MILESTONES.md` is the verified
per-milestone status (file counts, error and `sorry` counts, what each milestone still
lacks); `HANDOFF.md` is the plan, `QE-PLAN.md` the chronological record.

## License

MIT, except for the adapted ultrapower proof in
`QE/LocalQE/CountableSaturatedExtension.lean`, which is Apache-2.0.
Its original license, NOTICE, and source provenance are retained in
[`QE/LocalQE/vendor/definable-saturated/`](QE/LocalQE/vendor/definable-saturated/).
