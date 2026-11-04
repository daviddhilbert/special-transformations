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
definition `RV`), and the real work in `Milestone0/` and `QE/`: the frozen encoding
of `L_RV`/`ACVF` with Theorems 2.3 and 2.8 as statements, ten accepted model-building
snapshots, and the quantifier-elimination assembly. `MILESTONES.md` is the verified
per-milestone status (file counts, error and `sorry` counts, what each milestone still
lacks); `HANDOFF.md` is the plan, `QE-PLAN.md` the chronological record.

## License

MIT.
