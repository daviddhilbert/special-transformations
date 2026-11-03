---
name: lean-project-architecture
description: "Adapted from <strong>Scott Armstrong</strong>'s LeanAutoformalizationSkills: lean-project-architecture, lean-orchestrator, build-proof-dependency-graph and lean-public-release. Plan and organize Lean 4 projects, module boundaries, shared APIs, proof dependencies, coordinated formalization, and public releases. Use for work spanning a project or a requested campaign; not a prerequisite for editing one proof."
---

# Lean project organization

Start from the requested deliverable, the mathematical source when relevant, and
the repository's existing conventions. Keep the plan proportional to the work.
A module refactor does not require a frozen-anchor campaign, a dependency database,
or multiple agents.

## Ordinary project work

- Identify the public statements and definitions whose meaning must remain stable.
  Preserve their premises, carriers, quantifiers, and constant dependencies.
- Search the pinned dependencies for existing abstractions before introducing
  new ones. Separate reusable infrastructure from paper-specific assembly.
- Arrange imports as a dependency DAG. Put reusable definitions and access lemmas
  before consumers; split files at coherent API boundaries, not arbitrary counts.
- Validate affected targets and consumers. Use the repository's supported Lean
  module conventions; do not migrate toolchains or visibility rules incidentally.
- For coordinated work, give each authorized worker an owned area, exact target,
  allowed dependencies, validation command, and handoff. Use available delegation
  only when authorized; this skill does not require or authorize spawning agents.

## Select the relevant procedure

Read only the applicable row. All linked resources are included in this package;
script and asset paths in a guide are relative to the guide's directory unless
it says otherwise. Run bundled scripts with `--help` before choosing options.

| Task | Reference |
|---|---|
| Module/API design and ordinary project organization | [Architecture](references/project-architecture.md) |
| A project using or explicitly migrating to Lean modules | [Module system](references/module-system.md) |
| Public release, selective export, provenance and reproducible checks | [Release](references/release/guide.md) |
| Concurrent campaign builds and machine resource coordination | [Machine resources](references/orchestration/references/machine-resources.md) |
| Source errata and intentional deviations in a public release | [Errata record](references/orchestration/references/errata-and-deviations.md) |
| An adopted frozen-anchor formalization campaign | [Frozen architecture](references/frozen-architecture.md), then [Orchestration](references/orchestration/guide.md) |
| Landing checks for an adopted frozen-anchor campaign | [Landing guards](references/orchestration/references/landing-guards.md) |
| A source dependency database under that frozen-anchor profile | [Dependency graph](references/dependency-graph/guide.md) |

For a lightweight proof plan, list source results, actual dependencies, open
questions, and next provable steps. The bundled graph checker implements a
specific manifest-bound schema; do not introduce that schema for a simple plan.
A source graph records mathematical dependencies, not Lean proof completion.

The frozen-anchor references describe an optional, stricter project process.
Their approval, draft, quarantine, and independent-review requirements apply
only after that process is adopted. Do not silently introduce `DRAFT_SORRY` or
one-declaration-per-file rules into other repositories. Preserve existing frozen
interfaces and report source mismatches instead of weakening statements.

Use `lean-statement-audit` for a dedicated fidelity review and `lean-elaboration`
for a measured performance investigation when those skills are available. Neither
is an automatic extra phase for every architecture task.

## Upstream sources

This skill is adapted from [lean-project-architecture](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/tree/main/skills/lean-project-architecture), [lean-orchestrator](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/tree/main/skills/lean-orchestrator), [build-proof-dependency-graph](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/tree/main/skills/build-proof-dependency-graph) and [lean-public-release](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/tree/main/skills/lean-public-release) in Scott Armstrong's [LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills).

Synchronized against upstream commit [`1837b95`](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/commit/1837b95b3d5a9fd8d311367603902ad7fe261adf). The entrypoint and bundled guides retain the Open Math Model consolidation; see [NOTICE.md](NOTICE.md) for attribution and adaptations.
