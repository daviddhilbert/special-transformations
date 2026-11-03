# Project and API design

Adapted from the sources credited in this package's NOTICE and the
[upstream architecture reference](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/1837b95b3d5a9fd8d311367603902ad7fe261adf/skills/lean-project-architecture/references/project-architecture.md).

## Scope from dependencies

Choose the public results and their actual definitions. Separate external library
results, reusable infrastructure and paper-specific steps. A small plan can show
dependencies and open questions; a graph database is useful only when the project
needs to maintain one.

A source result `A → B` is not delivered by `A → Step → B`. Prove intermediate
results and apply them inside the proof. Preserve shared constants and witnesses
when splitting work. A compiled helper and a faithful formalization differ.

## Engineer the needed API

Search pinned libraries before introducing abstractions. Use representations with
the required operations and theorems. Compare carriers for mathematical meaning,
coercions, downstream APIs and measured cost, not past performance anecdotes.

For new definitions, provide characterization, evaluation or extensionality lemmas
that consumers need. Use simp attributes for appropriate normal forms. Do not
invent fallback semantics or assume a defining property to make code elaborate.

## Modules and coordination

Keep foundational definitions below consumers in the import DAG. Separate reusable
lemmas from final assembly, keep imports focused and split at stable boundaries.
Follow existing namespaces and file-size conventions. Splitting is not inherently
a performance improvement.

For projects using Lean modules, read [Module system](module-system.md). The
bundled [module checker](../scripts/check_lean_modules.py) checks a particular
module/registry profile; use it only when that profile applies. It reads the Git
index, so account for new files rather than silently overlooking them.

For authorized parallel work, give each worker owned files, an exact target,
allowed dependencies, validation and handoff. Keep shared API decisions with the
coordinator. Review diffs and compile the integrated result. Do not require
multiple agents for a small task.

The [frozen-anchor profile](frozen-architecture.md) is for campaigns that adopt
exact declaration manifests. Its approval and quarantine requirements are not
the default for every Lean project.

## Deliver

Build affected targets and consumers and report gaps. Follow the repository's
contribution process; do not assume upstream write access or require a forkless
workflow. Preserve user changes, dependency caches, attribution and toolchains.
