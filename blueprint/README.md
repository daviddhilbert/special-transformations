# Lean blueprint

The blueprint follows the main definitions and results of Yimu Yin's
*Special transformations in algebraically closed valued fields*, Sections 2–10.
Each node gives the paper numbering, links to the Lean declarations, and
records the mathematical dependencies. The section status files linked
throughout give the detailed coverage and hypotheses.

The Lean source links are pinned to checked proof commit
`932a5075ad91a825d4b8c1bf1396b2063e44fe40` with Lean 4.35.0, ACVF-QE
`173708265d7959e031bf9552ee884501fc21f2cb` and hilbert-mathlib
`88bb3386f616779bfd87eb453d8a7c899ad63961`. A declaration whose
implementation moved to hilbert-mathlib keeps its name and links to that
provider. The blueprint contains 63 nodes and links 158 distinct Lean
declarations. Each linked declaration passes a fresh type/axiom audit; its
source line is checked in `src/source-links.tsv`. The zero-degree nodes
retain the actual RV/Gamma weights and remain separate from the
positive-degree reference hypotheses. The v1.2 nodes add the input-free
named-Gamma Theorems 5.4/5.5 and the Gamma lift layer through Gamma
Theorem 9.16. See the [release verification record](../docs/RELEASE-v1.2.md)
and [errata and deviations](../docs/ERRATA-AND-DEVIATIONS.md).
Repository documentation links resolve through release tag `v1.2`.

## Build

Install Python, Graphviz with its development headers, and a LaTeX distribution
with `latexmk`. With a Python environment active, run these commands from
the repository root.

```sh
python -m pip install -r blueprint/requirements.txt
leanblueprint web
leanblueprint pdf
```

Open `blueprint/web/index.html` and select **Open the dependency graph**.
The SVG works from a local file, and each node opens its statement. Run
`leanblueprint serve` to use the interactive graph in the sidebar.
The print version is `blueprint/print/print.pdf`.

Purple boxes identify checked Lean imports, including the two Stacks
results used in Section 9. Amber boxes identify external hypotheses.

The shared statements are in `src/content.tex`. For each declaration added
there, record its source file and line at the checked revision in
`src/source-links.tsv`. The second column names the repository: `paper`
(this repository), `qe` (ACVF-QE) or `hilbert` (hilbert-mathlib), each
pinned in `src/source_links.py`. Lines are the declaration keyword lines.
