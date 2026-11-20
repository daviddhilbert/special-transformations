# Lean blueprint

The blueprint follows the main definitions and results of Yimu Yin's
*Special transformations in algebraically closed valued fields*, Sections 2–10.
Each node gives the paper numbering, links to the Lean declarations, and
records the mathematical dependencies. The section status files linked
throughout give the detailed coverage and hypotheses.

The Lean source links are pinned to checked proof commit
`097b3c13a82e0b0a1af3f782e6a16b4216d36616` with Lean 4.35.0, ACVF-QE
`173708265d7959e031bf9552ee884501fc21f2cb` and hilbert-mathlib
`88bb3386f616779bfd87eb453d8a7c899ad63961`. A declaration whose
implementation moved to hilbert-mathlib keeps its name and links to that
provider. The blueprint contains 63 nodes and links 159 distinct Lean
declarations. Each linked declaration passes a fresh type/axiom audit; its
source line is checked in `src/source-links.tsv`. The zero-degree nodes
retain the actual RV/Gamma weights and remain separate from the
positive-degree reference hypotheses. The v1.2 nodes add the input-free
named-Gamma Theorems 5.4/5.5 and the Gamma lift layer through Gamma
Theorem 9.16. After v1.2 the 4.9 node also links the discharged
`Section4.Paper.lemma_4_9`, and the links moved to the commit that adds it.
See the [release verification record](../docs/RELEASE-v1.2.md)
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

Check the registry, anchors, pins, counts and dependency graph with
`python3 scripts/check_blueprint.py`. After a Lean change to a linked file,
commit it and run `python3 scripts/check_blueprint.py --write --pin <commit>`
to move the repository pin and regenerate the anchors; then update the pin
quoted here and in `src/content.tex`. Add `--audit` (with `lake env python3`,
after `lake build`) for the type/axiom audit of every linked declaration.
