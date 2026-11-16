# Lean blueprint

The blueprint follows the main definitions and results of Yimu Yin's
*Special transformations in algebraically closed valued fields*, Sections 2–10.
Each node gives the paper numbering, links to the Lean declarations, and
records the mathematical dependencies. The section status files linked
throughout give the detailed coverage and hypotheses.

The Lean source links are pinned to checked proof commit
`d7d74197031665b4c1e9ea4486c1898ff32f2d50` with Lean 4.35.0. The updated
blueprint contains 57 nodes and links 136 distinct Lean declarations. Each
linked declaration passes a fresh type/axiom audit; its source line is
checked in `src/source-links.tsv`. The zero-degree nodes retain the actual
RV/Gamma weights and remain separate from the positive-degree reference
hypotheses. See the [release verification record](../docs/RELEASE-v1.1.md)
and [errata and deviations](../docs/ERRATA-AND-DEVIATIONS.md).
Repository documentation links resolve through release tag `v1.1`.

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
`src/source-links.tsv`.
