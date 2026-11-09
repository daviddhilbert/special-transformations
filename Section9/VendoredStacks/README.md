# Stacks proofs used by Section 9

The eleven Lean modules here come from the
[AxiomMath Stacks formalization](https://github.com/AxiomMath/Stacks/tree/5ed82d14634e8d9576bb844c7bd4e3da66d450e7)
at commit `5ed82d14634e8d9576bb844c7bd4e3da66d450e7`. Their upstream
Apache 2.0 license is in [LICENSE](LICENSE). They supply the filtered
étale presentation of the ordinary henselization and its universal
property. [Stacks 04GN](https://stacks.math.columbia.edu/tag/04GN),
[Stacks 04GS](https://stacks.math.columbia.edu/tag/04GS).

The port targets this repository's Lean 4.33.1 and Mathlib pin. It
removes an unused tactic import unavailable under the pin, makes one
augmentation cocone naturality equality explicit, and uses the pinned
indices of `HenselianLocalRing.TFAE`. The port uses the upstream Lean
module names to preserve the dependency layout.
