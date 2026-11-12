# Palomar preparation

Author and responsible maintainer: Yimu Yin.

The first submission selects **Theorem 5.5 and Corollary 5.6 only**, at the
author's request. Later Jacobian and measured-lifting results remain in the
verified library and are outside this first Comparator claim.

## Source and verification

This isolated candidate starts from released source
f76d100e07c0a791259244fc7fdf06f4dfaaf8ae. Unrelated edits in the author's
original checkout are not included. Existing releases and archives are unchanged.

The module-format production library and all 3,543 full headline type/axiom
audits passed at f2fbe2eea4083bb21174fa48b720eb80a901fbc0, GitHub Actions run
43274534495. Production Lean sources have not changed since that baseline;
subsequent Lean changes are confined to the independent statement/proof pair.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.

The portable Lake project pins Lean 4.35.0, Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, and ACVF-QE
8f90dfd22de9f2c821382830eee326d1f0cf4990. The MIT LICENSE and all retained
upstream license notices accompany the source.

## Independent statements

`PalomarPaperChallenge.lean` imports Mathlib and trusted Lean meta modules;
it imports neither the paper library nor ACVF-QE. Its current pruned form
has 790 physical lines and about 59 KB. The model, pure characteristic zero,
genuine saturation, small parameter set, and theorem-specific coefficient
condition remain explicit. No new paper hypothesis has been added.

The canonical and focus maps are intentional definition holes with
unconditional pointwise equations. Their Map types require definability over
the original parameters. The equations fully determine the maps by function
extensionality and proof irrelevance. `PalomarPaperSolution.lean` proves both
equations by reflexivity from the existing implementations.

Representation lemmas are additional checked Comparator obligations, not
assumptions of the two principal results. Original module-local matcher and
auxiliary-lemma caches are reset between copied source modules to preserve
compiler-generated declaration names. This changes compiler cache state,
not mathematical declarations or axioms.

The pruned dependency inventory follows the two explicit map interfaces,
excluding their unnecessary graph-construction implementations. Inventory
and source extraction are authoring tools, not verification evidence.

## Intake boundary

The exact final package must pass standalone compilation, strict comparison,
and Palomar's complete pinned reusable workflow before intake. The full
workflow discards submitted build state. Cached project builds are diagnostic
only. Source-to-paper fidelity remains self-assessed; no independent human
review or Palomar acceptance is claimed.

No Special transformations intake has been sent. Palomar requires agreement
on the exact repository, commit, comparator path and the author's responsible
maintainer relationship before the tag-and-secret-gist authentication.
Registration separately requires the author to read the actual private review
and explicitly approve publishing it. Earlier archive/publication instructions
do not replace that review-specific consent.
