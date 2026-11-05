# Reuse survey for Sections 2–3

Search date: November 4, 2026 (America/Los_Angeles). This is a record of
discovery and source inspection; compiler evidence is recorded separately.

## Pinned, directly reused dependency

- ACVF-QE, `f3ef4ee679f921079aa8f742a2807a9cc724d2d6`, MIT (with its separately
  attributed Apache adaptations). Lean 4.33.1; Mathlib
  `0df444a360eaa60ab8c11dca51a86af692955474` (Apache-2.0).
- Read `Proofs/Enc.lean`, `VFField.lean`, `VFValued.lean`, `RVCalc.lean`,
  `CanonicalRV.lean`, `CanonicalQF.lean`, and the verification script.
- `HasQE` preserves well-sortedness and the original parameter type.
  `theorem_2_3_quantifier_elimination` supplies it without additional premises.
- `CanonicalRV.encoded_eq_iff_close` supplies **both directions** of the
  leading-term equivalence; `rv_eq_of_close` alone supplies only one.
- Focused follow-up inspection found `ValOneEC.atomGood_of_isAlgClosed`,
  `good_solSet`, ball comparability and Swiss-cheese decomposition in
  `Proofs/JohnsonGeometry.lean`. These are proved, not merely the earlier
  `AtomGood`/`GoodMeetsBase` interface definitions in that file. Reusing these
  plus `hasQEb_ACVF_val` gives the new checked valued-language C-minimality
  theorem. Transferring arbitrary RV formulas still requires an interpretation
  bridge; the old C-minimality placeholder is not used.
- `LocalAssembly.fullQE` and `CanonicalStructure.sortedQF_*` provide the
  raw-to-sorted unary definability bridge on canonical tagged structures.
  This avoids rebuilding QE or assuming a closure-identification principle.
- Do not use `Enc.theorem_2_8_c_minimal`: its proof contains `sorry`.
- Existing package verification artifacts have matching source and the pinned
  checkout is clean. A fresh root import passed locally in WSL this session.
  This is not a fresh build of all 81 package modules.

## Local candidates

- `Sec3Average.lean`: port the valuation argument, derive the natural-number
  unit premise from the actual ACVF(0,0) theory, and add RV nonconstancy.
  Its old header wrongly describes that conclusion as a paper error and
  wrongly calls `vrv` injective. Use mutual preorder inequalities for values.
- `Archive/Milestone0/Saturation.lean`: genuine small-parameter saturation and
  homogeneity; useful interface. Its `MonsterACVF` specializes only ACVF,
  not ACVF(0,0). New context must retain the stronger theory and small base.
- `Sec3_frozen.lean` and its dependents: finite `SP` parameter pairs are useful
  witnesses, but cannot replace the arbitrary base S. Some targets are
  placeholders. Do not import them into the new section entry point.
- `UniformCover.lean`, `Sec3Count.lean`: formula constructions for the uniform
  cover step; they do not discharge saturation/compactness for Lemma 3.1.
- `Sec3FunIntoPower.lean`: useful set-theoretic descent proof; its
  identification of the additive maximal-ideal quotient with `ker rv` is
  incorrect. The equivalence relations must remain separate.

`Archive/audit_section3.py` stages exact sources under historical module
aliases and records all compiler exits, occurrences of `error`, and local
placeholder counts. Scratch logs are not proof certificates for paper items.

## Mathlib and external discovery

Pinned Mathlib source inspected: `Mathlib/ModelTheory/{Definability,Syntax,
Semantics,Complexity}.lean`, the ModelTheory file inventory, and valuation
modules. `BoundedFormula.restrictFreeVar` and `realize_restrictFreeVar`
provide the finite-support syntax bridge; `Set.Definable` gives the usual
arbitrary-base definition for the raw language. Sortedness still needs its
own bridge. No direct proof of C-minimality or sorted acl was found in these
searches. `Nat.recOnMul` is available for the residue-characteristic argument.

Web queries included “Lean C minimality algebraically closed valued fields
formalization”, “mathlib4 CMinimal algebraicClosure model theory”, “Reservoir
valued field quantifier elimination”, and “LeanPool Palomar TauCeti valued
fields C minimal”. Inspected the community projects/intentions registry,
LeanPool repository, Tau Ceti repository, Palomar landing page, and
TheoremSearch API documentation. Reservoir timed out; Formalpedia returned
an error. Palomar's landing page did not expose searchable results without
its runtime database. GitHub's direct ACVF-QE and current-upstream
AlgebraicClosure URL fetches missed the web cache. No additional importable
target proof was found; catalog and open/closed-PR coverage is incomplete.
No external candidate code was copied from these searches.

November 5 follow-up: inspected Mathlib's `Polynomial.continuous_eval₂`,
`Valued.mem_nhds`, `Valued.locally_const`, `Valuation.restrict_lt_iff` and
`ValueGroup₀.restrict₀_surjective`. These support the checked polynomial
leading-term stability and neighbourhood-infinitude prerequisites for 3.3.
`PolynomialSyntax.realizes` is a new bridge to the released LRV terms.

Links: [paper](https://arxiv.org/pdf/1006.2467v1),
[Mathlib](https://github.com/leanprover-community/mathlib4),
[community registry](https://leanprover-community.github.io/lean_projects.html),
[LeanPool](https://github.com/LeanPool/lean-pool),
[Tau Ceti](https://github.com/TauCetiProject/TauCeti),
[Palomar](https://palomar-registry.org/),
[TheoremSearch](https://www.theoremsearch.com/).
