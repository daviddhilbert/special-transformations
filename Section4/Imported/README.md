# Imported algebra for Section 4

`GrothendieckRing.lean` is copied from
`TauCeti/RingTheory/GrothendieckRing.lean` at Tau Ceti revision
`027f880ff251fa1cbd16ee9d6c03fb74ea254bed`:

[Source at the fixed revision](https://github.com/TauCetiProject/TauCeti/blob/027f880ff251fa1cbd16ee9d6c03fb74ea254bed/TauCeti/RingTheory/GrothendieckRing.lean).

Copyright 2026 The Tau Ceti contributors. The source is Apache-2.0 licensed;
its original header is retained and the license is in `TauCeti-LICENSE`.
The upstream package uses Lean 4.36.0-rc2. One proof replaces its newer
`AddMonoidHom.coe_ofClass` simplification with the pinned
`AddMonoidHom.coe_coe` lemma. This isolated module has only
Mathlib imports and has been checked against this project's unchanged Lean
4.33.1 and Mathlib pin. Compiler and axiom status belongs in the Section 4
status report, separately from this source provenance.

It supplies the ring structure and universal property on Mathlib's additive
group completion, without a cancellation hypothesis. It does not construct
the positive scissor quotient of definable sets. See `../REUSE-SURVEY.md` for
the comparison with Mathlib PR 28468 and the categorical group presentations.

The initial whole-file port candidate `PolynomialPrimeTrdegHeight.lean` came from
[the fixed upstream source](https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture/blob/e457fde9100c9b7226bd4d81af6860f210a531ab/RB31EndToEnd/Algebra/PolynomialPrimeTrdegHeight.lean).
The source belongs to the upstream formalization's contributors and is
Apache-2.0 licensed; `BodyPin-LICENSE` retains that license. The original
file has no separate author header. Its body and `RB31E2E` namespace were
initially copied unchanged, with an added provenance notice. The upstream
Lean version is 4.29.0 and its Mathlib pin is recorded in `../REUSE-SURVEY.md`.
The fresh whole-file compilation exited 1 because of changed polynomial
splitting APIs and related type conversions. That failed candidate is not
included in this publication. The proof of 4.8 uses the smaller
`PolynomialCoordinateBasis.lean` excerpt: the coordinate definition,
generation lemma, and two coordinate-basis proofs are retained unchanged,
with narrowed imports and the same namespace and license. That excerpt
passed its separate compiler run and all four full headline and axiom
audits and is integrated in the active library; the full height formula is
not needed by the chosen dimension argument.

`IntegralKrullDimension.lean` retains Robert Shlyakhtenko's source from
[Mathlib PR 41904](https://github.com/leanprover-community/mathlib4/pull/41904),
fixed head `71439003d3f0a5e3d6cc8ebed7a5f092606f138a`, file
`Mathlib/RingTheory/KrullDimension/Integral.lean`. It proves preservation
of actual Krull dimension under an injective integral homomorphism.
The original copyright and author notice is retained; `Mathlib-LICENSE`
contains the Apache-2.0 license. The proposal was open when inspected on
November 5, 2026. The unrelated edits in its other files are not copied.
Its pinned local compilation exited 0. The four full headline types and
axiom audits passed as part of the nine-headline algebra-port check.
It is integrated in the active section library.

`NoetherNormalizationTrdeg.lean` retains the first three theorems from
[NYLL's normalization source](https://github.com/n-yamaguchi-0729/NYLL/blob/2e9f92dc5fbeacd17189dcf0cdb499f528dfd77c/Nyll/SchemeTheory/NoetherNormalization/Trdeg.lean),
by Naganori Yamaguchi, assisted by OpenAI Codex. The original notices and
`FieldArithmetic.Chapter06` namespace are retained. The unused import for
the later generator-sensitive results is omitted. `NYLL-LICENSE` and
`NYLL-NOTICE` retain the upstream Apache-2.0 materials. Its upstream Lean
version is 4.35.0-rc2, with Mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Its pinned local compilation
and three full headline/axiom checks passed. The local
`../AffineKrullDimension.lean` bridge also compiled with exit 0 and passed
both headline audits. All nine audits use only the permitted axioms.
These modules and the bridge are integrated in the active library. They
supply the algebraic prerequisite for the definable comparison 4.8.

The publication audit's kernel-replay harness is adapted from Lean 4.33.1
`src/LeanChecker.lean` by Kim Morrison and Sebastian Ullrich. It uses
`Lean.Environment.replay` against the completed earlier-section boundary;
`Lean-LICENSE` preserves Lean's Apache-2.0 license. The harness is verification
tooling, outside the mathematical library and its exported declarations.
