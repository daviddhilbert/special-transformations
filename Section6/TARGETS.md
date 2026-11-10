# Section 6 targets

Source: [arXiv:1006.2467v1, Section 6](https://arxiv.org/html/1006.2467v1#S6).
The author permits all needed earlier-section material as given. Earlier
proofs are not restarted. See INPUTS.md for the exact imported interfaces.

The author's revised Definition 2.4 permits guarded rational VF factors;
see `../Section3/NORMAL-FORM-NOTE.md`. As the author clarified during the
continuation, this **does not change the notion of occurring polynomials**:
RV inversion commutes with rv. Retain the existing extraction of VF
polynomials below rv, recursively through RV inversion. The raw expression
`rv(P) * rv(Q)⁻¹` has the ordinary occurrences P and Q; rational notation
introduces no new kind of occurrence. Keep domain/zero-branch guards and
the convention `0⁻¹ = 0`; do not add a VF inverse symbol.

| Paper target | New implementation | Boundary |
| --- | --- | --- |
| Definition 6.1 | `FunctionalClosure`: all finite input/output arities, full graphs of partial functions, arbitrary parameter sets | Generic first-order language; specialize to the released LRV normalization |
| Closing step of 6.2 | `functionallyClosed_iff_dclClosed`; elementary-image transfer | No model-theory conclusion is assumed |
| VF step of 6.2 | `HenselianClosure`: valued-field automorphisms induce actual LRV automorphisms; Mathlib infinite Galois fixed-field theorem | Actual henselian valuation ring; standard valuation-invariance quotation; earlier algebraic-envelope and centre inputs |
| Lemma 6.2 | `Paper.lemma_6_2` | Given nontrivially valued henselian substructure with RV surjectivity. Constructs the valued algebraic closure inside the ambient model and proves functional closure there. |
| Geometric descent in 6.3 | `PreparedDescent`: restrictions of actual special bijections; realization of every substructure key; descent of prepared existential predicates | Section 5 preparation used as given; arbitrary predicates on RV; includes zero fibres |
| Logical step toward 6.4 | `RelativeSyntax.hasVFQE_of_step` | Generic conditional reduction in LRV; does not establish its geometric step hypothesis |
| Syntactic Lemma 6.3 | `SyntacticLemma63`, integrated and audited | Arbitrary original parameter names, actual existential FV tuple, output selected before substructure and RV expansion; uniform model application is in UniformNormalizedElimination |
| Full Lemma 6.3 | `Paper.lemma_6_3` | Uniform elimination of a finite existential VF tuple from a well-sorted VF-quantifier-free formula. Retains all free VF and RV variables and supplies the preparation, native envelopes and literal normalization by checked proofs. |
| Proposition 6.4 | `Paper.proposition_6_4` | Arbitrary RV-only expansion and original named base. All elimination inputs are supplied by checked proofs. |
| Corollary 6.5 | `Paper.corollary_6_5` | Ordinary henselian valued fields of pure characteristic zero, with angular component and arbitrary sorted auxiliary expansion. Both valuation branches. |

See [STATUS.md](STATUS.md) and [STATEMENT-REVIEW.md](STATEMENT-REVIEW.md)
for current evidence and exact hypotheses. Legacy Sec6.lean and Sec6QE.lean
are excluded from the active library.
