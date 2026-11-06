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
| Lemma 6.2 | `HenselianModel.lemma_6_2` | Actual substructures, elementary algebraic envelope, original base image retained |
| Geometric descent in 6.3 | `PreparedDescent`: restrictions of actual special bijections; realization of every substructure key; descent of prepared existential predicates | Section 5 preparation used as given; arbitrary predicates on RV; includes zero fibres |
| Logical step toward 6.4 | `RelativeSyntax.hasVFQE_of_step` | Generic conditional reduction in LRV; does not establish its geometric step hypothesis |
| Syntactic Lemma 6.3 | `SyntacticLemma63`, integrated and audited | Arbitrary original parameter names, actual existential FV tuple, output selected before substructure and RV expansion; uniform model application is in UniformNormalizedElimination |
| Full Lemma 6.3 | `UniformNormalizedElimination.eliminate`, integrated and audited | Uniform formula for finite normalized input, retaining free VF parameters; explicit earlier preparation and ordinary native-envelope inputs; final integrated check passed |
| Proposition 6.4 | `NamedLogic.proposition_6_4`, integrated and audited | Original base named; full arbitrary free/bound contexts. Earlier preparation, normal form, Marker and ordinary native-envelope inputs are explicit; final integrated check passed |
| Corollary 6.5 | `DenefPasTheorem.corollary_6_5`, integrated and audited | Actual angular-component splitting and both valuation branches, original arbitrary free names, proper sort discipline and only RF/Gamma binders; explicit standard/earlier inputs; final integrated check passed |

The final pinned Lake certificate checks 78 modules, 444 full headline
types/axioms and the combined ACVF-QE + Section5 + Section6 import, with
compiler exits 0 and only the three permitted axioms. Exact sources, logs,
cache/provider identities and compiled artifacts are preserved in
`.scratch/section6-final78-444/`. See STATUS.md and STATEMENT-REVIEW.md for
the exact conditional scope. Earlier assembled and paused-run checkpoints
remain historical evidence. Legacy Sec6.lean and Sec6QE.lean are excluded.
