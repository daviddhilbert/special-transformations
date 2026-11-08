# Section 5 targets

Source: [arXiv:1006.2467v1, Section 5](https://arxiv.org/html/1006.2467v1#S5).
All needed earlier-section material is authorized as given. This checklist
tracks paper coverage; [STATUS.md](STATUS.md) records compiler evidence and
[INPUTS.md](INPUTS.md) records explicit hypotheses.

The November 6 normalization resolves the zero-fibre issue by choosing an
equivalent nonzero active locus. It leaves the actual map, inverse, endpoints,
length, alternation and original parameters unchanged and proves the printed
disjoint C-sharp codomain for that representative. The November 7
`Section5.Paper` exports cover real and named-Gamma parameters.
STATUS.md records the hypotheses and verification for each form.

| Source | Export or construction | Coverage |
| --- | --- | --- |
| Preamble | `hull_idem`, `isRVPullback_iff`, canonical image and tag lemmas | Shared released VF/RV sorts, all finite mixed arities, one absorbing RV point |
| Definition 5.1 | `Focus`, `Primitive`, `Chain`, `SpecialBijection`; Gamma focus/primitive/chain certificates | `ZeroNormalization`: same-map nonzero-locus representatives and printed disjoint C-sharp codomain, including original-Gamma certificates |
| After 5.1 | `SpecialBijection.preserves_pullback` | Includes zero-coordinate fibres; strict-radius assertions keep their nonzero premise |
| Lemma 5.2 | `lemma_5_2`, `lemma_5_2_after`; unary instance of `corollary_5_6_gamma` | Original-base actual deformation and retained initial chains |
| Remark 5.3 | `SpecialBijection.unary_inverse_fibre`, `SpecialBijection.remark_5_3` | Full nondegenerate output fibres, open polydisc and containment in an original RV fibre |
| Contraction paragraph | `exists_unique_definable_contraction`, `exists_unique_gamma_contraction` | Actual functions on key images, commuting square, uniqueness and complete original-base graphs |
| Theorem 5.4 | `theorem_5_4`, `theorem_5_4_gamma` | Any finite VF dimension and initial special bijection; exact original RV fibre; zero polynomials |
| Finite-family observation | `theorem_5_5_finite`, `theorem_5_5_finite_gamma` | Simultaneous preparation without discarding earlier contractions |
| Theorem 5.5 | `theorem_5_5`, `theorem_5_5_gamma` | Arbitrary definable original VF domain, contraction, pullback target and alternating concatenation |
| Corollary 5.6 | `corollary_5_6`, `corollary_5_6_gamma` | Every finite mixed VF/RV arity; actual special bijection and pullback image |
| Corollary 5.7, general | `Paper.corollary_5_7`, `Paper.corollary_5_7_gamma` | Actual same-base isomorphism to a canonical lift, starting from the finite-map dimension bound. The proofs construct the obstacles and dimensional presentations. |
| Corollary 5.7, finite | `Paper.corollary_5_7_finite`, `Paper.corollary_5_7_finite_gamma` | Both proofs transport finite RV fibres and construct an RV object with finite volume fibres. |

The final checkpoint verifies 28 modules and 282 headline types and axiom
lists. Twenty-six unchanged source-compiled modules were re-certified by a
fresh ordered kernel replay against the current given boundary, covering 1,186
declarations; the normalization and combined library were compiled freshly.
The original compiler receipts and exact source/artifact identities are retained.
All headline axioms are among the three permitted axioms. An additional
consumer check derived normalized real and Gamma Corollary 5.6 witnesses in
every mixed arity with compiler exit 0 and 39 permitted-axiom audits.
STATUS.md records the exact exits, scopes and evidence locations.

The finite-root and VF-dimension inductions are proved in Section 5 itself.
Earlier QE/root-free interfaces, invariant Gamma logic and specialization,
and the 4.2/4.13 category consequences are explicit accepted inputs. No
Section 5 conclusion or uniform special-bijection existence is an input.

The Gamma category exports give actual equivalences with full invariant
graphs to the actual Section 4 lift, together with the RV object's invariant
domain and volume. They express category isomorphisms directly as definable
bijections; a separate Mathlib category over Gamma bases is not introduced.
