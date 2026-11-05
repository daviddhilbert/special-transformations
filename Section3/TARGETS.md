# Paper checklist: Section 2 after QE and all of Section 3

Source: [arXiv:1006.2467v1](https://arxiv.org/pdf/1006.2467v1), Sections 2--3.
The numbering below was checked against that version. These are target
descriptions, not claims of completed formalization. All entries require
statement review, current compilation, and dependency/hypothesis audits.
Current item-level progress and verification scope are in [STATUS.md](STATUS.md).

## Section 2 after the statement of Theorem 2.3

| Item | Deliverable |
| --- | --- |
| Paragraph after 2.3 | Eliminate VF literals in favor of RV literals; define occurring VF polynomials. |
| Definition 2.4 and following paragraph | K-terms, RV-literals, domain/sort conditions, and a proved disjunction-of-conjunctions normal form using completed QE. The author approved rational VF factors with explicit pole and residue-domain guards on November 5, 2026; see [NORMAL-FORM-NOTE.md](NORMAL-FORM-NOTE.md). |
| Standing setup after 2.4 | ACVF(0,0), saturated ambient model, small base S, nontrivial Gamma(S), and ACVF_S via the atomic diagram. |
| Convention 2.5 | Base-relative definability, generated/definable and algebraic closure, and VF/RV/Gamma-generated bases. |
| Definition 2.6 | Open, closed and rv-balls; radii including special values; valuative centers; polydiscs and degenerate rv-polydiscs. |
| Definition 2.7 | C-minimality for structures and theories, with arbitrary parameters. |
| Theorem 2.8 | C-minimality of ACVF; do not consume the inherited placeholder. Preserve the theorem's full stated scope. |
| Notation 2.9 | Tuplewise rv/valuation/fibres and open/closed polydisc notation, including special-radius conventions. |
| Notation 2.10 | Mixed-sort coordinate indexing, projections, complements of coordinates, fibres and their compositions. |

## Section 3: Some structural properties

| Item | Deliverable / key scope |
| --- | --- |
| Lemma 3.1 | Descent of algebraicity from every point of a definable family to the base; compactness/uniform finite cover; review nonemptiness. |
| Corollary 3.2 | Both the VF-to-RV-fibre and RV-to-Gamma-fibre algebraicity descent statements, with tuples and base parameters. |
| Lemma 3.3 | Model-theoretic algebraicity of a VF element over VF and RV parameters implies field-theoretic algebraicity over VF(S) and the VF tuple. |
| Corollary 3.4 | The three field transcendence degrees agree, including arbitrary RV parameter sets as stated. |
| Corollary 3.5 | Every definable map from a subset of RV^m to VF^n has finite image. |
| Lemma 3.6 | Exchange in both VF and RV, with the correct closure and base. |
| Corollary 3.7 | Both nonalgebraicity-transfer statements: VF against a single RV parameter; RV against a Gamma parameter. |
| Lemma 3.8 | Same-valuation, zero-average finite family gives a pair of differences with the original valuation and RV nonconstancy; keep pure characteristic zero. |
| Lemma 3.9 | A finite definable subset of VF^n admits a definable injection into some RV^m over the required original parameters. |
| Lemma 3.10 | Algebraic families of closed balls have definable center functions. |
| Lemma 3.11 | A ball with the intended definable proper subset has a definable point; audit parameters and nonempty/proper conventions. |
| Corollary 3.12 | A definable map on rv^{-1}(B) to RV^m is constant on all but finitely many rv-fibres. |
| Lemma 3.13 | Algebraic ball families have centers for a (VF,Gamma)-generated base S. |
| Corollary 3.14 | For a VF-generated base with nontrivial Gamma(acl(S)), acl(S) is a model of ACVF_S(0,0). Requires the full substructure, not only its VF subfield. |
| Lemma 3.15 | The Gamma values at which a definable RV set has nonempty finite vrv-fibre form a finite definable set. |
| Paragraph before 3.16 | Sets over a base via surjective projection. |
| Notation 3.16 | Definable relations interpreted as quotient-to-powerset-valued functions, with invariant and saturated fibres and the specified domain. |
| Lemma 3.17 | A definable VF^times-to-powerset(RV^m) family whose value-group image is bounded on both sides is constant on a sufficiently small punctured ball. |
| Lemma 3.18(1) | Constancy on additive subgroup cosets outside finitely many exceptional cosets. |
| Lemma 3.18(2) | Definable quotient-valued representative family when the subgroup is a closed ball or S is (VF,Gamma)-generated; include the subgroup's ball classification. |
| Remark 3.19 | **Retracted by the author, November 5, 2026.** Excluded from proof obligations; see [RETRACTIONS.md](RETRACTIONS.md). |

The checklist includes cited results. A citation to the companion paper is not
itself a checked Lean proof. The author permits standard Marker/Engler--Prestel
results as explicit hypotheses; report any other remaining premise clearly.
