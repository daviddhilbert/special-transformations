# Section 7 targets

Source: [arXiv:1006.2467v1, Section 7](https://arxiv.org/html/1006.2467v1#S7).
Current work started November 6, 2026. See STATUS.md for verification evidence.

| Target | Exact scope | Current implementation |
| --- | --- | --- |
| Definition 7.1 | Finite sums of monomials, possibly repeated exponents, of equal weighted finite value; residue roots on a fixed nonzero RV tuple; simple common residue roots | Presentations, residue-root independence, simple common roots and derivative/Jacobian closure are verified. `exists_gammaPolynomial_residue_projection` verifies that each actual residue polynomial lifts at all-one weights and degree. The expanded entry-point audit and root check passed. |
| Lemma 7.2 | A unique simultaneous VF zero in the RV fibre of a simple common residue root of an n-by-n gamma-polynomial system | `generalized_hensel` and `encoded_generalized_hensel` prove the full assertion using the RV/Jacobian bridge and ordinary multivariate lifting over the actual henselian valuation ring. Fresh pinned compilation, full type review, allowed axioms, combined ACVF-QE import and the separate project-root check passed. |
| Definition 7.3 | A relation restricts to a bijection on every product of RV polydiscs indexed by the given RV correspondence | The full VF-power, arbitrary ambient pullback, and labelled companion-graph instances passed source, type, axiom and integration checks. |
| Lemma 7.4 | Over the original (VF,Gamma)-generated small base, RV algebraicity in the last coordinate supplies a base-coefficient gamma-polynomial residue root with nonvanishing last derivative | Verified as `lemma_7_4`. The full printed type and permitted axioms were reviewed, and the project-root check passed. |
| Remark 7.5 | Definable residue-field sets are constructible over the specified residue parameter field | Verified as `remark_7_5`, with the exact tuple pullback from the spectrum over the original residue parameter field. It uses Section 4 residue purity and released pure ACF QE. Source, full type, allowed axioms and expanded root import checks passed. |
| Theorem 7.6 | Every definable finite-to-finite correspondence in nonzero RV n-tuples has an original-base definable VF lift | Verified as `theorem_7_6` and `theorem_7_6_sorted`, using original-base polynomial systems, simultaneous integer combinations and genuine compactness. Source, type, axiom and project-root checks passed. |
| Corollary 7.7 | The canonical lift induces the paper's surjective Grothendieck semigroup homomorphisms, including its finite variants | The real-parameter statements and both `Section7.Paper` named-Gamma forms pass source, full type, axiom, and project checks. All use actual Gamma dimension and the proved Section 5 representations. |

The ambient paper setting is pure characteristic zero in a sufficiently
saturated model over a small named base. Generation assumptions are retained
where stated. Elementary valuation estimates and representative independence
hold over arbitrary valued fields and therefore need no saturation or
characteristic-zero premise. No new standard-reference hypothesis is adopted
in the present modules.

`none` is the single RV absorbing element, equal to `rv(0)`. Gamma and residue
values in Definition 7.1 are finite, represented here by nonzero elements of
Mathlib's multiplicative value-group-with-zero. Paper strict increase of value
is Mathlib strict decrease. A fixed value fibre alone is never used as an RV
fibre.
