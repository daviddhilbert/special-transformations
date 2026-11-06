# Section 4 target checklist

Source numbering: [arXiv:1006.2467v1](https://arxiv.org/pdf/1006.2467v1).
The needed Section 3 results are completed checked imports, as recorded in
[INPUTS.md](INPUTS.md).
Verification and remaining premises are recorded in [STATUS.md](STATUS.md).

| Number | Target | Main dependencies |
| --- | --- | --- |
| 4.1 | VF dimension from definable finite-to-one witnesses | Complete graph API; real and imaginary targets |
| 4.2 | Equivalent injective witnesses | Finite coding; genuine saturation; padding |
| 4.3 | Maximum over RV/Gamma fibres | Uniformization; parameter extension |
| 4.4 | Comparison with VF transcendence degree | 3.3--3.4; finite algebraic coordinates; 4.2 |
| 4.5 | Finite-valued relation image inequality | 4.4; complete definable relation |
| 4.6 | Full dimension and an open polydisc in a fibre | 4.3--4.4; C-minimality; Gamma radii |
| 4.7 | Bound from an included rv-polydisc | 4.6; absorbing-coordinate conventions |
| 4.8 | Zariski closure comparison | 4.4; commutative-algebra dimension bridge |
| 4.9 | RV dimension and its accompanying rank properties | RV exchange; compactness; definable finitary functions |
| 4.10 | Residue-fibre Zariski comparison | 4.9; residue-field normalization |
| 4.11 | A definable value tuple attaining RV dimension | 3.7; 3.15; induced Gamma structure |
| 4.12 | RV-fibre dimension | RV dimension; bounded finite arities |
| 4.13 | Invariance under definable bijections | 3.3; mutually algebraic VF bases; genuine RV ranks |
| 4.14 | VF categories and their characterizations | Dimension layer; finite RV fibres |
| 4.15 | Weight | Single absorbing RV element |
| 4.16 | RV categories and their morphisms | Definable maps; volumetric and finite-image conditions |
| 4.17 | Padding functor | Definable padding; full faithfulness |
| 4.18 | Canonical lifts | Definability; companions; category membership |
| 4.19 | Morphism criterion from a commuting lift | 3.2--3.3; algebraic-to-finite-image step |
| 4.20 | Bijective variant | 4.7; invariance of dimension |
| 4.21 | Multiplication and its units | Positive scissor quotient; degree-zero convention |
| 4.22 | Congruences and quotient structures | Additive and multiplicative compatibility |
| 4.23 | Congruence criterion | Equivalence; translations; multiplication |

Also include the unnumbered construction of the positive Grothendieck
semigroup, its disjoint-union description, commutativity and distributivity,
the groupification and its universal property, and the final injectivity
assertion for the padding homomorphism. Constructing lifts of arbitrary RV
isomorphisms is a Section 7 dependency, not an input silently available here.

The author clarified on November 5, 2026 that the unnumbered image inequality
after Definition 4.9 is for a definable **finitary** function, meaning each
set-valued output is finite. Formalize the full union of those finite values.

For empty sets and zero arities, state the chosen dimension convention
explicitly. Keep nonemptiness where an attained maximum or a polydisc
requires it. Compare these conventions separately with Krull dimension.
