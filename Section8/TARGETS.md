# Section 8 targets

Numbering follows [arXiv:1006.2467v1, pp. 19–22](https://arxiv.org/pdf/1006.2467v1#page=19).
The standing setting is the paper's small base in a sufficiently saturated
model of pure characteristic zero. A result may need less: in particular,
Lemma 8.1 uses only ACVF and finite first-order parameter support. For later
results keep real and genuinely imaginary Gamma parameters distinct and
retain the original base in all definability conclusions.

| Item | Target and first proof route |
| --- | --- |
| 8.1 | Finiteness for a definable VF set whose equal-radius open polydiscs at distinct points are disjoint. Use unary locality and induction on arity. The radius is finite, represented by a nonzero VF element. |
| 8.2 | For a total definable VF-to-VF tuple map, the source points isolated in the inverse image of some open neighbourhood of their output form an original-base definable set of VF dimension below the positive input arity. Prove the uniform two-radius relation and use 8.1. |
| Almost everywhere | A property on a full-dimensional definable set holds away from an original-base definable subset of strictly smaller dimension. Keep the VF and RV dimension versions distinct. |
| 8.3 | For a VF-unary map with a finite VF parameter tuple, a uniform finite set of positive rational slopes works on a definable locus with finite complement in each unary fibre. At each good point prove the locally constant branch or the exact value equation, with finite Gamma constants definable over the point and the base. |
| 8.4 | A definable bijection between proper centred balls of finite radius at zero taking centred open subballs to centred open subballs has slope one on a sufficiently small centred ball. Both the actual Gamma intercept and the radius must be definable over the original base. Prove integrality for the map and its inverse. |
| 8.5 | For a definable bijection between infinite unary VF sets, outside a finite definable exception find a ball and a nonzero RV scalar, both definable over the point and base, giving the RV difference identity for every pair in the ball. |
| 8.6 | For a multivariate VF map in a VF family, prove the one-sided value estimate on a definable locus of fibrewise full dimension. Keep the exponent uniform and positive, and the finite Gamma shift and radius definable over the point and base. |
| 8.7 | For a total definable VF tuple map, construct an original-base definable closed exception of dimension below the positive source arity; the map is continuous on its complement in the valuation topology. Prove definability and the needed dimension bound for the closure of the discontinuity set. |
| 8.8 | Define local constancy of an RV-set-valued function through equality of actual fibres on a VF neighbourhood. |
| 8.9 | An original-base definable family of RV sets is locally constant on a definable open VF locus of smaller-dimensional complement. Use the Section 3 additive constancy result in the unary case and dimension and uniformity for the induction. |

For 8.6, the named positive Gamma element is available from the paper's
standing assumption that `Γ(S)` is nontrivial. It is used to choose a
point below the endpoint of the ray of valid shifts.

For positive arity the dimension-drop targets use the ordinary Section 4 VF
dimension, including its nonemptiness conventions. With the library's
`dimVF(∅) = 0`, a strict bound below arity zero would be false. No analogous
restriction is needed for the finiteness statement in Lemma 8.1.
