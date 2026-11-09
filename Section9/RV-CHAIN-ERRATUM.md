# The pointwise RV chain rule after Definition 9.14

The sentence after Definition 9.14 asserts the chain rule wherever all
three Jacobians exist. The finite-volume condition alone does not give
this pointwise assertion. [Special transformations, page 25](https://arxiv.org/pdf/1006.2467v1#page=25).

Take the same definable label set for three `RV[1]` objects. The set has
three copies of `k×`, indexed by tags in `k×`, and one extra label `p`.
Here `k` is the residue field, viewed in `RV`. Give the three objects
volume coordinates `X`, `Y`, and `Z` as follows.

| Label | `X` | `Y` | `Z` |
| --- | --- | --- | --- |
| First copy, parameter `t` | `t` | `t` | `2t` |
| Second copy, parameter `t` | `t` | `2t` | `2t` |
| Third copy, parameter `t` | `t` | `3t` | `t²` |
| `p` | `1` | `1` | `1` |

Each volume map is finite-to-one. The identity on labels gives the
isomorphisms from `X` to `Y` and from `Y` to `Z`. At `p`, each of the
three pairwise volume correspondences has a smooth curve through
`(1,1)`. The remaining curve components miss `(1,1)` and the extra
label contributes a point already on the displayed curve.

- In the `X,Y` correspondence the curve is `y = x`, with slope `1`.
- In the `Y,Z` correspondence it is `z = y`, with slope `1`.
- In the `X,Z` correspondence it is `z = x²`, with slope `2`.

All three point-normalizations have scale `1`. Thus the RV Jacobian of
the composition is the residue unit `2`, while the product of the RV
Jacobians of the factors is `1`. Residue characteristic zero makes
these distinct. The failure occurs because the pairwise volume
correspondences forget which label contributed each branch.

The generic chain rule uses one graph point in all three
correspondences. Over a common coefficient field, take the coordinate
derivations of its first tuple and extend them to the joint graph
field. They produce tangent columns on each correspondence. When
the three tangents are graphs, the columns give the matrix product.
This proves the rule on the generic locus. The Gamma chain rule is
pointwise because the middle volume weight cancels directly.

The proposed replacement is an almost-everywhere identity for a
composable pair of essential isomorphisms in `RV[n]`. Outside a
same-base definable subset of the source labels of RV dimension less
than `n`, all three RV Jacobians exist and the composition Jacobian is
the product of the two factor Jacobians. The middle point is the image
of the same source label. The finite volume maps give the corresponding
bound on the source volume image of the exceptional labels.

Take the definable generic Jacobian for each of the three pairs. Pull the
middle pair's exception back through the first isomorphism. Outside the
union of the three exceptions the failure of the product identity is a
definable set of labels. If it has dimension `n`, its image in the joint
volume triples also has dimension `n` because the map has finite fibres.
Choose a full-dimensional fixed-value fibre of that image. Name the
scales and choose the normalized source tuple algebraically independent
over a small algebraically closed residue coefficient field. The two
other tuples are algebraic over the source tuple and are themselves
independent over the coefficient field, by the two finite projections.
The shared graph-field computation applies to this triple. It contradicts
membership in the failure set. The local scale cancellation is implemented
in `RVJacobianChain.lean`. `GenericRVJacobianChain.lean` proves the
proposed replacement with a same-base exception. `RVChainFinalAudit.log`
checks the full types and axioms, including the arity-zero version.

HK §5.5 also defines the RV derivative using the pairwise volume
correspondence. Its Definition 5.21 tests the RV Jacobian away from a
set of smaller RV dimension, which is the scope of the proposed
replacement. [Integration in valued fields, §5.5](https://arxiv.org/pdf/math/0510133v3#page=57).
