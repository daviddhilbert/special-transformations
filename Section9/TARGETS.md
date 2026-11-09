# Section 9 proof targets

The checklist covers the whole section of
[arXiv:1006.2467v1](https://arxiv.org/pdf/1006.2467v1#page=22). The active
lifting statements use essential isomorphisms in `RV[n]` and lifts into
`VF[n]`. Compiler and audit evidence is in [STATUS.md](STATUS.md).

| Target | Source or next proof obligation |
| --- | --- |
| Definition 9.1 | `Limits.lean` defines the extended limit sets and their minimality in the published language. |
| Lemma 9.2 | `FinitePointLimits.lean` gives equal VF closures of two minimal limit sets. `LimitTopology.lean` relates the Gamma-polydisc closure to the valuation topology. |
| Lemma 9.3 | `FinitePointLimits.lean`: union of the two closed minimal VF limit sets. `FiniteLimitSeparation.lean` gives uniqueness and the union rule for finite extended limit sets, including infinity. |
| Lemma 9.4 | `LimitCardinality.lean`: a finite minimal limit set injects into one nearby unary fibre. Its hit sets use `LimitBallDefinable.lean` and the checked unary definable germ theorem. |
| Lemma 9.5 | `LimitPolynomialCover.lean` supplies the polynomial over the original field. `LimitProjectiveRoots.lean` gives finite candidates in both charts. `LimitFiniteCandidate.lean`, `FiniteFibreLimit.lean`, and `LimitDefinability.lean` give the typed product, minimality and same-base definability. The full headline passed the post-restart audit. |
| Definition 9.6 | `Differentiation.lean`: the arbitrary-rank error estimate for the VF linear derivative and its uniqueness. |
| Lemma 9.7 | `Differentiation.lean`: composition of the linear derivatives. |
| Lemma 9.8 | `GenericDifferentiation.lean` proves full differentiation at VF-independent points using simple-root equations. `PartialDerivativesAE.lean` restricts to coordinate axes and bounds the exceptional set. |
| Corollary 9.9 | `PartialDerivativeFormula.lean` gives the same-base derivative graph. `PartialDerivativesAE.lean` applies generic continuity and gives one exceptional set for all partial derivatives. |
| Definition 9.10 | `VFJacobian.lean` defines the partial matrix determinant for VF functions. `MixedJacobian.lean` adds the fixed-label local chart on a mixed domain. The uniqueness proofs identify the Jacobian across choices of local chart. |
| Lemma 9.11 | `SpecialJacobianAE.lean` compiled the almost-everywhere determinant-one statement by the triangular derivative of a centripetal step and the chain rule. The printed everywhere clause has a discontinuous-focus obstruction. See [DIFFERENTIATION-ERRATA.md](DIFFERENTIATION-ERRATA.md). |
| Lemma 9.12 | `MixedJacobian.lean` and `MixedDifferentiationAE.lean` passed the full audits for the approved pointwise rule under full differentiability and its generic consequence for a finite-to-one first map. |
| Definition 9.13 | `RVFiniteEssential.lean` describes the essential restriction of the finite-volume objects and the VF dimension bound on the discarded degenerate locus. |
| Definition 9.14 | `GammaJacobian.lean` defines the Gamma weight ratio on nondegenerate labels. `RVJacobian.lean` proves uniqueness and projection of the point-normalized residue tangent determinant to the paper's Gamma quotient. `GenericRVJacobian.lean` proves same-base generic definability. `GenericRVJacobianChain.lean` passes the audit for the proposed generic chain rule. The pointwise RV claim has a finite-volume counterexample in [RV-CHAIN-ERRATUM.md](RV-CHAIN-ERRATUM.md). |
| Corrected Lemma 9.15 | `PaperLiftComparison.lean` passes the full audit for arbitrary lifts with a same-base exception in the source volume image. It supplies the candidate from 9.14 and uses `HenselizedGaussGraphInput VF`. `GaussGraphConstruction.lean` constructs that input from the authorized finite-extension reference. The unrestricted Gamma assertion was withdrawn by agreement. |
| Theorem 9.16 | `PrescribedVolumeLift.lean` passes the full audit for the same-base definable bijective lift with prescribed RV Jacobian outside a VF-small set. It uses both paper compatibility conditions and the explicit `HenselizedGaussGraphInput VF`. `ZeroArityVolumeJacobian.lean` covers the arity-zero case without that input. |

The separate Gamma descent lemma concerns bijections whose VF determinant
has constant finite valuation on a VF co-small part of each fibre.
[LEMMA-9.15.md](LEMMA-9.15.md) records the intrinsic coarsening argument.
It is separate from the forward lifting theorem.

## Root bounds for Lemma 9.5

For a unary input and unary output, every graph point is algebraically
dependent over the original VF parameter field. An independent point
would have an open polydisc inside the graph and an infinite second
fibre. Reuse `exists_polynomial_vanishing_on_selection` to obtain a
single nonzero polynomial over the original field that vanishes on
the graph. The finite-fibre version is in `LimitPolynomialCover.lean`.

For the polynomial `P(X,Y)`, divide out the maximal common power of `X`
from its coefficients in `Y`. The minimum input exponent occurs in the
support, and the coefficients in that row multiply distinct powers of
`Y`, so the specialization `P₀(Y)` at `X=0` is nonzero.
`LimitPolynomialNormalization.lean` implements the input factorization
and the choice of the input radius from the coefficient bounds. On the
chart `v(Y) ≥ 0` in additive
order, `P(x,Y)−P₀(Y)` has arbitrarily large valuation uniformly in `Y`
as `x` approaches zero. Away from small balls about the finitely many
roots of `P₀`, the product of its linear factors gives a uniform lower
bound on its absolute value. A root of `P(x,Y)` must therefore lie near
one of these roots. On `v(Y)<0`, use `Z=1/Y` and the reciprocal
polynomial in `Z` instead. The candidate `Z=0` represents infinity,
and the other candidates invert back to finite points. For a tuple of
outputs, use the coordinate projections of the graph and take the
product of the finite candidate sets.

A minimal subset of the finite candidate set exists by finite descent.
By separation and minimality, membership means that every output
neighbourhood of that point is hit arbitrarily close to the input centre.
The same characterization shows that any other minimal set is contained
in this finite set and hence equals it. For definability, represent both
radii by arbitrary nonzero VF elements and use a finite case split for
the coordinates at infinity. In multiplicative order, the output
condition for a finite coordinate is `v(y − b) < v(r)` and the condition
at infinity is `v(y * r) > 1`, where `r` represents the output radius.
This uses VF multiplication and valuation comparisons with the original
parameters. The auxiliary roots of `P₀` do not occur in the formula.

## Generic full differentiation for 9.8, 9.11 and 9.12

The positive exponent in the printed Lemma 8.6 need not give a bound
for the difference quotient by itself. An exponent below one leaves
an unbounded term after dividing by the increment. Use the separable
equation argument below to obtain the linear bound and the derivative
from the standing characteristic-zero assumptions.

Fix the input and output RV labels where the latter are locally
constant. At a VF point independent over the parameter field, each VF
output is algebraic over the field generated by the input and the
parameters. Clear the denominators in its characteristic-zero minimal
polynomial to obtain a polynomial `P(X,Y)` over the parameter field
whose output derivative is nonzero at the graph point. The definable
locus `P(x,f_j(x))=0` contains the generic point, so the checked
`independent_definable_mem_nhds` lemma supplies a neighbourhood on which
the same equation holds. Checked generic continuity supplies the
smallness of the output increment at that point.

Divide the first-order Taylor equation by the nonzero output
derivative. Bound its input linear term by `B` times the input size
with `B ≥ 1`, and its Taylor remainder by `C` times the square of the
maximum input and output sizes. Shrink using continuity so `C` times
the maximum is below one in multiplicative valuation order.
`ImplicitEstimate.lean` then bounds the error in the implicit linear
approximation by `C` times the square of the enlarged input size. This
proves full differentiation in arbitrary rank. The polynomial equation
is already valid on the neighbourhood, so this step can use continuity
directly. The stronger good-reduction comparison in 9.15 still needs
its own integral presentation.
