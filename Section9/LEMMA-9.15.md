# Lemma 9.15 and the comparison needed for volume descent

The numbering is from [Special transformations, arXiv v1, pp. 25–27](https://arxiv.org/pdf/1006.2467v1#page=25).
The comparison with HK uses [Integration in valued fields, arXiv v3, pp. 52–59](https://arxiv.org/pdf/math/0510133v3#page=52).

The author approved the following targets on November 7, 2026. Retain
9.15's RV comparison with its RV-small exceptional labels and fibrewise
VF-small exceptions. Delete the unrestricted Gamma assertion. Retain
9.16, including its pointwise Gamma compatibility hypothesis, and prove
the constant-finite-valuation descent statement below separately. Treat
all objects on their nondegenerate essential parts. The author also
approved the finite-volume category RV[n] as the active scope of the
comparison and lifting targets. New external mathematical references
outside the standing approvals require approval before use. The proof
modules state any remaining reference input explicitly and keep it
separate from hypotheses on the ACVF model or on the lift.

## The obstruction in arity two

Let `m` be the maximal ideal and use additive valuation `v`. On
`(m \ {0})²`, put `a = v(x)` and `b = v(y)`. Define `H` by the following
table. The last column is computed by differentiating each rational branch.

| Input | Output | Output values | `v(det DH)` |
| --- | --- | --- | --- |
| `a > 2b` | `(x, x/y)` | `(a, a−b)` | `a−2b > 0` |
| `b < a < 2b` | `(y²/x, y)` | `(2b−a, b)` | `2(b−a) < 0` |
| `a < b` | `(xy, x)` | `(a+b, a)` | `a > 0` |
| `a = 2b` | `(x/y, y)` | `(b, b)` | `−b < 0` |
| `a = b` | `(xy, y)` | `(2b, b)` | `b > 0` |

The three strict regions cycle in the order shown. The first two rational
maps are their own inverses on the torus. The inverse of `(xy, x)` is
`(y, x/y)`. The two ray maps are inverses. Thus `H` is a bijection of the
punctured product and extends by the identity on the two coordinate axes.
Valuation is locally constant away from zero, so every row, including each
ray, is open in the VF topology. The displayed determinants are the actual
valued-field derivatives on these rows. At a point of a row, the rational
Taylor remainder is bounded by a point-dependent constant times the square
of the largest increment in multiplicative order. Shrinking the polydisc
gives Definition 9.6's error bound in arbitrary valuation rank.

Conjugate `H` by translation by `(1,1)`. The resulting parameter-free
bijection of `(1+m)²` lifts the identity on the singleton RV object of degree
two with volume coordinate `(1,1)`. Its Gamma-Jacobian on RV is zero. The
full-dimensional VF locus off the axes has no point with valuation zero
of the determinant. The axes have VF dimension one, which bounds the
dimension of the agreement locus and excludes every VF-generic point.
This example also applies to the second claim of HK Corollary 5.23
if the claim means the valuation of the ordinary
determinant at a generic point of a polydisc. HK Proposition 5.22 is unary.
The passage from individual partial derivatives to the determinant of a
general polydisc bijection is where the obstruction occurs. The example
also refutes the repeated claim in [Yin, Integration in ACVF, Lemma 2.33](https://arxiv.org/pdf/0809.0473#page=6).

## RV comparison for arbitrary lifts in RV[n]

Use the actual graph of the lift, with its RV label fixed when taking a
derivative. The proof proceeds as follows.

1. Work on a fixed pair of source and target value-group fibres. Divide
   the VF coordinates by fixed representatives of the radii so that the
   coordinates are units. The change of determinant is exactly the
   product of the target representatives divided by the product of the
   source representatives. If a definable bad locus has RV dimension `n`,
   Lemmas 4.10–4.11 put an `n`-dimensional part in a fixed value fibre of
   the correspondence. The two projections are finite-to-one by the
   definition of the RV morphism and its inverse. Thus both normalized
   residue tuples are algebraically generic over a small algebraically
   closed valued coefficient field `E` that contains the fixed VF
   parameters and the scale representatives. Include representatives of
   fixed RV parameters in `E` if needed. Keep the varying RV label as an
   RV name. Dimension is unchanged by adding the fixed representatives.
2. At an actual lifted point `(x,y)`, the residues of `x` are independent
   over `k(E)`. The valuation on `E(x)` is consequently the Gauss
   valuation. By the VF algebraic-closure calculation of Section 3,
   naming the RV label adds no VF algebraicity, so `y` is algebraic over
   `E(x)`. Pass to the henselization of `E(x)`. Its value group is the
   divisible group of `E`. A finite extension containing `y` has the same
   value group and, by defectlessness in residue characteristic zero,
   its degree is the residue degree. Lift the minimal polynomial of a
   primitive residue generator to a monic integral polynomial and use
   Hensel in the extension to lift the generator as a simple root. Its
   powers then form an
   integral basis by linear independence of their residues, after
   normalizing coefficients by one of least valuation. This describes
   the actual branch using étale equations, even when a minimal polynomial
   for an individual `yᵢ` has repeated reduction.
3. The coordinate derivations on the Gauss field preserve its valuation
   ring and reduce to the coordinate derivations on `k(E)(res x)`. For
   the Gauss field this is the quotient rule in the localization of
   `O_E[X]` at the polynomials with at least one unit coefficient.
   Extend through the henselization and the finite unramified extension
   using the étale equations. In each implicit derivative the denominator
   is a unit, so the derivatives still commute with reduction. To
   identify them with derivatives of the lift, use the simple-root
   equations from the generic differentiation proof for 9.8. That
   proof works with the actual definable graph and supplies both the
   full derivative and its implicit slope in each coordinate. Applying
   the algebraic coordinate derivations to the same equations gives
   the same slopes by uniqueness of the scalar solution. The identity
   is checked in `ImplicitScalarDerivations.lean`. The construction and
   reduction of the bounded derivations are in
   `BoundedGraphDerivations.lean` and `RVGraphJacobianComparison.lean`.
4. Over the generic residue correspondence both projections are étale.
   The residue of the computed derivative is the derivative of that
   correspondence by uniqueness of extending derivations through a
   separable algebraic field extension. Its determinant is nonzero. Undo
   the diagonal scaling to recover the RV determinant of Definition 9.14.
   This argument applies to each VF representative of a generic source
   residue tuple. `PaperLiftComparison.lean` checks the uniform definable
   bad locus and the RV dimension argument over the original base, with
   the embedded graph-field construction explicit.

The relevant standard inputs are henselization and the fundamental
equality in residue characteristic zero, covered by the standing
authorization for [Engler–Prestel, *Valued Fields*](https://link.springer.com/book/10.1007/3-540-30035-X),
especially Theorem 3.3.3 for the Galois degree calculation, Section 4.1
and Theorem 4.1.3 for the permanence of henselianity under algebraic
extensions, and Theorems 5.2.2 and 5.2.5 for the henselization. On November 8, the author approved
[Stacks Project, Lemma 10.155.1](https://stacks.math.columbia.edu/tag/04GN)
and [Lemma 15.125.6](https://stacks.math.columbia.edu/tag/0ASK).
The Lean construction uses the checked étale presentation from 04GN and
the ordinary universal property from 04GS. It proves the valuation-ring
step in `FilteredValuation.lean` and gets equality of values for the
embedded Gauss extension from divisibility in `GaussExtension.lean`.
The finite-extension reference remains an explicit proof input.

`FiniteHenselianExtensionReference` takes a finite extension of a
henselian valued field of residue characteristic zero with unchanged
values. It asks for henselianity of the extension and equality of the
residue and field degrees. For the degree identity, take a finite
Galois closure and apply Theorem 3.3.3 to both Galois extensions in
the tower. Henselianity gives a unique valuation at each level, and
multiplicativity of the value-group indices and residue degrees gives
the formula for the original extension.

For the embedded graph-field input, start with the valuation ring of
the Gauss field. Its henselization maps locally to the ambient valuation
ring by [Stacks 04GS](https://stacks.math.columbia.edu/tag/04GS), since
the ambient ring is henselian. The henselization is a valuation ring
by the filtered étale construction. Its algebraicity over the original
ring gives injectivity of the map, which extends the inclusion of the
original valuation ring. The image
is the ambient valuation ring restricted to the image fraction field.
If an element of the image fraction field is outside the image ring,
its inverse belongs to the maximal ideal of the henselization. Locality
sends that inverse to the ambient maximal ideal. This gives the required
valuation-ring identification and transports the étale cover.
The field is algebraic over the Gauss field by the henselization theorem.
Adjoin the finitely many output coordinates and use the fundamental
equality over the resulting henselian base. The checked algebraic
value-group argument gives ramification index one. These are the fields
and degree facts recorded by `HenselizedGraphData.lean`.

Lean checks the reduction of the actual graph derivative, its affine
transport and the bound on the definable discrepancy over the original
base, all using the graph-field construction.
Theorem 9.16 and the lifting direction in Theorem 10.5 use that comparison
on the full-dimensional part of the chosen Section 7 lift. On each
lower-dimensional piece, the weighted Section 7 head lift gives the
Gamma value of its determinant. The finite-family representative theorem
then gives the two tails and the prescribed determinant factor over the
original base with the VF head as a variable. The pointwise Gamma
compatibility ensures that the corrected affine slope sends the source
ball onto the target ball. See [RV-CATEGORY-AUDIT.md](RV-CATEGORY-AUDIT.md).

## A separate Gamma descent statement

For descent, the required statement is this. Suppose a definable
bijection of two nondegenerate RV polydiscs has VF Jacobian of **constant
finite valuation** away from a smaller-dimensional definable subset of the
source. Then the constant is the sum of target radii minus the sum of
source radii. Applied fibre by fibre to a volume-preserving lift, the
ratio of the lifted volume forms provides precisely this constant. This
would replace the use of the false comparison in HK 5.24 and Yin 2.34.

### Intrinsic approach via a coarsened valuation

This is now the preferred proof route. Normalize the two polydiscs to
`mⁿ` by translations and diagonal scaling. The new constant is the old
constant minus the target radius sum plus the source radius sum. Work in
the additive valuation order. Choose a small algebraically closed valued
coefficient field `E` containing VF representatives of the parameters of
the normalized map, its exception and the constant `c`. Enlarge `E` if
necessary to have nontrivial value group. This is an auxiliary field for
the proof of an equality in Gamma.

1. Choose each positive coordinate value `γᵢ` infinitesimal over the
   positive values of the small algebraically closed field generated by
   `E` and the preceding coordinates. Finite satisfiability uses the
   divisibility of the value group, and small-parameter saturation gives
   the actual input tuple `x ∈ mⁿ`. The convex subgroup `Δ` of values
   infinitesimal over `Γ(E)` meets `Γ(E)` trivially. Write `w` for the
   coarsened valuation into `Γ/Δ`. The Lean construction localizes the
   fine valuation ring at the corresponding prime of coefficient
   thresholds. Distinct monomials
   in `x` with nonzero coefficients from `E` have distinct original
   values. Consequently, for every nonzero polynomial `P`,
   `w(P(x)) = min_I w(P_I)`. The tuple `x` is algebraically independent
   over `E`, and its `w`-residues are independent over the `w`-residue
   field of `E`. The value group of `E(x)` for `w` equals that of `E`.
2. Let `y = H(x)`. Section 3 gives `y` algebraic over `E(x)`. The
   coarsened valuation is nonnegative on `y`, since `H` takes values in
   `mⁿ`. The coordinate derivations of `E(x)/E` preserve its Gauss
   valuation ring by the polynomial and quotient rules. They also
   preserve the valuation ring of its henselization: extend through
   local étale algebras by lifting the dual-number homomorphism
   `a ↦ a + D(a)ε`, then use the quotient rule at localizations and pass
   to the filtered colimit. The Stacks Project, Lemmas 10.155.1 (04GN)
   and 15.125.6 (0ASK), supply the colimit presentation and its
   valuation-ring property under the author's standing reference
   approval. Engler–Prestel, Theorem 5.2.5, gives immediacy.
3. The finite extension of that henselization generated by `y` has the
   same value group by divisibility and finite index. Residue
   characteristic zero and the fundamental equality give field degree
   equal to residue degree (Engler–Prestel, Theorem 3.3.3, with the
   normal-closure argument). Choose a primitive residue generator and
   lift its minimal polynomial to a monic polynomial. Hensel gives a
   root with the chosen residue and unit derivative. The powers of
   this root give an integral basis: after dividing coefficients by one
   of least valuation, their residual combination is nonzero by
   independence of the residue powers. Differentiating the monic
   equation shows that the root derivative is integral. Thus the
   coordinate derivations give integral entries `Dᵢ(yⱼ)`.
4. Identify this matrix with the derivative in the original valuation
   using the simple-root equations for the actual definable graph, as in
   the RV argument above. `ImplicitScalarDerivations.lean` checks that
   the slopes from these equations are the coordinate derivation values.
   The auxiliary coarsening supplies their integrality.
5. The chosen `x` is outside the lower-dimensional exception, so the
   determinant has original value `c`. Integrality of all entries gives
   `w(det) ≥ 0`. Since the quotient by `Δ` preserves the order on `Γ(E)`,
   this gives `c ≥ 0`. To get the reverse inequality, apply the same
   construction to the inverse with a transcendental target tuple. Its
   preimage is transcendental since the target is algebraic over the
   preimage. Apply the checked pointwise VF chain rule to the two local
   charts and the identity map. The inverse determinant has value `−c`,
   which must also be nonnegative.

This route uses the same Gauss derivations and unramified extension
calculation as the RV comparison. The coarsening, Gauss tuple, derivative
identification, and two-sided determinant bound passed their Lean audits.
`GammaDescentAudit.log` checks the normalized and unnormalized
conclusions conditional on the embedded graph-field construction.

### Alternative via mixed characteristic

Normalize the source and target by translations and diagonal scalings to
`mⁿ`. It suffices to show that the constant shift is zero.

1. For a fixed graph formula, express the hypothesis in first-order form.
   One can take the exceptional set to be contained in the zero locus of
   a nonzero polynomial, by QE and absence of VF interior. Fix its degree
   as well as the graph formula for the transfer. Definition 9.10's
   partial derivatives and the constant determinant valuation use
   quantifiers over field elements and valuation comparisons. The
   mixed-characteristic argument supplies local analyticity on its good
   locus, so full differentiability is unnecessary as a premise. Real
   RV parameters and Gamma parameters can be represented by VF elements
   for this transfer.
2. In `Q_p^alg`, choose a finite extension `E / Q_p` containing all the
   representatives and parameters. Every automorphism over `E`
   preserves the valuation. The map and inverse therefore restrict to a
   bijection of `m_Eⁿ`, by the fixed-field theorem. This is the same VF
   restriction argument as in [HK, Example 12.8](https://arxiv.org/pdf/math/0510133v3#page=109).
   Here the parameter representatives are chosen in the finite extension
   to begin with. Off a proper algebraic
   set the restriction is locally analytic. To see this, use QE and the
   algebraic graph in characteristic zero. Outside the projections of
   intersections and non-étale points of its components, the implicit
   function theorem gives a local analytic branch. The quantifier-free
   graph stays true there since zero polynomial terms vanish on that
   branch and nonzero terms keep their leading terms. Apply the same
   reasoning to the inverse. Definable bijections preserve VF dimension
   by the VF algebraic-closure calculation, so both the omitted source
   set and its image lie in proper algebraic sets and have Haar measure
   zero on `E`-points.
3. For the local-field change of variables, the author approved François
   Loeser, *Arizona Winter School Lecture Notes on p-adic and Motivic
   Integration* (2003), [Proposition 1.2.1, pp. 1–2](https://swc-math.github.io/aws/2003/03LoeserNotes.pdf#page=2),
   on November 7, 2026. Its scope is an analytic isomorphism between open
   subsets of a local field. Establishing that scope for the good part of
   the restricted map is a separate step. A direct proof of the required
   measure comparison is also possible: at a good point `z` write
   `A = DH(z)`. On a sufficiently small lattice ball about zero,
   `A⁻¹(H(z+h)−H(z)) = h + e(h)` with `e` strictly contracting and
   `e(0) = 0`. The contraction theorem gives a bijection of the lattice
   ball onto itself. Thus the image of the ball about `z` is its linear
   image by `A`, up to translation. The Haar measure of the linear image
   scales by the absolute value of `det A`. Partition the good locus
   into countably many disjoint such balls and sum. This gives
   `μ(m_Eⁿ) = q⁻ᶜ μ(m_Eⁿ)`, with valuation normalized on `E` and `q` its
   residue cardinality. Both measures are finite and positive, so
   `c = 0`. The statement for each
   graph formula and exceptional polynomial degree then transfers to
   equicharacteristic zero by taking an ultraproduct as `p` tends to
   infinity and using completeness of ACVF in characteristic `(0,0)`.

The reference approval covers the local-field change-of-variables formula.
It does not certify a Lean theorem. The first-order transfer, identification
of the analytic locus, and application of the measure formula remain proof
obligations. No Haar measure on the ACVF model or its algebraic mixed-
characteristic approximants is needed. The unary HK comparison and the
later paper's unary Gamma-linearity argument retain their own scope.
