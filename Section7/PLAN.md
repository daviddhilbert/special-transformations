# Section 7 proof continuation

Read STATUS.md for compiler evidence. This plan separates the implemented
bridge from remaining work. The paper target is arXiv:1006.2467v1, Section 7.

## Generalized Hensel, Lemma 7.2

The construction below is implemented. The expanded verifier exited zero
on eighteen modules and 90 headlines, with stable resolved dependencies
and a successful combined ACVF-QE import. The separately compiled readable
statement review and root check also passed; see STATUS.md.

The intended conclusion is `∃! a`, where `a : Fin n → K` lies in the actual
RV fibre of the given nonzero tuple and every polynomial in the square
system vanishes at `a`. Gamma-polynomial conditions, finite residue values
and the simple-common-residue-root condition must be genuine definitions.
Use the ambient paper's pure-characteristic-zero scope when required by
derivative/valuation arguments. No `NormalizedHensel` premise may stand in
for the missing multivariate theorem.

1. The RV/Jacobian bridge is implemented in `GammaPolynomialAlgebra`,
   `JacobianNormalization`, `SimpleRootNormalization` and
   `IntegralNormalization`. Fresh compilation, full type review and headline
   axioms passed. `exists_integral_simpleRoot_normalization` constructs
   representatives `c`, row scalars `e` and a system `H` over the actual
   valuation ring, proves `map H_i = e_i F_i(cY)`, zero residue and a unit
   Jacobian at the all-one point. Derivative/determinant closure, simplicity
   at every RV representative, all row nonzeroness and exact-solution
   transport are proved, with no `JacobianResidueValue` or Hensel premise.
2. Prove ordinary multivariate simple-root lifting over a Mathlib
   `HenselianLocalRing R`. For polynomials `F_i` over `R` and an approximate
   point `a0`, the hypotheses are that each `F_i(a0)` lies in the maximal
   ideal and the evaluated Jacobian determinant is a unit. The conclusion
   is a unique exact zero congruent to `a0` modulo that ideal.
3. For existence, form the quotient by the polynomial equations and localize
   at the Jacobian determinant. Use pinned Mathlib's naive square-system
   `PreSubmersivePresentation`, compose with the localization presentation,
   prove its Jacobian a unit and its relative dimension zero, and invoke
   the standard-smooth-to-etale instance. Apply the proved generic
   `Imported.EtaleLifting.residuePoint_lifts`; explicitly recover polynomial
   evaluations and the original residue coordinates from the algebra map.
4. For uniqueness, inspect and adapt the identified unramified-diagonal
   source, or prove the divided-difference matrix argument. Do not assume
   maximal-ideal nilpotence or adic separatedness: these do not follow for
   the general nondiscrete valuation rings in scope. The generic uniqueness
   statement needed is equality of etale-algebra sections agreeing modulo
   an ideal contained in the target's Jacobson radical.
5. After the ordinary theorem is proved, apply `valuationRing_henselian` to
   the algebraically closed valued field and the already constructed system
   `H`. Map the lifted coordinates into the field; show that congruence to
   one modulo the maximal ideal is exactly the unit RV fibre, using
   `Valuation.mem_maximalIdeal_iff` and `RVCalc.rv_eq_iff` (including the
   nonzero-coordinate argument). Use `normalization_solution_iff` and
   invertibility of each `c_i` to transport both existence and uniqueness.
   The row `F_i != 0` premises and all scalar choices are already derived.
   Retain arbitrary finite arity, including zero. No surjectivity of the
   whole value-group carrier is needed.

## Continue to paper-specific lifting

For Lemma 7.4, use the original `GammaParameters.Base B`, genuine
`Saturated M κ`, `Cardinal.mk B.real < κ`, ACVF00 and
`VFGammaGeneratedBase B`. The inputs are a nonzero `Fin (n+1)` RV tuple and
algebraicity of its last coordinate over that same base plus the first
`n` RV coordinates. The output is a residue value and an actual polynomial
over `vfDefinableClosureFieldBase B`, mapped into VF. Its last partial
derivative is tested at the residue value divided by the last weight.
The field membership bridge identifies this coefficient field with the
actual VF part of the original base. No arbitrary normalizing representative
may become a coefficient of the output.

1. Remove Gamma names from the finite RV algebraicity witness using the
   checked `algebraic_rv_gamma_base_iff` on the base with the finite input
   tuple adjoined. Use the checked finite-row relation or parameter-promotion
   interface, then `model_uniform_raw_normal_form` to obtain guarded RV
   comparisons on the original real parameter slots.
2. `GeneratedRVRepresentatives` uses algebraic lifting and a finite mean to
   represent each named nonzero RV coefficient in the original VF field.
   The named RV zero is represented by VF zero. VF terms and their guarded
   rational expressions are evaluated in the same field. VF slots cannot
   depend on an RV input coordinate.
3. Freeze the actual coordinate values and choose a true guarded clause at
   the point. Valuation comparisons of raw monomials, pole guards and
   residue membership of individual summands are constant on this value
   fibre. For each flat residue factor, lift the monomials to Laurent
   monomials over the original VF field, omitting zero coefficients.
   Clear negative variable exponents by a common monomial on the nonzero
   fibre. Equal weights give a genuine gamma-polynomial presentation,
   including repeated exponents and cancellation.
4. A side of an RV equality is the leading term at its prescribed value
   of that weighted polynomial evaluation. For equal prescribed values,
   the equality is a residue-root test on the difference; for unequal
   values, it holds exactly when both sides drop below their prescribed
   values. `WeightedLeadingTerms` drafts the equal-value calculation.
   Retain the guard comparisons as well as the printed main equalities.
5. Normalize for evaluation only, by field representatives and a scalar
   at each residue value. On the varying last unit coordinate, specialize
   all other coordinates and reduce to the actual residue field. The
   chosen clause's truth pattern is given by finitely many polynomial
   root tests. A finite nonzero last-coordinate fibre forces a nonzero
   specialized polynomial vanishing at the point, by the finite-root
   argument in `PolynomialFibreExtraction`. In residue characteristic
   zero, a suitable iterated derivative still vanishes while the next
   derivative does not. Specialization commutes with differentiation;
   transport through the normalization chain rule and map the derivative
   of the *original* polynomial over the original coefficient field.

Remark 7.5 is verified: `FieldConstructibility` and `ResidueConstructibility`
use pure ACF QE and checked Section 4 residue purity over the original
residue parameter field. The comparison is through actual evaluation
kernels, including residue zero.

Theorem 7.6 uses both coordinatewise simple systems, alignment of their
residue values, simultaneous integer combinations, genuine small-parameter
compactness and definable gluing. The draft uses the simple coordinate
derivative of the opposite row, multiplied by that coordinate, as the
balancing polynomial. Its degree and exact value equal those of the opposite
row, and it stays in the original coefficient field. The diagonal
derivative terms survive reduction; derivative terms from the multipliers
multiply residue roots and vanish on reduction.
`IntegerAvoidance` verifies the common determinant choice in residue
characteristic zero. Lemma 7.2 supplies both unique directions of each
local fibre graph. Quantify the fibre-bijection property over both entire
fibres to get an original-base definable local domain. Compactness may
use the finite representative codes for the given correspondence's
Gamma parameters internally; only original-base formulas appear in the
finite cover and first-piece gluing. Do not assume `Sec7Prereq.localLift`.

For Corollary 7.7, use Section 4's `volume_relation_definable`, actual
finite-volume-image hypotheses in both directions, actual canonical lift
and the scissors presentation's universal property. The balanced
correspondence draft treats the nonzero piece by Theorem 7.6 and recursively
deletes one zero on each side on the remaining pieces. Equal weight gives
the matching zero, and the VF fibre forces VF zero in the deleted slots.
Attach the original RV label and its image under
the RV isomorphism to each fibre graph to obtain the definable lift
isomorphism. Show preservation of empty objects and restrictions/scissors;
then descend the object assignment to the actual positive quotients.
Use both `CategoryLift.corollary_5_7` variants for surjectivity after checking
their explicit earlier inputs (`UniformVerticalObstacles`, dimensional
reduction, and finite-fibre invariance). The finite draft now constructs
the required real mixed presentation from the checked Section 4 finite-map
characterization and injection refinement. It supplies finite-fibre
invariance by transporting a finite map through the presentation
bijection. The general variant retains its earlier dimensional
presentation input. The Gamma variants additionally
state their logic, support and presentation inputs. Verify those bridges
or record exact authorized earlier hypotheses, without treating an
unmatched premise as discharged. A free monoid or a chosen family of
underlying bijections is not the paper's quotient.

Run fresh pinned compilation, full type and hypothesis review, permitted
axiom audit and affected imports at each coherent boundary. Run independent
checks concurrently, and wait only for inputs a check actually needs.
Never stop proof jobs or restart Linux. Publish only with explicit authorization.
