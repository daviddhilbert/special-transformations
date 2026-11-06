# Section 3 and remaining Section 2 preliminaries

Start with [STATUS.md](STATUS.md), then [TARGETS.md](TARGETS.md).
The original [HANDOFF.md](HANDOFF.md) records the starting constraints.

This is a subdirectory of `special-transformations`, not a separate repository.
The scope is all of Section 3 plus everything in Section 2 after
the QE statement. QE is complete in the pinned ACVF-QE dependency.

Existing section-related Lean files have been moved here from `QE/`;
`Balls.lean` came from `Milestone0/`. `LegacyScaffold/` contains earlier stubs.
The initial relocation preserved their contents byte for byte. A subsequent
audit compiled the 24 top-level legacy snapshots and their nine local
dependencies under their historical staging names. Eight misleading legacy
comment blocks have since been corrected without changing proof code.

The new checked library starts at [Library.lean](Library.lean), which imports
only new audited modules and the pinned ACVF-QE definitions. It includes
base-relative closure and compactness infrastructure, exact C-minimality,
sorted tuple descent, ball and coordinate interfaces, both assertions of
3.6 and 3.7, results 3.8–3.15, 3.17, both parts of 3.18, and
quotient-family notation. Finite coding preserves the original parameter base
and includes its complete graph in all VF tuple arities. Closed-ball centers
are defined on the actual ball quotient over the same original base. Definable
points use a nonempty proper subset without naming the containing ball.
Uniform polynomial support also proves finite RV-fibre exceptions. Lemma 3.15
uses the actual Gamma quotient and preserves the original base. A separate audit
records the {1,-1} obstruction to the unrestricted classification in Remark 3.19;
the author has [retracted the whole remark](RETRACTIONS.md), which is excluded
from the remaining proof obligations. Additive subgroups are proved to be balls,
and the uniform root set gives the finite exceptional additive cosets in 3.18(1).
Both alternatives of 3.18(2) include the complete original-base quotient
graph and a realizing representative in every class, including genuine
Gamma-named bases. The entry point
does not certify every item in the section. See [STATUS.md](STATUS.md) for the
exact hypotheses and the remaining work.

The actual Gamma quotient now has its ordered divisible group operations and
full invariant-preimage parameter interface. The checked Gamma-base extensions
include C-minimality, VF algebraicity and exchange, finite RV-to-VF tuple images,
finite VF-tuple coding, closed-ball centers, definable points in balls, finite
value-fibre sets, bounded-family constancy, RV-fibre exceptions, and additive-coset
exceptions. Descent3.1 now handles every finite mixed VF/RV/Gamma indexing tuple and
VF, RV and Gamma outputs over arbitrary small real/Gamma ambient bases. Both
fibre cases of3.2 have all three output sorts over those same bases. Full
proper code preimages retain exactly the original parameters; both real and
Gamma parts of the ambient base have explicit cardinal bounds.
General same-base dcl transitivity,
monotonicity and idempotence are now proved, including the basic generated-base
laws. Full Gamma acl transitivity and the actual closure-base laws are now proved. The last published combined certificate covers
193 modules and 1040 actual headline type/axiom checks, plus a fresh root import.

After building dependencies, run `lake env python3 Section3/verify.py` for the
new library or `lake env python3 Archive/audit_section3.py` for the isolated
legacy compiler audit. Neither script pushes anything.

See [LEGACY.md](LEGACY.md) for reuse candidates and pitfalls, and
`../Archive/MOVE-INDEX.json` for the complete old-to-new path map.

Definition 2.4 is being formalized with the author's approved rational VF
factors and explicit domain guards; see [NORMAL-FORM-NOTE.md](NORMAL-FORM-NOTE.md).
The semantic proof of 3.17 is independent of that still-open syntactic theorem.

The coefficient-preserving geometry now lifts RV points algebraic over a VF
parameter set into any algebraically closed VF subfield containing that set,
even when that subfield's valuation is trivial. Full VF/RV modelhood in
3.14 is now proved: the actual acl carrier is an elementary submodel with
normalized sorted operations and the named base's atomic diagram. Genuine
VF-generated Gamma bases have the same real acl as their real part, and
every Gamma name is represented inside that model. The only additional
hypothesis is nontriviality of the actual value group of acl; no saturation
is needed. Finite/cofinite RV fibres, uniform finite-side bounds
and pure finite-threshold endpoint lemmas supply the exchange proof;
the full reverse-fibre argument in `RVExchange` now proves RV exchange
3.6, including genuine Gamma-named bases. The Gamma assertion
of 3.7 is now checked by the complete separation and finite-support argument
in `RVGammaAlgebraicity`. It permits arbitrary existing Gamma names and needs
only the real base to be small, under ACVF(0,0) and genuine saturation.


The dcl of pure VF and arbitrary Gamma generators introduces no new real
algebraic elements beyond the real generators: for VF this holds in all
ACVF, and for RV it uses the standing ACVF(0,0)/saturation/small-real-generator
hypotheses. RV elements in that acl lift into the relative VF algebraic
closure of the pure VF generators. These are checked prerequisites for the
remaining general ball-center theorem. The same-radius closed hull of an
open disc is also proved intrinsic, using actual VF boundary points.


Corollary 3.4 now also covers genuine Gamma-named bases: the VF dcl and acl
fields are characterized by their actual same-base predicates and have the
same transcendence degree as the generated VF field. The standing VF-field
base convention is retained; no saturation or cardinal bound is needed.
Proper open balls now have their actual quotient and intrinsic closed-hull
map. Full definable-family hull preservation and mixed-ball centers are now checked.


Finite Gamma algebraic sets now have each element individually definable over
the original real/Gamma base, so acl and dcl agree in Gamma. The proof retains
entire value fibres. The intrinsic open-to-closed hull map also preserves full
family definability over that same base, for arbitrary families. These results
need only ACVF; the full ball-center theorem is checked in GeneralBallCenters.


Lemma 3.13 is now checked in `GeneralBallCenters.lean` for actual mixed
families of closed and proper-open balls, including singletons and the whole
field. One function has both complete code graphs over the original Gamma
base. The proof uses `OpenBallCenters` to obtain algebraic points, a finite
real-base cover and a common mean. Genuine saturation, small B.real and
(VF,Gamma)-generation are explicit. Both remaining branches of 3.18(2) are checked in GeneralCosetChoice.
Gamma acl transitivity is now checked in GammaAlgebraicClosure. The guarded
rational normal form in Definition 2.4 is the only remaining proof target.


`GeneralCosetChoice.lean` completes Lemma 3.18(2). The exceptional cosets are
represented by a finite family of actual balls, with both full code preimages
defined over the original base. Closed centers come from 3.10; generated-base
centers come from full 3.13. Substituting each exceptional center's profile
and using constancy on the other cosets gives the full quotient graph and
realization property. The closed case needs no saturation; the generated
case retains 3.13's precise saturation and real-base size hypotheses.


`GammaFullDescent.lean` completes the remaining parameter and sort scopes of
3.1/3.2. Ordered Gamma acl=dcl, full output-class closure and a partial
least-value relation provide finite actual-Gamma rows. The compactness cover
and universal intersection retain the original base. Mixed Gamma indexing
uses the entire nonzero RV preimage and eliminates each decoded name from
all of its representatives. These results need no characteristic assumption;
genuine saturation, a countable lower bound, both base size bounds and
nonemptiness are explicit.


`GammaAlgebraicClosure.lean` proves transitivity in both real and Gamma
outputs over arbitrary real/Gamma algebraic parameter sets. Finite original
real support and a same-base finite algebraic tuple cover feed the checked
finite-row image construction. It proves extensivity, monotonicity,
idempotence and dcl(acl(B))=acl(B), with no saturation, cardinality or
characteristic assumptions. The active Section 3 targets are now closed;
Remark 3.19 is retracted. The remaining Section 2 target is the agreed guarded
rational normal form of Definition 2.4.
