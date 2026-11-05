# Current proof status

Work is in progress. **All of Section 3 is not yet formalized.** The new
`Library.lean` entry point deliberately excludes the legacy target files.
QE is imported from the unchanged ACVF-QE pin.

The current combined certificate covers 102 modules, 198 headline type/axiom
checks and a fresh root import. Every checked source and dependency fingerprint
matches the tree; only the three permitted standard axioms occur.
The pinned compiler and dependencies are unchanged.

## Checked components

| Component | Exact scope and remaining work |
| --- | --- |
| `Parameters`, `ParameterBridge`, `ClosureBridge` | Definability, algebraicity and dcl over arbitrary base sets, finite character, and sorted/raw unary bridges on canonical models. `CanonicalParameters` proves invariance of sorted definability and closure under normalization. `SortedTuples` supplies the full finite mixed-tuple bridge and elimination of sorted definable parameters. Gamma closure remains open. |
| `ModelContext` | ACVF(0,0), actual small substructure, nontrivial finite values, genuine cardinal saturation and strong homogeneity; ambient model of the named-base atomic-diagram theory. Finite parameter extensions remain small. See `ClosureConventions` for definable closure and VF/RV generation. Gamma generation remains open. |
| `Compactness`, `DefinableCompactness`, `TupleCompactness` | Finite inconsistency and finite subcovers from genuine saturation, with arbitrary finite tuple arities and visible parameter cardinal bounds. |
| `Counting`, `RawAlgebraicity`, `FiniteRelations`, `TuplePromotion`, `TupleRelations`, `TupleDescent` | First-order bounded-fibre counting, cardinality equivalence, promotion over all coordinates of a tuple, and the complete raw-language descent proof. |
| `SortedDescent.lemma_3_1` | Descent for every finite mixed tuple arity and a nonempty definable family over the original arbitrary small base. Any ACVF model, genuine κ-saturation, κ at least countable, and base size below κ. Normalization and its saturation transfer are proved internally; no canonical-totalization premise. |
| `FibreDescent.corollary_3_2_vf` | VF-to-RV half, with tuples, nonempty domain and original parameters. Any ACVF model, genuine small-parameter saturation, countable lower bound on κ and the stated base bound; canonical representation is internal. The RV-to-Gamma half is open. |
| `AlgebraicFinite` | A definable subset of the raw algebraic closure of a small base is finite, proved via genuine saturation. |
| `RingSyntax`, `PolynomialRoots`, `RootDefinability`, `FieldBase` | Polynomial root sets are sorted-definable over their named coefficients and finite for a nonzero polynomial. Over a base whose VF part is a field, VF model-theoretic and field-theoretic algebraicity agree. The standing field convention is explicit; inverse closure constructs it from an LRV substructure. |
| `SortedFiniteImage.corollary_3_5_sorted` | Full finite input/output arities and partial domains: every sorted-definable RV-to-VF function has finite image. Any ACVF model and any original small base, with genuine saturation. The full original-base graph is a premise. `FiniteImage` also proves finite-valued tuple-relation images on canonical models. No C-minimality or field-base premise. |
| `QuantifierFree`, `RVLiteralReduction`, `RVNormalForm` | Completed QE used over the original arbitrary base. VF equalities are replaced by RV equalities and sort predicates discharged on sorted assignments. K-term/monomial normalization and the full specific RV-literal DNF of Definition 2.4 remain. |
| `BallGeometry` | Extended radii with the reversed order, whole-field and singleton conventions, polydiscs, rv-fibres and degeneracy; the exact nonzero rv-fibre/open-ball bridge. See `DiscCentres` for the RV-fibre classification. `ValuativeCentre`, `TupleValuation` and `MixedRV` supply valuative centers, coordinate minima in the reversed order, and mixed-tuple rv/fibre notation, including empty and degenerate cases. |
| `Coordinates` | Sorted mixed coordinates, restriction/projection, complementary-coordinate fibres, assembly and projection composition (Notation 2.10). |
| `Average.lemma_3_8` | Both valuation and RV-nonconstancy conclusions. Explicit hypotheses: ACVF(0,0), distinct family, size at least two, common valuation and zero sum. The natural-number unit premise is proved from residue-characteristic-zero axioms. No extra mathematical hypothesis. |
| `FiniteCoding.lemma_3_9` | Full finite VF tuple arities: a finite sorted-definable A has an injection into some RV^m with its complete sorted graph definable over the original arbitrary S. Only ACVF(0,0), finiteness and the stated definability are required; no saturation, canonical representation, field-base convention or extra named elements. The proof uses uniform finite-family means and recursive RV splitting, then codes every VF coordinate. |
| `ClosedBallCodes.lemma_3_10` | Every finite original-S-definable set of actual closed-ball imaginaries has a center function, with its complete graph sorted-definable over the same S. The quotient identifies real VF codes exactly when their underlying balls agree; a checked coverage theorem codes every closed ball, including singletons and the whole field. Only ACVF(0,0), finiteness and the full original-base family preimage are required. No saturation, canonical representation, field-base convention, chosen representatives or assumed center theorem. Nested families are included. |
| `BallDefinablePoint.lemma_3_11` | If a ball contains a nonempty proper S-definable subset, it contains a point in the actual sorted definable closure of the original S. The ball itself need not be S-definable. Every ACVF(0,0) model and arbitrary base S; no saturation, canonical representation, field-base convention, positive-component decomposition or assumed center theorem. The intended nonempty condition is explicit: allowing the empty subset would make the printed shorthand false. |
| `RVFibreConstancy.corollary_3_12` | A function on the full RV preimage of B, with any finite RV output arity and its complete original-S sorted graph, is nonconstant on only finitely many RV fibres. Strengthened to every ACVF model, with no characteristic-zero or saturation premise. One finite original-base root set controls all RV output tuples simultaneously; exceptional fibres belong to its finite RV image. |
| `VFAlgebraicity.lemma_3_3` | All VF and RV parameter tuple arities and the original arbitrary base. Model-theoretic VF algebraicity implies algebraicity over the field generated by the base's VF elements and the VF tuple. RV parameters do not enlarge it. Assumes only ACVF; no added saturation, characteristic, C-minimality or local-stability premise. Proved through `PolynomialSyntax`, `PolynomialLocal`, `RVTermLocal`, `QFLocal`, `ValuedNeighbourhood` and `VFAclField`. |
| `QuotientFamilies.notation_3_16` | Invariance and saturation characterize unique quotient-to-powerset descent. Definability remains over the same base; surjective projection is equivalent to nonempty values. No arbitrary representatives are named. |
| `CMinimal.theorem_2_8_c_minimal` | The exact frozen `IsCMinimalWS` target of Theorem 2.8, for every ACVF model, every parameter type and every sorted assignment. Only ACVF is assumed; no characteristic, saturation, canonical-totalization or interpretability premise is added. `ValuedDefinability`, `RVRepresentatives`, `LiftTerms`, `RepresentativeDefinability`, `QFInterpretation`, `BooleanCombinations` and `GeometryBridge` prove the full translation and ball conversion, using the checked ordinary valued-language result in `ValuedCMinimal`. The inherited placeholder is not used. |
| `DefinableConstants`, `VFDefinableClosure` | VF definable closure is a field and VF model-theoretic algebraicity is equivalent to algebraicity over the field generated by the original VF parameters, in every ACVF model and over every base. `SortedFunctionClosure`, `SortedInverseClosure` and `SortedParameterElimination` remove the canonical-model restriction. Generated fields are not identified with definable closure. |
| `TranscendenceDegrees.corollary_3_4` | All three actual VF fields have the same transcendence degree over VF(S), for every finite VF tuple and arbitrary RV parameter set B. Only ACVF and the standing VF-field base convention are required; no canonical-model, saturation, characteristic or cardinal bound on B. |
| `VFExchange.lemma_3_6_vf` | VF exchange over the original standing VF-field base, in every ACVF model. Derived from the proved closure identification and Mathlib algebraic matroid exchange. The RV assertion remains open. |
| `ClosureConventions` | Definable closure is monotone and idempotent, and adjoining it preserves sorted acl, in every ACVF model. A genuine raw LRV substructure is constructed on canonical models. VF-generated and (VF,RV)-generated bases use definable closure. Gamma generation remains open. |
| `RVIndependence.corollary_3_7_vf` | VF half, strengthened to arbitrary original bases S and arbitrary RV parameter sets. Adjoining RV parameters does not change VF algebraicity. Only ACVF is needed; no field-base convention, canonical representation or saturation is assumed. The Gamma assertion remains open. |
| `DiscCentres` | Every open or closed disc avoiding zero lies in one RV fibre, including the singleton-radius convention. This supplies the geometric classification behind the checked valuative-center formulas. |

Additional checked tools:

- `DefinableReduct`, `NormalizationReduct`, `NormalizationSaturation`: actual
  first-order interpretation of every normalized symbol and formula, including
  universal quantifiers, and genuine saturation transfer over the same small base.
- `FibrePromotion`, `FiniteGluing`, `DefinableLocalChoice`: exact fibre
  promotion and parameter-preserving finite gluing; pointwise choices in dcl
  give a partial function with its complete graph definable over the original
  small base. These are tools, not a proof of the paper's center theorems.
- `ValuativeCentre`: Definition 2.6, with infinity represented by multiplicative
  valuation zero in the reversed order; explicit open/closed ball formulas.
- `AlgebraicTransitivity`: transitivity of sorted algebraic closure over
  arbitrary sets, with no saturation or canonical-model premise, using finite
  parameter witnesses and finite products of finite algebraic sets.

- `AlgebraicClosure`: monotonicity and idempotence of the actual sorted acl,
  acl-parameter elimination, dcl(acl(S)) = acl(S), and a raw algebraic-closure
  substructure on canonical models. Modelhood in Corollary 3.14 remains open.
- `Barycentre`, `FiniteBarycentricCode`, `FibreEnumerations`,
  `BarycentreSyntax`, `FiniteFibreMeans`, `DefinableMeans` and
  `RawBarycentricCode`: complete enumeration formulas, original-base definable
  means of uniformly bounded finite families, strictly smaller centered RV
  fibres, and a uniformly definable recursive finite code. The size bound used
  in 3.9 is proved from the cardinality of A.
- `CanonicalContext`: normalization preserves ACVF(0,0) and the carrier of
  every original substructure. The selected bridge type audits print structure
  arguments explicitly, distinguishing original and normalized interpretations.
- `ValueQuotient`: the actual RV quotient by mutual value inequalities, its
  unique infinity class, nonzero representatives, and agreement with equality
  of values under a compatible valuation. Ordered-group operations and the
  full imaginary-parameter/generation interface remain open.

- `PolynomialSupport`, `PolynomialObstacles`, `RootFreeConstancy`:
  a finite list of occurring unary VF polynomials controls a quantifier-free
  formula. Their finite root set plus zero is definable over the original S;
  membership is constant on every open ball missing it. Polynomial RV constancy
  on open and closed balls follows from factorization and `BallTranslation`.
- `SortedBoolean`: explicit normalized-raw/sorted bridges in all tuple arities,
  and same-base finite unions. Original and normalized structure arguments
  are printed in the selected type audits.
- `MinimalBallFamilies`, `ClosedBallRoots`, `ClosedBallCentres`, `MeanInBalls`:
  minimal families are definable without listing their infinitely many real
  codes; only distinct ball values are finite. A root-free open enlargement
  and the checked Johnson finite-cover theorem force a finite definable
  hitting set. Means give uniform centers, and `ClosedBallChoice` transfers
  the complete graph to every original model before quotient descent.

- `NearestRoots`, `NearestRootDefinability`, `BallDefinablePoint`: roots
  nearest to a member of A form a finite nonempty set definable over exactly
  S. This set lies inside every containing ball that meets the root set;
  its mean gives the definable point. A single finite root set controls open
  and closed balls, and nonempty proper containment forces an intersection.
- `EncodedBallGeometry`: the frozen open, closed, singleton and whole-field
  predicates survive normalization and agree with the compatible valuation's
  disc predicates. Field operations of two models are not equated by assertion.
- `MixedPolynomialSyntax`, `MixedPolynomialSupport`, `MixedRootFree`:
  for one VF coordinate and arbitrary finite RV coordinates, the occurring
  VF polynomials are independent of the RV tuple. Their finite root set and
  its definability remain over the original S, uniformly for every RV tuple.

Results 3.13–3.15 and 3.17–3.19, the RV half of 3.6, and the Gamma halves of 3.2 and 3.7 remain open in
the new shared library. Legacy conditional reductions are not counted as proofs.
Keep `TARGETS.md` as the full target checklist.

## Verification

`lake env python3 Section3/verify.py` checks the new modules, actual headline
types, allowed axioms and root import. Generated logs are in
`.scratch/section3-verified/`. A verification run is complete only when its
`status.txt` says `PASS`; partial results do not certify the current tree.
The checked batch record is copied into `verification/` after it is stable.
A subsequent source change requires a fresh matching verification record.

The legacy audit compiled 24 top-level Section 3 snapshots plus nine local
dependencies in isolation, all with exit 0. `Sec3_frozen` has four local
placeholders and `Sec3_sat` has eight. The three older scaffold files have
not been compiler-audited in that run; their two-point RV0/stub interfaces
are unsuitable for reuse. Explicit hypotheses in the other snapshots remain
load-bearing. This audit is not an axiom audit of every legacy theorem.

Local verification uses WSL Lean 4.33.1 and the matching pinned Mathlib cache,
plus unchanged source-matching ACVF-QE verification artifacts. The earlier
temporary installation disappeared after WSL stopped; the exact compiler was
restored in the standard persistent toolchain directory. The exact pinned
Mathlib source and all 8,690 compiled cache artifacts were restored in a
persistent Linux dependency cache, linked from the workspace.
No dependency revision was changed; no push was made.
