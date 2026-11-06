# Current proof status

Work is in progress. **All of Section 3 is not yet formalized.** The new
`Library.lean` entry point deliberately excludes the legacy target files.
QE is imported from the unchanged ACVF-QE pin.

The last published combined certificate covers **192 modules, 1021 headline type/axiom
checks and a fresh root import**. The certificate records source and dependency fingerprints at that checkpoint; only the three permitted standard axioms occur.
The pinned compiler and dependencies are unchanged. QE uses the released
language with named RV inversion.

Unless a row explicitly uses `GammaParameters.Base`, its parameter set `S : Set M`
contains real VF/RV parameters only. Such a result does not automatically cover
a base with named Gamma imaginaries. The new interface and bridges distinguish
those scopes. General Gamma-base dcl transitivity, monotonicity, idempotence and basic generated-base laws are now checked; Gamma acl transitivity remains a separate obligation.

## Checked components

| Component | Exact scope and remaining work |
| --- | --- |
| `GammaPresentation`, `GammaOperations`, `GammaValueLaws`, `GammaDensity` | The actual Gamma quotient has a nontrivial divisible densely ordered commutative group structure; GammaTop has the one absorbing infinity class, maximal in the paper order. Operations and comparisons agree with the released RV multiplication and preorder. VF valuation is a multiplicative map into GammaTop and reverses the compatible Mathlib valuation order. All ACVF; no characteristic, saturation or extra representative parameters. No zero-minimal ordered-group-with-zero instance is introduced. |
| `GammaCodes`, `GammaParameters`, `GammaParameterBridge`, `GammaSpecialization` | Genuine imaginary parameters via full, globally invariant first-order preimages on all nonzero RV representatives, over exactly the real base S. The semantic relation constructor and empty-Gamma equivalences for definability, acl and dcl have checked types. Specialization explicitly adjoins RV names; it is not their elimination. Arbitrary Gamma sets are handled through finite formula support. Their general dcl and basic generation laws are now proved in `GammaClosureLaws` and `GeneratedBaseLifting`; full Gamma acl closure laws remain separate. |
| `GammaCodeDefinability`, `GammaFamilyIntersection`, `GammaDescent` | The full nonzero-RV code equivalence is first-order definable and normalization-compatible. Algebraicity of a real VF/RV output descends along any nonempty finite-arity Gamma-definable real family over a small real ambient S. This includes the RV-to-Gamma-fibre case of 3.2 for real outputs. The resulting finite witness has a full invariant preimage over exactly S and its given Gamma tuple; temporary representatives are removed from that conclusion. Genuine kappa-saturation, kappa at least countable, and a small real S. GammaFullDescent now extends this to arbitrary small real/Gamma ambient bases, all output sorts and mixed Gamma indexing tuples. |
| `GammaProjection`, `GammaFiniteMeans`, `NearestPairs`, `GammaNearestRoots`, `GammaBallDefinablePoint` | Full 3.11 over genuine Gamma-named bases: a nonempty proper definable subset of a ball gives a point in the same-base definable closure. The containing ball is not named. Finite real-base covers and nearest-root means preserve full code invariance. ACVF(0,0), with no saturation or extra named point. Original and normalized interpretations are distinguished explicitly. |
| `GammaValueFibreCounting`, `GammaFiniteValues` | Full 3.15 over genuine Gamma-named bases. The actual Gamma values with nonempty finite RV fibre form a finite set whose entire RV preimage is definable over that same base. First-order counting preserves the original support; the uniform natural-number bound is proved after specialization and adds no parameter or premise. ACVF(0,0), no saturation. |
| `RVOperations`, `PolynomialRVMonomial`, `RVSmallPowers`, `SmallFamilyConstancy` | Full 3.17 over real or genuine Gamma-named bases, for all finite RV output arities and the complete graph on the punctured VF domain. Actual Gamma bounds give a Gamma threshold, and every larger threshold gives constancy. The proof handles absorbing-zero coordinates by bounding only nonzero coordinates. It works in every ACVF model, with no saturation, characteristic-zero, field-base or syntactic-normal-form premise. Semantic term homogeneity treats residue zero/junk branches explicitly. RV receives a group-with-zero structure, without a linear order; estimates use the reversed actual value group. Definition 2.4 remains separate. |
| `GammaBaseTools` | Same-base finite Boolean operations, sorted complements, real-coordinate preimages, arbitrary tuple-output parameter promotion, and universal restoration of Gamma-support invariance. Common real representative names are used only for compactness preparation, with their actual cardinal bounds. These tools alone do not prove ambient-Gamma-base descent; the real-output extension is now checked in `GammaBaseDescent`. General dcl idempotence and basic generation laws are now checked in `GammaClosureLaws` and `GeneratedBaseLifting`. |
| `AlgebraicBaseGeometry` | Valued QE preserves an algebraically closed coefficient field: the resulting finite Boolean combination has both centers and radii in that field's image. Only the ambient valuation must be nontrivial. The RV-lifting bridge is checked in `AlgebraicRVLifting`; full VF/RV modelhood in 3.14 is now checked in `AclModel` and `GammaAclModel`. |
| `RVFibreGeometry` | Definable subsets of each actual RV value fibre are finite or cofinite, with real or Gamma-named bases. Genuine saturation gives a uniform bound on finite sides of definable row pairs. Pure order lemmas give finite image from uniform cut bounds and a canonical endpoint for nonempty proper sets determined by finitely many thresholds. These prerequisites now feed the checked Gamma separation and RV exchange proofs below. |
| `AlgebraicRVLifting` | In ACVF(0,0), an RV element algebraic over a VF parameter set S has a VF representative in any algebraically closed VF subfield containing S. The subfield valuation may be trivial. Valued-language QE, C-minimality and the full RV interpretation preserve precisely that coefficient subfield. Separately, an algebraically closed valued subfield with nontrivial restricted valuation embeds elementarily in the ambient valued field. These results now feed the checked full LRV acl modelhood proof in `AclModel`. |
| `GammaBaseDescent` | Full 3.1 for real VF/RV outputs and nonempty finite real-tuple families over a genuine Gamma-named ambient B. Both B.real and B.gamma are small, with genuine kappa-saturation. Finite row cuts, a uniform finite cover and universal intersection retain the full invariant defining relation over exactly B. GammaFullDescent now supplies Gamma outputs, arbitrary mixed Gamma indexing tuples and all four fibre corollaries. General dcl and basic generation laws are checked below. |
| `GammaFullDescent` | Full Lemma 3.1 for arbitrary finite mixed VF/RV/Gamma indexing tuples, all three output sorts, and an arbitrary small real/Gamma ambient base; both fibre cases of 3.2 likewise cover real and Gamma outputs over that base. Families have their full proper code preimages over exactly B, and temporary representatives are removed. Scope: all ACVF, genuine kappa-saturation, kappa at least countable, both B.real and B.gamma small, and nonempty indexing family. Gamma acl=dcl, real-parameter promotion, output value-class closure and a partial least-value relation yield globally finite actual-Gamma rows. No arbitrary minimum-existence, representative section, extra names, characteristic or new reference premise. |
| `GammaThresholdGeometry` | Every actual Gamma-definable unary set, over real or Gamma-named bases, is determined by finitely many actual Gamma thresholds. C-minimal VF ball geometry and angular infinitude supply the thresholds; no completeness or o-minimality premise is assumed. A nonempty proper set has an intrinsic unique endpoint. ACVF(0,0), no saturation. |
| `GammaRVSeparation` | A uniform first-order family indexed by actual Gamma, with finite RV rows, has finite union. The full guarded graph on every proper RV code is required. Intrinsic endpoints have first-order order cuts over exactly the original real base; genuine saturation gives uniform finite-side bounds, and checked 3.15 completes finiteness. ACVF(0,0), kappa at least countable, and small real base. This is proved separation, not an assumed stability/orthogonality interface. |
| `RVGammaAlgebraicity` | Full Gamma assertion of 3.7: adjoining Gamma names does not enlarge RV algebraic closure, including with arbitrary existing Gamma names. More strongly, RV algebraicity over B is equivalent to RV algebraicity over B.real. Actual Gamma tuple projection and globally finite row cuts remove each witness's finite Gamma support. ACVF(0,0), genuine kappa-saturation, kappa at least countable and small B.real; no cardinal bound on B.gamma, VF-field-base, homogeneity or canonical-model premise. RV exchange is now checked in `RVExchange`. |
| `RVExchange` | Full RV exchange 3.6 over arbitrary small real bases and genuine Gamma-named bases. A finite forward relation is constructed from the algebraic witness. Finite/cofinite angular traces, genuine saturation and first-order counting define a finite bad-output set over the original base plus one Gamma value; checked 3.7 removes that Gamma name. Every reverse value fibre is finite, and 3.15 gives the full finite reverse relation. ACVF(0,0), genuine kappa-saturation, kappa at least countable and small B.real; no bound on B.gamma, VF-field-base, homogeneity, canonical-model or assumed exchange/stability premise. |
| `AclFieldImages`, `AlgebraicSubfieldModel`, `AclModelGeometry`, `AclModel` | Full Corollary 3.14 for a VF-generated real base: its entire VF/RV acl, with internally normalized operations and the actual inclusion of the named base, models ACVF_S(0,0). The acl carrier and all correctly sorted operations are those of the original model. Nontriviality means two actual nonzero RV values in acl with distinct Gamma images. Algebraic closedness, the RV image, the actual Tarski-Vaught witness property, full LRV elementarity and the named atomic diagram are proved. ACVF(0,0), no saturation, cardinal bound, canonical-model or modelhood premise. |
| `GammaClosureElimination`, `GammaAclModel` | Full invariant-fibre elimination for real definable names and definable Gamma names. For a genuine VF-generated Gamma base B, real definable sets and real acl agree with those over B.real; no saturation or representatives are added. Corollary 3.14 gives a full VF/RV model with exactly that actual acl carrier, and every original Gamma name has a nonzero RV representative inside it. Real atomic-diagram naming is supplied by `corollary_3_14` in `AclModel`. General dcl and basic generation laws are now checked below; full Gamma acl transitivity remains separate; the remaining descent extensions are checked in GammaFullDescent. |
| `GammaClosureLaws` | General parameter elimination over genuine real/Gamma bases: replace real names by their same-base singletons and Gamma names by their entire same-base value fibres, retaining finite supports and full invariance. This proves dcl extensivity, monotonicity, idempotence, equality of definable sets after adjoining dcl, and preservation of real/Gamma algebraicity after adjoining dcl. ACVF only; no characteristic, saturation, cardinality, representative-section or closure-law premise. Full algebraic-closure transitivity over arbitrary real/Gamma algebraic names remains separate. |
| `GeneratedBaseLifting` | VF-generated and (VF,Gamma)-generated bases are dcl-closed, and VF generation implies (VF,Gamma) generation. VF acl over the dcl of generators equals VF acl over the real generators in all ACVF. Under ACVF(0,0), genuine kappa-saturation, kappa at least countable and small real generators, RV acl likewise equals RV acl over the real generators; pure VF generators therefore give lifts into their relative VF algebraic closure. No bound on the Gamma generator set, no size bound on its whole dcl and no nontrivial coefficient-valuation premise. These prerequisites now feed the full Lemma 3.13 in GeneralBallCenters. |
| `OpenBallHullGeometry` | For strict valued-field discs with actual nonzero VF radii, containment compares the radius values, equality identifies those values, and equal open discs have equal same-radius closed hulls. The proof uses actual boundary points and works over any field and multiplicative valuation. No algebraic-closedness, density, completeness, saturation or characteristic hypothesis. The actual mixed ball-code family and full center construction are now checked in GeneralBallCenters. |
| `GammaDefinableClosureField` | Full Gamma-base Corollary 3.4. The actual VF parts of dcl and acl over a real/Gamma base are proved to be fields; their membership predicates are the original same-base closure predicates. Primitive functions and VF inverse preserve same-base dcl by the checked imaginary-parameter elimination. For every finite VF tuple and arbitrary additional RV parameter set, the generated VF field, the actual VF dcl field and the actual VF acl field have the same transcendence degree over VF(S). ACVF only, with the paper's explicit VF-field base convention; no characteristic, saturation, cardinal bound, canonical-model or field-closure premise. |
| `OpenBallCodes` | Proper open discs have a well-sorted membership formula, exact ordinary-valuation semantics, an actual ball quotient and its full real-code family preimage. Passing to the same-radius closed hull is well defined on that quotient and contains the original open disc. Nonzero actual VF radius is explicit; singleton/whole-field cases remain covered by closed-ball codes. All ACVF, with no saturation or characteristic premise. Preservation of full family definability by the hull map is now checked in OpenBallFamilyHulls; the full center theorem 3.13 is now checked in GeneralBallCenters. |
| `GammaFiniteOrder` | Algebraic and definable closure agree on the actual Gamma imaginary over every genuine real/Gamma base. Minimum selection and finite minimum-erasure use the linear order, and all definability statements retain the full nonzero RV preimage; no RV representative singleton is selected. ACVF only, with no saturation, cardinality, characteristic or choice-function premise. This is an ordered-sort closure result, not full arbitrary-base acl transitivity. |
| `OpenBallFamilyHulls` | The complete parameter-free graph of the intrinsic closed-hull map includes every equivalent closed-ball code. It proves that the full closed-code preimage of the hull image of any definable proper open-ball family is definable over the same real/Gamma base. No family finiteness, saturation or characteristic assumption is needed. Centers inside open balls are checked in OpenBallCenters; GeneralBallCenters proves the full mixed-family 3.13. |
| `GammaRealMap` | Pullback along a globally normalized-real-definable tuple map preserves full Gamma-support invariance and definability over the original base. The input sort guard is explicit. This helper does not assert definability of original off-sort function totalizations in the normalized model. |
| `OpenBallCenters` | Full proper-open-ball case of 3.13 on the actual open-ball quotient, with its complete original-base code graph. Closed-hull centers give finite definable VF center and RV offset images; the exact boundary-fibre identity and generated-base RV lifting give an algebraic VF point in each open ball. A finite cover over the real base supplies one hitting set, and means give code-independent centers. Main scope: ACVF(0,0), genuine kappa-saturation, kappa at least countable, small real part of B, and actual (VF,Gamma)-generation. No cardinal bound on the Gamma generator set, no nontrivial coefficient-valuation premise and no assumed center or algebraic-point theorem. The full mixed closed/open/singleton/whole-field theorem is checked in GeneralBallCenters. |
| `GeneralBallCenters` | Full Lemma 3.13 on the actual quotient of closed and proper-open ball charts by equality of their point sets, including equality across charts. Closed radius zero and whole-field codes supply all degeneracies; explicit ordinary-valuation coverage is checked. Every finite original-B-definable ball family has one center function with both complete real-code graphs definable over exactly B. A common finite real-base hitting set and its mean make the choice independent of the chart. Scope: ACVF(0,0), genuine kappa-saturation, kappa at least countable, small B.real and actual (VF,Gamma)-generation. No Gamma-generator cardinal bound, coefficient-valuation nontriviality, assumed center/choice theorem or field-instance equality. |
| `GeneralCosetChoice` | Full Lemma 3.18(2): the actual additive quotient has a selected powerset-valued profile with its complete graph definable over exactly the original real/Gamma base, and every selected value is realized in its coset. All finite RV output arities. The closed-ball alternative assumes only ACVF(0,0), closedness, subgroup and profile definability; no saturation. The (VF,Gamma)-generated alternative uses genuine kappa-saturation, kappa at least countable, small B.real and actual generation, with no Gamma-generator cardinal bound. The finite actual exceptional ball family is defined by equality of entire point sets in both charts; checked 3.10/3.13 construct its centers. No center/choice oracle, extra representatives, field-base convention or new accepted input. |
| `GammaCounting`, `GammaGoodRelations`, `GammaUniformCover`, `GammaOutputDescent` | Actual Gamma-output descent for 3.1 and both fibre cases of 3.2, over a small real ambient S. Together with the real-output results this covers all three output sorts in that scope. First-order counting is of pairwise value-inequivalent codes; the finite witness is a finite set of actual Gamma values, whose entire RV preimage is invariant and definable. Promotion is repaired by universal value-class closure before globally cutting the finite rows. Genuine saturation, kappa at least countable, small real S and nonempty indexing family are explicit. GammaFullDescent now covers arbitrary small ambient Gamma bases. |
| `GammaSupport` | Finite Gamma-support joining/reparameterization, same-base intersections, properness and monotonicity for real/Gamma algebraicity. The defining relations retain full code invariance and original real parameters. These calculus tools now feed the checked general dcl idempotence and generated-base laws below; full Gamma acl transitivity remains separate. |
| `FiniteAlgebraicCover`, `FiniteVFRealCover`, `GammaRealRestriction`, `GammaFiniteCoding` | A finite VF tuple set defined with additional RV or Gamma parameters is covered by a finite real-S-definable tuple set. Restricting the checked real-base code on that cover proves full 3.9 over genuine Gamma-named bases, with all VF tuple arities and its complete same-base graph. ACVF(0,0); no saturation or additional named elements. |
| `ClosedCentersFromFiniteSet`, `ClosedBallCenterCover`, `GammaClosedBallCenters` | Full 3.10 over genuine Gamma-named bases on the actual closed-ball quotient, including singleton and whole-field cases. A finite real-S-definable hitting set is constructed by covering the algebraic center image; means define an invariant total function on real codes, whose graph is restricted to the original Gamma-base family. ACVF(0,0), finiteness and full family preimage; no saturation, chosen representative parameters or assumed center theorem. Proper open-ball families are now handled in OpenBallCenters; GeneralBallCenters proves the full mixed-family form of 3.13. |
| `GammaBaseVFAlgebraicity` | Named Gamma parameters do not enlarge VF algebraic closure. Full Gamma-base versions of 3.3, VF exchange 3.6, and VF nonalgebraicity-transfer 3.7 (arbitrary additional RV and Gamma sets). Only ACVF; exchange retains its standing VF-field base convention. |
| `GammaBaseCMinimal`, `GammaBaseFiniteImage`, `GammaBaseFiniteExceptions` | C-minimality, finite RV-to-VF tuple images 3.5, finite RV-fibre exceptions 3.12, additive-subgroup ball classification and finite exceptional additive cosets 3.18(1), with genuine Gamma names in the base. Every theorem retains its real counterpart's characteristic and saturation scope; 3.5 assumes genuine kappa-saturation, kappa at least countable, and a small real base. No cardinal bound on the set of Gamma names is needed for these finite-support consequences. |
| `Parameters`, `ParameterBridge`, `ClosureBridge` | Definability, algebraicity and dcl over arbitrary base sets, finite character, and sorted/raw unary bridges on canonical models. `CanonicalParameters` proves invariance of sorted definability and closure under normalization. `SortedTuples` supplies the full finite mixed-tuple bridge and elimination of sorted definable parameters. General Gamma-base dcl laws are now checked in GammaClosureLaws; full Gamma acl closure laws remain separate. |
| `ModelContext` | ACVF(0,0), actual small substructure, nontrivial finite values, genuine cardinal saturation and strong homogeneity; ambient model of the named-base atomic-diagram theory. Finite parameter extensions remain small. See `ClosureConventions` for definable closure and VF/RV generation. General Gamma-base dcl and basic generation laws are now checked in `GammaClosureLaws` and `GeneratedBaseLifting`. |
| `Compactness`, `DefinableCompactness`, `TupleCompactness` | Finite inconsistency and finite subcovers from genuine saturation, with arbitrary finite tuple arities and visible parameter cardinal bounds. |
| `Counting`, `RawAlgebraicity`, `FiniteRelations`, `TuplePromotion`, `TupleRelations`, `TupleDescent` | First-order bounded-fibre counting, cardinality equivalence, promotion over all coordinates of a tuple, and the complete raw-language descent proof. |
| `SortedDescent.lemma_3_1` | Descent for every finite mixed tuple arity and a nonempty definable family over the original arbitrary small base. Any ACVF model, genuine κ-saturation, κ at least countable, and base size below κ. Normalization and its saturation transfer are proved internally; no canonical-totalization premise. |
| `FibreDescent.corollary_3_2_vf` | VF-to-RV half, with tuples, nonempty domain and original parameters. Any ACVF model, genuine small-parameter saturation, countable lower bound on κ and the stated base bound; canonical representation is internal. The RV-to-Gamma-fibre case for real outputs is checked in `GammaDescent`; Gamma outputs over real ambient S are checked in `GammaOutputDescent`; GammaFullDescent now covers full small imaginary ambient bases and all output sorts. |
| `AlgebraicFinite` | A definable subset of the raw algebraic closure of a small base is finite, proved via genuine saturation. |
| `RingSyntax`, `PolynomialRoots`, `RootDefinability`, `FieldBase` | Polynomial root sets are sorted-definable over their named coefficients and finite for a nonzero polynomial. Over a base whose VF part is a field, VF model-theoretic and field-theoretic algebraicity agree. The standing field convention is explicit; inverse closure constructs it from an LRV substructure. |
| `SortedFiniteImage.corollary_3_5_sorted` | Full finite input/output arities and partial domains: every sorted-definable RV-to-VF function has finite image. Any ACVF model and any original small base, with genuine saturation. The full original-base graph is a premise. `FiniteImage` also proves finite-valued tuple-relation images on canonical models. No C-minimality or field-base premise. |
| `QuantifierFree`, `RVLiteralReduction`, `RVNormalForm` | Completed QE used over the original arbitrary base. VF equalities are replaced by RV equalities and sort predicates discharged on sorted assignments. K-term/monomial normalization and the RV-literal DNF remain. The author approved rational VF factors with explicit pole and residue-domain guards on November 5, 2026; see [NORMAL-FORM-NOTE.md](NORMAL-FORM-NOTE.md). This is an agreed target, not a checked normal-form theorem. |
| `BallGeometry` | Extended radii with the reversed order, whole-field and singleton conventions, polydiscs, rv-fibres and degeneracy; the exact nonzero rv-fibre/open-ball bridge. See `DiscCentres` for the RV-fibre classification. `ValuativeCentre`, `TupleValuation` and `MixedRV` supply valuative centers, coordinate minima in the reversed order, and mixed-tuple rv/fibre notation, including empty and degenerate cases. |
| `Coordinates` | Sorted mixed coordinates, restriction/projection, complementary-coordinate fibres, assembly and projection composition (Notation 2.10). |
| `Average.lemma_3_8` | Both valuation and RV-nonconstancy conclusions. Explicit hypotheses: ACVF(0,0), distinct family, size at least two, common valuation and zero sum. The natural-number unit premise is proved from residue-characteristic-zero axioms. No extra mathematical hypothesis. |
| `FiniteCoding.lemma_3_9` | Full finite VF tuple arities: a finite sorted-definable A has an injection into some RV^m with its complete sorted graph definable over the original arbitrary S. Only ACVF(0,0), finiteness and the stated definability are required; no saturation, canonical representation, field-base convention or extra named elements. The proof uses uniform finite-family means and recursive RV splitting, then codes every VF coordinate. |
| `ClosedBallCodes.lemma_3_10` | Every finite original-S-definable set of actual closed-ball imaginaries has a center function, with its complete graph sorted-definable over the same S. The quotient identifies real VF codes exactly when their underlying balls agree; a checked coverage theorem codes every closed ball, including singletons and the whole field. Only ACVF(0,0), finiteness and the full original-base family preimage are required. No saturation, canonical representation, field-base convention, chosen representatives or assumed center theorem. Nested families are included. |
| `BallDefinablePoint.lemma_3_11` | If a ball contains a nonempty proper S-definable subset, it contains a point in the actual sorted definable closure of the original S. The ball itself need not be S-definable. Every ACVF(0,0) model and arbitrary base S; no saturation, canonical representation, field-base convention, positive-component decomposition or assumed center theorem. The intended nonempty condition is explicit: allowing the empty subset would make the printed shorthand false. |
| `RVFibreConstancy.corollary_3_12` | A function on the full RV preimage of B, with any finite RV output arity and its complete original-S sorted graph, is nonconstant on only finitely many RV fibres. Strengthened to every ACVF model, with no characteristic-zero or saturation premise. One finite original-base root set controls all RV output tuples simultaneously; exceptional fibres belong to its finite RV image. |
| `FiniteValueDefinability.lemma_3_15` | For an original-S-definable RV set A, the actual non-infinity Gamma values with nonempty finite A-fibre form a finite set whose full RV preimage is definable over exactly S. Every ACVF(0,0) model and arbitrary base S. Finiteness and uniform finite-fibre bounds follow from C-minimality and infinitely many residue-characteristic-zero angular classes. No assumed uniform bound, C-minimality consequence, Gamma section, extra representative or saturation premise. |
| `Remark319Audit` | A checked obstruction to the unrestricted printed classification, not a proof of Remark 3.19: the actual units subgroup {1,-1} has a parameter-free definable VF point set, which is neither a ball nor the full valuation-unit group in ACVF(0,0). The author retracted the whole remark on November 5, 2026 after checking its later-use status; see [RETRACTIONS.md](RETRACTIONS.md). It is excluded from proof obligations and is not counted as proved. |
| `AdditiveCosets.lemma_3_18_1` | Every original-S-definable additive subgroup is proved to be a ball. For any set-valued function to powersets of RV^m with its complete original-S sorted graph, the actual additive quotient has only finitely many classes on which that function varies. Every ACVF(0,0) model, arbitrary original S and all finite output arities. No extra field-base convention, saturation, canonical model, ball-classification or finite-exception hypothesis. Both alternatives of part (2), including genuine Gamma bases, are now checked in GeneralCosetChoice. |
| `ClosedCosetChoice.lemma_3_18_2_closed` | Closed-ball alternative of 3.18(2): a function on the actual additive quotient has its complete powerset-valued graph definable over exactly S, and each coset has a representative realizing that selected value. Every ACVF(0,0) model, arbitrary original S and all finite RV arities. Closedness is existence of an actual closed-ball imaginary with the subgroup as its point set, including whole-field and singleton cases. No assumed center/choice theorem, extra named representatives, field-base convention or saturation premise. GeneralCosetChoice now proves the generated alternative and extends the closed case to genuine Gamma bases. |
| `VFAlgebraicity.lemma_3_3` | All VF and RV parameter tuple arities and the original arbitrary base. Model-theoretic VF algebraicity implies algebraicity over the field generated by the base's VF elements and the VF tuple. RV parameters do not enlarge it. Assumes only ACVF; no added saturation, characteristic, C-minimality or local-stability premise. Proved through `PolynomialSyntax`, `PolynomialLocal`, `RVTermLocal`, `QFLocal`, `ValuedNeighbourhood` and `VFAclField`. |
| `QuotientFamilies.notation_3_16` | Invariance and saturation characterize unique quotient-to-powerset descent. Definability remains over the same base; surjective projection is equivalent to nonempty values. No arbitrary representatives are named. |
| `CMinimal.theorem_2_8_c_minimal` | The exact frozen `IsCMinimalWS` target of Theorem 2.8, for every ACVF model, every parameter type and every sorted assignment. Only ACVF is assumed; no characteristic, saturation, canonical-totalization or interpretability premise is added. `ValuedDefinability`, `RVRepresentatives`, `LiftTerms`, `RepresentativeDefinability`, `QFInterpretation`, `BooleanCombinations` and `GeometryBridge` prove the full translation and ball conversion, using the checked ordinary valued-language result in `ValuedCMinimal`. The inherited placeholder is not used. |
| `DefinableConstants`, `VFDefinableClosure` | VF definable closure is a field and VF model-theoretic algebraicity is equivalent to algebraicity over the field generated by the original VF parameters, in every ACVF model and over every base. `SortedFunctionClosure`, `SortedInverseClosure` and `SortedParameterElimination` remove the canonical-model restriction. Generated fields are not identified with definable closure. |
| `TranscendenceDegrees.corollary_3_4` | All three actual VF fields have the same transcendence degree over VF(S), for every finite VF tuple and arbitrary RV parameter set B. Only ACVF and the standing VF-field base convention are required; no canonical-model, saturation, characteristic or cardinal bound on B. |
| `VFExchange.lemma_3_6_vf` | VF exchange over the original standing VF-field base, in every ACVF model. Derived from the proved closure identification and Mathlib algebraic matroid exchange. The RV assertion is now checked in `RVExchange` under the standing ACVF(0,0)/saturation assumptions. |
| `ClosureConventions` | Definable closure is monotone and idempotent, and adjoining it preserves sorted acl, in every ACVF model. A genuine raw LRV substructure is constructed on canonical models. VF-generated and (VF,RV)-generated bases use definable closure. General Gamma-base dcl and basic generation laws are now checked in `GammaClosureLaws` and `GeneratedBaseLifting`. |
| `RVIndependence.corollary_3_7_vf` | VF half, strengthened to arbitrary original bases S and arbitrary RV parameter sets. Adjoining RV parameters does not change VF algebraicity. Only ACVF is needed; no field-base convention, canonical representation or saturation is assumed. The Gamma assertion is now checked in `RVGammaAlgebraicity` under the standing ACVF(0,0)/saturation assumptions. |
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
  substructure on canonical models. Full modelhood in Corollary 3.14 is now checked below.
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
  of values under a compatible valuation. Ordered-group operations and the imaginary-parameter interface are checked
  above; general dcl and basic generation laws are checked, while full Gamma acl closure laws remain separate.

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

- `FiniteBallBasis`, `RVUnaryLift`, `RadialBalls` and `AngularPattern`:
  a finite Boolean ball basis controls membership, and all but finitely many
  RV classes in each value fibre have the same membership. Basis centers are
  used only inside the proof, never added as parameters.
- `InfiniteValueFibres`, `FiniteValueFibres`, `GammaDefinability` and
  `FiniteValueDefinability`: positive integer multiples give infinitely many
  distinct angular classes at each nonzero value. A single finite RV set
  bounds every finite fibre; first-order counting defines the resulting
  Gamma set through its invariant full RV preimage. The actual Gamma group and parameter interface are checked above; general dcl and basic generation laws are checked, while full Gamma acl closure laws remain separate.

- `InitialSegments`, `BallInitial`, `AdditiveRadial` and `AdditiveClassification`:
  positive integer multiples and their translates avoid each finite off-zero
  ball basis. Definable additive subgroups are therefore downward closed in
  absolute value. A finite family of origin balls determining such a proper
  initial set contains that set itself. The exported classification chooses
  the compatible valuation internally.
- `BallFibreConstancy` and `AdditiveCosets`: the finite root set controlling all
  RV outputs forces each varying class in a ball partition to meet that set.
  Additive quotient fibres are proved to be translated balls, giving 3.18(1).
- `GammaValueEquiv`: the actual Gamma-with-infinity quotient is equivalent to
  Mathlib's restricted valuation value group; infinity maps to zero, RV
  multiplication agrees, and comparisons have the reversed order. The genuine
  non-infinity Gamma carrier is equivalent to its units. No representative is
  named in S. Global quotient operations and the imaginary-parameter interface are checked above; general dcl and basic generation laws are checked, while full Gamma acl closure laws remain separate.

- `DefinableCosets`, `ClosedClassCodes`, `ClassCenterRelation` and
  `ClosedClassGeometry`: the full original-base quotient kernel is definable.
  All real closed-ball codes of classes meeting R form a definable family
  with finitely many distinct ball values. The checked center theorem supplies
  a graph invariant under equality of balls, hence a functional center relation
  invariant on classes. No code or chosen point is added as an S parameter.
- `ProfileComposition`, `ClosedQuotientChoice` and `ClosedCosetChoice`:
  composition with that partial center relation preserves the full sorted
  graph over S. Classes without a center miss the uniform root set, so the
  original profile is constant there. Descent proves the entire quotient graph
  definable and supplies a representative of every class with the chosen
  value. Closedness of actual additive cosets is proved by translating a code
  of the subgroup; the whole-field and singleton flags are included.

The Gamma-base extension of 3.4 is now checked in `GammaDefinableClosureField`.
Both alternatives of 3.18(2) are now proved in `GeneralCosetChoice`, including
the closed case over genuine Gamma-named bases and the (VF,Gamma)-generated
case using full Lemma 3.13. The remaining work has two substantial blocks:
Gamma acl transitivity; and the author-approved guarded rational normal form
of Definition 2.4. Legacy conditional reductions are not counted as proofs.
Keep `TARGETS.md` as the full target checklist. Remark 3.19 is retracted; see
[RETRACTIONS.md](RETRACTIONS.md).

## Verification

`lake env python3 Section3/verify.py` checks the new modules, actual headline
types, allowed axioms and root import. Generated logs are in
`.scratch/section3-verified/`. A verification run is complete only when its
`status.txt` says `PASS`; partial results do not certify the current tree.
The checked batch record is copied into `verification/` after it is stable. The exact working-copy root source is embedded in the record. Its concurrent Section 4 and Section 5 imports use separately source/cache-matched consumer artifacts, including individually compiled Section 4 interfaces where recorded. This extra import check is not a Section 4 or Section 5 source/headline certificate.
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


The original shared QE scratch directory disappeared during this checkpoint.
The build dependency was restored in a private exact-pin clone. Eighty earlier
proof artifacts were reused after checking their exact compiler/dependency
fingerprints and identical Lean code against the pinned sources; the QE root
and all three headline type/axiom checks were run afresh and exited zero.
The new record includes those source and artifact identities. This restores
the completed dependency and adds no QE theorem, assumption or revision change.
