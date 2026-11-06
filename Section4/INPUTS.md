# Earlier-section inputs

Sections 2--3 are now completed in the scope recorded by
[their handoff](../Section3/HANDOFF.md), including the approved guarded
rational formulation of Definition 2.4 and the retraction of Remark 3.19.
Their verification is outside this Section 4 session. `verify.py` compiles
and audits Section 4, recording the actual compiled provider closure of its
earlier-section imports; it does not rebuild those proofs. The publication
audit checks the completed Section 3 source and compiler receipts before use.

The finite-to-one refinement uses these earlier inputs:

| Input | Use in Section 4 |
| --- | --- |
| Released LRV language, ACVF, and ACVF(0,0) | Common ambient theory and pure characteristic zero |
| `Saturated` and `definable_finite_subcover_tuple` | Obtain a single bound for a definable family of finite fibres |
| `HasMore`, its definability, and the finite-cardinality criterion | Form the definable cover by fibre-size bounds |
| `Barycentre.rawCode_definable` | Define the RV code uniformly over the original parameter base |
| `Barycentre.rawCode_eq_code` | Identify the uniform code with the code of the actual finite set |
| `Barycentre.code_injective_of_card_le` and `code_sorted` | Separate points and ensure that outputs lie in RV |
| Sorted/raw definability bridges | Compare the real presentations with the paper's sorted definability |
| Actual Gamma quotient and its definable equality relation | Present imaginary Gamma coordinates using all representatives |

The new Section 4 argument proves uniform bounds, combines coordinate codes,
descends the result across different presentations of one fibre, and adds
the resulting RV coordinates to a finite-to-one map. Uniform separation is
not taken as an additional input.

The generic dimension and category modules use ordinary finite real-code
presentations and full definable graphs. They do not require model-theoretic
assumptions beyond the ones explicitly displayed by their statements.

The dimension-comparison work additionally uses these earlier results as
given; it does not assess or rebuild their proofs:

| Input | Use in Section 4 |
| --- | --- |
| `algebraicAt_iff_raw` in a canonical totalization | Pass from a finite complete-graph fibre to sorted algebraicity. |
| `algebraicAt_vf_iff_parameterField` and `vfParameterField_union_rv` | Identify VF algebraicity with actual field algebraicity and remove RV-only parameter names. |
| `RawClosure.Tuple.good_relation_of_algebraic` | Promote algebraicity at a tuple to an original-base definable relation with finite fibres at every tuple. |
| `relativeTrdeg` and `relativeTrdeg_eq_of_algebraic` | Compare actual subfield transcendence degrees across algebraic extensions. |
| `small_union_finite` | Adjoin any finite target code to a small base; the fibre calculation displays the needed infinite-cardinal bound. |

The Section 4 proofs supply the field generator bound,
coordinate selection, finite definable cover, gluing, and dimension
comparison. Those conclusions are not added as earlier-section inputs.

The commuting-lift argument for 4.19 uses the accepted all-arity
`corollary_3_2_vf`, with its nonempty definable VF tuple family and the
smallness of the base plus the fixed RV tuple. It also uses
`AlgebraicAt.eliminate_algebraic_params`, closure under the named RV map,
and `RawClosure.finite_of_definable_subset_algebraic`. Section 4 proves
definability of the volume-fibre image and applies that last theorem over the
same small base; the finite-image conclusion is not assumed.

The geometry proofs reuse the accepted unary local-polynomial result,
the ring-term interpretation, elimination of definable parameter names,
and nontriviality of the model's valuation. Section 4 supplies the finite-tuple
syntax and locality proof, finite polynomial avoidance, generic points,
and the polydisc/dimension equivalence. None of these Section 4 conclusions
is used as an earlier-section hypothesis.

The RV rank work states the RV half of Section 3 exchange explicitly as
`RVExchangeInput`, uniformly over actual parameter sets:

```lean
∀ (B : Set M) (x y : CanonicalRV.RVSort M),
  AlgebraicAt (insert y.val B) .rv x.val →
  ¬ AlgebraicAt B .rv x.val →
  AlgebraicAt (insert x.val B) .rv y.val
```

This is authorized material from Section 3, including its uniform parameter
scope. It is a theorem hypothesis, with no custom axiom. The actual RV
closure operator, its closure laws and finite character, its bridge to a
Mathlib matroid, and all Section 4 dimension comparisons are proved
separately in Section 4. The RV rank and dimension chain is included in the
verified library; [STATUS.md](STATUS.md) records its verification. Parameter
invariance uses the existing genuine `StronglyHomogeneous` definition,
in addition to genuine saturation. Section 4 proves the nonalgebraic type
extension and automorphism-movement steps from those standing assumptions;
neither step is added to the earlier-section input list.

The 4.11 sequence argument takes the Gamma half of Section 3.7 explicitly
as `GammaRVAlgebraicityInput κ`: for any base with real part smaller than κ,
adding actual Gamma names does not enlarge RV algebraic closure. This
includes an arbitrary set of Gamma names. The existing Section 3 compiled
interfaces `GammaParameters.algebraic_rv_gamma_base_iff`, `lemma_3_6_rv`,
and `gamma_definable_finite_thresholds` are now available and are taken as
given. `EarlierRVInputs.lean` derives both named inputs from them, extending
small-base RV exchange by finite formula support. No Section 3 proof was
rebuilt or audited for this step.

The complete `lemma_4_11` exports neither of these named inputs as an open
hypothesis. Its premises are canonical totalization and the existing genuine
`BaseContext`: pure characteristic zero, saturation and homogeneity at its
uncountable cardinal, a small substructure, and nontrivial named values.
Section 4 proves the minimal-controller definability, original-base Gamma
point, infinite-row elimination, independent-sequence iteration, and both
rank bounds. The complete lemma and its helpers are included in the verified
library; [STATUS.md](STATUS.md) records the compiler, type and axiom checks.

The complete residue comparison `ResiduePurity.lemma_4_10` is now proved in
Section 4 relative to the given earlier material. Its final inputs are the
canonical totalization, the genuine standing `BaseContext`, an RV-definable
set over its original base, an arbitrary same-value normalizing tuple, and
nonemptiness. Section 4 proves exact-base pure residue-field definability,
field/RV algebraicity equivalence, tuple rank/transcendence-degree equality,
zero-aware normalization, finite coefficient-name extension, and the actual
Krull/Zariski dimension comparison. Pure ACF QE and its finite/cofinite
root-set result are reused from the pinned ACVF-QE; no stable-embedding or
field-algebraicity assertion is added as an input. The given Section 3
exchange theorem is instantiated from `BaseContext` via `EarlierRVInputs`.
The comparison and its helpers are included in the verified library.
[STATUS.md](STATUS.md) records the completed compiler, type and axiom checks.
