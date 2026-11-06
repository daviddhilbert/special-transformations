# Syntactic continuation of Section 6

Historical construction notes. The completed scope and final verification
are recorded in STATUS.md and HANDOFF.md. Statements of pending work and
publication restrictions below describe earlier checkpoints, not the current
status or the author's November 6 commit-and-push authorization.

November 6, 2026. The author requests completion of Lemma 6.3, Proposition
6.4 and Corollary 6.5, taking all needed earlier sections as given. No
earlier proof or QE campaign is restarted. No push is authorized.

## Frozen statement and scope

Lemma 6.3 must choose an output formula before a model or a free assignment:
for every finite tuple of existential VF variables and every VF-free
quantified formula, there is an equivalent formula whose binders range
only over RV. Keep arbitrary RV-only expansions, all remaining VF/RV free
variables, named base parameters, pure characteristic zero and nontrivial
henselian valuations. Proposition 6.4 eliminates all VF quantifiers by
logical induction. Corollary 6.5 requires actual interpretation in the
residue/value sorts of a Denef–Pas language, preserving quantifier classes.

The latest author clarification is that revising Definition 2.4 does not
change "occurring polynomials": inverse commutes with rv, and
`rv(f/g) = rv(f)/rv(g)`. Use the existing rv-leaf extraction recursively
through RV inverses. Retain rational domain and zero-branch guards. RV has
one absorbing point and its inverse is totalized; VF inverse is unnamed.
No new numerator/denominator occurrence convention is introduced.

## Construction

1. `RVFormula` reuses Mathlib finite free-variable restriction and finite
   existential binding. Its occurrence enumeration depends only on syntax
   and its replacement theorem holds under all auxiliary quantifiers.
2. `RVTermSupport` works in the actual sum of published LRV and an
   arbitrary RV-only signature. It proves equality of RV terms from their
   ordinary polynomial support, including nested inverses and extra
   function symbols. A quotient has the ordinary rv leaves f and g.
3. `RVAbstraction` restricts native LRV symbols to their RV signatures,
   abstracts VF polynomial leaves and translates the guarded RV fragment.
   The semantics uses the source model's RV carrier, with arbitrary extra
   RV structure. It does not extend that extra structure to ACVF or
   transfer RV quantifiers into an algebraically closed field. The earlier
   removal of VF literals/normal form is accepted as given.
4. `SyntacticDescent` combines an actual complete contraction graph
   formula with the checked prepared-map descent. The graph domain is
   present even for an empty occurrence tuple. This assembly theorem alone
   is not full Lemma 6.3: it displays the graph-interpretation premise.
5. `ContractionGraph` obtains a quantifier-free LRV formula for the actual
   full contraction graph over the same base, using earlier sorted
   definability and released QE. Connect its pure RV translation to the
   graph-interpretation premise in step 4, with constants from the original
   base and all free assignments explicit.
6. Discharge uniformity. A preparation chosen separately in each ambient
   model is insufficient for `VFQE_step`. One sound route is to encode
   finite preparation certificates in first-order syntax, obtain local QF
   guards by released QE, and use ordinary compactness for a finite cover.
   An alternative is the standard fragment-definability criterion plus
   common ACVF envelopes over tuples of the same QF type. Such compactness
   or elementary-amalgamation inputs must have their full generic types
   and Marker citations; they may not assume relative QE or bundle the
   Section 6 conclusion into saturation. Then extend/apply the logical
   induction to the actual arbitrary RV-only expansion.

   Preferred certificate payload: native formula codes for the pullback
   domain B, the graph of a definable bijection VF^n → B, and the full
   functional graph G on RV keys and the finite polynomial-value tuple.
   Validity says that the bijection is total/unique in both directions,
   B is a whole pullback, and G is exactly the image of that graph together
   with the polynomial values, with one output per key. These are finite
   first-order relational conditions; no special-chain witness needs to
   be encoded. Actual Section 5 special bijections supply the witnesses.
   Build the validity formula compositionally, apply released canonical
   ACVF QE for its local guard, and use `finite_formula_cover` for one
   finite family before the model/free assignment. Prove the local
   equivalence from functional closure and key realization, then use
   `uniform_of_local_certificates`. Its cover/correctness premises must
   be discharged from these data, not left as new henselian inputs.
7. `AngularComponent` derives the algebraic splitting of the actual
   leading-term quotient from a multiplicative angular component agreeing
   with residue reduction on valuation-one elements. Its value group is
   the valuation's image on units. The final Denef–Pas result additionally
   needs explicit translations of atoms, zero/nonzero RV cases and RV
   quantifiers into residue/value quantifiers. A quotient-group splitting
   alone is not counted as Corollary 6.5.

## Verification discipline

Compiler, axiom and full-hypothesis evidence are separate. The old
eight-module/31-headline checkpoint remains in `.scratch/section6-checkpoint31`.
New developments are individually checked before integration. Development
records are `.scratch/section6-verified/Section6.*.development.json` and
matching logs; interactive diagnostics are development feedback, not final
compiler certificates. Only the final library verifier and headline audit
can update the integrated count. Earlier compiled interfaces are accepted
as given and inventoried; they are not rebuilt.

## Direct term-map route identified during continuation

Use the already accepted **general definable-map** `Section5.map_preparation`
for the finite native RV term map. There is no need to rederive the earlier
VF-term-to-MvPolynomial conversion. After finite abstraction, an RV leaf
is rv of a well-sorted FV term; a syntactic induction shows that such a
term is in the image of the native LRV inclusion, since every extra
function has RV result. Build its full definable tuple map with the given
Map.ofCodes and Term.definableFun_realize. Original parameter names are
finite: constantsVarsEquiv followed by the already checked abstractLeft
extracts them from syntax. Partition that finite parameter context by its
declared VF/RV sorts before invoking RVAbstraction. Name its RV parameters
back using the actual constants-variable equivalence. This discharges the
pointwise PolynomialNormalForm-style presentation from the actual finite
abstraction, rather than assuming a new Section 6 replacement assertion.
The polynomial-specific descent modules remain useful checked instances.

For global theory uniformity, retain the full concrete obligations: the
henselian theory is specified in HenselianTheory (no algebraic-closedness
or divisibility schemes), native/standard model recognition is separate,
and a genuine elementary test-family cover must be obtained from the
authorized earlier envelopes and standard small-model universality. The
generic ElementaryCover definition is not itself a verified construction
of that cover and is not a substitute definition of saturation. Likewise,
SortedFragment still requires actual type invariance in its application.

## Current continuation: named base and Denef-Pas

The named-base wrapper is now constructed in NamedLogic, reusing
constantsVarsEquiv. It is included in the passed assembled239 audit.
The two-coordinate compiler PairSyntax is uniform; the concrete auxiliary
entries for equality, multiplication, inversion and the angular map are
included in the same snapshot. DenefPasRV/DenefPasResidue subsequently
pass development checks for the residue domain and its operations.

For the remaining full three-sort transfer, use the existing PairSyntax
compiler in both directions where possible. A forward interpretation may
introduce field witnesses, since 6.4 subsequently removes them. A raw-to-
guarded syntax adapter is being constructed in ExpandedRawLogic; its atomic
sorting premise is not yet discharged and is not a new accepted input.
HenselianNativeSyntax reuses CanonicalQF through the actual native envelope
embedding to sort native atoms and normalize native terms. Next specialize
to a relational RV expansion, so every term is native. Sort an added RV
relation by the computed sorts of its native terms and the proved extra-
relation sort axiom. Then prove AtomicSorting and SortCover for the actual
henselian theory and apply the constructed 6.4 theorem.

A possible forward code from two native-carrier coordinates onto
K + (RF + GammaInfinity) uses the second coordinate as payload. A field
payload codes that field element. An RV payload codes its residue coordinate
when the first coordinate is field zero, and its value coordinate otherwise.
This total code is onto. Canonical RV representatives encode RF r by (r,1)
and GammaInfinity g by (1,g). A relational Morleyization of the DP auxiliary
language can supply fixed native RV relations; their definitions must later
be translated back by an actual auxiliary formula dictionary. No DP QE or
full formula-translation statement may be assumed as an input. This forward
code and its atomic dictionary are still a plan, not a proved interface.
The alternative direct typed-term translation remains possible if simpler.

The native henselian theory includes the released nontrivial valuation
axiom. Check the original DP scope before declaring 6.5 complete; a genuinely
trivially valued DP model requires a separate argument (ac identifies VF
with RF), or an explicit source definition excluding that case. Do not
silently extend the nontrivial native-envelope theorem to trivial valuations.

Assembled281 now certifies the raw relational QE adapter and the auxiliary
quantifier lift (90 source identities, 281 headline type/axiom lists).
DenefPasNativeCodes is an actual proved total forward code with a right
inverse; it is no longer only a plan. DenefPasNormalization subsequently
passes development checks, normalizing all codes before arbitrary auxiliary
relations inspect them. DenefPasMorley and DenefPasOrder are the next drafts.
The source DP presentation uses a disjoint union of RF and Gamma for auxiliary
symbols. Before calling the final result the full many-sorted Corollary 6.5,
check the metadata/normalization bridge for the auxiliary symbols as well as
the field-free binder class. Merely having no FV binders is not a substitute
for a correct interpretation of the original DP language. The final forward
and backward atomic dictionaries and substitution of (ac(P),val(P)) remain.
