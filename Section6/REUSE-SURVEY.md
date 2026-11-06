# Section 6 reuse survey

Date: November 5, 2026 (America/Los_Angeles).
Lean 4.33.1; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`;
ACVF-QE `f3ef4ee679f921079aa8f742a2807a9cc724d2d6`.
No dependency or language upgrade.

## Local comparison and decisions

| Source | Inspected scope | Decision |
| --- | --- | --- |
| `Section6/Sec6.lean` | Finite-SP tuple syntax; functional closure from dcl closure; VF closure and RV centres assumed | Preserve the legacy file. Replace the finite-parameter interface by arbitrary-base complete graphs. Prove the VF fixed-field argument instead of assuming `HenselAclStep`. |
| `Section6/Sec6QE.lean` | Sort guard semantics, VF-free syntactic class, generic induction from an assumed one-step elimination; only LRV | Attribute and adapt the generic logical reduction into `RelativeSyntax`. Do not copy its conditional henselian headline or claim it covers arbitrary RV expansions. |
| `.scratch/HenselizationStep.lean` and `RVHenselLifting.lean` | Henselization universal property and elementary lifting over algebraically closed fields | Different target. The needed standard input is automorphism invariance of a henselian valuation, not a new henselization campaign. |
| Released `ValuedModelMap.lean`, `TypedModelMap.lean`, `SortedEmbeddings.lean` | Actual field/RV component maps and embeddings of normalized LRV models | Direct imports. Construct surjectivity for a field automorphism and derive the genuine LRV automorphism. No assumed automorphism correspondence is needed. |
| Pinned Mathlib `FieldTheory/Galois/Infinite.lean` | `InfiniteGalois.mem_range_algebraMap_iff_fixed`, infinite algebraic Galois extensions | Direct import; avoids rebuilding the fixed-field theorem. Valuation invariance remains the explicitly permitted standard quotation. |
| Pinned Mathlib `RingTheory/Henselian.lean` | Actual `HenselianLocalRing`, defined by root lifting | Use the actual predicate on the restricted valuation ring. Do not replace it by functional closedness. |
| `Section4/DefinableGeometry.lean`, `Section5/VerticalConstruction.lean`, `Core.lean`, `GeneralExistence.lean` | Full graphs and real codes, actual mixed points, bijections and inverses, preparations and contractions | Reuse as authorized earlier material. New proofs show that those actual maps restrict to the substructure and that all its RV keys have points. |
| Pinned Mathlib `ModelTheory/Definability.lean`, `ElementaryMaps.lean`, `Semantics.lean` | Finite-coordinate images, formula substitution, elementary preservation and existential tuples | Direct generic reuse for functional closure and elementary-envelope transfer. |

The local sources retain their author credit and licenses. Mathlib is
Apache-2.0; ACVF-QE is MIT with separately credited ports. No external
proof source was copied. The logical induction is adapted from this
repository's own legacy file, with attribution in the new file.

## External discovery

Focused queries included `Lean henselian fields relative quantifier
elimination RV formalization`, Mathlib source and PR queries for henselian
valuations and fixed fields, and targeted searches of Reservoir, Lean Pool,
Palomar, Tau Ceti, TheoremSearch and Formalpedia. No importable formal
henselian RV elimination result was found in these searches. Search-index
coverage is incomplete; catalog interfaces were not exhaustively searched.
The broader registries and current-upstream comparison in
Section4/REUSE-SURVEY.md were also consulted.

The [paper's Section 6](https://arxiv.org/html/1006.2467v1#S6) was read to
fix numbering and distinguish the geometric descent from syntactic
elimination. Related mathematical QE results returned by the search,
including [Flenner's paper](https://arxiv.org/abs/0910.2682), are mathematical
references, not Lean dependencies or authorized Section 6 assumptions.
[Mathlib](https://github.com/leanprover-community/mathlib4) and
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) searches found generic
algebra/valuation material rather than a verified compatible elimination
module. No external candidate is claimed as locally verified reuse.

Compiler evidence, imported-interface fingerprints, full headline types
and axiom outputs are recorded separately in STATUS.md and `.scratch/`.

A focused current-upstream source check also inspected
`Mathlib/RingTheory/Henselian.lean` on the web: it supplies the ordinary
root-lifting predicate, rather than an RV functional-closure or elimination
theorem. The raw upstream `FieldTheory/Galois/Infinite.lean` fetch failed
with a cache miss; the pinned local file was inspected directly and is the
actual dependency. The Engler–Prestel input is the uniqueness
characterization in Theorem 4.1.3; the automorphism-preorder formulation is
the consequence used here, not a quotation of a Section 6 conclusion.

## Syntactic continuation, November 6, 2026

The author again authorizes earlier sections as given and clarifies that
Definition 2.4 uses guarded rational VF factors. Read
`Section3/NORMAL-FORM-NOTE.md` and the existing `PolynomialSupport.term`:
the latter already recurses through RV inversion. The author subsequently
clarified that the change to Definition 2.4 does not affect the notion of
occurring polynomials, since inverse commutes with rv. The new finite-arity/
expanded-language support uses that existing convention, without a new
numerator/denominator occurrence definition. The earlier normal form is
not rederived.

The identity `rv(f/g) = rv(f)/rv(g)` is already supplied by the earlier
actual `Section3.RVOperations.rvHom` and the generic group-with-zero
homomorphism laws. It is used as given; no replacement RV construction or
new proof of that earlier input is needed in Section 6.

Pinned Mathlib `Syntax.lean` / `Semantics.lean` provide `freeVarFinset`,
`restrictFreeVar`, `realize_restrictFreeVar`, `Formula.iExs` and its semantics.
Use these directly: they already prove replacement under all auxiliary
quantifiers. `Complexity.lean` supplies quantifier-free preservation by
embeddings. These are preferable to a fresh formula datatype or term
substitution implementation. The new language expansion is the actual
Mathlib sum with published LRV; all extra symbols have RV signatures.

Focused web searches for Lean relative/RV/Denef–Pas elimination, current
Mathlib code and PRs, and local Mathlib/Tau Ceti/catalog snapshots found
no compatible completed specialized elimination development. Returned
mathematical papers are references, not Lean proof dependencies. Pinned
Mathlib has no angular-component interpretation implementation in the
searched source. This is a limited survey, not an existence claim.

The exact paper Section 6 was reread at
https://arxiv.org/html/1006.2467v1#S6. Its printed inverse-free wording is
superseded by the author's language and Definition 2.4 corrections.
Compiler status and remaining syntactic obligations are recorded separately.

The generic compactness criterion was surveyed separately before its
implementation. The local catalog snapshot of Mathlib PR #40561,
`QuantifierElimination.lean`, was inspected (including its Apache-2.0
header and compactness/model-pair proofs). Its authors are Yağız Kaan
Aydoğdu, Yusuf Demir and Salih Erdem Koçak. The module depends on a newer
`ElementaryExtensionPair` absent from the pinned project. `FragmentCompactness`
credits and generalizes its two-model argument to arbitrary Boolean
fragments, deriving its compactness core from the pinned finite-cover
lemma already checked here. No newer Mathlib dependency is imported.
The inspected PR #40561 snapshot is head
`095ae36e89f0eb4a0a5444a9144ef6e508d797d2`
(https://github.com/leanprover-community/mathlib4/pull/40561).
Its Apache-2.0 notice and authors are preserved in FragmentCompactness;
the license text is retained at Section4/Imported/Mathlib-LICENSE.
Interactive checking of the generalized criterion passed; a standalone
compiler check and integrated type/axiom audit remain required.

For the Denef–Pas interpretation, a focused current Mathlib search for
interpretations and relationalization returned Basic, Syntax, Semantics,
Types and relational-language examples, but no compatible finite-product
interpretation compiler. Existing pinned syntax and formula substitution
remain the reuse boundary. This is a limited source search, not a claim
that no other such implementation exists.

A further native-syntax check found the exact normalization utility in
released `CanonicalQF`: `sortedTerm_sort` and `sortedTerm_realize`.
`TypedNativeTerms` therefore imports that checked earlier proof and supplies
only the adapter removing `Fin 0`; its initial independent normalization
implementation was replaced before final verification. `GeneratedParameters`
reuses Mathlib `Substructure.mem_closure_iff_exists_term` and this adapter.
`PairInterpretation` reuses pinned `Set.Definable.preimage_comp`, finite
conjunctions and `exists_of_finite` / `forall_of_finite` to construct actual
first-order formulas from atomic graph definitions. No new formula datatype
or dependency revision is introduced.

Per-model `Set.Definable` does not itself choose one formula across all
models. `PairSyntax` supplies a fixed atomic formula dictionary and
constructs term graphs, relation substitution and all quantifiers using
pinned `Formula.iInf`, `iExs`, `iAlls` and relabeling. Its realization theorem
quantifies over every model realizing the same dictionary. It uses the
existing formula datatype. The Denef–Pas dictionary remains separate.

The outer-bound syntax continuation reuses the unchanged retained
`Shared/ParamBridgeShift.lean` and `Shared/ParamBridgeRelabel.lean`:
`sortAssem_*` and `relabelAux_*` supply index arithmetic, while the new
module handles only the expanded formula constructors. Matching earlier
source/artifact copies were found in `.scratch/section3-audit/`. A fresh
pinned compilation of these exact source copies and an audit of the five
used helper headlines all exited 0 under `.scratch/section6-shared-*`;
the headline axioms are within the permitted three.

For the 6.5 language specification, Pas's original paper, Definition 2.3,
uses the ring language in VF and RF and a value sort with an element
infinity: [primary PDF, printed page 140](https://www.math.ens.psl.eu/~zchatzid/GdT17/Pas.pdf#page=4).
This is a definition reference, not an assumed proof of 6.5. The auxiliary
dictionary must preserve that infinity and allow auxiliary expansions.

The named-base wrapper reuses pinned Mathlib
`BoundedFormula.constantsVarsEquiv` and `realize_constantsVarsEquiv`.
It opens constants as ordinary free parameters before the proved arbitrary
context elimination and closes them afterwards. Atomic diagram sentences
supply the original sorts; it does not assume elimination over named bases.

The additional raw-syntax bridge is restricted to relational RV expansions.
RelationalTerms proves that every term is a term of the published language.
HenselianNativeSyntax transfers released CanonicalQF sorting through the
ordinary native envelope embedding, using Mathlib IsQF.realize_embedding.
HenselianRelationalSorting uses only these term facts and the already proved
extra-symbol sort axioms to discharge AtomicSorting. ExpandedRawLogic then
splits an unrestricted binder over the two actual native sorts and invokes
the constructed 6.4 theorem. These adapters are current development work,
not an assumed DP translation. TrivialAngularComponent reuses Mathlib's
residue homomorphism, its surjectivity and field-hom injectivity to build the
angular-component field equivalence in the trivial-valuation branch.

The completed development forward dictionary reuses PairSyntax for the whole formula recursion. ForwardPatterns supplies only the finite RF/Gamma input/output cases, including zero-arity symbols and canonical wrong-sort defaults. ForwardEquality and ForwardCross use Morley relations indexed by fixed auxiliary formulas. The next RVReduct adapter reuses RVAbstraction.formula_realize, its native polynomial-leaf extraction and the existing finite-support machinery; none of those earlier proofs is restarted.

Focused follow-up for proper auxiliary sort syntax (November6): inspected Mathias-Stout/Many-sorted-model-theory, https://github.com/Mathias-Stout/Many-sorted-model-theory (Apache2.0). Its README defines a different intrinsically sorted Signature/Term/BoundedFormula family over arbitrary sort families. This is useful background but is not a drop-in bridge for the pinned Mathlib formula datatype and published LRV used here. No code from that development is imported or ported. The narrow adapter should keep the existing formula datatype and use finite sort metadata, reusing the local canonical-sorting/guarded-formula pattern. Coverage is a focused source/README search, not a claim that no compatible bridge exists elsewhere.

Build follow-up: the pinned Lean 4.33.1 Environment/Frontend sources explain
that legacy non-`module` imports load the full private import information.
The released QE modules use that legacy format. The new module system
cannot import such a module directly, so changing module-system headers
would require altering the pinned dependency and is not used. Instead the
57 small DP fragments are grouped into four coherent modules with exact
body identity checks. This reuses all existing proofs, preserves the public
names and leaves the published language and pins unchanged. MODULES.md
records the organization; compiler and integration evidence remain separate.
