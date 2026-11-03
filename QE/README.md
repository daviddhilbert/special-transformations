# Theorem 2.3 — quantifier elimination: accepted artifacts

Artifacts of the QE campaign. Each file is self-contained (`import Mathlib` only), is a snapshot
of `Milestone0/Encoding.lean` where it uses the encoding, and is evidence rather than library
code. `make qe` elaborates all eight.

## Status

Nothing here discharges the `sorry` at `theorem_2_3_quantifier_elimination` in
`Milestone0/Encoding.lean`. Two reductions exist, each conditional on named `Prop`s, with no
axiom added; Weispfenning's theorem is never assumed as an axiom, only taken as a hypothesis.

| Layer (see `../QE-PLAN.md`) | State |
| --- | --- |
| (C) Yin's Lemmas 3.2–3.8 | **nearly complete**: 3.2, 3.3's group core, 3.5's value core, 3.7, 3.8's value half, and the henselian step of 3.4. Open: 3.3's residue half, 3.4's polygonal case, the `RV` half of 3.5, the assembly into an `L_v`-monomorphism |
| (A) the reduction | **present twice**, with different hypothesis sets |
| (B) a QE criterion | **the ends are proved, the middle is not.** `QF_type_bridge.lean`: QF-type invariance ⟹ `HasQE` (arbitrary `L`,`T`). `Johnson_criterion.lean`: prime models + amalgamation + 1-ec ⟹ existential QF-determinism, validated on ACF. `QE_step_induction.lean`: `QEExStep` ⟺ bounded QE and ⟹ `HasQE`. **Almost joined**: `Bounded_compactness.lean` proves `QEExStep` from quantifier-free-existential determinism, so the model-theoretic half of the join is done. What remains is bookkeeping: its `IffB` is `Theory.Iff` up to unfolding, and `QE_step_induction.lean`'s `HasQE_of_QEExStep` takes `Theory.Iff` — the two files need merging (they are standalone by convention) for the end-to-end statement. `HasPrimeModels` is discharged only for field bases |
| (B) hypothesis (ii) | amalgamation reduced to one statement ★ about `O₁ ⊗_{O₀} O₂` (Johnson 2.2.4, 2.2.6); everything else in §2.2 proved |
| (D) Weispfenning | held as `LvTwo.Weispfenning : Prop := HasQE ACVF` in `Reduction_Lv.lean` |

## Files

| File | What it proves | Layer |
| --- | --- | --- |
| `Lemma32_root_lifting.lean` | **Yin's Lemma 3.2** in full generality: `F ≠ 0`, `b ≠ 0`, `I ⊆ supp F` with `2 ≤ |I|`, `v (F.coeff i · b^i) = 1` on `I` and `< 1` off it, `v (Σ_{i∈I} F.coeff i · b^i) < 1` (the rendering of `F̄(t) = 0`) give `b'` with `rv b' = rv b` and `F b' = 0`. Not the Newton polygon: `exists_root_residue_one` via `Splits.eval_eq_prod_roots`, and `noCancellation` from multiplicativity of the Gauss norm. Also `rv_eq_iff`, Remark 3.1's first half. | (C) 3.2 |
| `RV_henselian.lean` | the `RV` sort over a Mathlib `Valuation K Γ₀`; `rv_eq_iff : rv x = rv y ↔ v (x-y) < v x` and the leading-term calculus (`rv_add_of_lt`, `rv_poly_eval_eq_of_lt`, `v_add_lt_iff`); `residueFieldUnitsEquivKernel : (ResidueField 𝒪)ˣ ≃* ker vrv`; and **`instHenselianLocalRing : HenselianLocalRing ↥(v.valuationSubring)`** for `[IsAlgClosed K]` — absent from Mathlib — with `exists_root_of_eval_lt_one` and `exists_root_rv_eq`. Trap recorded: `rv (-x) = rv x` fails in residue characteristic `≠ 2`. | (C) henselian step |
| `Lemma37_transcendental.lean` | **Lemma 3.7 complete**: `e_transc` (maximum term value), `value_mem_of_adjoin`, `zpow_notMem_valueGroup` giving `Γ(⟨Ŝ,e⟩) = Γ(Ŝ) ⊕ ℤ·vv(e)`, and the value half of 3.8 (`value_transfer` with `_sum`, `_eq_one` = (★), `_adjoin`). **Non-vacuity**: in `ℚ(X)` at infinity, `v (X+1) = v (X+2)`. | (C) 3.7–3.8 |
| `Lifting_transcendental.lean` | Lemma 3.8 and Lemma 3.3's group core over an arbitrary `Valuation K Γ₀`: `value_eval₂`; `lift_value_full` (values **and** the `rv`-relation transfer from `F(e)` to `F'(d)`); `leading_index_transfer` (`RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv(e)⟩`); `divHull` with its universal property. | (C) 3.3, 3.7–3.8 |
| `Semantics_saturation.lean` | the semantic half of Remark 3.1: `embedding_realize_isQF` (QF preserved by embeddings — Mathlib has only the `EquivLike` version), `realize_iff_of_hasQE` (QE makes monomorphisms from substructures partial elementary; model completeness), `IsSaturated κ`, `exists_extension_of_saturated_succ`. | (A)/(B) semantics |
| `Reduction_Lv.lean` | **the full chain of Section 3**, with the two-sorted `L_v` defined in the frozen tagged style (VF ring language, Γ-sort with `0,1,⊤,+,−,≤`, `vv : VF → Γ∪{∞}`). `theorem_2_3_quantifier_elimination (IsSat) (hWeis) (hQEtoEmb) (hRemark31) (hProp39) (hShoenfield) : HasQE Axioms.ACVF`. `Weispfenning : Prop`; `HasQE.mono`; `Language.Embedding.ofIsExpansionOn` for Remark 3.1. | (A) + (D) as hypothesis |
| `Reduction_assembly.lean` | a second, independent reduction: `theorem_2_3_of_hypotheses (hShoen : ShoenfieldTest) (hAlg : AlgIngredients) : HasQE ACVF`, with `prop39`, the exhaustion of `K(M)` by Zorn (`exists_vf_all`, via `DirectLimit.partialEquivLimit`), and `AlgIngredients.rv` recording that `RV = rv(VF) ∪ {0}` is **not** derivable from the frozen axioms (see `../Milestone0/DECISION.md`, twelfth defect). | (A) |
| `BackAndForth.lean` | the general model theory that `Reduction_assembly.lean` uses | (A) |

| `Bounded_compactness.lean` | **`QFExDetermined → QEExStep`, the compactness argument carried out in `BoundedFormula α n`.** `toFormula : BoundedFormula α n → Formula (α ⊕ Fin n)` has no converse, so a finite set of `Formula`s in its image is pulled back by `Finset.attach` plus choice and the witness is pushed forward again — no inverse needed. Proves `exists_realize_bounded` (compactness for bounded formulas), `lifsup`/`liinf` with their `IsQF` and realization lemmas, `exists_qf_imp_bounded` (isolation), and **`qeExStep_of_qfDet`**: the cover — if no finite set of quantifier-free consequences covered `θ.ex`, compactness would give a tuple satisfying `θ.ex` and falsifying every quantifier-free consequence, contradicting isolation. | (B) the join |
| `QE_step_induction.lean` | **the syntactic half of the join**: `QEExStep T` (one existential over a quantifier-free formula is removable) is *equivalent* to full bounded-formula QE — `hasQEb_iff_QEExStep`, `QEAllStep_iff_QEExStep` — and gives `HasQE` in the frozen shape (`HasQE_of_QEExStep`). What is missing to close the join is `QFExDetermined → QEExStep`, blocked concretely: `BoundedFormula.toFormula : BoundedFormula α n → Formula (α ⊕ Fin n)` has no converse in Mathlib, and the compactness argument produces the `Formula` side. See the file header. | (B) the join, syntactic half |
| `QF_type_bridge.lean` | **the compactness step, for arbitrary `L` and `T`.** `hasQE_of_qf_type`: if a quantifier-free type determines every formula across models of `T`, then `HasQE T` in the frozen shape — isolate a QF `ψ` with `T ⊨ᵇ (ψ ⟹ φ)` per tuple, cover `φ` by finitely many such `ψ` (otherwise compactness gives a tuple satisfying `φ` and falsifying every QF consequence), and `⨆ψ` is QF and equivalent to `φ`. Also `qf_type_of_hasQE` and the equivalence `hasQE_iff_qf_type`. Saturation-free. | (B) compactness |
| `Johnson_criterion.lean` | **Johnson's Lemma 2.1.4**, proved in the semantic form his argument produces: `qfDetermined`, from `T₀ ⊆ T`, `HasPrimeModels`, `HasAmalgamation` and `OneECIn`. The proof is the paper's diagram: prime model `S'` over the base, embedded into both `M` and `N`, amalgamated into `D`, formula pushed along `gN ∘ e` by `isQF_subst`, truth transferred across `kM` by `embedding_realize_isQF`. Definitions `OneECIn`, `HasPrimeModels`, `HasAmalgamation` are stated, not assumed in conclusions. Also `embedding_realize_isQF` and `IsQF.subst`. | (B) the criterion |
| `ACF_validation.lean` | **the criterion exercised on ACF.** `oneEC_field_acf` (Claim 2.1.5 hard half: term-to-polynomial translation, finite root sets inside `K`, `IsQF.recOn`, infinitude of `K`), `amalgamation_field` (tensor product), `primeModels_over_field_model`, hence `acf_qfDetermined`: over any base **field** `E`, a one-variable QF formula has the same existential theory in any two algebraically closed fields containing `E`. `acf_qfDetermined_general` is the same over arbitrary `S`, conditional on `HasPrimeModels`. **This is the semantic content, not syntactic QE** — the compactness step to `HasQE acf` is not done. | (B) validation |
| `PrimeModels_partial.lean` | partial: `ker_lift_eq` — two embeddings of an abstract `S` into fields have the same polynomial relations. The core of "`Frac(S)` prime over `S`"; the assembly is not done. | (B) partial |
| `Lemma35_divisible_hull.lean` | **the value-theoretic core of Yin's Lemma 3.5** (`lift:divisible:hull`), the radical case of Proposition 3.9. `IsSeparated v e n` renders Yin's `v (e^i) ∉ Γ(S)` for `0 < i < n` elementwise; then `exists_leading_term` (a nonzero `Σ_{i<n} b_i e^i` has the value of exactly one term), `linearIndependent_pow`, `same_rv_class`, `irreducible_X_pow_sub_C` and `natDegree_le_of_eval₂_eq_zero` (the degree count and irreducibility the source asserts), and `exists_valued_image` — Claim (★) in value form: every element of `K(e)` matches an element of `N` with the same value and vanishing. Reuses `RV_henselian.lean` and Chevalley. | (C) 3.5 |
| `PrimeModels_valued.lean` | **Johnson 2.1.4 hypothesis (i)** for `T₀` = valued fields in `L_val`: `prime_models_over_substructures` and the diagram completion `prime_model_property`. `vFrac` extends a faithful valuation to `FractionRing R`, and `vFrac_le_iff_of_le_iff` shows the *predicate* on `R` determines the relation on `Frac R` — Johnson's "the binary predicate uniquely determines the valuation structure". `exists_lift`/`lift_unique` give the universal property. Also defines `L_val` (`Language.val`) and proves `isValEmb_iff_embedding`. | (B) hypothesis (i) |
| `Johnson23_valuation.lean` | **the valuation-theoretic half of §2.3.** Lemma 2.3.6 complete: `valueGroup_dlo` (divisible, dense, no least or greatest), `exists_pow_val_eq`, and `Infinite (ResidueField 𝒪)` via a **second, independent proof** of `isAlgClosed_residueField` (monic lift along `exists_monic_map_eq`, split over `K`, `v (f.coeff 0) = ∏ v aᵢ ≤ 1`) — the statement `Milestone0/accepted/ResidueField.lean` proved by a different route. Also Lemma 2.3.5 (`subset_residueClass_of_isBall`), the closed/open ball comparability, and Lemma 2.3.7 in the `B = O` case. **Trap recorded**: multiplicatively `∃x, v x < 1` is trivial via `v 0 = 0`; nontriviality must be `∃x ≠ 0, v x < 1` or `∃x, 1 < v x`, and closed balls are the `≤` ones. | (B) §2.3 inputs |
| `Amalgamation_reduced.lean` | **§2.2 down to one ring-theoretic statement.** `chevalley_subring` and `chevalley_hom'` (Lemma 2.2.1(1),(2) in the primes `q ⊆ p` form); `valuedEmbedding_of_localHom` with `fracLift_*` (Remark 2.2.2); `isValEmbedding_of_mem_iff` — **`L_val`-embeddings are exactly injective ring homs with `x ∈ O ↔ f x ∈ O'`**, so QF `L_val`-types are the theory of the valuation ring; `valExtension_of_fieldExtension` (Corollary 2.2.3); and `amalgamation_of_ring_amalgamation` — Lemma 2.2.7 **relative to** the flatness statement ★, which is where 2.2.4–2.2.6 live. | (B) hypothesis (ii), modulo ★ |
| `Chevalley_full.lean` | **Chevalley's lemma and Johnson's Corollary 2.2.3.** `exists_valuationSubring_comap_eq : ∃ V : ValuationSubring L, V.comap (algebraMap K L) = v.valuationSubring` — the contraction, hence `O \ m = Vˣ ∩ O` and `m = m_V ∩ O`; `exists_hasExtension` — a valuation extends along **any** field extension, no finiteness or separability; `exists_hasExtension_domination` — order and `< 1` both preserved, the form §2.2 uses; `chevalley (R : Subring L) (p : Ideal R) [p.IsPrime]` — Lemma 2.2.1(1) in full; `exists_algClosed_nontrivial` — every nontrivially valued field embeds in a model of ACVF (Theorem 2.0.1(2)). Built on `IsLocalRing.exists_factor_valuationRing`. | (B) amalgamation input |
| `Chevalley.lean` | **superseded by `Chevalley_full.lean`**, kept for the record: the containment half only (`exists_valuationSubring_le_of_algebra`), with a header arguing the contraction half needs the maximal-ideal argument. It does — the argument was available as `IsLocalRing.exists_factor_valuationRing`. | (B) — superseded |

## Duplication and coherence

- `Lemma37_transcendental.lean` and `Lifting_transcendental.lean` are **independent**
  formalisations of overlapping lemmas (one over `Valuation` with an `Algebra` frame, the other
  over a `Subfield`), and neither imports the other. Agreement between them is stronger evidence
  than either alone.
- `Reduction_Lv.lean` and `Reduction_assembly.lean` are two reductions with different hypothesis
  sets. They have **not** been compared, and `VFGenerated ↔ IsVFGen` is an unproved coherence
  obligation between them.

## The next campaign's route

Layer (B) was attacked twice — Shoenfield's test needing saturation, and a syntactic
one-quantifier criterion — and both stalled, the second because Mathlib has no model-theoretic
saturation to build on. The next run replaces the criterion rather than patching it.

**Will Johnson, *Fun with Fields*, Chapter 2** (`https://math.berkeley.edu/~willij/drafts/will-thesis.pdf`,
extracted to `.ultramath/refs/johnson-ch2.txt`). His Lemma 2.1.4 needs **no saturation**:

> Let `T₀` have prime models over substructures and the amalgamation property. If the 1-ec
> models of `T₀` form an elementary class axiomatized by `T`, then `T` has QE.

Applied with `T₀` = valued fields in the one-sorted `L_val` (ring language plus the predicate
`v(x) ≤ v(y)`) and `T` = ACVF:

| Step | Content | Mathlib support |
| --- | --- | --- |
| prime models over substructures | fraction field, valuation determined by the predicate | `RatFunc`-level constructions exist |
| amalgamation (§2.2) | Chevalley's lemma plus tensor products of valuation rings | **`Valuation.LocalSubring.exists_le_valuationSubring`** — every local subring sits in a valuation ring — is the heart of Chevalley |
| 1-ec = ACVF (§2.3) | QF definable sets over an algebraically closed base are Boolean combinations of balls; swiss cheeses; "no ball is a finite union of proper subballs" | [`../Milestone0/Balls.lean`](../Milestone0/Balls.lean) already has the C-relation and ball nesting |
| validation | **ACF through the same criterion**, one page in §2.1 | — |

Everything in the files above stays valid under this route: (C) is needed for the `L_RV`
transfer either way.

