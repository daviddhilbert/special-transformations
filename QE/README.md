# Theorem 2.3 — quantifier elimination: accepted artifacts

Artifacts of the QE campaign, below `QE-PLAN.md`'s four-layer breakdown. Each file is
self-contained (`import Mathlib` only), is a snapshot of `Milestone0/Encoding.lean` at the
commit named in its header where it uses the encoding at all, and is evidence rather than
library code. `make qe` elaborates all of them.

| File | What it proves | Layer |
| --- | --- | --- |
| `Lemma37_transcendental.lean` | **Lemma 3.7 complete**, plus the value half of Lemma 3.8. `e_transc` gives the maximum term value (`∃ j, v b = v (b_j e^j)` for `b = Σ b_i e^i ≠ 0`), `e_transc_aeval` its polynomial form, `value_mem_of_adjoin` puts every unit of `K(e)` in `v a · (v e)^n`, and `zpow_notMem_valueGroup` gives `Γ(⟨Ŝ,e⟩) = Γ(Ŝ) ⊕ ℤ·vv(e)`. `value_transfer` and its `_sum`, `_eq_one` (claim (⋆)) and `_adjoin` variants transfer values across a value-preserving `σ` with `w d = v e`; `infiniteOrderMod_of_divisible` connects to Lemma 3.8's divisibility hypothesis. **Non-vacuity**: in `ℚ(X)` with the valuation at infinity, `K = ℚ`, `e = X`, `d = X+1`, the hypotheses hold simultaneously and `v (X+1) = v (X+2)`. | (C) Lemmas 3.7–3.8 |
| `Lifting_transcendental.lean` | Lemma 3.8 (`lift:value:full`) and Lemma 3.3's group core, over an arbitrary `Valuation K Γ₀`. `value_eval₂` is Lemma 3.7's no-cancellation formula; `lift_value_full` transfers the value of every `p(e)` **and the `rv`-relation** `v (p(e) - a·q(e)) < v (p(e))` from `F(e)` to `F'(d)`; `leading_index_transfer` gives `RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv(e)⟩`; `divHull` with its universal property `divHull_le` is the divisible hull of `Γ(S)` that Lemma 3.3's `S*` needs. | (C) Lemmas 3.3, 3.7–3.8 |

`Reduction_Lv.lean` and `Reduction_assembly.lean` are **two independent reductions** of Theorem 2.3
in the frozen encoding, with different hypothesis sets; they have not been compared, and
`VFGenerated ↔ IsVFGen` is an unproved coherence obligation between them.

`Lemma32_root_lifting.lean` and `Lifting_transcendental.lean` are **independent formalisations of the same lemmas** — one over `Valuation K Γ₀`
with an `Algebra` frame, the other over a `Subfield` of the ambient field — and neither imports
the other. Agreement between them is stronger evidence than either alone.

| `Reduction_Lv.lean` | **the full chain of Section 3**, with the two-sorted `L_v` defined (in the frozen tagged style: VF ring language, a Γ-sort with `0,1,⊤,+,−,≤`, and `vv : VF → Γ∪{∞}`). Headline: `theorem_2_3_quantifier_elimination (IsSat) (hWeis) (hQEtoEmb) (hRemark31) (hProp39) (hShoenfield) : HasQE Axioms.ACVF` — Weispfenning, QE ⟹ extension property, Remark 3.1, Lemmas 3.2–3.8, Shoenfield's test, each a named hypothesis and none an axiom. `LvTwo.Weispfenning : Prop := HasQE ACVF` with `HasQE.mono`; `Language.Embedding.ofIsExpansionOn` makes Remark 3.1's language claim a theorem. | (A) + (D) as hypothesis |
| `Reduction_assembly.lean` | **the reduction.** `theorem_2_3_of_hypotheses (hShoen : ShoenfieldTest) (hAlg : AlgIngredients) : HasQE ACVF` in the frozen encoding. Proves Proposition 3.9 (`prop39`), the exhaustion of `K(M)` by Zorn on partial equivalences (`exists_vf_all`, via `DirectLimit.partialEquivLimit`), and Theorem 3.10 from Shoenfield's hard direction. Hypotheses: `ShoenfieldTest` (Prop 3.9 ⟹ QE), `AlgIngredients.rv` (`RV = rv(VF) ∪ {0}`, **not derivable from the frozen axioms** — see `../Milestone0/DECISION.md`), `.prep` (Lemma 3.3 + henselization), `.one` (Lemmas 3.4–3.8), `.vfgen` (Remark 3.1 + Weispfenning). | (A) reduction |
| `BackAndForth.lean` | the general model theory it uses | (A) |

| `Lemma32_root_lifting.lean` | **Yin's Lemma 3.2** (`rv:root:lift:vf`), in full generality and with no unproved input: given `F ≠ 0`, `b ≠ 0`, a set `I ⊆ supp F` with `2 ≤ |I|`, `v (F.coeff i · b^i) = 1` on `I`, `< 1` off `I`, and `v (Σ_{i∈I} F.coeff i · b^i) < 1` (the rendering of `F̄(t) = 0`), there is `b'` with `rv b' = rv b` and `F b' = 0`. Method is not the Newton polygon: `exists_root_residue_one` (root of valuation `1`, via `Splits.eval_eq_prod_roots`) plus `noCancellation` (multiplicativity of the Gauss norm plus `v_sub_eq_max`). Also `rv_eq_iff : rv v x = rv v y ↔ v x = v y ∧ v (x/y - 1) < 1`, Remark 3.1's first half. | (C) Lemma 3.2 |
| `Semantics_saturation.lean` | the semantic half of Remark 3.1. `embedding_realize_isQF`: quantifier-free formulas are preserved by **embeddings** (Mathlib has only the `EquivLike` version). `realize_iff_of_hasQE`: QE makes every monomorphism from a substructure of a model partial elementary, with model completeness as a corollary. `IsSaturated κ` as a definition, and `exists_extension_of_saturated_succ`: a `κ`-saturated `N` matches any `n` further elements of `M`, the tuple type being finitely satisfiable — the only use of QE in the argument, entering through `exs`. | (A)/(B) semantics |

## What is not here yet

Nothing of layer (A) (the reduction), (B) (the criterion), or (D) (Weispfenning, which is a
hypothesis by decision). See `../QE-PLAN.md`. In particular `Milestone0/Encoding.lean` still
carries `theorem_2_3_quantifier_elimination : HasQE ACVF := by sorry`; no accepted artifact
discharges it.
