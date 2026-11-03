# Accepted artifacts from the model-building runs

Each file here is **self-contained** (`import Mathlib` only) and is a *snapshot* of
`Milestone0/Encoding.lean` at the commit named in its header, with one piece of
mathematics added and proved. They are not modules of the `SpecialTransformations`
library, they do not import each other, and several of them contain private copies of
the same definitions — that is deliberate: they are evidence, not code to be linked.

`make accepted` elaborates all of them.

| File | What it proves | Encoding snapshot |
| --- | --- | --- |
| `ACVFModel.lean` | **`ACVF` has a model.** `model_ACVF : (M K) ⊨ Axioms.ACVF` and `exists_model_ACVF : ∃ M, M ⊨ ACVF` at `K = ℂ`, on `M K = K ⊕ RV₀ K` with the trivial valuation; also `model_ACVF00`. So the theory is consistent and Theorems 2.3 and 2.8 are **not vacuous**. | `d608de6` — the current axioms, byte-identical apart from `def`→`abbrev LRV` and the two `sorry`ed targets |
| `ACVF_general_model_gamma.lean` | **the milestone.** The general model (as below) together with `exists_model_ACVF_nontrivial_gamma_padic`: at `ℂ_[p]`, `M ⊨ ACVF` and an element of `RV^×` outside the class of `1`, witnessed by `rv p` since `v p = 1/p ≠ 1`. And `milestone_model_with_nontrivial_gamma`: `∃ M S, M ⊨ ACVF ∧ Γ(S)` nontrivial in the non-vacuous reading (take `S = ⊤`). Plus `not_model_ACVF_S_padic` for every `S`, and `gamma_reading_vacuous` reconfirming that the loose `Γ(S)` predicate is vacuous. | `d608de6` |
| `ACVF_general_model.lean` | **the general model.** `model_ACVF [IsAlgClosed K] (v : Valuation K Γ₀) : (C v) ⊨ Axioms.ACVF` — all eight summands at `C v = K ⊕ RV v` for an **arbitrary** valuation, with `kAdd`/`kNeg` the residue-field operations transported through `KUnits ≅ k^×` and `rvGroup` including the divisibility scheme. **Converted to the one-element `RV`** (`rvZero = cKZero = cInfty = Sum.inr none`, `model_rvSurj` from `RVM.rv_surjective` in the paper's form), so this is the model-theoretic witness that the corrected transcription is the paper's theory: `0 = ∞` in the intended model, and every block of `ACVF` holds there. `model_ACVF00` needs `[CharZero K]` and `∀ n ≠ 0, 1 ≤ v n`, which fails at `ℂ_[p]`. | `d608de6` |
| `ACVF_residue_ops.lean` | the same six summands at `C v`, but with `kAdd`/`kNeg` interpreted by the **real residue-field operations**, transported along `ACVFResidue.kEquiv` (`kOf`, `ofK`, `kOf_ofK`, `ofK_inj`, `iKAdd_ofK`, `iKNeg_ofK`, `iRVMul_ofK`). `model_ACVF_of_components` reduces `(C v) ⊨ ACVF` to exactly `⊨ kField`, `⊨ kAlgClosed`, `∀ k ≥ 1, ⊨ rvDivisible k`. Also `model_residueCharZero_iff k : ⊨ residueCharZero k ↔ 1 ≤ v k` and `padicComplex_not_model_ACVF00`. | `d608de6` |
| `ACVF_gamma_padic.lean` | six of the eight summands of `ACVF` at `C v` for arbitrary `v` (`sortAxioms`, `vfField`, `vfAlgClosed`, `rvGroup`, `preorderRV`, `rvAxioms`), with `ACVF_eq_FRAG_union : ACVF = FRAG ∪ kField ∪ kAlgClosed`; and at `ℂ_[p]` a model of `FRAG ∪ atomicDiagram S` whose substructure `S` has **nontrivial `Γ(S)`** — `∃ t ∈ S, iRV t ∧ t ≠ 0 ∧ t ≠ ∞ ∧ ¬ (1 ≤ t ≤ 1)`, a predicate no trivial valuation can satisfy. Also `not_model_ACVF_S_padic`: `ℂ_[p]` has residue characteristic `p`, so `ACVF(0,0)` fails there for every `S`. | `d608de6` |
| `ACVF_fragment.lean` | four of the eight blocks of `ACVF` at the general carrier `K ⊕ RV₀ v` for an arbitrary valuation, against the **current** `pInK` guard: `sortAxioms` 16/16, `preorderRV` 7/7, `vfField` 10/10, `vfAlgClosed`. `model_ACVF_of_residue_blocks` reduces the rest to `rvGroup`, `rvAxioms`, `kField`, `kAlgClosed`. | `d608de6` |
| `ACVFModel_independent.lean` | the same theorem, reached by an independent re-base: the guard's semantic counterpart is made explicit as `InK z := (∃ u, z = unit u) ∨ z = 0` with `realize_pInK`, instead of the first file's route through the closure lemmas. Two agreeing proofs of the same statement. | `d608de6`, Parts 0–3 byte-identical apart from `def`→`abbrev LRV` |
| `ResidueField.lean` | `isAlgClosed_residueField`: the residue field of an algebraically closed valued field is algebraically closed (not in Mathlib); `K^× ≃* k^×`; the field structure on the paper's `K = K^× ∪ {0}`. | before the guard repairs |
| `VFAlgClosed.lean` | `model_vfAlgClosed`: the algebraic-closedness scheme holds at the intended structure `K ⊕ RV₀ v` for **any** valuation on an algebraically closed `K`; plus `realize_hornerPoly`, the term-evaluation lemma turning `hornerPoly` into the field Horner fold. | `d608de6` |
| `ACVFS_conservative.lean` | `ACVF_S(0,0)` is a conservative, equiconsistent extension of `ACVF(0,0)`: the atomic diagram can never create a contradiction; and `definable_iff_definable_expansion`, which is the paper's Convention 2.5 (parameters = 0-definability in the constant expansion). | `dfef4ca` |
| `IntendedModel.lean` | the tagged structure on `K ⊕ RV₀ v` with its unfolding toolkit; `sortAxioms` complete, all ten `vfField` sentences, all five `rvAxioms`, six `rvGroup` sentences and four `preorderRV` sentences hold at it. | `acf79f6` |
| `RepairedTheory.lean` | **converted to the one-element `RV`.** The old obstruction to `0 = ∞` is analysed and shown to be a symptom of the two-constant transcription; `zero_ne_infty` and `zero_eq_infty_imp_false`, whose statements deny the convention, are **removed rather than weakened**, and replaced by `zero_eq_infty : iRVZero = iRVInfty := rfl` and `kAlgClosed_lin_unit` (the linear instance of `kAlgClosed` with the root in `K`, consistent because `K = K^× ∪ {0}` contains the absorbing element). Also records why the `K`-guards must be `pInK` and not `pK`: `pK`-guarded `sdKAdd` would contradict the linear instance. | current encoding (one constant, `rv` surjective) |
| `Obstruction.lean` | the negative result that forced the first repair: every `L_RV`-structure satisfying the old `kField` axioms identifies the residue zero with `∞`, so the intended carrier modelled no such theory. | before the guard repairs |

Two of them (`ResidueField.lean`, `Obstruction.lean`) are snapshots of axioms that have
since changed; they are kept because their *theorems* are about the mathematics, not
about the encoding — the residue field being algebraically closed, and the fact that
`K^×` must not be confused with `RV ∖ {0, ∞}`.

`ACVFModel.lean` and `ACVFModel_independent.lean` are the exception: they carry the
current axioms, and they are the files that answer the question the others were building
toward — whether the theory has a
model at all. They model the trivial valuation, so the value group is trivial; they settle
consistency and non-vacuity of `ACVF` and `ACVF(0,0)`, but they are not models of
`ACVF_S(0,0)` under the paper's standing hypothesis that `Γ(S)` is nontrivial.

The repairs themselves are recorded, with the reasoning, in `../DECISION.md`.
