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
| `ACVF_fragment.lean` | four of the eight blocks of `ACVF` at the general carrier `K ⊕ RV₀ v` for an arbitrary valuation, against the **current** `pInK` guard: `sortAxioms` 16/16, `preorderRV` 7/7, `vfField` 10/10, `vfAlgClosed`. `model_ACVF_of_residue_blocks` reduces the rest to `rvGroup`, `rvAxioms`, `kField`, `kAlgClosed`. | `d608de6` |
| `ACVFModel_independent.lean` | the same theorem, reached by an independent re-base: the guard's semantic counterpart is made explicit as `InK z := (∃ u, z = unit u) ∨ z = 0` with `realize_pInK`, instead of the first file's route through the closure lemmas. Two agreeing proofs of the same statement. | `d608de6`, Parts 0–3 byte-identical apart from `def`→`abbrev LRV` |
| `ResidueField.lean` | `isAlgClosed_residueField`: the residue field of an algebraically closed valued field is algebraically closed (not in Mathlib); `K^× ≃* k^×`; the field structure on the paper's `K = K^× ∪ {0}`. | before the guard repairs |
| `VFAlgClosed.lean` | `model_vfAlgClosed`: the algebraic-closedness scheme holds at the intended structure `K ⊕ RV₀ v` for **any** valuation on an algebraically closed `K`; plus `realize_hornerPoly`, the term-evaluation lemma turning `hornerPoly` into the field Horner fold. | `d608de6` |
| `ACVFS_conservative.lean` | `ACVF_S(0,0)` is a conservative, equiconsistent extension of `ACVF(0,0)`: the atomic diagram can never create a contradiction; and `definable_iff_definable_expansion`, which is the paper's Convention 2.5 (parameters = 0-definability in the constant expansion). | `dfef4ca` |
| `IntendedModel.lean` | the tagged structure on `K ⊕ RV₀ v` with its unfolding toolkit; `sortAxioms` complete, all ten `vfField` sentences, all five `rvAxioms`, six `rvGroup` sentences and four `preorderRV` sentences hold at it. | `acf79f6` |
| `RepairedTheory.lean` | the repaired axioms are no longer inconsistent: the old `0 = ∞` derivation fails at each step, and `zero_ne_infty : M ⊨ ACVF → rvZero ≠ rvInfty` shows the theory now *refutes* the identification. | `acf79f6` |
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
