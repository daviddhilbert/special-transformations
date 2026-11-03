# Accepted artifacts from the model-building runs

Each file here is **self-contained** (`import Mathlib` only) and is a *snapshot* of
`Milestone0/Encoding.lean` at the commit named in its header, with one piece of
mathematics added and proved. They are not modules of the `SpecialTransformations`
library, they do not import each other, and several of them contain private copies of
the same definitions — that is deliberate: they are evidence, not code to be linked.

`make accepted` elaborates all of them.

| File | What it proves | Encoding snapshot |
| --- | --- | --- |
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

The repairs themselves are recorded, with the reasoning, in `../DECISION.md`.
