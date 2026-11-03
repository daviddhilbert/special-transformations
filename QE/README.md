# Theorem 2.3 — quantifier elimination: accepted artifacts

Artifacts of the QE campaign, below `QE-PLAN.md`'s four-layer breakdown. Each file is
self-contained (`import Mathlib` only), is a snapshot of `Milestone0/Encoding.lean` at the
commit named in its header where it uses the encoding at all, and is evidence rather than
library code. `make qe` elaborates all of them.

| File | What it proves | Layer |
| --- | --- | --- |
| `Lifting_transcendental.lean` | Lemma 3.8 (`lift:value:full`) and Lemma 3.3's group core, over an arbitrary `Valuation K Γ₀`. `value_eval₂` is Lemma 3.7's no-cancellation formula (`v (p(e))` is the sup of the term values) for `e` of infinite order modulo `Γ(F)`; `lift_value_full` transfers the value of every `p(e)` and the `rv`-relation `v (p(e) - a·q(e)) < v (p(e))` from `F(e)` to `F'(d)` when `σ : F ≃+* F'` preserves the valuation and `w d = v e`; `leading_index_transfer` gives `RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv(e)⟩`; `divHull` with its universal property `divHull_le` is the divisible hull of `Γ(S)` that Lemma 3.3's `S*` needs. | (C) Lemmas 3.2–3.8 |

## What is not here yet

Nothing of layer (A) (the reduction), (B) (the criterion), or (D) (Weispfenning, which is a
hypothesis by decision). See `../QE-PLAN.md`. In particular `Milestone0/Encoding.lean` still
carries `theorem_2_3_quantifier_elimination : HasQE ACVF := by sorry`; no accepted artifact
discharges it.
