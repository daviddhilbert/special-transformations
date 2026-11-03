# Plan: Theorem 2.3 — quantifier elimination for `ACVF`

The paper's headline result, and the engine behind Theorem 2.8 (C-minimality). This file
records how it is proved, what it needs, and where it lands in the formalization. It is not
one of the six milestones in `HANDOFF.md`; those cover the paper's Sections 4–10. QE is a
cross-cutting prerequisite that the milestone plan only ever asked to *state*.

## What the paper actually does

Yin does not induct on formulas. `qe.tex` §3 proves QE for `ACVF` in `L_RV` by
**Shoenfield's test**, and confines the mathematics to a transfer from the two-sorted
`L_v`:

| Reference | Content |
| --- | --- |
| Remark 3.1 (`L:v:and:L:RV`) | `L_RV` is an expansion of `L_v` (sorts VF and Γ, map `vv`); two valued fields are monomorphic as `L_RV`-structures iff as `L_v`-structures; a monomorphism with **VF-generated** domain extends when the target is saturated — *by Weispfenning's theorem* (`weis:qe`: `ACVF` in `L_v` admits QE), which the paper cites and does not prove |
| Lemma 3.2 (`rv:root:lift:vf`) | a root in `RV` of an `RV`-polynomial whose coefficients are `rv(b_i)` lifts to a root in `VF` |
| Lemma 3.3 (unnamed) | builds `S*` with `VF(S*) = VF(S)`, `K(S*) = K(M)`, `Γ(S*)` the divisible hull of `Γ(S)` |
| Lemmas 3.4–3.8 (`lift:all:root`, `lift:divisible:hull`, `lift:transcendental`, `e:transc`, `lift:value:full`) | the case analysis removing the VF-generated hypothesis |
| Lemma (`lift:any:sec`) | extends `f` over one new `RV`-element |
| Proposition 3.9 (`lrv:mono:lift`) | every monomorphism of substructures extends to `M → N` |
| Theorem 3.10 (`qe:acvf`) | `ACVF` in `L_RV` admits QE — Shoenfield's test applied to 3.9 |

The author describes the argument as "elementary and self-contained except some fundamental
facts in the theory of valued fields". Those facts are Weispfenning's theorem.

## The dependency chain, and what exists here

| Layer | Status |
| --- | --- |
| The statement to prove | **exists**: `Milestone0/Encoding.lean`, `theorem_2_3_quantifier_elimination : HasQE ACVF := by sorry`, with `HasQE T := ∀ α φ, ∃ ψ, ψ.IsQF ∧ T ⊨ᵇ (φ ⇔ ψ)` |
| (A) Reduction `HasQE_Lv → HasQE ACVF` | **this is the target.** Yin's Theorem 3.10 modulo Weispfenning |
| (B) A QE criterion (Shoenfield / back-and-forth / extension pairs) | **missing**. Mathlib has no model-theoretic saturation (`rg -i saturat Mathlib/ModelTheory` is empty) and no QE notion; the `HasQuantifierElimination` stack (#40561, #41112–#41116) is unmerged. `PartialEquiv`, `ElementaryEmbedding` and compactness are present |
| (C) Lemmas 3.2–3.8 | **missing**, but algebraic; `RVModel.lean` and `accepted/ResidueField.lean` supply `rv`, `vrv`, `𝒪`, `𝔪`, `K^× ≃* k^×` |
| (D) Weispfenning: QE for `ACVF` in `L_v` | **out of scope by decision.** Left as an explicit Lean `Prop` hypothesis, never an axiom |

## Where it inserts

```
SpecialTransformations/QE/Criterion.lean   -- (B)
SpecialTransformations/QE/Valued.lean      -- L_v and ACVF in it
SpecialTransformations/QE/Lifting.lean     -- (C), Lemmas 3.2-3.8
SpecialTransformations/QE/Main.lean        -- (A): HasQE_Lv -> HasQE ACVF, filling the sorry
```

`Main.lean`'s headline replaces the `sorry` at `theorem_2_3_quantifier_elimination` in
`Encoding.lean`, and `SpecialTransformations/Main.lean`'s status table moves Theorem 2.3 from
*not started* to proved-modulo-Weispfenning.

## Payoff

Theorem 2.8 (C-minimality) is a corollary: QE reduces a definable subset of `VF` to a
quantifier-free formula, and quantifier-free `L_RV`-formulas define Boolean combinations of
balls. `Milestone0/Balls.lean` already has the C-relation `v (y-z) < v (x-y)` with its four
axioms and the ball nesting lemmas, so that half is not starting from zero.

## Honest scale

Layer (D) is the largest single item in the whole formalization and is not formalized in any
proof assistant that I could find. The reduction (A) with (C) proved is a real theorem about
the paper's argument and is the point of the current run; it is *not* Theorem 2.3 itself.
