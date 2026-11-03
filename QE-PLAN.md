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

## Route change (current)

The criterion in layer (B) was attacked twice and both attempts stalled: Shoenfield's test needs
saturated models, which Mathlib does not have, and a purely syntactic one-quantifier criterion
could not be closed. The campaign now follows **Will Johnson, *Fun with Fields*, Chapter 2**
(`https://math.berkeley.edu/~willij/drafts/will-thesis.pdf`, text at
`.ultramath/refs/johnson-ch2.txt`), whose Lemma 2.1.4 is saturation-free:

> Let `T₀` have prime models over substructures and the amalgamation property. If the 1-ec
> models of `T₀` form an elementary class axiomatized by `T`, then `T` has QE.

with `T₀` = valued fields in the one-sorted `L_val` (ring language plus `v(x) ≤ v(y)`) and
`T` = ACVF. Its three inputs are: prime models over substructures (fraction field), amalgamation
(Chevalley's lemma, for which Mathlib's `Valuation.LocalSubring.exists_le_valuationSubring`
supplies the heart), and 1-ec = ACVF via ball combinatorics, which `Milestone0/Balls.lean`
already covers. The validation is **ACF**, proved through the same criterion in the same chapter.

Layer (C), Yin's Lemmas 3.2–3.8, remains necessary under this route too: Johnson gives QE in
`L_val`, and moving it to the paper's `L_RV` still goes through Remark 3.1 and the lifting
lemmas.

## Honest scale

Layer (D) is the largest single item in the whole formalization and is not formalized in any
proof assistant that I could find. The reduction (A) with (C) proved is a real theorem about
the paper's argument and is the point of the current run; it is *not* Theorem 2.3 itself.

## State after the Johnson campaign (update)

The criterion in layer (B) no longer needs saturation. `QE/ACF_HasQE.lean` proves, generic in
`L : Language.{0,0}`,

```
hasQE_of_johnson : T₀ ⊆ T → HasPrimeModels T₀ T → HasAmalgamation T₀ →
  (∀ M N, M ⊨ T → OneECIn (f : M ↪[L] N)) → QECriterion.HasQE T
```

from `JohnsonCriterion.qfDetermined` + `QE/H_of_qfDetermined.lean` (the last mile `H`) +
`hasQE_of_qfDet` (compactness). Instantiated at `T₀ = Theory.field`, `T = acf` it gives
`HasQE acf` unconditionally, in the frozen shape; the three hypotheses are discharged by
`QE/PrimeModels_full.lean` (prime models: `Frac (FreeCommRing S ⧸ ker (FreeCommRing.lift e))`),
`amalgamation_field` (tensor products) and `oneEC_field_acf`.

So layer (A) is now reachable in two steps, neither of them Shoenfield's:

1. **QE in `L_val`** by `hasQE_of_johnson` at `L = Language.val`, `T₀` = valued fields,
   `T` = nontrivially valued algebraically closed fields. Hypotheses: (i) prime models —
   `QE/PrimeModels_valued.lean` has the mathematics (`vFrac`, `prime_model_property`) and needs
   repackaging into `HasPrimeModels`; (ii) amalgamation — `QE/Amalgamation_reduced.lean` modulo
   ★ alone (Johnson 2.2.4/2.2.6 on `O₁ ⊗_{O₀} O₂`); (iii) 1-ec — Johnson §2.3, where
   `QE/Johnson23_valuation.lean` now has 2.3.4, 2.3.5, 2.3.6, 2.3.7 in full generality, ball
   comparability, and the cell decomposition behind 2.3.2; missing are `cell_swissCheese`
   (normalising a cell's complement family to subballs), 2.3.1, 2.3.3, 2.3.8, 2.3.9.

2. **The transfer `L_val → L_RV`.** The paper's Theorem 2.3 is stated in `L_RV`
   (`paper.tex:509`, quoting `qe.tex` Theorem 3.10), so QE in `L_val` alone does not discharge
   it. Three routes, and why the obvious one is not the paper's:

   * **(T1) Syntactic translation.** Show that every `L_RV`-formula is `ACVF`-equivalent to an
     `L_val`-formula, and every quantifier-free `L_val`-formula to a quantifier-free
     `L_RV`-formula. Then QE in `L_val` gives QE in `L_RV` by composition. The translation
     works term by term: `rv` is multiplicative, so an `RV`-term built from `rv(F_i(X))`,
     `RV`-parameters and products is `rv` of a `VF`-term once the parameters are named; the
     `RV`-literals become `v s ≤ v t` (`rv s ≤ rv t`) and `v (s - t) < v s` (`rv s = rv t`);
     and a quantifier over `RV` becomes `y = 0 ∨ ∃ x (VF), y = rv x`. **The last step is
     exactly the surjectivity of `rv` onto `RV ∖ {0}` — the twelfth encoding defect
     (`Milestone0/DECISION.md`)**: the frozen `rvSurj` is guarded by `pUnits` and only reaches
     the class of `1`, so the frozen axioms do not presently give it. Either derive it in the
     theory (it may follow from the multiplicativity/ordering axioms plus the `pUnits` form),
     or repair the guard — which changes the frozen hash and requires re-verifying
     `Milestone0/accepted/` and every `QE/` snapshot that embeds it. That decision is
     recorded, not taken.
   * **(T2) Johnson directly in `L_RV`.** The criterion is generic, so it applies to the frozen
     language as it stands. The junk problem that blocks Yin's Remark 3.1 does *not* hit
     hypothesis (i): `HasPrimeModels` only quantifies over `S` that embed into a model, and a
     model of `ACVF` has no `RV`-element outside `rv(VF) ∪ {0}`. It does make (i) itself harder
     (the prime model must be built in the tagged one-sorted language) and replaces (iii) by
     the `RV`-definable version, i.e. Yin §4's C-minimality analysis rather than §2.3.
   * **(T3) Yin's route** (`qe.tex` §3): Shoenfield's test with saturated models plus
     Weispfenning's QE in `L_v`. Dead here: Mathlib has no model-theoretic saturation, and it
     needs `Proposition 3.9` (extension of monomorphisms) whose proof is Lemmas 3.2–3.8.

   Recommendation: (T1), because it uses QE in `L_val` — which step 1 delivers — and reduces
   the remaining work to a term-by-term syntactic translation plus one axiom question, instead
   of an extension theory for monomorphisms.

### The twelfth defect is now the last obstacle, and it may affect the *truth* of the target

**Convention (as the author states it).** There is no separate `0` in `RV`: writing `rv(0) = 0`
makes `0` the absorbing element of `RV`, and the paper's `∞` is then just another name for it —
one distinguished element, not two. Read that way, `RV = RV^× ∪ {rv(0)}` with `RV^×` the
multiplicative group, `K^× ⊆ RV^×` the residue-field units, and `RV^× / K^× = Γ`.

What the frozen encoding does with the two constants (checked in `Milestone0/Encoding.lean`):

* `rvZeroEq : rv (0_VF) = rvInfty`, so **`rvInfty` is `rv(0)`**, the absorbing top
  (`leTop`, `leInftyEq`, `rvMulInfty : t · ∞ = ∞` for all `t`);
* `rvZero` is the residue field's zero, used in `pInK` and in the field axioms on
  `K = K^× ∪ {0}`; `rvMulZeroK` makes it absorbing only for `t ∈ pInK`;
* no axiom distinguishes `rvZero` from `rvInfty`, and none identifies them. In the author's
  convention they coincide, in which case `pRV` (`t ≠ rvZero`) and `pK` (`t ≠ rvInfty`) are the
  same predicate and one of the two constants is redundant.

So the defect, stated in the corrected notation: the frozen axiom is

```
rvSurj : pUnits t → ∃ x (VF), rv x = t        -- rv hits only the residue-field units
```

whereas the paper's Definition 2.2(6) has `rv` **onto `RV ∖ {rv(0)}`**, i.e. onto the value
classes as well. The single missing axiom is

```
rvSurj' : t ≠ rv(0) → ∃ x (VF), rv x = t
```

— one guard, `t ≠ rv(0)` (in the encoding: `t ≠ rvInfty`), with no second symbol. The intended
model satisfies it, since `RV = K^×/(1+𝔪)` is by construction a quotient of `VF^×`.

Two consequences, in increasing order of seriousness:

1. **It blocks (T1).** The translation of an `RV`-quantifier is
   `∃ y (RV), … ↦ y = rv(0) ∨ ∃ x (VF), …[rv x]`, and that needs every `RV`-element other than
   `rv(0)` to be in the image of `rv`. With the frozen guard the translation is not justified.

2. **It may make the frozen `HasQE ACVF` false**, which is the serious one. The frozen axioms
   confine `RV` only through the preorder, the multiplicative structure, `K ⊆ RV` as a field and
   the guard above, so a model plausibly admits **junk**: an element `z ∈ RV` with
   `z ≠ rv(0)`, `¬ pUnits z`, `z ∉ image(rv)` — absorbing (`z · t = z`), in a fresh preorder
   class between `1` and `rv(0)`, with the residue-field operations defined arbitrarily off `K`.
   On such a model the formula

   ```
   φ(x) := ∃ y (VF), rv y = x
   ```

   defines `image(rv) = pUnits ∪ {rv(0)}`, whereas in the intended (junk-free) model it defines
   `RV ∖ {rv(0)}` — and no quantifier-free formula can tell a value class from junk `z`, because
   every quantifier-free test available on `RV` is `pUnits`, `= rv(0)`, `≤`, `·` and the
   operations on `K`. If such a model exists, no quantifier-free `ψ` has `ACVF ⊨ φ ↔ ψ`, i.e.
   the frozen statement is unprovable as frozen.

What settles it, in either direction:

* **a junk model**: a structure on the frozen language with `VF` unchanged and `RV` extended by
  one absorbing element in a fresh preorder class, all axioms checked. This is a mechanical
  (if long) construction, and existing models in `Milestone0/accepted/` give the junk-free part;
* **or an invisibility proof**: that junk is not distinguishable by quantifier-free formulas and
  that `φ` is nevertheless QF-equivalent (this would need `image(rv)` to be QF-definable in every
  model, which is what the defect denies).

Either way the outcome is a decision about the frozen encoding, not about the mathematics: the
paper's theory is junk-free, and the repaired axiom is the paper's own. Note also that the
correct convention (`rv(0)` the only absorbing element) suggests a second, smaller repair: the
encoding's two constants `rvZero` and `rvInfty` should be identified, or at least one of them
kept.
