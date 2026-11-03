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
   `T` = nontrivially valued algebraically closed fields. State of the three hypotheses
   (measured, at commit 1c7ab23):

   **(i) prime models: done.** `QE/PrimeModels_val_partial.lean` (1461 lines, compiles, axioms
   clean) now has the whole chain: the `Language.val` theory `valField`, the `isValPred`
   dictionary, the fraction-field predicate `predFrac` with `predFrac_isValPred`, the coordinate
   ring `coordRing e` with `coordEmbedding`, the prime model `valPrimeField e = FractionRing
   (coordRing e)` with `predVal e`, `valPrimeField_model`, `valPrimeEmbedding`, the universal
   property `valPrimeField_universal`, the bridge `ringStructOfVal` + `model_field_of_valField`
   (a `valField.ModelType` is a field in `L_ring`, which is what the packaging needs), and
   `hasPrimeModels_valField : HasPrimeModels valField valField` with
   `hasPrimeModels_mono : T' ⊆ T → HasPrimeModels T₀ T' → HasPrimeModels T₀ T`.  **Still to
   write: the `L_val` axiomatisation `ACVF_val` of nontrivially valued algebraically closed
   fields** (algebraically closed + nontrivial valuation as `L_val` sentences), then
   `hasPrimeModels_mono h_ACVF_sub hasPrimeModels_valField` gives hypothesis (i).

   **(ii) amalgamation: open.** `QE/Amalgamation_reduced.lean` reduces it to `star` alone, the
   ring-theoretic amalgamation for valuation rings, which is Johnson 2.2.4–2.2.7: `O₁ ⊗_{O₀} O₂`
   is nonzero (torsion-free over a valuation ring is flat), a minimal prime contracts to `0` in
   each factor (2.2.6), a prime over the residue-field tensor contracts to `mᵢ`, and Chevalley
   2.2.1(2) produces the valuation ring of the amalgam.  Johnson's proofs are in
   `.ultramath/refs/johnson-ch2.txt` lines 190–360.  In progress in swarm `smw0fcnxx`.

   **(iii) 1-ec: closed.** `QE/OneEC_val.lean` (4247 lines, compiles, axioms clean) now ends
   with `oneECIn_of_nontrivial : [IsAlgClosed K] → (hnt : ∃ x ≠ 0, w (f x) < 1) → OneECIn F`,
   with no input left: 2.3.1(i) (`finite_rootSet`), the syntax bridge (`termToPoly`), 2.3.1(ii)
   (`atomGood_of_isAlgClosed`, by the cell decomposition over (nearest root, tie set)), 2.3.2
   (`boolCombCheese`), and 2.3.8 (`cheeseMeetsBase`, whose Johnson body 2.3.3/2.3.5/2.3.6/2.3.7
   with `valueGroup_dlo` and `infinite_residueField` now sits in the same file).  The composition
   is `goodMeetsBase_of_nontrivial` fed to `oneECIn_of_inputs'`.  `hnt` is not removable: 2.3.8 is
   false for a trivial valuation.

   Still entirely to write after (i)–(iii): `HasQE (L := Language.val) ACVF_val`.  Everything
   above is at the level of concrete valued fields; `hasQE_of_johnson` wants the abstract
   `L_val`-structures, which the `ringStructOfVal` bridge now makes reachable.

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

## The other assembled route, and why the plan still prefers Johnson's

There are **two** chains in the tree that reduce `HasQE ACVF` (the frozen statement of Theorem 2.3
in `Milestone0/Encoding.lean`) to named hypotheses.  This section records the second one, which
this plan did not mention, so that nobody thinks Johnson's criterion is the only way.

**Yin's own route** — `QE/Reduction_assembly.lean`, `theorem_2_3_of_three`:

```
theorem_2_3_of_three : ShoenfieldTest →
  (∀ M N, M ⊨ ACVF → N ⊨ ACVF → Saturated N → PrepStep)   -- Lemmas 3.3 + henselization
  (∀ M N, … → Saturated N → OneStepVF)                     -- Lemmas 3.4-3.8
  (∀ M N, … → VFGenCase)                                   -- Remark 3.1 + Weispfenning QE in L_v
  → HasQE ACVF
```

The fourth ingredient of `theorem_2_3_of_hypotheses` (`RV = rv(VF^×) ∪ {0}`, the paper's
surjectivity of `rv`) is **discharged** there (`RVeqRvVF_of_model`), which is what the ruling on
`rvSurj` bought.

So Theorem 2.3 has four remaining hypotheses on this route (`ShoenfieldTest`, `PrepStep`,
`OneStepVF`, `VFGenCase`) against three plus a syntactic transfer on Johnson's.  The plan keeps
preferring Johnson's because `ShoenfieldTest` needs model-theoretic saturation, which Mathlib does
not have, whereas on Johnson's route saturation never appears; `PrepStep`, `OneStepVF` and
`VFGenCase` are all stated with `Saturated N` as a hypothesis, so that route cannot be closed
without building saturation.  `VFGenCase` additionally depends on Remark 3.1, i.e. exactly the
`rv`-surjectivity/junk question that the ruling settled on the encoding side but that is not yet
formalised as a transfer lemma.

It is worth knowing that `QE/Reduction_assembly.lean` compiles and that `RVeqRvVF_of_model` is
proved there: if saturation ever becomes available, that route is the shorter one.

## What remains, item by item, with the specific difficulty of each

Written at commit `e6fdc8a`.  The tree compiles: all 47 `.lean` files in `QE/` and `Milestone0/`
have 0 errors, and there are exactly **three** real `sorry`s in it —
`Milestone0/Balls.lean:502` (`infinite_boolComb_contains_openBall`, which Theorem 2.8 needs, not
2.3) and `Milestone0/Encoding.lean:923,930` (`theorem_2_3_quantifier_elimination` and
`theorem_2_8_c_minimal`).

1. **`CheeseMeetsBase`** — **proved** in `QE/CheeseMeetsBase.lean` (commit `eeb827b`,
   swarm `smw0fobjd` member m4):
   `cheeseMeetsBase [IsAlgClosed K] (f) (w) (hnt : ∃ x ≠ 0, w (f x) < 1) : CheeseMeetsBase f w`.
   The file carries a private copy of the `OneEC_val.lean` framework (byte-identical), the body of
   `Johnson23_valuation.lean` in `namespace Johnson`, and ~100 lines of bridge: `IsKBall` is
   `IsValBallK` with the `singleton` constructor dropped (the radii need no transport because
   `(w.comap f) b` is definitionally `w (f b)`, which is why the second trap below does not bite),
   the trace on `K` of an `IsKBall` is an `IsValBall` for `w.comap f`, and 2.3.8 is re-proved for
   an arbitrary `[Fintype ι]` — that is the index shape `SwissCheese` uses, Johnson states it for
   `Fin n`, and the re-proof is where the work is.
   **The nontriviality `hnt` is not removable**: with `w ∘ f` trivial the traces on `K` are points
   or everything and 2.3.7 is false in the form used.
   **Still to do, and it is bookkeeping, not mathematics**: merge this file with
   `QE/OneEC_val.lean` to get `GoodMeetsBase` — `goodMeetsBase_of_swissCheese` composes
   `boolCombCheese` (in `OneEC_val.lean`) with `cheeseMeetsBase` (in this file) — and then feed
   `oneECIn_of_inputs'`.  The two files share the framework definition for definition, but the
   merge has to be done by hand: appending the Johnson body to `OneEC_val.lean` by line arithmetic
   broke the parse (my attempt did), so splice it deliberately.

2. **`star`** — **proved** in `QE/Amalgamation_reduced.lean` (commit `7cc89e8`, swarm
   `smw0fcnxx` member m3), which grows to 786 lines with every line it had preserved.  Johnson's
   proof of 2.2.7 verbatim, and the piece that looked like hard algebra is not: "torsion-free over
   a valuation ring is flat" (2.2.4.2) is Mathlib's
   `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout` (a valuation ring is Bezout), so it is one
   line.  Then `TensorProduct.map_injective_of_flat_flat` gives `B₁ ⊗_B B₂ ↪ A₁ ⊗_B A₂`, a
   minimal prime of the former lifts to one of the latter and contracts to `0` in each factor
   (2.2.6), the prime `p` comes from `k₁ ⊗_{k₀} k₂` being nontrivial, and Chevalley's two-prime
   form (`chevalley_hom'`, already in the file) finishes.  The file ends with an `example`
   typechecking `amalgamation_of_ring_amalgamation star`, i.e. the amalgamation property for
   *valued fields* at `Type u`.
   **Still to do**: transport that to `HasAmalgamation valField`, which is the same
   `ModelType`/`valStructOf` step as item 3.

3. **Hypothesis (iii) at the `ModelType` level.**  `oneECIn_of_inputs'` is stated for concrete
   valued fields with the `L_val` structure `valStructure w`; `hasQE_of_johnson` wants it for
   `M N : valField.ModelType` with arbitrary `L_val` structures.  The missing lemma is

   ```
   valStruct_ext : (s : val.Structure M) → [Field M] → [CompatibleRing M] →
     valRingHom.IsExpansionOn M → s = valStructOf M (predM : M → M → Prop)
   ```

   A first attempt failed with an **instance diamond**: declaring `IsExpansionOn` for
   `valStructOf M predM` while the ambient `val.Structure M` is `s` makes typeclass search
   synthesise an instance that is not definitionally the one the typing rules infer.  The fix is
   not to declare the instance but to state the function-symbol equality as a plain `have` with
   explicit `@Structure.funMap` applications, and to rewrite `x` to `![x 0, x 1]` on the relation
   side (`predM x y` is `RelMap le ![x, y]`, and `x = ![x 0, x 1]` is `funext` + `fin_cases`).
   Once that lemma exists, `OneECIn` transports along the structure equality and (iii) closes.

4. **The assembly `HasQE (L := Language.val) ACVF_val`.**  `hasQE_of_johnson` takes the three
   hypotheses plus `valField ⊆ ACVF_val` (proved); hypothesis (i) is `hasPrimeModels_ACVF_val`.
   Nothing beyond 1–3 is missing.

5. **The transfer `L_val → L_RV`.**  Not started.  Route (T1): `RV = rv(VF^×) ∪ {0}` (a theorem in
   the frozen encoding, `RVeqRvVF_of_model`) lets an `RV`-quantifier `∃ y (RV), ψ` be written
   `∃ y' (VF), y' ≠ 0 ∧ ψ[y'/y]`, with `rv (t)` read as `t` and `rv t ≤ rv s` as `v t ≤ v s`.
   The work is the recursion through the *tagged* encoding of `Milestone0/Encoding.lean`
   (`allSorted`, `tRVZero`, the junk conventions of each function symbol), not the mathematics.

## Cross-checks that exist but are not in `QE/`

Two hard results in this development have more than one formal proof.  The second proofs live in
the swarm records (`.ultramath/`) and are not copied into `QE/`, because this repo's files are
standalone snapshots and copying them would duplicate several hundred lines for no gain.  They are
recorded here so that a reader knows the evidence exists.

* **`star`** (Johnson 2.2.7 for valuation rings).  Landed proof: `QE/Amalgamation_reduced.lean`,
  Johnson's route via 2.2.5 and 2.2.6 (minimal primes of `B₁ ⊗_B B₂`, transported along
  `B₁ ⊗_B B₂ ↪ A₁ ⊗_B A₂`).  **Independent second proof**:
  `.ultramath/smw0fcnxx/m2/Star.lean` (781 lines), same statement verbatim, axioms
  `{propext, Classical.choice, Quot.sound}`, by a different route — two going-down steps for flat
  maps (`Ideal.exists_ideal_le_liesOver_of_le`) replace both 2.2.5 and 2.2.6, so the argument
  never mentions minimal primes.  Both proofs reduce to Mathlib's
  `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`.
* **`CheeseMeetsBase`** (Johnson 2.3.8).  Landed: `QE/CheeseMeetsBase.lean` and, merged,
  `QE/OneEC_val.lean`.  One independent attempt
  (`.ultramath/smw0fobjd/m2/CheeseMeetsBase.lean`) turned out to be a *copy of the landed file*
  rather than a second proof; its own design was unused.  So 2.3.8 currently has one proof, not
  two, and that is worth knowing before trusting it.

`AtomGood` (2.3.1(ii)) does have two independent proofs: the landed cell decomposition
(`QE/OneEC_val.lean`, member m4 of swarm `smw0f42v0`) and an erase-recursion proof
(`.ultramath/smw0f42v0/m8/AtomGood.lean`, member m8), both checked.

### The last glue step, with the two sub-obstacles met so far

`HasQE (L := Language.val) ACVF_val` is now assembly: `hasQE_of_johnson` needs
`valField ⊆ ACVF_val` (proved), `HasPrimeModels valField ACVF_val` (proved), `HasAmalgamation
valField`, and `h1ec : ∀ M N : valField.ModelType, M ⊨ ACVF_val → OneECIn f`.  The ingredients for
the last two are in the tree — `star` (with `amalgamation_of_ring_amalgamation`) and
`oneECIn_of_nontrivial` — and both are stated on *concrete* valued fields, so each needs the same
transport to `valField.ModelType`.  The two structure equalities for that are now proved
(`valStruct_ext` and `valStructOf_eq_valStructure`, commits `296163f` and `d3d1985`), so a model's
own `L_val`-structure is propositionally `valStructure v` for a genuine Mathlib valuation `v`.

What is left, with the obstacles already met:

1. **Transporting an `Embedding`, and with it `OneECIn`, along those structure equalities.**  `f :
   M ↪[val] N` depends on the structures as *instance* arguments, so rewriting them does not
   rewrite `f`; one needs a cast of embeddings (`hM ▸ hN ▸ f`) together with the matching
   `OneECIn` congruence.  This is where the next attempt starts; it is fiddly, not deep.
2. **The nontriviality of the valuation, extracted from `M ⊨ ACVF_val`.**  `M ⊨ axNontrivial`
   must become `∃ x : M, ¬ predM (funMap ValFunc.one …) x`.  Two attempts failed on the `simp
   only` set.  The goal that is left after
   `simp only [axNontrivial, axNontrivialF, Sentence.Realize, Formula.Realize,
   BoundedFormula.realize_ex, BoundedFormula.realize_not, leF_realize, …]` is

   ```
   (∃ a, ¬ (leF 1 (var (Sum.inr 0))).Realize default (Fin.snoc default a))
     ↔ ∃ x, ¬ predM (@Structure.funMap Language.val M _ 0 ValFunc.one fun i => i.elim0) x
   ```

   so `leF_realize` is not firing on that occurrence; proving the two directions by hand from
   `leF_realize 1 (var (Sum.inr 0)) default (Fin.snoc default a)` and `realize_oneTerm'` is the
   way in.  Note the sentence must be read with the *value of the constant* `1`, not with
   `(1 : M)`, because an abstract `L_val`-structure has no `One` instance — that mistake is what
   made the first version unprovable.

### Update after the Assembly_val work

`QE/Assembly_val.lean` (5844 lines) is the file where the two halves of the `L_val` development
finally meet: it is `PrimeModels_val_partial.lean` followed by the body of `OneEC_val.lean` with
that file's private copy of the language removed, so both speak the same
`FirstOrder.Language.val`.  Only three names were defined in both files (`ValFunc`, `ValRel`,
`valStructure`) — exactly the preamble that is dropped.  One trap: the merged file also needs
`open scoped Polynomial`, without which `K[X]` in `termToPoly` parses as an indexing notation and
produces 51 cascading errors that look unrelated.

Two new results there:

* `isAlgClosed_of_model` — a model of `ACVF_val` is algebraically closed.  **Until this existed,
  nothing in the tree used the algebraic-closedness half of `ACVF_val`**, and
  `oneECIn_of_nontrivial` requires `[IsAlgClosed K]`, so the transport of hypothesis (iii) could
  not even be started.  This was a missing piece nobody had listed.
* `fieldOfModelValField` — the field instance the statement needs.

And a correction to `ACVF_val` itself (commit `c9b882f`): the nontriviality sentence was
`∃ x, ¬ (v 1 ≤ v x)`, which is satisfied by `x = 0` in **every** valued field, so it said nothing.
It is now `∃ x, x ≠ 0 ∧ ¬ (v 1 ≤ v x)`, and `axNontrivial_realize` is restated accordingly.

**The one remaining blocker for the transport**, with the exact error, is recorded in the file:

```
"QE/Assembly_val.lean:5856:10: error: synthesized type class instance is not definitionally
equal to expression inferred by typing rules, synthesized sM, inferred valStructure v"
```

`M.struc = FirstOrder.valStructure v` cannot even be *stated*: `Language.val.Structure` is a class,
so the equation itself trips instance checking, whichever side is written first, with or without a
`letI` naming the instance.  Everything else in the proof of `oneECIn_of_modelType` is in place —
`valStruct_ext`, `valStructOf_eq_valStructure`, `embeddingCast`, `oneECIn_congr'`,
`oneECIn_of_nontrivial`, `isAlgClosed_of_model`, and the nontriviality transfer through
`axNontrivial_realize`.  The likely way round it is not to state the equation at all but to
restate `OneECIn`, or the goal, with the `valStructure` instances supplied by `letI` from the
start, so that no equation between instances is ever needed.

## Layer (A) for `L_val` is DONE

Commit `feb1415`:

```
hasQE_ACVF_val : QECriterion.HasQE (L := Language.val) ValPM.ACVF_val
```

in `QE/Assembly_val.lean` (9455 lines), by `HQEDerive.hasQE_of_johnson` with all four hypotheses
proved in the same file:

| hypothesis | lemma |
|---|---|
| `valField ⊆ ACVF_val` | `ValPM.valField_subset_ACVF_val` |
| prime models over substructures | `ValPM.hasPrimeModels_ACVF_val` |
| amalgamation | `ValOneEC.hasAmalgamation_valField` |
| 1-ec | `ValOneEC.oneECIn_of_modelType` |

So quantifier elimination for the theory of nontrivially valued algebraically closed fields **in
the one-sorted language `L_val`** is a theorem, unconditionally.  That is layer (A).

`Assembly_val` now carries, in one file: `valField` and its model theory; the coordinate ring,
the prime model and its universal property; `ACVF_val`; the `ModelType` bridge (`valStruct_ext`,
`valStructOf_eq_valStructure`, `isAlgClosed_of_model`, `embeddingCast`/`oneECIn_congr`);
`OneEC_val`'s whole machinery (syntax bridge, `Good`/`IsKBall`, 2.3.1(i)(ii), 2.3.2, 2.3.8,
`oneECIn_of_nontrivial`); `star` (Johnson 2.2.1–2.2.7) and `hasAmalgamation_valField`; and
Johnson's criterion.  Three merges were needed (`OneEC_val`, `Amalgamation_reduced`, `ACF_HasQE`)
because the repo's files are standalone snapshots.

The key step of `hasAmalgamation_valField` is `le_iff_valuationSubring_valuation_le`: the order of
a valuation is the order of its valuation subring's canonical valuation.  That is what lets
Johnson's §2.2 theorem, stated for `ValuationSubring`s, apply to the valuations that
`exists_valuation_of_isValPred` produces, and the amalgam is then repackaged as a model of
`valField` through `valStructure_model`.

## What is left: the transfer `L_val → L_RV`

`Milestone0/Encoding.lean`'s `theorem_2_3_quantifier_elimination : HasQE ACVF` is stated in the
frozen tagged language `L_RV` (sorts `VF`/`RV` as the relations `memVF`/`memRV`, `rv : VF → RV`,
the residue-field operations `kAdd`/`kNeg`, the preorder `rvLe`).  Route (T1) needs:

1. **QF `L_val` → QF `L_RV`.**  Purely syntactic: `v x ≤ v y` becomes `rvLe (rvMap x) (rvMap y)`,
   and the ring symbols go to `vfAdd`/`vfMul`/`vfNeg`/`vfZero`/`vfOne`.  This direction is easy
   and is where the transfer should start.
2. **`L_RV` → `L_val`.**  An `RV`-quantifier `∃ y (RV), ψ` becomes `y = 0 ∨ ∃ x (VF), x ≠ 0 ∧ ψ[rv x / y]`
   using the paper's `rvSurj`, which the frozen encoding now has.  `rv t ≤ rv s` becomes
   `v t ≤ v s`; `rvMul` is multiplication.  The subtle symbol is `kAdd`, the *residue field's*
   addition: on units `kAdd a b = c` is `∃ x y, rv x = a ∧ rv y = b ∧ rv (x + y) = c` — the
   quantifiers are needed because `rv (x + y)` depends on the residues, and when `a + b = 0` the
   value of `x + y` drops and the junk conventions of `kAdd` take over.  `memUnits` and the
   preorder are `v x = 1`-shaped, hence QF in `L_val` given the `rv`-identification.
3. **Composition**, and then models: an `LRV`-model of `ACVF` restricts to an `L_val`-structure on
   its `VF` sort, which is where `hasQE_ACVF_val` applies.

## The model correspondence: what exactly has to be extracted

The transfer's remaining crux is: from `M ⊨ Axioms.ACVF` (an `L_RV`-structure), produce an
`L_val`-structure modelling `ValPM.ACVF_val`.  Reading the axiomatisation in
`Milestone0/Encoding.lean` (now copied into `Assembly_val`), the shape is:

* `Axioms.sortAxioms = sortClosure ∪ {sdCover, sdDisjoint}`.  **`sdDisjoint`** says the two sort
  predicates are disjoint (so an element is in at most one sort) and **`sdCover`** that every
  element is in one of them or is the RV-zero; `sortClosure` gives closure: `sdVFZero`,
  `sdVFOne`, `sdVFAdd`, `sdVFNeg`, `sdVFMul` (VF is a ring **and** closed under its own symbols),
  `sdRv` (`rv : VF → RV`), `sdRVZero`, `sdRVOne`, `sdRVMul`, `sdUnits`, `sdKAdd`, `sdKNeg`,
  `sdKMul` (K = K^× ∪ {0} closed under the residue operations).
* `Axioms.vfField` is `fieldAxioms .vf tVFZero tVFOne tVFAdd tVFMul tVFNeg`, a `List` of nine
  `allSorted`-guarded sentences: associativity, commutativity, neutrality of `0` and `1`,
  inverses, distributivity, `0 ≠ 1`, and "every nonzero element is invertible" (the language has
  no inverse symbol, so invertibility is `∃ y, x·y = 1`).
* `Axioms.vfAlgClosed` is the scheme `{acfScheme .vf … k | 1 ≤ k}`, i.e.
  `∀ a₀ … a_{k-1} ∃ x (VF), x^k + a_{k-1}x^{k-1} + … + a₀ = 0` — this is what must become
  `IsAlgClosed` of the `VF`-sort field, by the same argument as `isAlgClosed_of_model` but with
  `hornerPoly` in place of `Field.genericMonicPolyHasRoot`.
* `Axioms.rvAxioms = {rvZeroEq, rvEqInfty, rvMulHom, rvSurj, rvUltrametric}` and
  `Axioms.preorderRV`.  The predicate to use on VF is `fun x y => iLe (iRv x) (iRv y)`;
  `preorderRV` gives reflexivity/transitivity/totality, `rvUltrametric` the ultrametric
  inequality, `rvMulHom` multiplicativity (hence `IsValPred.scale`), `rvZeroEq` the absorbing
  behaviour of `rv 0`.  Nontriviality of the valuation for `OneECIn` comes from the same place:
  an element with `¬ (vv 1 ≤ vv x)` and `x ≠ 0`.

**The gateway lemma, which does not exist yet and should be written first:**

```
sortedHyps_realize : (sortedHyps ss).Realize v x ↔ ∀ i, sortPred (ss i) (x i)
```

`sortedHyps` is a `List.finRange k`-`foldr` of `⊓`-conjunctions, so the proof is an induction on
that list (generalised to an arbitrary enumerating list) together with the realisation lemmas for
`⊓` and `⊤`.  With it, every `allSorted ss φ ∈ ACVF` gives its semantic content
`∀ x̄, (∀ i, x i ∈ s_i) → φ.Realize`, and the whole extraction becomes uniform.

Then, in order: the subtype `{x // iVF x}` with the ring operations (closure from `sortClosure`,
laws from `vfField`); `Field` on it; `IsValPred (fun x y => iLe (iRv x) (iRv y))`; `IsAlgClosed`
from `vfAlgClosed`; the `ACVF_val` model; instantiate `hasQE_ACVF_val`; translate back through
`valFormulaToRV`; conclude `HasQE Axioms.ACVF` and discharge `theorem_2_3_quantifier_elimination`.

## The extraction from an `L_RV`-model, and a third defect in the frozen encoding

### What is in `Assembly_val.lean` now (the model correspondence, first half)

The transfer's remaining crux is: from `M ⊨ Axioms.ACVF` (an `L_RV`-structure) produce an
`L_val`-structure modelling `ValPM.ACVF_val`.  The file now has, in section 23 and all green:

* the unfolding toolkit: `realize_tv`, `sortPred_realize`, `pVF_realize`, `pRVsort_realize`,
  `pVF_realize`, `pRV_realize`, `pUnits_realize`, `realize_pLe`, `realize_tRv`, `realize_tVFAdd`,
  `realize_tVFMul`, `realize_tVFZero`, `realize_tVFOne`, `realize_tRVZero`, `realize_tRVMul`,
  `realize_tRVOne`, plus the gateway `sortedHyps_realize` and the uniform extraction
  `allSorted_realize`;
* the `VF` sort as a ring: `vf_add_assoc`, `vf_add_comm`, `vf_add_zero`, `vf_add_neg`,
  `vf_mul_assoc`, `vf_mul_comm`, `vf_mul_one`, `vf_left_distrib`, `vf_zero_ne_one`,
  `vf_mul_inv_or_zero`, and `vfFieldOfModel : Field (VFType (M := M))` — the eight equational
  laws and invertibility, from `Axioms.vfField`;
* the `RV` preorder and the axioms of `rv`, semantically: `le_refl`, `le_trans`, `le_total`,
  `le_top` (`x ≤ ∞`), `le_infty_eq` (`∞ ≤ x → x = ∞`), `rv_zero_eq` (`rv 0 = ∞`),
  `rv_eq_infty` (`rv x = ∞ → x = 0`), `rv_mul_hom`, `rv_ultrametric`.

Two traps cost turns here and are worth recording: `simp only` does **not** reduce the tuple
applications `![x, y, z] 2` (`Matrix.cons_val_two` is not in the default set), so an
`![x, y, z]`-indexed extraction has to finish with a full `simp` or a `rfl`-shaped lemma; and a
frozen axiom is an opaque `def`, so `ΔtRVInfty` and `Axioms.rvZeroEq` must be named in the simp
set before `realize_tRVZero` / `Formula.Realize` can fire on them.

### The defect: `leMulCompat` does not say what the paper's item 5 says

`valField`'s `axScale` is an **iff**: `z ≠ 0 → (v x ≤ v y ↔ v x·z ≤ v y·z)`.  It is what makes the
predicate a valuation (`valuativeRelOfIsValPred`'s comment says so: "`scale` (an iff) gives both
multiplicativity and cancellation"), so the extracted structure needs it.  Transported along
`valFormulaToRV` it becomes, for `a b c ∈ RV` with `c ≠ rv(0)`,

```
iLe a b ↔ iLe (iRMul a c) (iRMul b c).
```

The frozen axiom that is supposed to supply this is

```
leMulCompat : pRV &0 ⟹ pRV &1 ⟹ pRV &2 ⟹ (pUnits &2 ⟹ (pLe &0 &1 ⟹ pLe (&0·&2) (&1·&2)))
```

— multiplication by an element of `Kˣ`, i.e. by an element of the **identity class** of
`RV/Kˣ = Γ`.  In Γ-terms that is a translation by `0`: it constrains almost nothing.  The paper's
item 5 is "the quotient `RV/Kˣ` is a divisible **ordered** abelian group, where the ordering and
the group operation are induced by `≤` and `×`" — i.e. translation-invariance of the Γ-order,
which is scaling by **every** `c ≠ 0`.  The frozen axiom has `pUnits` where the paper has
`c ≠ 0`: the same transcription slip as the old `rvSurj` (`pUnits` in place of `≠ rv(0)`).

**The axioms do not force the missing law.**  Take any model of `ACVF` — concretely the intended
one, `RV = Γ ∪ {∞}` with `Γ = RV^×/K^×` — and replace `≤` by `≤' := f∘≤` for a monotone
`f : Γ ∪ {∞} → Γ ∪ {∞}` with `f (∞) = ∞`, finite on `Γ`, and `f⁻¹ (f 0) = {0}`.  Each of the
eight axioms that mention `≤` survives:

| axiom | why |
| --- | --- |
| `leRefl`, `leTrans`, `leTotal` | a total preorder pulled back along a function is a total preorder |
| `leTop` | `f (∞) = ∞` is still the top |
| `leInftyEq` | `f γ = ∞` only for `γ = ∞` |
| `leClassOne` | the class of `1` is `{γ : f γ = f 0} = {0}` by `f⁻¹ (f 0) = {0}` |
| `leMulCompat` | multiplying by `h ∈ Kˣ` does not change the Γ-value, so it is the *identity* on Γ — the requirement becomes `f γ₁ ≤ f γ₂ → f γ₁ ≤ f γ₂` |
| `rvUltrametric` | `γ (x+y) ≥ min (γ x) (γ y)`, and `f` is monotone |

and no other axiom mentions `≤` or `Kˣ` (`pLe` occurs in exactly those seven sentences plus
`rvUltrametric`; `pUnits` in `leClassOne` and `leMulCompat`).  So if `f` is not injective the
model satisfies the frozen `ACVF` and **fails** the scaling law: with `Γ = ℚ`,
`f γ = γ` for `γ ≤ 1/2` and `f γ = 1/2` for `γ ≥ 1/2`, and `a = rv (t^{1/2})`,
`b = rv t`, `c = rv (t^{-1/2})` we get `f 1/2 = f 1`, i.e. `b ≤ a`, but
`f (1/2 - 1/2) = 0 > 1/2 = f (1 - 1/2)`, i.e. **not** `b c ≤ a c`.

Two consequences.

1. **The transfer (T1) cannot be completed against the frozen axioms.**  The extracted
   `L_val`-structure `S_M` (predicate `x ≤ y ↦ iLe (iRv y) (iRv x)`) is a model of `valField`
   only if the scaling law holds in `M`, so `hasQE_ACVF_val` cannot be instantiated at `S_M`.
2. **Whether the frozen target stays true is now open again.**  The coarsened models are models
   of the frozen `ACVF`, so any proof of `HasQE ACVF` must handle them.  (That is not a
   disproof: the coarsening only removes distinctions, and QF formulas have fewer atoms too.
   But it removes the route through `L_val`.)

### The repair, and what it costs

Restore the paper's item 5 in the encoding, by guarding with `pRV` and stating the iff:

```lean
def leMulCompat : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv]
    (pRV &0 ⟹ (pRV &1 ⟹ (pRV &2 ⟹ (pLe &0 &1 ⇔ pLe (tRVMul &0 &2) (tRVMul &1 &2)))))
```

The intended model satisfies it (`vrv` is multiplicative and `Γ` is an ordered group), and with
it the extracted predicate satisfies `axScale` — hence `S_M ⊨ valField`, and the transfer goes
through as planned.  This is a **frozen-encoding change**: `Milestone0/Encoding.lean`'s hash
moves and every snapshot that carries a copy of the axiom set must be re-verified, exactly like
the `rvSurj` repair (which was made on the author's instruction and is recorded in
`Milestone0/DECISION.md`).  It is therefore the author's call, and it is the one open decision.

### The frozen statement is **false**, not merely unprovable by this route

The coarsening above is not an artefact of the transfer: it refutes `HasQE ACVF` itself.  Take the
intended model and coarsen by the *sign* map, `f : Γ ∪ {∞} → Γ ∪ {∞}`, `f (∞) = ∞`,
`f 0 = 0`, `f γ = +1` for `γ > 0`, `f γ = -1` for `γ < 0` (in the paper's Γ-order, in which
`vv (1) = 0` is the least element and `vv (0) = ∞` the top).  Then:

1. **The coarsened structure is a model of `Axioms.ACVF`.**  Only the interpretation of `iLe`
   changes, and every axiom that mentions `iLe` — `leRefl`, `leTrans`, `leTotal`, `leTop`,
   `leInftyEq`, `leClassOne`, `leMulCompat`, `rvUltrametric` — survives, by the table above
   (`pGtOne` is used only by `residueCharZero`, which is not in `Axioms.ACVF`; `pLe` occurs in
   exactly those eight sentences).  In particular `leClassOne` stays exact because
   `f γ = f 0 → γ = 0`.

2. **A quantified formula defines the true order in it.**  For `a b : M` with `iRV a`, `iRV b`,
   `a ≠ 0`, `b ≠ 0`,

   ```
   θ (a, b) :≡ ∀ c, pRV c ⟹ pLe (tRVMul a c) (tRVMul b c)
   ```

   realises as "for all `γ_c`: `f (γ_a + γ_c) ≤ f (γ_b + γ_c)`", which holds iff `γ_a ≤ γ_b`
   (take `γ_c = -γ_a` for the converse).  So `θ` defines the **true** order on `RV^×`, which
   the coarsened `≤` no longer sees.

3. **No quantifier-free formula defines it.**  A quantifier-free formula in the two free
   variables `a`, `b` is a Boolean combination of atoms of three kinds: `iLe (a^i b^j) (a^k b^l)`,
   `a^i b^j = a^k b^l`, and `iUnits (a^i b^j)`.  Put `u = γ_a`, `v = γ_b`.  Restricted to the
   open quadrant `u > 0`, `v > 0`, every nonzero monomial `a^i b^j` has positive value, so every
   `iLe`-atom is *constant* there and every `iUnits`-atom is false; the remaining atoms are
   equations `(i-k) u + (j-l) v = 0`, i.e. finitely many lines through the origin.  Given any
   candidate `ψ`, take `p = (1, 1+ε)`, `q = (1, 1-ε)` with `ε` irrational and small: both are in
   the quadrant, neither lies on any of those finitely many lines (their slopes are rational), so
   **every atom has the same truth value at `p` and at `q`** — while `u ≤ v` holds at `p` and
   fails at `q`.  Hence `ψ` cannot agree with `θ` in this model, and since the model satisfies
   `Axioms.ACVF`, `ACVF ⊭ (θ ⇔ ψ)` for every quantifier-free `ψ`: **`HasQE Axioms.ACVF` is
   false as the encoding stands.**

What is machine-checked so far and what is not: the preservation of the eight axioms under a
monotone coarsening is elementary and is being formalised (swarm `smw14elno`, direction d2); the
two-point argument in item 3 is elementary finite combinatorics but is not formalised, and cannot
be cheaply, because the tree has no proved model of `ACVF` over a nontrivial valuation to coarsen
(`Milestone0/DECISION.md`, "Open (Milestone 1)").

This changes the status of the repair from a convenience to a necessity: with `leMulCompat` as
frozen, `theorem_2_3_quantifier_elimination` is not provable, exactly as the two-constant form of
the axioms was not satisfiable by its own intended model.  The difference between the two cases is
only that this one is refuted by a *model of the axioms* rather than by the intended model.

### The slip is systematic: three axioms, not one

Working out what the extracted predicate needs turned up the same mistake in two more places, and
the pattern is now clear: wherever `qe.tex` Definition 2.2 says `RV^×` (the multiplicative group of
*all* nonzero `RV`-elements, i.e. `pRV`), the encoding says `pUnits`, which is `Kˣ`, the subgroup of
value `1`.  The three places that matter:

| paper | encoding | what is missing |
| --- | --- | --- |
| item 6: `rv` onto `RV^×` | `rvSurj`, was `pUnits`-guarded | *already repaired* (author's ruling) |
| item 5: `RV/Kˣ` an ordered group | `leMulCompat`, `pUnits`-guarded, one direction | scaling by a non-unit, and reflection |
| item 2: `(RV^×, 1, ×)` a divisible group | `rvMulOne`, `rvMulInv`, `rvMulMem`, `rvDivisible`, all `pUnits`-guarded | `1 · t = t` and `t · t⁻¹ = 1` for `t ≠ 0` outside `Kˣ` |

The encoding's `rvGroup` therefore axiomatises *`Kˣ`* as a group (which is true, and is the kernel of
`vrv`), not `RV^×`; the group structure of the whole `RV^×` is never stated.  `Kˣ` and `RV^×` are
respectively the identity class and the whole group of `Γ = RV^×/Kˣ`, which is exactly why the
mistake is invisible in the intended model and fatal in the theory.

The last row is not academic: `valField`'s `axScale` is unguarded in `x` and `y`, so the extraction
needs the case `y = 0` of `predV x y ↔ predV (x z) (y z)`, i.e. `rv (x z) = ∞ ↔ rv x = ∞` for
`z ≠ 0` — cancellation by a nonzero `RV`-element.  Cancellation follows from inverses in `RV^×`
(`a = 1·a = (b⁻¹b)·a = b⁻¹·(ab) = ∞`), and from nothing weaker that the axioms contain.

So the minimal repair that makes the transfer go through is three sentences:

```lean
def leMulCompat : LRV.Sentence :=            -- item 5
  allSorted ![.rv, .rv, .rv]
    (pRV &0 ⟹ (pRV &1 ⟹ (pRV &2 ⟹ (pLe &0 &1 ⇔ pLe (tRVMul &0 &2) (tRVMul &1 &2)))))
def rvMulOne : LRV.Sentence :=               -- item 2, neutral law
  allSorted ![.rv] (pRV &0 ⟹ pEq (tRVMul tRVOne &0) &0)
def rvMulInv : LRV.Sentence :=               -- item 2, inverses
  allSorted ![.rv] (pRV &0 ⟹ exSorted .rv (pRV &1 ⊓ pEq (tRVMul &1 &0) tRVOne))
```

(`rvMulMem` and `rvDivisible` are also `pUnits`-guarded; they are consequences in the intended model
and are not needed for the transfer, but a faithful repair should move them too.)

### What is landed, and what is waiting for the ruling

Landed and green in `Assembly_val.lean` (frozen theory only, no repair needed):

* `rv_mem` (`x ∈ VF → rv x ∈ RV`), and the extracted predicate
  `predV x y := iLe (iRv y) (iRv x)` with **six of the seven** `valField` axioms:
  `predV_refl`, `predV_trans`, `predV_zero_le`, `predV_zero_eq`, `predV_ultra`, `predV_total`
  (plus the unguarded helpers `le_self` — reflexivity at `0` is the ultrametric inequality at
  `0 + 0` — and `le_top'`).

In `.scratch2/asm/` and not committed, because they need the ruled-on repair:

* `leMulCompatFull`, `rvMulInvFull`, `rvMulOneFull` as sentences, `ACVFplus = ACVF ∪ {those}`, the
  semantic forms `le_mul_compat_full`, `rv_mul_inv_full`, `rv_mul_one_full`, the cancellation lemma
  `rv_mul_ne_infty`, `predV_scale` and `isValPred_predV`.  All of them are proved except the
  bookkeeping at the end; `predV_scale` is the only place the repair is used.
* also in the scratch file: `realize_tRVOne` and `mem_ACVF_rvGroup`, two utility lemmas the main
  file does not have yet.

### Correction: the repair is **one** axiom, and the group axioms do not need to move

The section above ("The slip is systematic: three axioms") is superseded, and the reason is worth
keeping: it assumed item 5 stated with the `pRV` guards on `a` **and** `b`, which forces `axScale`'s
zero cases (`x = 0` or `y = 0`) into a cancellation argument, which needs inverses in `RV^×`, which
the encoding does not give.  Swarm `smw14elno` member m1 found the right statement instead — drop
the guards on `a` and `b`, keep `c ≠ 0`:

```lean
def leMulCompatFull : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv]
    (pRV &2 ⟹ (pLe &0 &1 ⇔ pLe (tRVMul &0 &2) (tRVMul &1 &2)))
```

Two facts make this exactly the repair and no more:

* the intended model satisfies it: `∞ = rv 0` is absorbing and the top, so at `a = ∞` or `b = ∞`
  both sides of the iff are true, and otherwise it is the translation-invariance of the `Γ`-order;
* it is *equivalent* to the `L_val`-side `axScale` transported to `RV`
  (`paperScale_of_vfPred_scale` and `vfPred_scale` in `.ultramath/smw14elno/m1/Scale.lean`), so
  nothing is being added beyond what `L_val`'s own theory already says.

The `pUnits`-for-`pRV` weakness of `rvMulOne`/`rvMulInv`/`rvMulMem`/`rvDivisible` is real — the
encoding axiomatises `Kˣ` as a group and never says `RV^×` is one — but with item 5 in the form
above it is **not needed** for the transfer, and it does not make the transfer's conclusion weaker.
It is a fidelity gap to fix when the encoding is next touched, not a repair this campaign needs.

### The fourth gap: nontriviality, which is separate and which the frozen axioms do not supply

`ValPM.ACVF_val` contains `axNontrivial` (`∃ x, x ≠ 0 ∧ ¬ v 1 ≤ v x`), and `oneECIn_of_nontrivial`
says its `hnt` cannot be dropped (Johnson 2.3.8 is false for a trivially valued field).  The frozen
`Axioms.ACVF` contains **no** nontriviality sentence — `qe.tex` Definition 2.2 does not either — so
trivially valued structures are models of it (see the correction below: the reading in which `rv` is
injective on `VF^×`, not the one in which `rv` is constant).  Swarm member m1
checked the axioms against that structure one by one (`HasNontrivVal`'s docstring in
`.ultramath/smw14elno/m1/Scale.lean`): `vfField`/`vfAlgClosed` are those of the ACF, `kField`/
`kAlgClosed` those of the residue field, `rvGroup` holds because `F` algebraically closed makes
`F^×` divisible, `preorderRV` because `iUnits` is exactly the class of `1`, and `rvUltrametric`
because all nonzero values are equivalent — while `HasNontrivVal` fails.

So the final theorem needs the case split: **nontrivially valued** (transfer to `ACVF_val`, which is
now assembled) and **trivially valued** (where `rv : F^× → RV^×` is injective on classes, `RV`
carries a copy of the field, and QE should follow from QE for `ACF` by a separate translation).  The
second case is not started and is a genuinely new piece of work, not bookkeeping.

### What the swarm landed (all six directions accepted, `smw14elno`)

| direction | file | statement |
| --- | --- | --- |
| d1 | `m5/VFAlgClosed.lean` | `isAlgClosed_vfType : IsAlgClosed (VFType)`, from `Axioms.vfAlgClosed` |
| d1 | `m5/VFPack.lean` | `model_valField` and `model_ACVF_val` packaging |
| d2 | `m1/Scale.lean` | `PaperScale`, `vfPred_scale`, `paperScale_of_vfPred_scale`, `valField_model_of_PaperScale`, `model_ACVF_val_of_axioms` — **the whole extraction assembly** |
| d3 | `m4/d4.lean` | the six non-scaling `valField` axioms at `S` (independent of the copy in `Assembly_val.lean`), `exSorted_realize` |
| d4 | `m2/Coarsening.lean` | the coarsening lemma: the eight `≤`-axioms survive `f∘≤`, scaling fails |
| d5 | `m6/ValEvalVF.lean` | `vfStruct`, the sort-restricted evaluator, `valFormulaToRVvf` and its bridge, `transfer_iff`/`theory_transfer` |
| d6 | `m3/QFTransfer.lean` | `isQF_valFormulaToRV`, QF sort-independence, `valFormulaEvalS` |

Every file compiles with `import Pre`, 0 errors, no `sorry`, axioms within
`{propext, Classical.choice, Quot.sound}`; I re-elaborated each one myself before accepting.

### The one gap left on the transfer

`m6`'s `transfer_of_isQF` runs from `L_val` to `L_RV`.  The frozen target needs the converse
coverage: **every `L_RV`-formula is `ACVF`-equivalent to some `valFormulaToRVvf θ`**.  That is
`RV`-quantifier elimination inside `L_val` — `∃ y (RV), ψ` becomes `y = rv 0 ∨ ∃ x (VF), x ≠ 0 ∧
ψ[rv x / y]` using `rvSurj`, plus the treatment of the residue-field operations (`kAdd` above all,
where the value drop at `a + b = 0` forces the junk conventions), `pUnits` (`v x = 1`), and the
preorder.  This is the last substantial piece, and it is independent of the repair decision: it can
be written now, against the frozen axioms, and it is what makes the frozen *statement* reachable
once the repair is in.

### The swarm's assembly is in the tree (commit after `63ba631`)

`QE/Assembly_val.lean` now carries, at the end, the accepted `smw14elno` work as part of the one
snapshot (the namespaces `VFAlgClosed`, `VFPack`, `VFRestrict`, `Smw14elno.M3` keep the pieces
apart; `Transfer` gains m1's `PaperScale` material):

* `SpecialTransformations.Milestone0.Transfer`: `mem_ACVF_sdRv`, `rv_ne_zero`, `mem_ACVF_rvSurj`,
  `rv_surj`, `exists_vf_of_rv`, `PaperScale`, `vfPred`, `vfPred_scale{,_raw,_forall,_mp,_mpr}`,
  `paperScale_of_vfPred_scale`, `paperScale_iff_vfPred_scale`, `valField_model_of_PaperScale`,
  `vfValStruct`/`vfRingStruct`/`vfCompatibleRing`/`vfValStruct_expansion`,
  `realize_genericMonicPolyHasRoot_of_isAlgClosed`, `HasNontrivVal`, `realize_axNontrivial`,
  **`model_ACVF_val_of_axioms`**;
* `VFAlgClosed.isAlgClosed_vfType` — from `Axioms.vfAlgClosed` through the Horner scheme;
* `VFPack.model_valField`, `VFPack.model_ACVF_val` — the second packaging;
* `VFRestrict`: the sort-restricted evaluator, `valFormulaToRVvf`, its bridge, `transfer_iff`,
  `theory_transfer`, `transfer_of_isQF`, `sentence_transfer_of_isQF`, and the counterexample showing
  the unguarded translation is not a bridge;
* `Smw14elno.M3`: `isQF_valFormulaToRV`, QF sort-independence, `valFormulaEvalS`, `qf_transfer`.

All green in one `lean QE/Assembly_val.lean` (0 errors), every `#print axioms` in
`{propext, Classical.choice, Quot.sound}`, no `sorry`.  Two independent proofs of two load-bearing
results are now in the tree: the six non-scaling `valField` axioms (m4's file and `predV_*`) and
`IsAlgClosed` of the `VF` sort (m5's Horner route and m1's `realize_genericMonicPolyHasRoot`).

So the extraction from an `L_RV`-model to a model of `ValPM.ACVF_val` is *proved*, with exactly two
hypotheses on the `L_RV` side: `PaperScale` (the repair) and `HasNontrivVal` (nontriviality).

### The repair is now a theory in the tree, and the extraction is conditional on it alone

`QE/Assembly_val.lean` (end of the `Transfer` namespace) now has

```lean
def leMulCompatFull : LRV.Sentence :=      -- Definition 2.2 item 5, in full
  allSorted ![.rv, .rv, .rv]
    (pRV &2 ⟹ (pLe &0 &1 ⇔ pLe (tRVMul &0 &2) (tRVMul &1 &2)))
def ACVFplus : LRV.Theory := Axioms.ACVF ∪ {leMulCompatFull}
```

with `model_ACVF_of_model_ACVFplus`, the semantic form `le_mul_compat_full`,
`paperScale_of_model_ACVFplus`, and

```lean
model_ACVF_val_of_model_ACVFplus (hM : M ⊨ ACVFplus) (hnontriv : HasNontrivVal M) :
  @Theory.Model Language.val (VFType) (vfValStruct …) ValPM.ACVF_val
```

— the extraction, from the repaired theory plus nontriviality.  So the state of the campaign is:

| statement | status |
| --- | --- |
| `M ⊨ ACVFplus` → `S_M ⊨ ValPM.ACVF_val` (nontrivial `M`) | **proved**, in the tree |
| QE in `L_val` for `ValPM.ACVF_val` | **proved** (`hasQE_ACVF_val`) |
| the read-back `L_val` witness → `L_RV`, QF half | **proved** (`VFRestrict.transfer_of_isQF`, `Smw14elno.M3.qf_transfer`) |
| every `L_RV`-formula is a guarded translate of an `L_val`-formula | **open** — swarm `smw1541fr` |
| trivial-valuation models have QE; per-model QE → theory QE | **open** — swarm `smw1541fr` |
| `HasQE Axioms.ACVF` | needs the ruling on the one-axiom repair, plus the two rows above |

The one-axiom repair is the only thing on this list that is not a piece of work.

### The residue field is not tied to `rv`: a fourth member of the family, and a second refutation

Swarm `smw1541fr` member m3 (`m3/KAdd.lean`, green, axioms clean) found that `iKAdd` and `iKNeg`
are constrained **only** by `sdKAdd`, `sdKNeg`, `kField`, `kAlgClosed` — all `pInK`-guarded — and
that no axiom links them to the field's addition through `rv`.  The three gaps, with their status:

1. **No `kAddLink`.** `kAdd (rv x) (rv y)` is unconstrained by `rv (x + y)`.  m3 proves the
   conditional form: given `KAddAdditive` (the link), `kAdd (rv x) (rv y) = rv u` is
   `(iUnits (rv (x+y)) ∧ rv (x+y) = rv u) ∨ (¬ iUnits (rv (x+y)) ∧ rv u = ∞)` — the case split is
   real, since at `x = 1 + t, y = -1` in `k((t))` the sum is `t`, not a unit, while the residue sum
   is `0`.
2. **No `rvEqLink`.** `rv a = rv b` is `¬ (v b ≤ v (a - b))` in the intended model; m3 proves the
   equivalence *from* the link and shows the link is what is missing.  This one is the same defect
   as the `RV^×` group-law weakness recorded earlier, since `rv a = rv b ↔ rv (a/b) = 1` needs
   cancellation.
3. **Junk conventions off `K`.** `kAdd`/`kNeg` values outside `K` are free; m3's `kJunkZero`,
   `kNegJunkZero` pin them to `∞`, and `kAdd_off_K`/`kNeg_off_K` show what that buys.

**This is a second, independent refutation of the frozen `HasQE`, and it is worth stating in full.**
Take any model of `ACVF` and replace `iKAdd` by `σ`-twist of the field addition, where `σ` is an
automorphism of `(K^×, ·)` that is not field-theoretic (for `K = ℂ` or `ℚ̄` there are many).  All
axioms survive: `kField` and `kAlgClosed` because `(K, +_σ, ·)` is again an algebraically closed
field with the *same* multiplication and `1`, `sdKAdd`/`sdKNeg` because `σ` permutes `K^×`, and
`leClassOne` because inside `K^×` the order of `RV` is trivial — every unit is `≤`-equivalent to
`1`, so the twist is invisible to `≤`.  In that model the *true* residue addition is definable by a
quantified formula, `∃ x y (VF), rv x = a ∧ rv y = b ∧ rv (x + y) = c`, but not by a
quantifier-free one built from `iKAdd_σ` and `·` — that is what makes the twist a twist.  So
`HasQE ACVF` fails here too, for a reason disjoint from the coarsening above: not "the order is too
weak" but "the residue-field symbols are not tied to the field".

**The repair list is therefore four items, not one**, and each is a "say what the paper means"
edit rather than a change of mathematics:

| # | axiom(s) | what it restores | needed for |
| --- | --- | --- | --- |
| 1 | `leMulCompat` with `pRV` and `⇔`, guards on `a`, `b` dropped (**landed as `leMulCompatFull`**) | item 5: `RV/Kˣ` an ordered group | `axScale`, i.e. `S_M ⊨ valField` |
| 2 | `rvMulOne`, `rvMulInv` guarded by `pRV` | item 2: `(RV^×, 1, ×)` is a group | `rv a = rv b ↔ v (a-b) ≤ v b`, cancellation |
| 3 | `kAddLink`, `rvEqLink` (m3's `Axioms`) | the residue field is the residue field | the cover: `rv`-equality and residue atoms in `L_val` |
| 4 | `kJunkZero`, `kNegJunkZero` (or any fixed convention) | totality of the residue symbols | harmless, pins the junk |

Items 1 and 2 are one-sentence edits to existing axioms; items 3 and 4 are two new sentences plus
two conventions.  All four are decisions about the frozen encoding, and all four need the author's
ruling before the target `HasQE Axioms.ACVF` can be true, let alone proved.

### Correction on the "trivial valuation" case (swarm `smw1541fr`, m4)

Earlier in this file — following m1's `HasNontrivVal` docstring — I wrote that the trivially valued
structure on an algebraically closed field satisfies every axiom of the frozen `ACVF` and fails
nontriviality.  That is only true of the **fine** reading.  The **coarse** reading, "every
`VF`-element is `0` or has `rv x = rv 1`", is *inconsistent* with the frozen axioms: with `rvSurj`
it forces `RV = {∞, 1}`, hence `K = pInK` has at most two elements, contradicting `kAlgClosed` at
degree 2.  Machine-checked as `no_coarse_triv` in `.ultramath/smw1541fr/m4/Triv.lean`, with
`exists_rv_ne_one` as the positive form.

The consistent reading is m4's `FineTriv`: `rv` injective on `VF`, the order trivial
(`iLe (rv x) (rv y) ↔ x ≠ 0 ∨ y = 0`), `Kˣ` the nonzero elements, and the residue operations the
field's own.  In that case `HasNontrivVal` fails (all nonzero values are `≤ v 1`) and the structure
is a model.  So the final theorem's case split is `HasNontrivVal` versus its **negation**, and the
second case is `FineTriv`, not "rv constant".

Two reusable by-products of that direction, both unconditional (every model, not just the trivial
one):

```
rv_exists_vf  : (∃ a, iRV a ∧ ψ a) ↔ ψ ∞ ∨ ∃ x, iVF x ∧ x ≠ 0 ∧ ψ (rv x)
exSorted_rv_realize_vf   -- the same at the level of BoundedFormula
allSortedK_realize, kHyps_realize, exSortedK_realize   -- extraction for the pInK-guarded axioms
```

The first is exactly the `RV`-quantifier elimination step of the cover, from `rvSurj` alone; the
last three fill a real gap, since the preamble had no extraction lemma for the `K`-guarded axioms
and every residue-field argument needs one.

### The assembly skeleton, and the fragment that is already fully transferred

Two more directions came back (both accepted).  Together they turn the endgame into three named
hypotheses.

**`hasQE_ACVFplus_of_transfers`** (`.ultramath/smw1541fr/m6/FinalAssembly.lean`, in the tree's
`SpecialTransformations.Milestone0.HasQE` shape, proved not postulated):

```lean
NontrivialTransfer ACVFplus → TrivialTransfer ACVFplus → CaseSeparation ACVFplus →
  CaseSplit ACVFplus → SpecialTransformations.Milestone0.HasQE ACVFplus
```

with

* `NontrivialTransfer T`: models of `T` with the same quantifier-free `L_RV`-type satisfy the same
  formulas, *provided both are nontrivially valued* — this is where the cover (`L_val` + QE +
  `transfer_of_isQF`) plugs in;
* `TrivialTransfer T`: the same for the fine-trivial case, where the residue operations and `rv` are
  the field's own (`FineTriv`), so the `L_val` reading of every atom is quantifier-free and `ACF`'s
  QE suffices;
* `CaseSeparation T`: QF-equivalent models agree on triviality;
* `CaseSplit T`: every model is nontrivial or fine-trivial.

The compactness step `QFTypeDetermines → HasQE` is **closed** (`m6/QFComp.lean`): the step
`Assembly_val.lean` recorded as missing (`QFExDetermined → QEExStep`) already exists in the repo as
`QE/Bounded_compactness.lean`, whose `IffB` is the same `Prop` as `Theory.Iff`.

**Caveat on `CaseSeparation`, which is not bookkeeping.**  `IsTrivialVF` says every nonzero
`VF`-element has `v x ≤ v 1` — that quantifies over `VF`, so triviality is not a
quantifier-free condition, and QF-equivalent models need not agree on it.  The hypothesis is
therefore doing real work and must be justified (or eliminated) before the assembly counts as
complete; `m6/REPORT.md` says the same, and the plan records it here so it does not get lost.

**`frag_QE_sentence`** (`.ultramath/smw1541fr/m5/Cover.lean`): for every `L_RV`-formula in the
*image* of `L_val`, QE is proved outright — `hasQE_ACVF_val` plus `VFRestrict.transfer_of_isQF`,
with the model hypothesis `S ⊨ ValPM.ACVF_val` explicit.  So the transfer is complete on the
fragment, and what remains is precisely that every `L_RV`-formula lies in it — which is what the
`kAdd` defect blocks.

**A new fact worth having:** `Cover.rv_one : iRv iVFOne = iRVOne` — `rv (1) = 1` is not an axiom and
had been assumed by m4's `FineTriv` and by m1's docstrings.  It follows from the frozen axioms
through the group laws (`iRVOne` is idempotent, `rvSurj` gives a preimage, `iUnits` gives an
inverse).

### Correction: "per-model QE implies theory QE" is **false**

I proposed that as the compactness step that would let the trivial/nontrivial case split be handled
per model.  It is wrong, and m6's counterexample settles it: take the empty theory `T = ∅` in a
language with one unary predicate `P` and the one-point model `{a}` with `P = {a}`.  Every formula
is equivalent *in that model* to `⊤`, `⊥` or `P (x)`, so the model has QE; yet `∀ x, P x` has no
quantifier-free equivalent modulo `∅`.  The gap in my argument was real: proving `T` has QE needs
one model in which *every* candidate witness fails at once, and per-model QE only supplies a
witness per model.

The correct statement is the two-model one, `QECriterion.QFTypeDetermines T`: models with the same
quantifier-free type satisfy the same formulas.  That is what `m6/FinalAssembly.lean` uses, and what
`m6/QFComp.lean` closes against `QE/Bounded_compactness.lean`.  Everything in the section above
about the assembly stands; only the justification I gave for the case split was wrong, and the case
split is now carried by `NontrivialTransfer` + `TrivialTransfer` + `CaseSeparation` + `CaseSplit`
rather than by compactness on models.

### The assembly's `CaseSplit` is false as stated (m6's definition vs m4's theorem)

`m6/FinalAssembly.lean` states

```lean
IsNontrivialVF M : ∃ x, iVF x ∧ x ≠ iVFZero ∧ ¬ iLe (iRv iVFOne) (iRv x)
IsTrivialVF M    : ∀ x, iVF x → x = iVFZero ∨ iRv x = iRv iVFOne
CaseSplit T      : ∀ M, M ⊨ T → IsNontrivialVF M ∨ IsTrivialVF M
```

and m4's `no_coarse_triv` — accepted, machine-checked, merged into `Assembly_val.lean` — proves that
`IsTrivialVF` in that form is **empty**: no model of `Axioms.ACVF` satisfies it.  So `CaseSplit`
demands `IsNontrivialVF` in every model, and that fails in the fine-trivial case (a trivially valued
algebraically closed field: `vv x = 0` for all `x ≠ 0`, so `iLe (iRv 1) (iRv x)` holds for every
nonzero `x` and there is no witness for `IsNontrivialVF`).  `CaseSplit` is therefore not an open
hypothesis to be proved — it is false as stated, for the same reason m4's correction gives.

The right pairing is `IsNontrivialVF` against its **negation**, which reads

```
∀ x, iVF x → x ≠ iVFZero → iLe (iRv x) (iRv iVFOne)      -- every value is at most the value of 1
```

— "every nonzero element is in the valuation ring", which is the fine-trivial case and is exactly
the `ord` half of m4's `FineTriv`.  Classical logic gives the disjunction at once; what does *not*
come for free is the implication `x ∈ 𝒪 → vv x ≤ vv 1` for the inverse direction, since
`vv (x⁻¹) ≥ 0` must be turned into `vv x ≤ 0`, and that is scaling by an element of `RV^×` — repair
item 1 again.  So even this one-line case split waits on the same ruling.

`TrivialTransfer` is stated against the empty predicate, so as written it is vacuously true and
carries no content; when the trivial case is restated as the negation of `IsNontrivialVF`, m4's
`FineTriv` dictionary is the right content for it.  This must be fixed before the assembly's
hypothesis list is quoted anywhere — or, better, dropped: the last section shows that adding
nontriviality to the theory removes the case split altogether, so `CaseSplit`, `CaseSeparation` and
`TrivialTransfer` should not be repaired but removed from the endgame.

### Third refutation, and the simplification it forces: add nontriviality, drop the case split

Swarm `smw1541fr` m1 (`m1/PerModelQE.lean`, accepted; green, axioms clean) proved the general
engine

```
sentence_iff_of_qfSentence_iff : HasQE T → (models agreeing on all QF sentences are elementarily equivalent)
not_hasQE_of_qfSentence_equiv  : the refutation form
hasQE_of_qfSeparated           : two QE model classes + a quantifier-free separator ⇒ HasQE
```

and turned it on `ACVF`.  Every closed `L_RV` term is a numeral, or `rv`, `·`, `kAdd`, `kNeg`,
`kMul` applied to numerals, so a quantifier-free `L_RV` sentence is arithmetic on `rv (n)`; in a
trivially valued and in a nontrivially valued algebraically closed field of the *same* residue
characteristic, `rv (n) = rv (1)` for every `n ≠ 0`, so the two agree on **all** quantifier-free
sentences — while they disagree on nontriviality, `∃ x ∈ VF, x ≠ 0 ∧ ¬ (v x ≤ v 1)`.  Hence

**`HasQE (Axioms.ACVF ∪ {leMulCompatFull})` is false**, and the frozen statement fails for a third
reason, disjoint from the coarsening (item 5) and the residue-link (item 3) ones.

Two consequences, and the second is a real simplification.

1. **The repair list gains nontriviality.**  The paper's own theorems need it — Theorem 2.8
   (C-minimality) is false for a trivially valued field, and `ValPM.ACVF_val` carries
   `axNontrivial` for exactly that reason — so the axiom set must exclude the trivial valuation.
   As an `L_RV` sentence: `∃ x, pVF x ⊓ ∼(x = 0) ⊓ ∼(pLe (tRv x) (tRv tVFOne))`, the exact
   transport of `ValPM.axNontrivial`.
2. **The case split disappears.**  With nontriviality in the theory, m6's `CaseSplit`,
   `CaseSeparation` and `TrivialTransfer` are all unnecessary: the endgame is
   `model_ACVF_val_of_axioms` (items 1, 2 + `IsAlgClosed` + nontriviality) + `hasQE_ACVF_val` +
   the cover (item 3) + `transfer_of_isQF`, glued by `QFTypeDetermines` — one case, no gluing, no
   separator.  m4's `FineTriv` work stays useful as the characterisation of what is being
   excluded, and m1's `hasQE_of_qfSeparated` records exactly why gluing would have needed a
   quantifier-free separator that triviality cannot supply.

Revised repair list, now five items:

| # | edit | restores | status |
| --- | --- | --- | --- |
| 1 | `leMulCompat` with `pRV`, `⇔`, guards on `a`,`b` dropped | item 5, `RV/Kˣ` ordered | **in the tree** (`leMulCompatFull`) |
| 2 | `rvMulOne`, `rvMulInv` guarded by `pRV` | item 2, `RV^×` a group | needed for `rv`-equality and cancellation |
| 3 | `kAddLink`, `rvEqLink` | the residue field is the residue field | needed for the cover |
| 4 | `kJunkZero`, `kNegJunkZero` | junk conventions | harmless, pins the symbols |
| 5 | `axNontrivial` in `L_RV` | nontriviality | **needed, and it replaces the case split** |

### The atom translations, and the swarm is solved (6/6)

Swarm `smw1541fr` ended solved: six directions accepted.  The last two pieces:

**The four `rv`-atoms** (`m2/PLeUnits.lean`, green, axioms clean).  An `L_RV`-atom mentioning `rv` of
a `VF`-term is one of exactly four things, and three are translated unconditionally:

| `L_RV` atom | `L_val` image | status |
| --- | --- | --- |
| `pLe (rv s) (rv t)` | `leF t s` (`v t ≤ v s` — the swap is the reversal) | `translate_pLe`, unconditional |
| `pUnits (rv s)` | `v s = v 1` (`leOneF s`) | `leOneF_iff_pUnits`, unconditional |
| `pInK (rv s)` | `v s = v 1 ∨ s = 0` (`inKF s`) | `inKF_iff_pInK`, unconditional |
| `pEq (rv s) (rv t)` | `leEqF s t` | **conditional on `rvFibreIff`** |

with the junk cases (`not_units_zero`, `pUnits_tRv_zero`, `leOneF_zero`, `leOneF_ne_zero`) settled,
and two facts *derived* that no axiom states: `not_units_zero : ¬ iUnits iRVZero` (from `rvMulInv` at
`0`, `rvMulInfty` and `kField`'s unguarded `0 ≠ 1`), which removes the `pRV` guard from
`leClassOne`; and `rv_one_eq : iRv 1 = iRVOne`, which m5 also proved by a different route — two
independent proofs of a fact two directions had silently assumed.

`rvFibreIff` is the repair sentence that makes the fourth atom provable:

```
pEq (rv s) (rv t) ⇔ (pLe (rv s) (rv t) ⊓ pLe (rv t) (rv s) ⊓ (s = 0 ⊔ (…v (s - t) < v s…)))
```

i.e. `rv`-equality is order-equivalence together with the value comparison `v (s - t) < v s` — the
familiar `a/b ∈ 1 + 𝔪`.  This is repair item 3 in its final form, and it is what `m3`'s
`kAddLink`/`rvEqLink` pair was pointing at.

**Swarm state**: 6 of 6 accepted, all files green with axioms clean.  Two directions independently
located the same obstruction (m3 from the residue operations, m2 from the order/predicate atoms), and
two independently proved `rv 1 = 1`.  The repair list stands at five items, with items 1 and 5
already in the tree as `leMulCompatFull` and (pending) `axNontrivialRV`.

## The repair is applied, and the extraction is unconditional

`Milestone0/Encoding.lean` now carries `Axioms.repairRV` (additive: `leMulCompatFull`,
`rvMulOneRV`, `rvMulInvRV`, `kAddLink`, `kNegLink`, `rvEqLink`, `kJunkZero`,
`kNegJunkZero`, `axNontrivialRV`), and `QE/Assembly_val.lean` carries the same set.  Consequences
in the tree, all green and axiom-clean:

* `Transfer.paperScale_of_model : M ⊨ ACVF → PaperScale M` — item 5 as a theorem, not a hypothesis;
* `Transfer.hasNontrivVal_of_model : M ⊨ ACVF → HasNontrivVal M`;
* `Transfer.model_ACVF_val_of_model : M ⊨ ACVF → (VFType) ⊨ ValPM.ACVF_val` — the extraction,
  with no hypotheses at all.

So the endgame is now: `hasQE_ACVF_val` (proved) + the cover (swarm `smw163dd5`) +
`transfer_of_isQF` + `QFTypeDetermines` (proved) ⇒ `HasQE Axioms.ACVF`.  The case split is not
needed, because nontriviality is an axiom now.

## The target is one hypothesis away

With the repair applied and m6's f6 direction merged (`TrivialHalf`, `FineQE`), the tree now has

```lean
Transfer.hasQE_ACVF_of_nontrivialTransfer :
  FinalAssembly.NontrivialTransfer Axioms.ACVF → SpecialTransformations.Milestone0.HasQE Axioms.ACVF
```

— that is Theorem 2.3, from a single hypothesis.  The three things that used to be hypotheses are
gone: the trivial half is vacuous (`TrivialHalf.trivialTransfer`, since the coarse trivial reading is
unsatisfiable), the case split follows from nontriviality (`caseSplit_of_allNontrivial`), and
nontriviality itself is now an axiom, converted to the `IsNontrivialVF` form the assembly wants by
`Transfer.isNontrivialVF_of_model` (an `RV^×`-inverse lifted through `rvSurj`, then scaling by
`v a` — which is where item 2 and item 5 of the repair are actually used).

`NontrivialTransfer T` is: two models of `T` with the same quantifier-free `L_RV`-type at matching
tuples satisfy the same formulas.  Discharging it is *exactly* the cover plus QE in `L_val`: the
cover turns an `L_RV`-formula into `valFormulaToRVvf θ`, `hasQE_ACVF_val` replaces `θ` by a
quantifier-free `θ'` in the `L_val`-structure on the `VF` sort (a model of `ValPM.ACVF_val` by
`model_ACVF_val_of_model`), and `VFRestrict.transfer_of_isQF` reads `valFormulaToRV θ'` back.  Swarm
`smw163dd5` is producing the cover now; when it lands, Theorem 2.3 is closed.

## The cover cannot be term-level (m1's counterexample)

`RVNF` (swarm `smw163dd5`, accepted, in the tree) settles a premise of the cover the wrong way
round, and that is worth knowing before anyone spends a day on it: the *literal* normal form "every
`RV`-term is, at every `VF`-tuple, either `0` or `rv s` for one `L_val`-term `s`" is **false** in
every nontrivially valued model.  The term

```
T := kAdd (mul (kAdd (rv v₀) (rv v₁)) (rv v₂)) (rv 1)
```

is `rv 1` wherever `v (v₀ + v₁) > 0` — the inner `kAdd` lands in `𝔪`, so it is `0`, and `0 · b = 0`
forgets `v₂` — while at `(1, 0, c)` it is `rv (c+1)`.  So no single `s` works, and the cover must be
*formula-level with a guard per candidate*, not term-level.

What survives, and what `RVNF` proves, is the finite-**list** normal form:
`t = 0 ∨ ∃ s ∈ t.vals, t = rv s`, where `vals` is closed under sums and products
(`vals (kAdd a b) = vals a ++ vals b ++ (vals a + vals b)`), together with the per-construct axiom
accounting (`rv` needs none; `mul` uses `rvMulHom` and `rvMulInfty`; `kAdd` both branches of
`kAddLink` plus `kJunkZero`; `kNeg` the `kNegLink` pair), the residue-operation lemmas
(`iKAdd_rv_rv`, `iKAdd_zero_rv`, `iKAdd_rv_zero`, `iKNeg_rv`, `iKAdd_mem_K`, `iKNeg_mem_K`,
`iRVMul_*`, `iRv_eq_zero_iff`), and `MulTerm`, where the normal form *is* exact (`t = rv valT`) and
the three atoms are single quantifier-free `L_val` formulas.

**One reconciliation outstanding**: `RVNF`'s theorems are stated for
`ACVFrep = ACVF ∪ residueLink ∪ {M2.rvFibreIff}`, while the tree's repaired `ACVF` carries
`rvEqLink`.  `rvFibreIff` — `rv s = rv t ↔ (rv s ~ rv t ∧ (s = 0 ∨ v (s−t) > v s))` — should follow
from `rvEqLink` (`rv s = rv t ↔ ¬ (v t ≤ v (s − t))`) by transitivity of `≤`, and that derivation is
a ten-line lemma nobody has written yet.  Until it is, `RVNF`'s results are conditional on
`rvFibreIff`.

## Correction: `rvEqLink` had transposed arguments, and the repair was inconsistent

Swarm `smw163dd5` member m5 audited the repair (`m5/Audit.lean`, green, axioms clean) and found
that `Axioms.rvEqLink` — the residue-equality link I added — had its two `pLe` arguments the wrong
way round.  At `x = y = 1` it read `rv 1 = rv 1 ↔ ¬ (v 1 ≤ v 0)`, which `leTop` refutes, so
`RepairAudit.ACVF_no_model : (M ⊨ Axioms.ACVF) → False` was a theorem and the repaired theory was
**inconsistent**.  Everything proved from it — `paperScale_of_model`, `model_ACVF_val_of_model`,
`hasQE_ACVF_of_nontrivialTransfer` — was therefore vacuous: true, but for the wrong reason.

The fix is one transposition, and the corrected sentence is the one m2's accepted `rvFibreIff`
already carried:

```
rv a = rv b  ↔  ¬ (v (a - b) ≤ v b)
```

Applied to `Milestone0/Encoding.lean` and to `QE/Assembly_val.lean`; both compile, and the
instantiation that refuted the old form passes on the new one (`m5.Fixed.rvEqLinkFixed_instance`).
New hash of `Encoding.lean`: `2012dfe0dd103f0aa3ccd0a87114ad75ce844dc6388afd76e94f876e0c7c62f5`.

What this changes in the record: the repaired theory is now *not known to be inconsistent*, which
is strictly weaker than known consistent.  No model of it exists in the tree, so the honest status
of every theorem derived from `repairRV` is "derived from a theory whose consistency is open".  The
next artifact that would settle this is a model — `RVModel.lean` extended to `repairRV` — and that
is now the highest-value thing in the campaign, ahead of the cover, because a second sign error in
the repair would make the cover pointless in the same way.

Also resolved by the same direction: `rvFibreIff` follows from the corrected link in both
directions (`leEqF_iff_pEq_of_link`), which closes the reconciliation between `RVNF` and the tree's
axiom set.

## The cover is reduced to one dictionary hypothesis

`RVElim` (swarm `smw163dd5` m3, accepted, merged) does the quantifier half of the cover and leaves
the atoms:

* `bfSubst`/`realize_bfSubst`, `substLast`, `substLastWith` — substitution under binders, which the
  tree lacked and which is why earlier attempts at the quantifier step stalled;
* `rvExElim`/`rvAllElim` — `∃ y ∈ RV, ψ  ↔  ψ[∞] ∨ ∃ x ∈ VF∖{0}, ψ[rv x]`, at tuples of any sort,
  from `rvSurj` alone; and `all_split`/`ex_split`, which split an unguarded quantifier into a `VF`
  and an `RV` part using only `sdCover`/`sdDisjoint`;
* `exists_VFQ` — every formula is uniformly equivalent at `VF`-tuples to one whose only quantifiers
  are `∀x ∈ VF`, i.e. `valFormulaToRVvf`'s shape;
* `coverVF_of_atoms : AtomCover → CoverBridge.CoverVF Axioms.ACVF`.

So the cover now rests on `AtomCover`: an `L_val` description of each `L_RV` atom at `VF`-tuples.
Three of the four atoms are already unconditional in the tree (`Transfer.M2.translate_pLe`,
`leOneF_iff_pUnits`, `inKF_iff_pInK`), and the fourth — `rv s = rv t` — is `RepairFixed.leEqF_iff_pEq_of_link`,
which derives it from the corrected `rvEqLink` (commit `6ee852c`) rather than assuming a separate
sentence.  Assembling `AtomCover` from those four is the last step of the cover.

`RepairFixed` (m5's `Fixed.lean`, merged) also carries the corrected link and its porting lemmas, so
the tree and `Milestone0/Encoding.lean` now agree on the repair's exact sentences.

## The cover must be stated for the well-sorted sublanguage (or the junk must be pinned)

Swarm `smw163dd5` m2 (accepted) found an encoding-level obstruction that no amount of proof work
can get around: `L_RV` is a **one-sorted** encoding of a two-sorted language, so `BoundedFormula`
admits ill-sorted terms — `rv (rv x)`, the `VF` operations at an `RV` element, `kAdd` at a `VF`
element — and **no axiom constrains the junk values**.  `sortClosure` only says `rv` maps `VF` into
`RV`, and `sdCover`/`sdDisjoint` only say the carrier is a disjoint union.  So the truth of an atom
containing such a term is not a function of the `L_val`-structure, and

```
CoverBridge.CoverVF Axioms.ACVF      -- quantifies over all BoundedFormula
RVElim.AtomCover                     -- its `eq`/`rel` fields quantify over all Tm n
```

are **false**, not merely unproved.

Two ways out, and they are not exclusive:

1. **State the cover on the well-sorted sublanguage** — the paper's actual two-sorted `L_RV`, where
   `rv : VF → RV` and no ill-sorted term exists.  This is what `QFCover`/`QFRes` do, and it is the
   right level for the *mathematics*: the paper's formulas are well-sorted, so the theorem that
   matters is about them.
2. **Pin the junk values**, which is a repair item: for every function symbol, a sentence fixing its
   value at arguments outside its intended sort.  `Milestone0/Partiality.lean` already proves this is
   conservative — totalising the paper's partial symbols with junk `= ∞` is conservative under two
   hypotheses that Definition 2.1(2d) supplies — so this is bookkeeping in principle, but it is a
   finite list of sentences per symbol per wrong sort.

Which of the two the frozen target needs depends on what `HasQE` is supposed to quantify over.  The
frozen `HasQE` quantifies over *all* `BoundedFormula`s, so as it stands it needs (2); the paper's
Theorem 2.3 needs only (1).  This is a decision about the target statement, and it is the same
decision as the trivial-valuation one in kind: how much of the one-sorted encoding the theorem is
supposed to be about.

## Constraints any model of the repaired `ACVF` must satisfy (swarm `smw16q93m` m1)

Nobody has built a model yet, but the necessary conditions are now machine-checked, and one of them
kills the obvious construction:

* **The order cannot be `u ≠ ∞ ∧ vrv u ≤ vrv v`.**  `rvUltrametric` at `x = y = 0` forces
  `iLe ∞ ∞` (`le_infty_self`), and with `leInftyEq` the first column is exactly `{∞}`
  (`le_infty_iff`).  The correct reading of `≤` on `RV` is

  ```
  iLe u v  :=  (u = ∞ → v = ∞) ∧ vrv u ≤ vrv v
  ```

  which is reflexive at `∞` — the naive form is *inconsistent* with the frozen axioms.
* `kAddLink` is well posed only because, at units, `rv x = rv y` with `x ≠ y` forces `rv (x - y)` to
  be a non-unit.  That is the lemma the residue-addition construction must prove, and it is now
  available from the axioms.
* Nontriviality gives a strictly positive `RV`-element, hence `Kˣ ⊊ RV ∖ {0}`; `Kˣ` is closed under
  negation and `rv (-1)` is a unit.
* The junk conventions do force `0` off `K`, as intended.
* **`ACVF(0,0) ≠ ACVF`**: the characteristic-0 schemes are *not* derivable from the rest, since
  `rv (n·1)` remembers the residue of `n`.  The repository's `ACVF(0,0)` and `ACVF_S(0,0)` are
  genuinely stronger theories, not notation.

## The repaired axioms have a candidate model, and the field is Mathlib's

Two results from swarm `smw16q93m` (m1, m6; accepted, green, axioms clean) move the consistency
question from open to nearly closed.

**The field.** Mathlib's `PadicComplex p` (`ℂ_[p]`) is algebraically closed, of characteristic 0,
with a **nontrivial** valuation `v : ℂ_[p] → ℝ≥0` (`v p = 1/p`) and an algebraically closed residue
field.  Since `ℝ≥0` is a `LinearOrderedCommGroupWithZero`, `Milestone0/RVModel.lean` applies to it
verbatim, and `axNontrivialRV` is `v p < v 1`.  No construction was needed for g1.

**The structure and the repair's content.** Over an arbitrary `Valuation K Γ₀`, `Model.lean`
builds the carrier `K ⊕ Option (Kˣ ⧸ (1+𝔪))`, all twelve function and four relation symbols total
with junk conventions, `LRV.Structure`, and proves the mathematical content of the repaired
sentences as lemmas: `rv x = rv y ↔ v (x - y) < v y` (the corrected `rvEqLink`, right sign),
`kAddAux_congr` (the residue sum is well defined on `rv`-classes — the part that could have failed),
`kAdd_units`/`kAdd_junk_*` (`kAddLink`, `kJunkZero`), `kNeg_units`/`kNeg_junk`, and
`rvLe_rvMul_iff : c ≠ 0 → (a·c ≤ b·c ↔ a ≤ b)` (`leMulCompatFull`).

So the nine repaired sentences are no longer hypotheses in search of a model; they are theorems
about a Mathlib valuation.  Still missing for `Theory.Model Axioms.ACVF` of that structure: the
case analysis over the axiom list (bookkeeping over the union, plus the `Fin.snoc`/match steps in
realization) and `kField`, `kAlgClosed`, `vfAlgClosed`.  Until that lands, the honest status stays
"not known to be inconsistent", but the distance is now bookkeeping rather than mathematics.

### The well-sorted cover is in the tree

`QFCover` and `QFRes` (swarm `smw163dd5` m2, accepted, merged) give the quantifier-free cover for
the *well-sorted* sublanguage — the paper's two-sorted `L_RV` — at `VF`-tuples:

* `QFCover.qf_cover` / `qf_cover_at` / `qfq_cover`: the multiplicative fragment, needing only
  `rvFibreIff`, with a single `θ = φ.toVal` covering every formula at every `VF`-tuple;
* `QFCover.exists_qf_of_covered`: from `HasQEb ValPM.ACVF_val` and `VFType ⊨ ValPM.ACVF_val`, a
  quantifier-free witness outright — no `CoverVF` hypothesis;
* `QFRes.qf_cover` / `qfq_cover`: the same with `kAdd`/`kNeg`, via the case-splitting presentation
  `RVT.pres` (no single term exists, by m1's counterexample), with the hypotheses `rvFibreIff`,
  `KAddAdditive`, `KNegAdditive`, `KJunkZero`, `KNegJunkZero` — all of which are consequences of the
  repaired axioms in `Model.lean`'s valuation setting.

So on the well-sorted fragment the cover is no longer a hypothesis; what remains for it is
`RV`-quantifiers, which is `RVElim`'s `exists_VFQ` and is also in the tree.
