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
