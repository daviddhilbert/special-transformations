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

## The repair is consistent (m3, swarm `smw16q93m`, accepted)

```
IModel.model_repairRV (v : Valuation K Γ₀) {x : K} (hx : x ≠ 0) (hv : v x < 1) :
  (C v) ⊨ Repair.repairRV
```

— all nine sentences of the repaired axiom set hold at the intended `L_RV`-structure of an arbitrary
non-trivially valued field, proved one sentence at a time.  With `PadicComplex p` and `x = p` (so
`v p = 1/p < 1`) this is an unconditional consistency proof **relative to a Mathlib-valued field**,
and it retires the caveat that the `rvEqLink` erratum put on everything derived from `repairRV`.

Two findings recorded with it:

1. **`kJunkZero` forces the strict junk convention**: `kAdd t s = 0` unless *both* arguments are in
   `K`.  The accepted `Milestone0/accepted/ACVF_residue_ops.lean` defines `kAdd` as
   `ofK (kOf t + kOf s)`, which returns `s` when `t ∉ K` and `s ∈ K` — so that file's `kAdd` *fails*
   `kJunkZero`.  The model is that file with the single definition replaced by
   `if IK t ∧ IK s then ofK (kOf t + kOf s) else none`.  An accepted artifact is thus corrected, and
   the correction is recorded rather than smoothed over.
2. **`rvEqLink` holds at the intended structure**, including `a = b ≠ 0`
   (`rv_eq_iff_lt : rv a = rv b ↔ v (a - b) < v b`), independently confirming the transposition fix
   of commit `6ee852c`.

Still not claimed: `kField`, `kAlgClosed`, `rvDivisible` — the three hypotheses of the accepted
`model_ACVF_of_components` — so `(C v) ⊨ Axioms.ACVF` is not yet asserted.  With `PadicComplex p`
those concern an algebraically closed residue field and a divisible value group.

## Decision: the target is restated over the well-sorted fragment

The author's ruling: `HasQE` is restated over the well-sorted fragment rather than adding junk
conventions for every symbol at every wrong sort.  So the target becomes

```
HasQE T := ∀ (α) (sα : α → SortTag) (n) (sn : Fin n → SortTag) (φ : LRV.BoundedFormula α n),
  WellSorted sα sn φ → ∃ ψ, ψ.IsQF ∧ WellSorted sα sn ψ ∧
    T ⊨ᵇ (sortedHyps sα sn ⟹ (φ ⇔ ψ))
```

with `WellSorted` the syntactic sort discipline for the one-sorted encoding: terms carry a sort
(`rv t` needs `t : VF` and gives `RV`; the `VF` ring symbols need `VF` and give `VF`; `·`, `kAdd`,
`kNeg` on `RV` need `RV` and give `RV`; the constants have their sorts), atoms are formed only
between terms of one sort and with the relations' declared sorts (`memVF`/`memRV`/`memUnits` need
`RV`-sorted arguments except `memVF`, which needs a `VF` one; `rvLe` needs two `RV` ones), and a
quantifier is admitted only in guarded form, `∀ x, x ∈ s → ψ`, so no quantification over the
carrier escapes the sorts.  The equivalence is relativised to tuples of the declared sorts
(`sortedHyps`, already in the file), which is what makes it a statement about the paper's two-sorted
language rather than about junk.

Why this is the right choice: the paper's `L_RV` **is** two-sorted, so ill-sorted terms are not its
formulas at all; freezing them would be axiomatising the encoding's artefact rather than the
mathematics.  And the well-sorted fragment is exactly what the merged cover covers — `QFCover`/
`QFRes` build sorted terms (`VFT`/`RVT`) and sorted quantifier-free formulas, and `RVElim.exists_VFQ`
does the quantifier step — so this restatement is what the existing proofs already establish.

## The model is complete on both halves; only the gluing is missing

Swarm `smw16q93m` ended solved (4 accepted), and between m4 and m3 the model exists in pieces:

| half | file | what is proved |
| --- | --- | --- |
| frozen `ACVFpaper` | `m4/ACVFModel_repair.lean` (3,211 lines, `import Mathlib` only, with a byte-identical copy of the repo's language and `Axioms`) | `model_ACVFpaper` at `C v = K ⊕ Option (Kˣ/(1+𝔪))`: `sortAxioms` 16/16, `vfField` 10/10, `vfAlgClosed`, `kField` 10/10, `kAlgClosed`, `rvGroup` incl. divisibility, `preorderRV` 7/7, `rvAxioms` 5/5 |
| `repairRV` | `m3/EqLink.lean` | all nine repaired sentences, one at a time (`model_repairRV`), over any field with a valuation and an element of value `< 1` |
| the field | `m6/Model.lean`, `m1/Necessary.lean` | `PadicComplex p` is algebraically closed, char 0, with a nontrivial valuation into `ℝ≥0` (`v p = 1/p`), and `le` on `RV` must be stated `(u = ∞ → v = ∞) ∧ vrv u ≤ vrv v` |

So the model's mathematical content is done on both halves, 11 + 9 sentence footprints, all clean.
What is *not* done is the last gluing: `Axioms.ACVF = sortAxioms ∪ ACVFpaper` with `repairRV ⊆ ACVFpaper`,
so `(C v) ⊨ Axioms.ACVF` follows by combining `model_ACVFpaper` with `model_repairRV` (a union of two
`Theory.Model`s, then the sort axioms), and instantiated at `PadicComplex p` with `x = p` it also
discharges `axNontrivialRV`.  That is bookkeeping over two unions, and it is the last step standing
between the tree and "the repaired axioms have a model, in Lean".

## The tuple-level QE is in the tree (`hasQEb_of_hasQE`)

The direct route needs quantifier elimination *at tuples*, not only for sentences with parameters.
That reduction is now proved:

```
Transfer.hasQEb_of_hasQE (h : QECriterion.HasQE T) (α) (n) (φ : LRV.BoundedFormula α n) :
  ∃ ψ : LRV.Formula (α ⊕ Fin n), ψ.IsQF ∧
    ∀ (M) [LRV.Structure M] [Nonempty M], M ⊨ T → ∀ v x,
      (φ.Realize v x ↔ ψ.Realize (Sum.elim v x))
```

— a formula with `n` free variables is the sentence `φ.toFormula` over the parameter type
`α ⊕ Fin n`, `T ⊨ᵇ` for that sentence is exactly the pointwise equivalence
(`Theory.realize_iff`), and `BoundedFormula.realize_toFormula` identifies the two realizatons.  The
witness is allowed to use the tuple as parameters, which is what the transfer consumes.

With this, the two obligations that stood between the direct route and `HasQE` are down to one:
`AtomCover` (assembly from `M2.translate_pLe`, `leOneF_iff_pUnits`, `inKF_iff_pInK`,
`RepairFixed.leEqF_iff_pEq_of_link` and the cross-sort facts) — on the well-sorted fragment, whose
`WellSorted` the swarm `smw17pts2` is building.  `NontrivialTransfer` does not appear anywhere on
that route.

## What the restatement actually leaves to prove (m1, swarm `smw17pts2`)

Two corrections to my own framing, both from m1's accepted direction:

1. **The quantifier-free case is trivial.** For well-sorted QF `φ`, the witness is `ψ := φ`, for
   *every* theory `T`, with no hypothesis at all — so the entire content of the restated `HasQE` is
   the quantifier step.  I had implied the QF case needed the cover; it does not, and the cover's
   role is exactly to reduce an arbitrary well-sorted formula to a quantifier-free one.
2. **`hasQEb_ACVF_val : QECriterion.HasQEb ValPM.ACVF_val` is proved unconditionally** — the
   tuple-level QE for the `L_val` theory, where the tree previously had only the sentence shape.
   With `VFRestrict.vfStruct hM = vfValStruct hM` identified, `QFCover_exists_qf` needs only
   `rvFibreIff` and `QFRes_exists_qf` only a model of `RVNF.ACVFrep`.

So the restated target reduces to: *every well-sorted formula is equivalent, at tuples of the
declared sorts, to a quantifier-free one* — with the quantifier elimination of `RV` done
(`RVElim.exists_VFQ`) and the atom dictionary available.  The remaining work is the composition,
which is h4.  `rvEqLink ⇒ rvFibreIff` is *not* open: `RepairFixed.leEqF_iff_pEq_of_link` derives the
`rv`-equality atom from the corrected link.

The two `WellSorted` constructions (mine in `Encoding.lean` by the image of the sorted syntax, m1's
by a recursive `TmSort` with a guard predicate) agree on content; mine relativises the sorts
semantically (`sortEval` on the assignments), which avoids the ill-sorted-parameter defect m1 flags
in the syntactic-guard formulation.

## The two formulations of the restatement agree, and the axiom audit is machine-checked

m3 (accepted, `Downstream.lean`/`AuditAxioms.lean`, green):

* `hasQEws_iff_semantic` — the guarded formulation `T ⊨ᵇ (sortedHyps ⟹ (φ ⇔ ψ))` and the semantic
  one ("agree at every declared-sort tuple in every model") are **equivalent**.  So the
  `Encoding.lean` patch (semantic, `sortEval`) and the swarm's guarded version are the same
  statement, and the ill-sorted-parameter defect m1 flagged cannot arise in either.
* `qf_sentence_of_HasQEws` — at `Fin 0` the restated conclusion is literally the old one.
* `vf_tuple_version` — at `sn ≡ .vf` it is exactly `exists_qf_of_coverVF`'s conclusion, with no
  cover hypothesis.
* `hasQEws_of_hasQEws_param` — the general `α`/`sα` statement implies the `Empty`-parameter one.

**Axiom audit, machine-checked**: `sdCover`, `sdDisjoint`, `sdUnits` are *not well-sorted* — and they
are exactly the three sentences that axiomatise the **one-sorted carrier**, not the paper's
two-sorted language.  The other ~55 axioms are well-sorted.  So `ACVF` contains statements outside
the fragment, which is correct (they describe the encoding's carrier) and must be said, and now it
is checked rather than assumed.  `not_isQF_exSorted` gives non-vacuity, `sortedHyps_satisfiable`
gives that every sort assignment is realised in every model, and `isBoolComb_of_HasQEws` reduces
Theorem 2.8 (C-minimality) to the restated QE plus the tree's missing fact that quantifier-free
one-variable formulas define Boolean combinations of balls.

## The statement of QE is frozen; the proof runs in parallel (author's ruling)

Only the *statement* of Theorem 2.3 is needed for the paper's downstream development, so the
campaign splits:

* **The statement is frozen and green.**  `Milestone0/Encoding.lean`'s `HasQE` is the restated,
  well-sorted form (`d01d590b7bdc0b8912617aea0eb44e9fb2acf7349db2535f9ee7f84961ddf995`, and the
  hash moves again when the `sorry` is replaced).  See `DECISION.md`.
* **Everything downstream is developed against it as a hypothesis**, not against its proof:
  `Downstream.hasQEws_iff_semantic` (the guarded and semantic forms of the statement agree),
  `qf_sentence_of_HasQEws` (at sentences it is the old form), `vf_tuple_version` (at `VF`-tuples it
  is exactly `exists_qf_of_coverVF`'s conclusion), `hasQEws_of_hasQEws_param`, plus
  `isBoolComb_of_HasQEws`, which reduces Theorem 2.8 (C-minimality) to `HasQE` together with the
  statement that quantifier-free one-variable formulas define Boolean combinations of balls.  Those
  are merged into `QE/Assembly_val.lean` (20,833 lines, green).
* **The proof of QE keeps running** — h4's quantifier step in swarm `smw17pts2`, and the model
  gluing in `smw18cfdk`.

So the meaning of the `sorry` in `Encoding.lean` has changed from "the target of the campaign" to
"the one statement whose proof is in flight, while its consequences are being developed".  The
paper's Theorem 2.8 work can now proceed on that basis.

## The repaired axiom set has a model — proved

`.ultramath/smw18cfdk/m1/ACVFModel_full.lean` (3,820 lines, self-contained, green, no sorry/axiom):

```
IModel.model_ACVF (v : Valuation K Γ₀) [IsAlgClosed K] {x : K} (hx : x ≠ 0) (hv : v x < 1) :
  (C v) ⊨ Axioms.ACVF,      C v = K ⊕ Option (Kˣ/(1+𝔪))
```

unconditionally in everything but the field.  So the axiom set of `Milestone0/Encoding.lean` — the
frozen Definition 2.2 axioms plus `repairRV` — **is satisfiable**, and the caveat that everything
proved from `repairRV` was conditional on consistency is retired.

How it was done, and why it is credible: it stays entirely on m4's carrier and m4's `Repair2`
residue bridge, so no two files' `C`/`kAdd`/`rv` were mixed — the reconciliation risk I flagged when
setting the direction was avoided rather than papered over.  It does the case analysis over the
literal list `Axioms.repairRV` (nine sentences), then `rw [Axioms.ACVFpaper]` with eight
`model_union`s (`repairRV` occurs twice in that union), then `Axioms.ACVF = sortAxioms ∪ ACVFpaper`.
The only divergence from the repository text is `abbrev LRV` for `def LRV` in the copied prefix —
the same term, with `LRV_eq_mk` by `rfl` and no axioms; the diff of lines 17–650 is exactly that
line.  `model_ACVF'` takes nontriviality as an existential instead.

Missing: instantiation at `PadicComplex p` (`m3/Base.lean` has `padic_valuation_lt_one`), which is
the other direction of that swarm and would make the consistency statement closed — no hypotheses
at all.

### Closed: `Axioms.ACVF` is satisfiable, no hypotheses

`swm18cfdk` m2 (accepted) delivers the closed statements:

```
IModel.model_ACVF_padic {p} [Fact p.Prime] : (C (PadicComplex.valued p).v) ⊨ Axioms.ACVF
IModel.exists_model_ACVF : ∃ (M : Type) (_ : LRV.Structure M), Theory.Model M Axioms.ACVF
IModel.isSatisfiable_ACVF : Theory.IsSatisfiable Axioms.ACVF
```

on a concrete Mathlib object (`PadicComplex.isAlgClosed`, `padic_ne_zero`,
`padic_valuation_lt_one`), assembled in the exact union order of `Axioms.ACVFpaper` (where
`repairRV` occurs twice) and of `Axioms.ACVF = sortAxioms ∪ ACVFpaper`, with the list case analysis
done by elaboration.

**Reconciliation note that mattered**: m3's `Repair.*` sentences are textually identical to the
tree's, but m3's `kIn`/`kOf`/`kNeg` differ definitionally from m4's `kIn`/`jota`/`kNegFun` (no junk
guard on `kNeg`), so m3's proofs were *not* ported; the nine sentences were reproved on m4's carrier
and its `Repair2` bridge.  That was the trap in the direction and it was avoided rather than stepped
in.

## Theorem 2.8's statement is frozen, and Section 3 has started (author's ruling)

Both Section 2 targets are now statements-only, with their proofs running in parallel:

* `HasQE ACVF` — restated over the well-sorted fragment, green, hash in `DECISION.md`;
* `theorem_2_8_c_minimal : ∀ (M) [LRV.Structure M] [Nonempty M], M ⊨ ACVF → IsCMinimal M` — frozen.
  The axiom set now contains nontriviality, so this quantifies over the right class of models
  (C-minimality is false for a trivially valued field), and `Axioms.ACVF` is known satisfiable, so
  the statement is not vacuous.  One audit remains on it, of the same kind that `HasQE` needed:
  `IsCMinimal` quantifies over definable subsets — if its parameters range over the whole carrier,
  ill-sorted parameters raise the junk problem again and the statement needs the well-sorted
  relativisation too.  That is a statement question, not a proof question, and it is recorded here
  rather than left implicit.

`SpecialTransformations/*.lean` are stubs (17–38 lines, no proofs), so the paper's Section 3 —
$\RV[*,\cdot]$ objects, the lifting map $\mathbb{L}$, special bijections — is untouched.  Swarm
`smw18ygko` (4 directions) is on it: s1 freezes Section 3's statements in Lean the way the Section 2
targets were frozen, s2 formalizes the objects and their category, s3 the lifting map, s4 the
special bijection and its first theorem with the Section 2 facts named as hypotheses.

## The unrestricted `IsCMinimal` is false — the restatement was the only true form

Swarm `smw18pb0w` m3 (accepted, `Assembly.lean`, green) proves

```
CM.not_isCMinimal_of_two_rv (hM : M ⊨ ACVF) (hr : iRV r) (hs : iRV s) (hne : r ≠ s) : ¬ IsCMinimal M
```

Every ball lies inside `{x | iVF x}`, so a finite Boolean combination of balls cannot separate two
distinct `RV`-elements, which every model of `ACVF` has.  The unrestricted `IsCMinimal` had dropped
the paper's "subset of `VF(M)`".

So `encoding.lean`'s original `theorem_2_8_c_minimal` was **false**, not merely unproved — and the
restatement committed in `27b6c10` (`IsCMinimalWS`) is the only true form.  m3's `CM.IsCMinimalVF`
(`s ⊆ vfSet M` plus definability) and `IsCMinimalWS` are the same repair reached independently; the
two should be proved equivalent, which is bookkeeping now that both exist.

Same section: `isBoolComb_of_HasQEws` assembles the frozen QE statement plus `BallsBridge` into the
ball-combination conclusion for well-sorted one-variable `φ`, `ballsBridge_of_atomBridge` reduces the
bridge to per-atom facts, and the dictionary (`rv_eq_set_eq` via `correctedLink_of_model`,
`rv_eq_atom_of_bridges`, `leRV`, `unitRV`, `neRV`) is in place.  Missing and named: `ValueBridge`
(b1) and `ZeroBridge`.  Caveat on record: over *all* ill-sorted atoms the quantifier-free bridge is
false (`vfAdd (rv x) 1` is junk), so the dispatch must run on a sorted fragment.

## The `WellSorted` decision (m5's recursive predicate vs mine)

Two definitions now exist:

| | definition | coverage proved | parameters |
| --- | --- | --- | --- |
| mine (`Encoding.lean`, commit `3307aad`) | image of the sorted syntax `STm`/`SBf` | closure under connectives, quantifiers, atoms (m2) | **arbitrary `α`**, sorts relativised semantically by `sortEval` |
| m5's (`WellSorted_block.lean`, patch-ready) | recursive: `TmSort` (`none` = junk), `Occurs`/`GuardsLast`, inductive `WellSorted` | **`allSorted`, `allSortedK`, `allOne`, `exSortedK`, `sortedHyps`, `kHyps`, `alls`, `Cover.Frag.wellSorted_toRV`, `QF.wellSorted_toRV`** | needs `[Fintype α]` for the parameter guard |

The coverage column is the one that decides it: `HasQE` needs *the axioms of `ACVF` and the tree's own
translations* to be well-sorted, and only m5's definition has that proved.  So the plan is to adopt
m5's predicate and generalise its parameter guard the way mine does (semantic `sortEval`
relativisation), keeping the equivalence of the two predicates on `Fintype`-parameterised formulas as
the cross-check.  Two facts to carry: `VFQ` does **not** imply `WellSorted` (matters, because h4's
output is `VFQ`), and substitution closure is h2's.

## Status of the `WellSorted` adoption (attempted, reverted, delegated)

Tried to swap m5's recursive `WellSorted_block.lean` into `Milestone0/Encoding.lean` in place of the
image-of-sorted-syntax definition: 26 errors, because m5's block is written for insertion after
`def allOne` inside `namespace LRV`, and the spliced position does not match its signature
placement.  Reverted; `Encoding.lean` is green again at
`4d841a365904e177fd71f31241b193f60359cdbb4a53a34e53e94154eba8c313`.

Delegated to swarm `smw1951gd` with the author's ruling attached: adopt m5's predicate, generalised
so no `[Fintype α]` is needed (the semantic `sortEval` relativisation the frozen statements already
use), deliver a compiled `Encoding.lean` plus the diff, and prove the axioms and the tree's
translations are still well-sorted under the adopted predicate.  Same swarm, in parallel: **Section
4's statement freeze** (the pattern of Section 3's `smw18ygko`), the `VFQ → WellSorted` bridge that
h4's output needs, and the cross-check that the two predicates agree for `[Fintype α]`.

### The frozen `IsCMinimal` is refuted twice, and the replacement is `IsCMinimalWS`

Two independent refutations of the encoding's unrestricted `IsCMinimal`, both machine-checked:

* `SMW18pb0w.m3`: two distinct `RV`-elements cannot be separated by a Boolean combination of balls
  (all balls lie in the `VF` half) — `not_isCMinimal_of_two_rv`;
* `m2` (`Dict.lean`): the singleton `{1}` of the `RV` sort is `Definable₁` over `{1}`
  (`Set.Definable.singleton_of_mem`) but is not a ball combination, since `0 = ∞` is a distinct `RV`
  element — `not_isCMinimal`.

So `theorem_2_8_c_minimal` as originally frozen was **false, not unproved**, and the encoding had
dropped the paper's "subset of `VF(M)`".  Both directions independently name the same replacement:
the well-sorted, `VF`-restricted statement, which is what was frozen as `IsCMinimalWS` in `27b6c10`.

m2's dictionary is the exact correspondence and is worth keeping beside the statement:
`isBall_subset_iVF`, `rv_const_of_isBoolComb`/`dichotomy_of_isBoolComb` (a ball combination is
constant on the `RV` half), `isBoolComb_iff_split`, `isCMinimal_iff`, and
`IsCMinimal → IsCMinimalOnVF` (the paper's Definition 2.7) with the converse isolated as a
*trace-definability* hypothesis, named rather than assumed.  `Bridge.lean`'s
`isBoolComb_of_pattern` converts an arbitrary Boolean pattern over a finite family of sets into a
`IsBoolComb`, which is what the ball combinatorics needed.

Bookkeeping: `IsCMinimalWS ↔ IsCMinimalOnVF`, and `IsCMinimalWS`'s own `vfSet`-cut versus m3's
`IsCMinimalVF`.

### The value-only half of the balls bridge is done (m4, `ValueOnly.lean`)

Two things here are worth more than the direction asked for.

**The extracted predicate is a real valuation.** `exists_valuation_predV` produces a Mathlib valuation
`w` on `VFType` with `iLe (iRv y) (iRv x) ↔ w x ≤ w y` — the order reversal pinned as a theorem
rather than a convention.  That is what lets every `L_val`-side result apply to the `L_RV` model, and
it is the lemma I would have written had I known how cheap it was.

**The cell decomposition, on the `L_val` side.** `valueOnly_atom_isBoolComb` (a single comparison
`v (P x) ≤ v (Q x)`), `valueOnly_family_isBoolComb` (a finite family of polynomial pairs under an
arbitrary Boolean pattern), and `valueOnly_qf_isBoolComb` (any quantifier-free `Language.val`
formula in one variable), reusing Johnson 2.3.1(ii)'s `atomGood_of_isAlgClosed` and `good_solSet`.
Plus the ball dictionary that makes it speak about the frozen target's balls: `lift`/`lift_closedBall`/
`lift_openBall` matching `IsClosedBall`/`IsOpenBall`, `isBoolComb_lift_isKBall`,
`isBoolComb_lift_of_good`, with the edge cases covered (`univ`, `b = 0` closed = singleton, `b = 0`
open = ∅), and the `IsBoolComb` closure API (`inter`, `empty`, `iUnion_finset`, `iInter_finset`,
`patternSet`, `isBoolComb_boolFun`).

**What that leaves for the bridge**: the `L_RV` side of the one-variable case — translating a
well-sorted `Bf 1` formula into `L_val` (the atoms are `M2`'s, the terms are polynomials) and then
applying `valueOnly_qf_isBoolComb`.  That is the "L_RV term→polynomial translation" m4 names as the
unchanged part, and it is now the only piece of (BallsBridge) that is missing.

## Section map correction, and what "well-sorted parameters" means for Section 3

The paper's sections (`.ultramath/refs/paper.tex`): §3 "Some structural properties" (659), §4
"Categories of definable subsets" (801), §5 "$\RV$-pullbacks and special bijections" (1247), §6
"Interlude: quantifier elimination for henselian fields" (1419), §7 "Lifting functions from $\RV$ to
$\VF$" (1470), §8 "More on structural properties" (1724).  So the items I earlier attributed to
"Section 3" — $\RV[*,\cdot]$, the lifting map $\mathbb{L}$, special bijections — are §5 and §7; §3
itself is the geometry of definable sets (definable closure, exchange — citing
`Yin:QE:ACVF:min` Lemma 4.3 — and dimension).  Swarm `smw18ygko`'s members have been working across
§3–§7, and m2's `Section3SupplyFrozen.lean` currently freezes the Section 2 *supply*
(`cminimal_of_frozen`) rather than §3's own statements.

**The refinement the author asked for.**  Every statement of §3–§8 that quantifies over a parameter
set or over a definable object must be stated over *sorted* parameters, exactly as `HasQE` and
`IsCMinimal` now are:

* a parameter set is a pair of a `VF`-part and an `RV`-part (each with its sort declared), not an
  arbitrary `Set M`;
* `dcl`/`acl`, definability, and every "definable subset" in §3 are taken over *well-sorted* formulas
  with those parameters — the notion `DefinableVF`/`WellSorted` in `Milestone0/Encoding.lean`;
* and where a statement is about subsets of one sort, the set is cut down to that sort (`s ⊆ VF` or
  `s ⊆ RV`) as `IsCMinimalWS` does, rather than quantified over the carrier.

The reason is the same one that refuted the unrestricted `IsCMinimal` and `HasQE`: the carrier admits
ill-sorted terms and ill-sorted parameters, whose values no axiom fixes, so a statement that
quantifies over them is either false or says nothing about the paper's language.

## Section 3 draft: sorted parameter pairs (REC) and the SWL naming

`QE/Sec3_draft.lean` is the draft the author asked for, checked against a compiled
`Milestone0/Encoding.lean`.  It fixes two conventions and records the section's inventory.

**REC — the sorted parameter pair.**  Every §3 statement quantifies over parameters *split by sort*,
never over an arbitrary `Set M`:

```lean
structure SP (M : Type*) [LRV.Structure M] where
  n m : ℕ
  vf : Fin n → M
  rv : Fin m → M
  vf_sorted : ∀ i, iVF (vf i)
  rv_sorted : ∀ j, iRV (rv j)
```

with `SP.paramSet` (the union of the two ranges — the paper's `ā, t̄`), `SP.toFun` (the tuple as one
function on `Fin n ⊕ Fin m`), `SP.sortMap` (VF for the left summand, RV for the right), and
`SP.DefinableVF`/`SP.DefinableRV` — `S`-definable subsets of one sort, defined by a `WellSorted`
formula with `S`'s parameters.

**SWL — the naming.**  Each statement of §3 is `swl_<paper-label>`; the prefix marks that it is the
well-sorted version (parameters an `SP`, every formula `WellSorted`).  The bare name is reserved for
a statement over arbitrary parameters, and where both exist the `swl` one is the target.

**The inventory** (in the file, one row per paper item): `acl:VF:transfer:acl:RV`, `dcl:to:ac`,
`function:rv:to:vf:finite:image`, `exchange`, `alg:ind:imag`, `average:0:rv:not:constant`,
`finite:VF:project:RV`, `effectiveness`, `ball:proper:sub:center`, `ball:RV:finite`,
`algebraic:balls:definable:centers`, `aclS:model`, `inf:RV:def:gam`.

**Two decisions the draft surfaces and does not take silently**: `acl` has no definition in the tree
(it must be "some well-sorted formula with a *finite* solution set contains `x`", over `SP`), and the
paper's §3 is stated relative to a *substructure* `S` — so `VF(S)(ā)` and `Γ(S)` must be built from
`SP`, which is the one genuinely new construction §3 needs.

## Definitions 4.15–4.17 are formalized, and they do not need Section 2 (m4, accepted)

`.ultramath/smw18ygko/m4/RVCategory.lean` (559 lines, `import Mathlib` only, green, no sorry,
footprints clean; intended repo path `SpecialTransformations/RVCategory.lean`):

* Definition 4.15 (weight) and **Definition 4.16 in full** — objects `(U, f)` with `U ⊆ RV^m`
  definable and `f : U → RV^k` definable, the companion `U_f`, volumetric and finite-fibre morphisms
  at fixed `k`, and identity/composition/associativity as a genuine Mathlib `Category (Obj D k)`;
* `RV[k]` as the full subcategory of finite-to-one maps (Full and Faithful instances included);
* the direct sums `RV[≤i,·]` and `RV[*,·]` as Sigma categories;
* **Definition 4.17**: `E_k : RV[k,·] ⥤ RV[k+1,·]`, proved Faithful, Full and injective on objects;
* `F_{f,f'} : U_f → U'_{f'}` and the fact that the inclusion map is a morphism.

Design point worth keeping: definability enters through a six-field **`LDefinability RV`** parameter
(definable sets and functions, identity, composition, restriction, appending `∞`) rather than through
the encoding, so the construction is parametric in the notion of definability.  That is what lets it
be instantiated both at the repository's `RV` sort and at `WithTop ℕ`, and it keeps it clear of the
junk problem.

**The dependency finding is the news**: nothing in 4.15–4.17 needs QE (Theorem 2.3) or C-minimality
(Theorem 2.8).  Those enter only in §4.1's dimensions and in Lemma 4.19's `acl`.  So a large block of
Section 4 is independent of both frozen statements, which is what makes running the sections in
parallel sound rather than optimistic.

Gaps named: `VF[k,·]` and its dimensions are not done; and instantiating at the repository's `RV`
sort needs `Top (RV v) := ⟨none⟩`, which `SpecialTransformations/Basic.lean` lacks.

## Section 3 frozen statements, over `SP`, with `acl`/`dcl` (draft: `QE/Sec3_frozen.lean`)

Definitions added: `SP` (the REC record), `SP.paramSet`, `SP.toFun`, `SP.sortMap`, `SP.base`,
`SP.extendVF`/`SP.extendRV`, `SP.DefinableVF`/`DefinableRV`, and the two closure notions

```lean
SP.acl S x := ∃ φ, WellSorted S.sortMap (fun _ => .vf) φ ∧
  ({y | iVF y ∧ φ.Realize S.toFun ![y]}).Finite ∧ iVF x ∧ φ.Realize S.toFun ![x]
SP.dcl S x := ∃ φ, WellSorted S.sortMap (fun _ => .vf) φ ∧
  {y | iVF y ∧ φ.Realize S.toFun ![y]} = {x}
```

Frozen (SWL naming, each with `sorry`): `swl_acl_const_of_fibres`, `swl_acl_VF_transfer_acl_RV`,
`swl_exchange`, `swl_function_rv_to_vf_finite_image`, `swl_finite_VF_project_RV`.  The remaining
items of the inventory (`dcl:to:ac`, `alg:ind:imag`, `average:0:rv:not:constant`, `effectiveness`,
`ball:proper:sub:center`, `algebraic:balls:definable:centers`, `aclS:model`, `inf:RV:def:gam`) need
one more notion each — the field `VF(S)`, `trdeg`, or `vrv` on `SP` — and are listed in
`QE/Sec3_draft.lean`'s inventory table with the notion each consumes.

**Their proofs are not missing, they are external**: the paper cites them from
arXiv:1006.1393 (`Yin:QE:ACVF:min`) — exchange is Lemma 4.3 there, the average lemma 4.9, the
`VF`-projection 4.10, the finite image 4.12, effectiveness 4.15, the algebraic balls 4.17, and
`aclS:model` Corollary 4.18.  So these are *quoted* theorems: freezing the statement is the
deliverable, and each docstring says which external lemma it corresponds to.  Any of them that is
re-proved here should be marked as such, and the ones left quoted should be flagged in the final
report rather than counted as formalized.

## Section 3 has its first proved item, and Definition 4.18 is formalized

**Lemma 4.9 re-proved, sorry-free, for an arbitrary valued field** (m2, `AverageLemma*.lean`):
`exists_pair_val_sub_eq`, and `rv_eq_iff_val_sub_lt` — "`rv`-fibres are balls" — plus
`exists_pair_rv_ne`.  This is the one §3 item whose printed proof §3 does not cite from
arXiv:1006.1393, so it is the natural one to have formalized first, and it is the dictionary the
balls bridge and the §3 freezing both consume.  The characteristic-0 hypothesis appears explicitly as
`v (k : K) = 1`, not silently.

**Definition 4.18 — the lifting map** (m3, `Lift.lean`, 28 theorems, axioms clean): object data
`RVObj`/`VFObj`, the companion `U_f`, `lift`, **`lift_eq_iUnion` reproducing the paper's display
verbatim**, `rvMap`, `rv (L (U,f)) = U_f`, `lift_nonempty_iff`, the padding `E_{i,k}`, `L_{≤k}`, `L`
on `RV[*,·]`, `rv_surjective`/`rvSection` (why `U_f ⊆ rv (L (U,f))`), `rvFiber_finite`, and
`instTopRV : Top (RV v) := ⟨rvInfty v⟩` — closing the gap m4 flagged in
`SpecialTransformations/Basic.lean`.  Not formalized and declared: definability in the monster model,
`dim_VF` (hence the dimension half of `L(U,f) ∈ VF[k]`), `RV:morphism:condition` (its conclusion
needs `acl`/`dcl` and the finite-image fact, which the printed proof does not supply), and
`RV:isomorphism:weaker:condition`.

**The interface, frozen as a structure** (m2, `Section3Supply`): `hACVF`, `qe`, `cminimal`, plus §3's
`rvToVF_finiteImage`, `finiteVF_injects_RV`, `ballProperSub_center`, `ballRV_finite`, each field
quoting the paper item it freezes; `frozen_targets_fit` proves the frozen `theorem_2_3` and
`theorem_2_8` have *verbatim* the types of `qe` and `cminimal`, so the interface cannot drift from the
frozen statements.  `REPORT.md` lists what the tree lacks as *vocabulary*: `acl`/`dcl`/exchange,
saturation, a `Γ`-sort, algebraic sets of balls, definable subgroups.

## The balls bridge is down to the `RV`-term atoms (m1, accepted)

The `L_RV` term-to-polynomial translation — the piece I had named as the last one — is done:

* `Syntax.lean`: `ev` with evaluation lemmas for all eleven function symbols, and the bridge
  `polyOf`/`eval_polyOf`: **a well-sorted `VF`-term at a `VF`-tuple is the evaluation of an explicit
  `Polynomial (VFType)` whose coefficients are the parameters**; then the atom lemmas
  `atom_{eq,rvEq,le,units}_iff`;
* `RVSort.lean`: the `RV` side of the sort discipline — and it needs `kJunkZero`/`kNegJunkZero`,
  i.e. the junk conventions added in the repair are what make the `RV`-term analysis go through;
* `QFFrame`/`Glue`: `isBoolComb_of_isQF`, the complete quantifier-free Boolean induction with the
  atomic case as its only hypothesis, and `hQF_of_atom` proving it is *verbatim* the `hQF` that
  `Downstream.isBoolComb_of_HasQEws` consumes — the two directions' interfaces meet exactly;
* `Integration.lean`: the atoms at `L_RV` terms **with parameters** — `atom_eq_isBoolComb`,
  `atom_zero_isBoolComb`, `atom_le_isBoolComb` (through m4's value-only case),
  `atom_rvEq_isBoolComb` via `rvEq_set_eq` — and `VFQF_isBoolComb`; `polyOf_single` reduces a zero
  set to one polynomial's zero set.

Missing and named: atoms at general `RV`-terms, the units atom, and the `Bf 1 → A.Definable₁`
packaging.  Nothing conceptual is left in the bridge.

## `VFQ` does not imply `WellSorted` — the bridge needs one condition (m3, accepted)

* `tmSort_iff_exists_stm` and `wellSorted_toLRV`: the recursive `TmSort`/`WellSorted` and the
  image-of-sorted-syntax predicate agree at the term level, and every `SBf` image is `WellSorted` —
  so **adopting the recursive predicate loses nothing**, which closes the cross-check I had listed
  as a separate risk.
* `VFQ.exists_sbf`/`VFQ.wellSorted`: under `VFQAtomSorted` (atoms relate terms of declared sorts, and
  `∀` extends by a `VF`-variable) a `VFQ` formula has an *exhibited* `SBf` preimage and is
  `WellSorted` under either predicate.
* `VFQ.not_vfq_implies_wellSorted`: `rv (rv x) = rv (rv x)` is `VFQ` and well-sorted for neither, so
  `VFQ` alone cannot feed the frozen `HasQE` — the condition is necessary, not convenient.

So h4's output needs `VFQAtomSorted`, and the requirement should be built into the quantifier step
rather than discovered when the assembly is attempted.

## Saturation in Marker's shape, and §3 restated over a monster model

The author has ruled (see `Milestone0/DECISION.md`, "the saturation interface is Mathlib-shaped")
that saturation enters as `Saturated M κ` plus a monster-model structure, in the shape of Marker's
*Model Theory*, **not** as three stated consequences; and that model theory may be taken as given
while the paper's own lemmas must be proved.

`Milestone0/Saturation.lean` (new, green: `lean` exit 0, 0 errors, no `sorry`, no `axiom`, no
`sat_*` axiom anywhere) carries exactly that interface, for Mathlib's general
`FirstOrder.Language`:

* `Sat.typeOf`, `Sat.mem_typeOf`, `Sat.FinitelySatisfiable`,
  `Sat.finitelySatisfiable_typeOf` — types over a parameter set, in the form the compactness
  arguments of §4 use;
* `Sat.Saturated N κ := ∀ A (v : A → N), #A < κ → <every finitely satisfiable type over v is
  realized>`, with `Saturated.anti` (fewer parameters is weaker) and `Saturated.realizes`;
* `Sat.PartialElementary v w` (every formula with parameters from `A` agrees at tuples from `A`)
  and `Sat.StronglyHomogeneous M κ` (every such map on fewer than `κ` parameters extends to an
  automorphism `M ≃[L] M`);
* `Sat.MonsterModel L T`: carrier `M`, `κ ≥ ℵ₀`, `M ⊨ T`, saturation, homogeneity — with
  `MonsterModel.small A := #A < κ`, `MonsterModel.realizes`, `MonsterModel.exists_automorphism`,
  `MonsterModel.mk_fin_lt`, `MonsterModel.small_of_finite`, and `Sat.MonsterACVF` for
  `L = LRV`, `T = Axioms.ACVF`.

Because the saturation lives in a *structure* rather than in axioms, no footprint grows: a
statement about the monster model mentions `𝕄 : MonsterACVF` and `𝕄.small A`, and the interface
cannot be used to smuggle a paper lemma in as a hypothesis.

**§3 restated over the monster model** (`QE/Sec3_sat.lean`, three more frozen targets, `sorry` as
usual, plus two parameter-pair abbreviations `SP.singleVF`, `SP.singleRV`, the `VF`-zero
`SP.iVFZero` and the explicit list sum `SP.sumVF`):

| paper label | frozen as | needs |
| --- | --- | --- |
| `alg:ind:imag` | `swl_alg_ind_image` | `acl`, the monster model |
| `average:0:rv:not:constant` | `swl_average_zero_rv_not_constant` | `VF`-sum, `iRv` only |
| `ball:proper:sub:center` | `swl_ball_proper_sub_center` | `IsBall`, `DefinableVF`, `dcl` |

**The remaining five §3 items are blocked on vocabulary, not on saturation**, and each blocker is
named in `QE/Sec3_sat.lean`'s header: `dcl:to:ac` needs `VF(S)(ā)^{alg}`, i.e. the `Field`
structure on `{x // iVF x}` that only `QE/Assembly_val.lean` has (`vfFieldOfModel`), plus
`Subfield.closure` and `AlgebraicClosure`; `inf:RV:def:gam` needs the `Γ`-sort, `vrv` and a
monster model *of the expansion* `LRVΓ`; `effectiveness` and `algebraic:balls:definable:centers`
need "algebraic set of closed balls" and "`𝓑` has centers", which this paper quotes from
arXiv:1006.1393 (Definitions 4.13/4.14) without defining; `aclS:model` needs `Γ(acl(S))` and the
substructure interpretation of `acl(S)` in `ACVF_S(0,0)` (`Encoding.lean` Part 5 has the theory,
not the interpretation).

State corrections made in the same commit:

* `QE/Sec3_frozen.lean` did not elaborate against the current `Encoding.lean`: after the recursive
  `WellSorted` was adopted, `WellSorted` lives in `namespace LRV`, so `open LRV` is needed
  *inside* `namespace SpecialTransformations.Milestone0`.  Its five frozen statements are green
  again; the file had silently stopped compiling when the adoption landed.
* the QF balls bridge is **not** in `QE/Assembly_val.lean`; it is only in
  `.ultramath/smw18pb0w/m1/*.lean` (`import PreC`).  The line in an earlier entry that "everything
  of value is merged here" is false for it.

**Swarm `smw19wtoj`** (5 members, 150 min) is working the rest of the way to `HasQE`, one
direction per obstruction: w1 `exists_toFrag` in the all-`VF` context (from h4's
`H4_attempt.lean`), w2 free-variable substitution by `rv`, w3 the mixed-context QF fragment with
`RV`-variables, w4 the arbitrary-parameter bridge (finite support + relabelling), w5 the assembly
`exists_toFrag → qfq_cover → hasQE_ACVF_val → QF witness`.  The pieces w2 and w3 exist because
the fragment + `L_val` route as planned in `smw17pts2`'s h4 only covers `α = Empty` and all-`VF`
contexts, and the frozen `HasQE` quantifies over all parameters and all variable sorts; that gap
was not visible in the earlier plan.

## Two swarms closed solved: §5 special bijections, and the adequacy audit

**`smw18ygko` m1, accepted — Section 5 (special bijections) formalized.** `.ultramath/smw18ygko/m1/Sec5.lean`
(1122 lines, standalone, green, no `sorry`/`axiom`): Definition 5.1's apparatus (`Pt`, `key`, `SamePD`,
`polydisc`, `rvHull`, `IsRVPullback`, degenerate pullbacks, `Csharp`, `rvHullSharp`, focus map, `eta`,
`SpecialBijection`, `IsDeformedRVPullback`), with `eta_wellPosed` proved from the hypotheses (both
implicit points derived, not assumed), `etaInv ∘ eta = id`, and the paper's unique contraction
`exists_unique_contractionVF`. Statements 5.2/5.4/5.5 are frozen as `def … : Prop`. Recorded dead end:
`T(A)` need not be an `RV`-pullback after one centripetal step (witness ℚ_p, λ=1: `1+p`, `1+p²` share an
`rv`-polydisc, `p`, `p²` do not) — which is why the paper deforms rather than maps directly.

**`smw1951gd` m4, accepted — adequacy audit of the frozen targets.** `Adequacy.lean` (against the
pre-adoption encoding) proves `STm.realize_toLRV`, `SBf.realize_toLRV` at arbitrary assignments, hence
`hasQE_iff_hasQESBf`, `isCMinimalSBf_iff_isCMinimalWS`, `definableVF_iff`, plus `SBf.Sat_congr`
(the `WellSorted` witness cannot change the defined set). `AxiomReading.lean` (against the current
`Encoding.lean`) reads the three carrier axioms: `carrier_cover`, `carrier_disjoint`, `units_mem_rv`,
which is exactly why `WellSorted` excludes `sdCover`/`sdDisjoint`/`sdUnits` and nothing else of `ACVF`.

**§3 restated over the interface in full, except two items.** `QE/Sec3_sat.lean` now also carries
`SP.swl_dcl_to_ac` (`dcl:to:ac`: `IsAlgebraic ↥(VFGen S) (vfOf b hb)` from `acl S b`),
`SP.swl_effectiveness` and `SP.swl_algebraic_balls_definable_centers` (the latter with centres
definable over `S`), on top of `swl_alg_ind_image`, `swl_average_zero_rv_not_constant`,
`swl_ball_proper_sub_center`. Six frozen statements, file green, six `sorry` warnings, no `axiom`.

New vocabulary, and the reason for each shape:

* `Sec3.VFType`/`Sec3.vfOf`, `Sec3.VFGen S = Subfield.closure (VF-part of S)` — the paper's
  `VF(S)(ā)`.  The `Field` instance on `VFType` is `QE/Assembly_val.lean`'s `vfFieldOfModel`,
  proved from the same axioms but in that file's copy of the encoding; it cannot be imported, so
  the statements carry `[Field (Sec3.VFType M)]` as an instance argument.  The field laws are not
  an extra hypothesis about the mathematics: they are determined by `Axioms`, and the argument
  disappears when the two copies of the encoding are unified.
* `Sec3.IsCentreOf` (a centre of a closed ball) and `Sec3.HasCenters` (a set meeting each ball of
  the family in exactly one point, that point being a centre) — the paper's use is
  `|A_t̄ ∩ b| = 1`, and "has centers" is *defined* here rather than quoted.
* "algebraic set of closed balls" is **not** defined in this paper: it quotes QE:ACVF:min
  Definition 4.13.  It is therefore a *parameter* `(IsAlgBalls : Set (Set M) → Prop)` of the two
  statements that use it, so a later formalization of 4.13 instantiates them without restating
  the lemmas.  This is the one hypothesis in §3 that is a placeholder, and it is visible in the
  statement rather than hidden.
* "`S` is `(VF, Γ)`-generated" is not formulable without the `Γ`-sort; it is recorded in the
  docstring of `swl_algebraic_balls_definable_centers` and the conclusion is frozen with
  `S`-relative definability.

Two §3 items remain unstatable, each with its missing development named in the file header:
`inf:RV:def:gam` (the `Γ`-side vocabulary of `LRVΓ`: `pMemGamma`, `gVrv`'s interpretation,
`Γ(S)`, `vrv⁻¹(γ)`, and a monster model of the expansion) and `aclS:model` (`acl(S)` as an
`LRV.Substructure` with relativized satisfaction, plus `Γ(acl(S))`).

**The balls bridge is merged into `QE/Assembly_val.lean`.** The seven swarm files
(`ValueOnlyM4`, `Syntax`, `RVSort`, `QFFrame`, `Glue`, `AssemblyM3`, `Integration`, 2 413 lines)
are now part of the assembly: 23 246 lines, `lean` exit 0, 0 errors. Three `rfl`s had to become
`try rfl` — the merged `simp` set closes those goals before the `rfl` runs; nothing else changed.
**Correction to an earlier claim:** `Assembly_val.lean` does contain two `sorry`s, and always did —
it embeds a copy of `Encoding.lean`'s Part 6, so it carries that file's
`theorem_2_3_quantifier_elimination` and `theorem_2_8_c_minimal` as `sorry` placeholders. "No
`sorry`" was true of the assembly's own results, not of the file. Removing or restating them is
part of the `HasQE` restatement (they are the *old* two-variable `HasQE`/`IsCMinimal`, not the
frozen well-sorted ones).

**Yin QE:ACVF:min Definition 4.14 formalized** (`QE/Sec3_sat.lean`, from the quoted text in
`.ultramath/refs/qe.tex`): an algebraic set of balls is a definable set of balls containing
finitely many balls; `𝓑` has centers if there is a definable `f : 𝓑 → VF` with `f(𝔟ᵢ) ∈ 𝔟ᵢ`.
The formal version is `Sec3.IsAlgebraicSetOfBalls`/`IsAlgebraicBall`/`AlgebraicUnion`/
`IsDefinableSetOfBalls`/`IsSetOfCenters`/`HasCenters`/`rvBall`, and the two §3 statements that
used to take "algebraic set of balls" as an unconstrained predicate now take the real definition:
`swl_effectiveness` (4.15) and `swl_algebraic_balls_definable_centers` (4.17). Also frozen:
`swl_rv_effectiveness` (QE:ACVF:min 4.16), the fact behind `ball:proper:sub:center`. Seven frozen
statements in the file, green, seven `sorry` warnings, no `axiom`.

## Swarm `smw19wtoj`: the QE route is now assembled, and it has found a defect in the frozen predicate

Four of the five directions delivered; every file checked here by compiling it, not by report.

**w5 (m5, accepted) — the assembly.** `.ultramath/smw19wtoj/m5/Main.lean`: `qf_of_QFq`
(unconditional), `qf_witness_of_exists_toFrag` (modulo w1's statement), and
`hasQEws_of_exists_toFrag`, a *`Downstream.HasQEws` instance* — the interface the downstream
C-minimality consumes. It derives rather than assumes the five hypotheses of `QFRes.qfq_cover`
(`Asm.model_rvFibreIff`, the four `QFRes.K*` links) and `hasQEb_ACVF_val` (from
`hasQE_ACVF_val`'s inputs), and gets `WellSorted (valFormulaToRV θ')` without any `GuardsLast`
argument, because a QF formula needs none.

**w1 (m1, accepted) — `exists_toFrag` for the paper's guarded discipline, plus a defect.**
`.ultramath/smw19wtoj/m1/W1.lean`: `exists_toFrag_WSg` covers all cases, `.vf` and `.rv`
(The `.rv` case is closed by `QFq.allVF` together with `exists_vf_of_rv` from `rvSurj`), and
`WSg.toWellSorted` embeds the guarded discipline into the frozen predicate. **The embedding is
one-directional and cannot be reversed**: the frozen `WellSorted.all` admits a body
`(x ∈ s ⟹ ⊥) ⟹ ψ`, which `GuardsLast` accepts and which is false at a junk element, so the
induction needs `JunkTrueAt s n χ := ∀ T a, ¬ sortEval s a → χ.Realize (snoc T a)`, and
`GuardsLast` does not imply it. Consequence: **the frozen `WellSorted.all`/`.ex` are too weak to
support the QE proof they are supposed to enable.** The fix is a junk-truth condition on the guard
in the frozen predicate (a third revision of `Encoding.lean`), or stating the target over the
paper's guarded discipline `WSg`. **This is an author decision and is not taken unilaterally.**

**w2 (m4, accepted) — the substitution.** `.ultramath/smw19wtoj/m4/SubstRv.lean`: `substLastRv`
(and the general-`α` `substFormulaRv`), `realize_substLastRv`, `tmSort_substLastRv` and
`wellSorted_substLastRv`: replacing the last free variable by `rv` of itself preserves `TmSort`,
`WellSorted` (with the context's sort updated `.rv → .vf`) and realization. Together with w1 this
gives the `.rv` quantifier case both halves — the `rvSurj` rewrite and the substitution.

**w4 (m2, rejected once) — the parameter bridge, partial.** `.ultramath/smw19wtoj/m2/Shrink.lean`
compiles and proves `realize_shrinkAux` — the depth-indexed relabel that Mathlib's
`BoundedFormula.relabel` cannot do, plus `tupleAt_snoc` — but not the `TmSort`/`WellSorted`
transport that makes it usable, and `ShrinkSort.lean` does not compile. Sent back with the route:
fix the index as an explicit `K = m + (n + k)` (or `termination_by`), prove `tmSort_shrink` in
the shape the `.all` step needs, reuse `junkTrueAt_guard` from w1, then the finite-support
extraction. The deliverable remains `hasQE_of_hasQE_empty`.

**w3 (m3) — the mixed-context fragment (with `RV` variables) is still running.**

**w3 (m3, accepted) — the mixed-context fragment exists.** `.ultramath/smw19wtoj/m3/QF2.lean`
(858 lines, green, no `sorry`/`axiom`): `VFT2 sn`, `RVT2 sn` with `rvar` (the free-`RV`-variable
constructor `QFRes.RVT` lacks), `QF2 sn`, and `QFq2 sn` with `allVF`/`allRV`. The design decision
that makes it work: the fragment is indexed by the *sorted context* `Fin n → SortTag`, so
`Fin.snoc sn s` is literally the shape of `WellSorted.all` and no variable renaming is needed.
`QF2.wellSorted_toRV` and `QFq2.wellSorted_toRV` are proved **with no model hypothesis**, so the
fragment's image lies inside the frozen `WellSorted` unconditionally — a future mixed-context
`exists_toFrag` gets the target's well-sortedness conjunct for free. Also proves
`{KJunkZero,KNegJunkZero,KAddAdditive,KNegAdditive}_of_model`, deriving the four repair hypotheses
from `Axioms.ACVF` alone, independently of w5's route. Not proved, and correctly diagnosed: no
`qfq_cover` in a mixed context (an `RV` free variable has no `L_val` image — the same obstruction
from the other side), and the `mul`-cancellation normal form for off-`K` elements.

**w4 (m2, accepted, half) — the shrink side of the parameter bridge.** `Shrink.lean` and
`SortTransport.lean` are both green (0 errors, no `sorry`). After one rejection the blocking item
was cleared, and the diagnosis was the useful part: with the index as a *type* (not the composite
`m + (n + k)`) and the sort `s` quantified inside the motive, `induction t` goes through, giving
`tmSort_shrink` outright. Also proved: `shrink_sortPredG` (the sort *guard* survives the relabel,
without which every quantifier case would fail for a reason unrelated to the mathematics), and
`wellSorted_shrink_of_isQF` — the lemma the assembly consumes, with no `GuardsLast` obligation
because QF formulas have none. Plus `realize_shrinkAux` and `tupleAt_snoc` from the first attempt.

**Not delivered:** `hasQE_of_hasQE_empty` and `Forward.lean`. The remaining route is
`occurs_relabel` (needs an explicit 5×5 `rcases`: `Occurs` decomposes only the conjunction shape,
so `split` will not fire in `.imp`), then `guardsLast_relabel`, `tmSort_relabel`,
`wellSorted_relabel` (`Fin.natAdd m'`), finite support, assembly. **Check before writing those
four:** they are only needed for the finite-support extraction, and if the witness can be produced
by `exists_toFrag` directly at the shrunk context without being relabelled forward, the whole
forward direction is unnecessary.

## Swarm `smw19wtoj` closed: board and state

Five directions, five accepted (one of them half). The QE route now stands as:

1. `exists_toFrag` **for the paper's guarded discipline** `WSg` (m1) — all cases, `.vf` and `.rv`;
2. the `rv`-substitution `substLastRv` with `TmSort`/`WellSorted` preservation (m4);
3. the mixed-context fragment `QF2`/`QFq2` indexed by the sorted context, with the image inside
   `WellSorted` proved with no model hypothesis (m3);
4. the assembly `exists_toFrag → qf_witness_of_exists_toFrag → hasQEws_of_exists_toFrag`, a
   `Downstream.HasQEws` instance (m5);
5. the shrink side of the parameter bridge (m2).

Three things block `theorem_2_3_quantifier_elimination` itself, in order of decisiveness:

* **`Encoding.lean`'s `WellSorted.all`/`.ex` are too weak.** `WSg → WellSorted` but not back: the
  frozen rule admits `(x ∈ s ⟹ ⊥) ⟹ ψ`, which `GuardsLast` accepts and which fails at junk
  elements, so the induction needs `JunkTrueAt` on the guard. Either the frozen predicate gets a
  junk-truth condition on the guard (third revision of `Encoding.lean`) or the target is stated
  over `WSg`. **Author's decision.**
* **No `qfq_cover` in a mixed context** (an `RV` free variable has no `L_val` image) and the
  `mul`-cancellation normal form for elements off `K`. This is what a mixed-context elimination of
  the `RV` quantifier needs beyond `QFq2`.
* **The forward half of the parameter bridge** (`hasQE_of_hasQE_empty`), unless the shortcut above
  works.

## Standing instruction: when the Shoenfield swarm returns, compare the two proofs

Author's instruction: **once `smw1b0thh` returns, compare its criterion against the fragment
criterion already in the tree and report where the two proofs disagree.** The comparison is not
"do both compile" — it is a four-column table for each criterion:

| | `QECriterion` (in `QE/Assembly_val.lean`) | fragment Shoenfield (w1) |
| --- | --- | --- |
| quantifies over | two models `M`, `N` and tuples with the same QF type | a substructure `S ⊆ M` and an embedding `S ↪[L] N` |
| QF type over | all QF formulas of the encoding | only the *well-sorted* QF formulas, at sorted tuples |
| concludes | `QECriterion.HasQE T` (sentence level, `⊨ᵇ`) | the frozen `HasQE` on the fragment |
| model theory used | compactness only | compactness + substructure closure + QF-preservation by embeddings |

The disagreements to look for, in order of interest:

1. **Where the fragment restriction enters.** `QECriterion`'s criterion is a two-model statement
   with no sort discipline at all; it was rejected as the route for `L_RV` because per-model QE
   does not imply theory QE (m6's counterexample) and because the unrestricted statement is false
   (three refutations). If w1's fragment version is correct, it must use `WellSorted` in *two*
   places — in the type it compares and in the tuples it compares at — and the audit question is
   whether the two-model criterion can be recovered from it, and vice versa.
2. **Whether the guard repair is needed at all.** The Shoenfield route never constructs
   `exists_toFrag` and never pushes a translation through a binder, so it should be *independent*
   of the `GuardsLast`/`JunkTrueAt` issue that forced the edit in `Encoding.lean`. If it is, that
   is the single most valuable outcome: the route to `theorem_2_3` that does not depend on a
   predicate that is itself under revision.
3. **The saturation hypothesis.** `QESat.exists_extension_of_saturated` needs `N` to be
   `κ`-saturated with `|S| < κ`; a *criterion* must not need saturation (it is a criterion, not a
   step).  If w1's statement comes out with a saturation hypothesis, it is not the criterion and
   the difference must be reported as such.
4. **What each route leaves open.** The main route leaves the mixed-context elimination and the
   parameter bridge; the Shoenfield route should leave the QF-type-determination for `L_RV` (w2)
   — and the comparison has to say whether those two leftovers are the *same* obligation in
   different clothing. If they are, two proofs of one lemma is not two proofs of the theorem, and
   that must be said plainly rather than counted as independent confirmation.

Status: swarm `smw1b0thh` started with four directions (fragment criterion; `L_val` ⇒ `L_RV`
QF-type transfer; a worked instance on two `C v` models; audit of the existing criterion files).

## The QF-type assembly over the fragment: exact restatement, and what `NontrivialTransfer` becomes

With the Marker ruling, the abstract criterion is free.  What is not free, and is what the
assembly below isolates, is the ACVF-specific content.  The four definitions to restate are
`TransferAt`, `NontrivialTransfer`, `TrivialTransfer`, `CaseSeparation`
(`QE/Assembly_val.lean:15630–15653`); `CaseSplit` (`15657`) needs no change, since it speaks
about one model.

**`TransferAt`, fragment form.**  Keep it a family over a class `P` of models, and put the sort
discipline in three places — the parameter tuples, the variable tuples, and the formula class on
both sides of the implication:

```lean
def TransferAtWS (P : (M : Type) → [LRV.Structure M] → Prop) (T : LRV.Theory) : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (M : Type) [LRV.Structure M] [Nonempty M] (hM : M ⊨ T), P M →
  ∀ (N : Type) [LRV.Structure N] [Nonempty N] (hN : N ⊨ T), P N →
  ∀ (v : α → M) (xs : Fin n → M) (w : α → N) (ys : Fin n → N),
    (∀ a, sortEval (sα a) (v a)) → (∀ i, sortEval (sn i) (xs i)) →
    (∀ a, sortEval (sα a) (w a)) → (∀ i, sortEval (sn i) (ys i)) →
    (∀ ψ : LRV.BoundedFormula α n, WellSorted sα sn ψ → ψ.IsQF →
      (ψ.Realize v xs ↔ ψ.Realize w ys)) →
    ∀ φ : LRV.BoundedFormula α n, WellSorted sα sn φ →
      (φ.Realize v xs ↔ φ.Realize w ys)

def NontrivialTransferWS (T : LRV.Theory) : Prop := TransferAtWS IsNontrivialVF T
def TrivialTransferWS (T : LRV.Theory) : Prop := TransferAtWS IsTrivialVF T
```

**What `NontrivialTransfer` becomes, item by item** (this is the answer to the question):

1. **Same class predicate.**  `IsNontrivialVF M` is unchanged — `∃ x, iVF x ∧ x ≠ 0 ∧ ¬ (rv 1 ≤ rv x)`
   is a statement about the model, not about the tuple, and needs no sort discipline.
2. **Three new hypotheses, all about *sortedness of the data*:** both parameter tuples are
   sort-respecting (`∀ a, sortEval (sα a) (v a)`, and the same for `w`), and both variable tuples
   are (`∀ i, sortEval (sn i) (xs i)`, and the same for `ys`).  These are exactly the guards the
   frozen `HasQE` carries, so the transfer hypothesis now speaks about the same objects the target
   does.
3. **The QF agreement is restricted to *well-sorted* QF formulas** (`WellSorted sα sn ψ` added),
   not all QF formulas of the encoding.  This is the change that makes the hypothesis *provable*:
   the unrestricted version ranges over `rv (rv x) = rv (rv x)` and its relatives, which no axiom
   constrains — that is precisely the refutation recorded in `QE-PLAN.md`.
4. **The conclusion is restricted to well-sorted `φ`.**  So the transfer no longer claims anything
   about ill-sorted formulas, and the resulting assembly lands on `HasQEws WellSorted` /
   `HasQEwsParam` rather than on the old unrestricted `Assembly_val.HasQE`.
5. **`CaseSeparation` gets the same three kinds of restriction** (sorted tuples, well-sorted QF
   formulas); its conclusion `IsNontrivialVF M ↔ IsNontrivialVF N` is unchanged.

**Why this is not a weakening that makes the work disappear.**  Proving `NontrivialTransferWS` is
where the guard repair now *bites*: to push the equivalence through a quantifier, the body's
behaviour at elements outside the sort matters, because `BoundedFormula.all` ranges over the whole
carrier.  That is exactly the `JunkTrueAt` obstruction that m1 isolated and that the `GuardTrue`
edit addresses.  So the fragment restatement of the assembly and the guard repair are the same
obligation seen from two sides — which is worth knowing before doing either: doing the guard repair
makes `NontrivialTransferWS` provable, and attempting `NontrivialTransferWS` is the sharpest test
of whether the repaired predicate is strong enough.

**The assembly chain, fragment form**, mirroring `qfTypeDetermines_of_transfers` (15667) and
`hasQE_ACVF_of_nontrivialTransfer` (16347):

```
TransferAtWS IsNontrivialVF T  +  TransferAtWS IsTrivialVF T  +  CaseSeparationWS T  +  CaseSplit T
  ⟹  QFTypeDeterminesWS T                       (same case split as 15667, proved)
  ⟹  HasQEws WellSorted T                        (needs the fragment compactness step)
  ⟹  the frozen HasQE T                          (needs the semantic/syntactic guard bridge)
```

Step 2 is the one to check against Marker: the standard compactness argument is Marker's, but its
*relativization to a fragment* is not verbatim in the book, so either it is proved (w1 of
`smw1b0thh`) or it becomes a single named `Marker.*` axiom with its relativization documented.
Step 3 is the bridge between the semantic `sortEval` guard of the frozen `HasQE` and the syntactic
`sortedHyps` conjunction of `HasQEws` — a genuine but small obligation, and independent of both
routes' remaining mathematics.

## The QF-type route's hypothesis is refuted, not merely unproved (`smw1b0thh` m3, accepted)

`Missing.nontrivialTransfer_iff_hasQEb` (`.ultramath/smw1b0thh/m3/AvAudit.lean:264`, compiled,
axioms clean):

```
FinalAssembly.NontrivialTransfer Axioms.ACVF  ↔  QECriterion.HasQEb (L := LRV) Axioms.ACVF
```

So the one remaining hypothesis of `hasQE_ACVF_of_nontrivialTransfer` (`Assembly_val:16347`) is
*equivalent to unrestricted QE*, which is false (three refutations). That theorem is therefore
vacuous, and the QF-type route as stated in `Assembly_val` cannot close anything. The fragment
restatement in `QE/TransferWS.lean` is not a strengthening for convenience — it is the only live
form of the route.  `FragAudit.qfTypeDeterminesWS_of_hasQE` proves the easy half at the fragment.

Three audit findings, recorded as obligations:

1. none of `OneEC_val`, `Amalgamation_reduced`, `CheeseMeetsBase`, `Reduction_Lv`,
   `PrimeModels_val_partial`, `H_of_qfDetermined`, `QF_type_bridge` proves a *relativised*
   Shoenfield test; `Reduction_Lv` states it as a `def : Prop` only;
2. missing: the fragment transfer and a fragment compactness step
   (`FragAudit.MissingFragmentCriterion`);
3. `hasQE_ACVF_val` + the ball dictionary does **not** suffice — three compiled gaps:
   `Missing.HasQEb_ACVF_val`, `Missing.VFQ_to_QFq`, `Missing.MixedContextCover`.

Independence of the two routes is therefore partial: they share the mixed-context and `RV`-parameter
obligations; the demonstrated gain is independence from the `GuardsLast`/`JunkTrueAt` repair, and
that is an argument, not a compiled fact.

## `L_val` reaches only a strict sub-fragment (`smw1b0thh` m2, accepted)

`.ultramath/smw1b0thh/m2/W2.lean` (compiled on top of a byte copy of the assembly, 0 errors, no
`sorry`, axioms clean):

* `tmSort_valTermToRV` — `L_val` terms translate to `VF`-sorted terms;
* `wellSorted_valFormulaToRVvf` — **and the image is inside the frozen fragment**, which the tree's
  transfer (`VFRestrict.valFormulaToRVvf`) never established: it never mentioned `WellSorted`;
* `transfer_of_qfType_VF` — two models of `ACVF` whose `VF` sorts model `ACVF_val`, at `VF`-tuples
  with equal QF well-sorted `L_RV` type, have equal full `L_val` type — via guarded `L_val` QE, with
  **no cover**, unlike `CoverBridge.transfer_at_vf_tuples`.

**The boundary, which is the point:** `L_val` reaches only the image sub-fragment — atoms
`s = t`, `v s ≤ v t`, and `VF`-guarded quantifiers.  `rv s = rv t`, `kAdd`/`kNeg`/`rvMul`, the
`Kˣ` predicate and `RV`-quantifiers have no `L_val` preimage.  So w1's fragment-Shoenfield
hypothesis cannot be discharged from `L_val` alone; this is the same wall as
`Missing.VFQ_to_QFq` + `Missing.MixedContextCover` in the audit, seen from the second route.

Named gaps: no compiled bridge `vfValStruct = vfStruct`; and `hasQE_ACVF_val` is `HasQE` at
`n = 0`, while tuples need `HasQEb`.

## The guard repair landed, and the endgame for `ACVF` lost three of its four hypotheses

**Guard repair applied** (commit `f18b6f5`).  `Milestone0/Encoding.lean` sha256 `86d7ea7e…`,
green, 0 errors, the two frozen `sorry`s.  `QE/Assembly_val.lean`'s embedded copy re-spliced
verbatim, also green.  `Occurs := InAntecedent`; `GuardTrue` is an inductive family with an `.all`
clause (the existential of the earlier attempt cannot survive `wellSorted_alls`, which recurses to
the body `BoundedFormula.all χ`); `WellSorted.all`, `wellSorted_alls`, `wellSorted_allOne` gain the
`GuardTrue` hypothesis; every `wellSorted_allSorted*`/`exSorted*`/`all_guarded`/`ex_guarded`
signature is unchanged, so Part 6.1's audit (`wellSorted_ACVF`) did not move.  Full inventory and
the reasons for the shape are in `Milestone0/DECISION.md`, section "The guard repair: applied".

**What the repair was for.**  `nontrivialTransferWS_ACVF` needs, in the `all` case, the body `χ` to
be true at carrier elements *outside* the sort, because `BoundedFormula.all` quantifies over the
whole one-sorted carrier.  `GuardsLast` does not imply that (m1's finding:
`(x ∈ s ⟹ ⊥) ⟹ ψ` satisfies it and is false at junk elements); `GuardTrue` is the syntactic
condition that does, and the `Semantic` bridge `GuardTrue → JunkTrueAt` is now the named next
deliverable rather than an obstruction.

**The case split closed.**  `TrivialHalf.allNontrivial_ACVF : AllNontrivial Axioms.ACVF`
(`= ∀ M ⊨ ACVF, IsNontrivialVF M`), from `Transfer.isNontrivialVF_of_model`, whose compile status
had been unrecorded.  Hence `caseSplit_ACVF`, `caseSeparation_ACVF`, and

```
Transfer.hasQE_ACVF_of_nontrivialTransfer : FinalAssembly.NontrivialTransfer Axioms.ACVF
    → QECriterion.HasQE Axioms.ACVF
```

so the endgame has one hypothesis instead of four.  Side effect, recorded because the reverse was
believed: `TrivialHalf.not_fineTriv` shows `TrivCase.FineTriv` has **no** model of the frozen
`Axioms.ACVF` (`fineTriv_not_nontrivial` contradicts `isNontrivialVF_of_model`); the trivially
valued model of §10 satisfies a weaker axiom set.  So "Theorem 2.3 has two cases" is not an
obstruction here, and the `axNontrivialRV`-or-two-theorems choice is moot.

**Swarm `smw1bwjo2`** (8 members, 150 min) is running on the layer above: d1 term-sort soundness,
d2 the junk-truth induction (`GuardTrue → JunkTrueAt`), d3 the `TransferWS` plumbing, d4 the
composition, d5 the parameter bridge's forward half, d6 the mixed-context QF cover, d7 the `mul`
normal form, d8 fragment compactness.  Artifacts land under `.ultramath/smw1bwjo2/m{1..8}/` and
are unvetted until compiled.

## The first failure point of the transfer, located (`QE/FailProbe.lean`, green)

Sequencing step 3 ("`nontrivialTransferWS_ACVF` far enough to locate its first failure").  The
answer is in `QE/FailProbe.lean`, which compiles against the repaired encoding (0 errors, no
`sorry`, no axioms beyond the kernel's): the induction on the `WellSorted` derivation has an
immediate atomic and `imp` case, and its `all` case splits on the bound element `b : N` into
exactly two inputs, both now statements:

* `¬ sortEval s b` — **junk-truth of the body**, i.e. `GuardTrue → JunkTrueAt`
  (`all_step_forward_junk`: junk-truth at `b` *is* the conclusion, nothing else is used).  This is
  the branch the guard repair was for; it is no longer an obstruction, only an unproved semantic
  lemma (swarm d2).
* `sortEval s b` — a sorted `a : M` whose quantifier-free type over `(v, xs)` equals that of `b`
  over `(w, ys)` (`all_step_forward_sorted`, which takes it as `ext` and does nothing else).  This
  is **realization of a QF type in a fixed model**, and the transfer's hypothesis does not supply
  it: `M ⊨ T` and "`(v,xs)` and `(w,ys)` have the same QF type" say nothing about `b`'s type over
  the parameters.

So the transfer's content is not spread through the induction — it is (i) `GuardTrue → JunkTrueAt`
and (ii) the one-element QF-mate property, which is the paper's §3/§4 effectiveness of the residue
field, or a saturation/compactness substitute for it.  Two consequences worth keeping:

1. **A direct proof of `NontrivialTransferWS` cannot be cheap**, and this is the precise reason:
   `NontrivialTransfer` is equivalent to `HasQEb` (`Missing.nontrivialTransfer_iff_hasQEb`,
   `.ultramath/smw1b0thh/m3/AvAudit.lean`), and its `all` case needs a type-realization step that
   is not in its own hypothesis.  The transfer is a *reformulation* of QE, exactly as
   `QFTypeDetermines` is.  (One tempting repair is to prove the Shoenfield extension property
   instead — every partial isomorphism of finitely generated substructures is elementary — but
   `smw1b0thh` m4 settled that it is **unusable in this encoding**: junk values lie outside the
   fragment, so a partial isomorphism has nothing to say about them, and the QF-type form is the
   only formulation available.  The live target is therefore the atom form,
   `FragmentAtomQFTypeDetermines Axioms.ACVF`, `.ultramath/smw1b0thh/m4/FragAtoms.lean:100` —
   equivalences to `HasQE Axioms.ACVF` proved there, and the files need re-porting against the
   repaired `WellSorted`, which is what swarm d8 is for.)
2. **The fictitious `a` can be replaced by saturation only if saturation is assumed**, which the
   frozen statements are not written with (`TransferAtWS` has no saturation hypothesis).  So the
   choice is between (a) proving the QF-mate property for `ACVF` — the real mathematics — and (b)
   restating the transfer over saturated models.  (b) is not available for the frozen `HasQE`,
   which has no saturation hypothesis either.

**The same wall, seen twice.**  This is also why the two other "criterion" routes converged: W1's
`QFTypeDetermines` is *equivalent* to the target, and `Assembly_val`'s `hasQE_of_transfers` needs
the compactness step `QFComp.hasQE_of_qfTypeDetermines` precisely to manufacture, by compactness in
a *third* model, the element that this induction cannot manufacture in `N`.

## Section 3: the frozen targets audited against the source, and two of them were false

Before continuing §3 (the saturation/`acl` section) I checked what was there.  The chain
`Enc → Saturation → Sec3_frozen → Sec3_sat` still compiles against the repaired encoding (all four
`lean` runs exit 0), so the guard repair cost §3 nothing — `acl`/`dcl` only *hypothesise*
`WellSorted`, they never build one.

What was wrong was the statements.  Six of the thirteen frozen §3 items are not transcriptions of
their source sentences; three are false as frozen.  The inventory is in `DECISION.md` §"Section 3
statement audit".  The sharpest: `average:0:rv:not:constant` was frozen with the paper's own slip
("and hence `rv` is not constant on the set") as a conjunct, which contradicts its own hypothesis —
now machine-checked as `SP.swl_average_conclusion_unsat`; and `swl_exchange` had three free parameter
pairs instead of `acl(b) ∖ acl(∅) ⊑ acl(a)`, which is not exchange and is refutable.

`QE/Sec3_frozen.lean` is rewritten (green, 5 `sorry`s) with:

* `extendVFParam`/`extendRVParam` (the parameter pair `S` together with one element — the paper's
  `ā, a`), `singleVF`/`singleRV` moved up from `Sec3_sat` so that exchange can be stated;
* `DefinableFun` (a definable graph) — the missing hypothesis of `function:rv:to:vf:finite:image`;
* corrected `swl_acl_const_of_fibres`, `swl_acl_VF_transfer_acl_RV`, `swl_exchange`,
  `swl_function_rv_to_vf_finite_image`, `swl_finite_VF_project_RV`;
* proved: `dcl_subset_acl`, `acl_self` (`a` is algebraic over `{a}`).

`QE/Sec3_sat.lean` is green with 7 `sorry`s; `swl_average_zero_rv_not_constant` now states the two
halves of `vv(c_i - c_j) = α` (the encoding has a *preorder* on `RV`, so equality is equivalence), the
two ball lemmas gained the nonemptiness their only recorded use has, and
`swl_average_conclusion_unsat` is proved.

**Next in §3.**  `alg:ind:imag` is the one item the file always said should be proved (the paper
gives its proof).  With the statements now right, its proof needs exactly three inputs: exchange
(frozen), the transport `acl (singleRV t) a → acl (singleVF b) a` for `rv b = t` (parameter change
along a definable term), and "the `rv`-fibre of `t ∉ {rv 0, rv 1}` is infinite while `acl` of a
finite parameter set is countable".  The first is a frozen target, the second is formula relabelling,
the third is a cardinality argument on formulas.  That is the shape recorded for the next attempt;
none of it is started.

## Swarm `smw1bwjo2` accepted output: junk-truth proved, and the transfer reduced to one step

Two members submitted and both were checked here (compiled, read, `#print axioms` inspected); both
accepted and merged into the tree, since `.ultramath/` is not a build directory.

**m5, d2 — `QE/JunkTrue.lean`** (green, no `sorry`).  The semantic payload of the guard repair, and
it needed *less* than expected: no `TmSort` soundness and no model axiom, only the realisation of the
guard atom.

| lemma | content |
| --- | --- |
| `Junk.guardAtom_realize` | `xᵢ ∈ s` realises to `sortEval s (x i)` |
| `Junk.junkFalse` | `InAntecedent s i η` makes `η` false off the sort |
| `Junk.junkTrue` | `GuardTrue s i χ` makes `χ` true off the sort (incl. the `.all` clause) |
| `Junk.all_realize_iff_sorted` | at a junk-true body, the encoding's unguarded `∀` **is** the guarded one |
| `Junk.junkTrueAt_sortedHyps` | the paper's body shape `sortedHyps ⟹ ψ` supplies `JunkTrueAt` |
| `Junk.not_wellSorted_all_witnessG` | the junk-sensitivity witness is `GuardsLast`-guarded, has a well-sorted body, and is rejected by the repaired predicate |

The last row is the one that closes the question `HANDOFF.md` opened with the experiment: the repair
is not bookkeeping, and it is now machine-checked that it rejects exactly the witness that motivated
it while admitting `sortedHyps`.

**m8, d5 — `QE/FragmentTransfer.lean`** (green, no `sorry`).  The composition:

```
transferAtWS_of_qfStep : QFStep P T → TransferAtWS P T
nontrivialTransferWS_ACVF_of_qfStep : QFStep IsNontrivialVF Axioms.ACVF → NontrivialTransferWS Axioms.ACVF
```

with `QFStep` = *for a sorted element of one model there is a sorted element of the other with the
same well-sorted quantifier-free type at the extended tuple*.  The induction is
`BoundedFormula.rec` with the sorted context and both tuples in the motive (inducing on the
`WellSorted` derivation does not work — it is an indexed family), and the `all` case splits the bound
value by `sortEval s`, closing the junk side with `Junk.junkTrue` and the sorted side with `QFStep`
and the hypothesis.

**So the frontier has moved and is now sharp:** `NontrivialTransferWS Axioms.ACVF` ⟸
`QFStep IsNontrivialVF Axioms.ACVF`, with `AllNontrivial Axioms.ACVF` already proved
(`Assembly_val`).  `QFStep` is *not* the conclusion in disguise — it quantifies only over
quantifier-free formulas, at one added element — and it is precisely the one-element back-and-forth
step that `QE/FailProbe.lean` had localized as the obstruction and that §3/§4 are supposed to supply.

Three directions of the swarm died without a solution (m1 d8 fragment compactness, m6 d7 the
mixed-context QF cover, m7 d2 sort soundness); m2 (parameter bridge), m3 (`mul` normal form) and m4
(`TransferWS` plumbing) were still running when this was written.

### `smw1bwjo2` bookkeeping, and a caveat on the `QFStep` frontier

The two reminder events for m5 and m8 fired *after* their verdicts; both had already been accepted
and merged (`QE/JunkTrue.lean`, `QE/FragmentTransfer.lean`, commit `801cef4`).  Nothing was owed.

m8's extra artifact `.ultramath/smw1bwjo2/m8/Check_bridge.lean` compiles (0 errors): it restates
`QE/TransferWS.lean`'s definitions and closes

```
example : TransferComp.NontrivialTransferWS Axioms.ACVF = NontrivialTransferWS Axioms.ACVF := rfl
```

**but both sides are the file's own copies** — `TransferWS.lean` is not imported (it carries the two
frozen `sorry`s and no module name), so the `rfl` compares copy to copy, not copy to tree.  What it
does establish is that the copies are definitionally the same as each other; I checked by `diff` that
the definitions in `Check_bridge.lean` and in `QE/TransferWS.lean` are textually identical, which is
what the claim needs.

**The caveat, in m8's own words and it is right:** `QFStep` "is a QF-type-realisation/saturation
statement, false for some model pairs, so not derivable from `Axioms.ACVF`; it needs the monster
model or the RV-side QF analysis."  That is consistent with what this file already records elsewhere:
`TransferAtWS` is *equivalent* to fragment QE (so it is true if the theorem is), while `QFStep` is a
**strengthening** of it — for a fixed pair of tuples with equal QF type, the transfer can be settled
by QE without ever finding a QF-mate for a new element.  So `transferAtWS_of_qfStep` is a correct
composition whose hypothesis is stronger than the conclusion's, and the frontier is one of:

1. **`QFStep` at monster models** — then the compactness step (`QFComp.hasQE_of_qfTypeDetermines` in
   `Assembly_val`, and `W1.exists_list_of_models_bounded`) has to carry the result back to arbitrary
   models.  This is the route that joins §3's saturation interface (`MonsterModel.realizes`,
   `Milestone0/Saturation.lean`) to the main line, and it is the reason the §3 work is not a
   side-quest.
2. **The direct transfer by the paper's §4 special transformations**, which is what the paper does and
   what the `smw18ygko/m1/Sec5.lean` skeleton is for.

Either way the junk-truth half is closed (`QE/JunkTrue.lean`) and the composition is available for
free, so the work that remains is the RV-side content and nothing else — the same conclusion the
second route reached from the criterion side.

### `smw1bwjo2` m2 (parameter bridge): the relabel half verified and merged, the bridge still open

m2 delivered its direction in two files and said plainly that `hasQE_of_hasQE_empty` was not among
them.  I compiled both (in the right order — `Relabel` imports `Shift`), 0 errors, no `sorry`, and
`#print axioms` on `wellSorted_relabel`, `guardTrue_relabel`, `inAntecedent_relabel`,
`realize_shiftAux` gives `{propext, Classical.choice, Quot.sound}`.  Merged as
`QE/ParamBridgeShift.lean` and `QE/ParamBridgeRelabel.lean` (namespace `ParamBridge` unchanged;
the `import Shift` line became `import ParamBridgeShift`).

* `wellSorted_relabel` — the transport the *earlier* swarm recorded as not delivered:
  `g : α → β ⊕ Fin m` sending each parameter to a same-sorted parameter or to one of `m` new leading
  variables, `WellSorted sα sn ψ` ⟹ `WellSorted sβ (sortAssem sG sn) (ψ.relabel g)`.  The guard
  transports by `InAntecedent`'s constructors, which is exactly what the compiled `Occurs` could not
  do.  This is what §3 needs to move `acl` between parameter pairs, as well as the bridge.
* `guardsLast_of_GuardTrue` — a fact about the frozen predicate: `GuardTrue s i χ → GuardsLast s i χ`,
  so `WellSorted.all`'s `hg` field is *redundant* given `hj`.  The frozen constructor keeps both; the
  guard information is carried once, not twice.  Recorded, not changed.
* `realize_shiftAux` — full semantics of the variables→parameters gadget, which is the other half of
  the bridge.

**Verdict: rejected, once, with guidance** — the direction's named deliverable is absent and m2 had
already diagnosed its own obstruction, so it continues rather than stops.  The guidance given: the
stuck lemma `wellSorted_shift` looks like a *corollary of `wellSorted_relabel` at `β := α ⊕ Fin k`,
`m := 0`*, since then the variable side does not move (`Fin (0 + n) = Fin n`, and `Fin.natAdd 0` is
the identity), so the "index value fixed as the context grows" obstruction — the one that killed the
earlier attempt — does not arise; the growth is entirely on the parameter side, which `hg` absorbs.
If `shiftAux` also renumbers variables, the general-`N` formulation with `hN : N = n + k` at the use
site is the fallback.

**Still missing, so the bridge is still open:** `hasQE_of_hasQE_empty` itself, and the three lemmas
between: `wellSorted_shift` (`tmSort_shift`, `shift_sortPredG'`, `inAntecedent_shift`,
`guardTrue_shift`), whose intended statements are in `.ultramath/smw1bwjo2/m2/SUMMARY.md`.

## Swarm `smw1bwjo2` closed solved — three of the three named blockers are done

m2's second round delivered the parameter bridge, and accepting it ended the swarm (it was the last
member working).  Final board: **3 accepted**, 3 abandoned (fragment compactness, the mixed-context
QF cover, sort soundness), and 2 (m3, m4) that ended without a verdict — m3's file is green and
merged below, m4 submitted nothing.

**The bridge is closed** (m2, plus two elaboration errors fixed here):

```
QE/ParamSupport.lean        support/paramsOf of a formula, realize_congr
QE/ParamShrink.lean         shrinkAux V k, realize_shrinkAux   (the inverse gadget)
QE/ParamSortTransport.lean  wellSorted_shrink_of_isQF
QE/ParamBridgeShift.lean    the variables→parameters gadget, realize_shiftAux
QE/ParamBridgeRelabel.lean  wellSorted_relabel, guardTrue_relabel, guardsLast_of_GuardTrue
QE/ParamBridge.lean         hasQE_of_hasQE_empty_aux : ∀ T, HasQEempty T → HasQE T
```

All six compile in dependency order, no `sorry`, axioms within {propext, Classical.choice,
Quot.sound}, and the `HasQE` on the right is the encoding's *frozen* one — the hypothesis of
`theorem_2_3_quantifier_elimination`, quantifying over every `α` and every `Fin n`.  So one of the
three blockers the handoff named is gone: QE at the empty parameter context gives full QE.

The construction (m2's) is worth recording because the key step is not obvious: the parameter type is
shrunk to the formula's finite support, *and then one extra witness is adjoined for each sort that
occurs* (`sα (V (g a)) = sα a` must hold for **every** parameter, not only those in the support, or
`wellSorted_relabel` does not apply); the parameters are promoted to leading variables so that
`HasQEempty` fires at context `card + n`; then `shrinkAux` brings the quantifier-free witness back
(quantifier-free is what lets `wellSorted_shrink_of_isQF` transport it), and `realize_relabel`,
`realize_congr`, `realize_shrinkAux` match the truth values.  The two things I closed were `hleft`'s
`Sum.inr` case (`Function.comp_apply` must be unfolded *before* `rw [hga]`, and kept in the simp set
after it, because the rewrite re-creates the composition) and the argument order of
`realize_shrinkAux` (`V, k, χ, v, x` — `(fun e => e.elim)` was landing in the `k` slot).

**The `mul` normal form is closed too** (m3, verified and merged as `QE/MulNormalForm.lean`; its report
arrived after the swarm had ended, so there is no verdict on record — the file is checked here
instead: 0 errors, no `sorry`, axioms clean on the five headline theorems).  Cancellation off `Kˣ`
works because the *repaired* `rvMulOneRV`/`rvMulInvRV` are unguarded:
`rv_mul_eq_mul_iff : a ≠ 0 → (a * b = a * c ↔ b = c)`, `rv_mul_solution_unique`, and the word layer
`mkMul` with `mkMul_perm`, `mkMul_pow_times_factor` (`tⁿ · rest`), plus the formula layer
`pEq_tRVMul_iff`/`pEq_mkMul_cons_iff`.  That is exactly what `qfq_cover` (`smw19wtoj` m3's named gap)
was missing.

**So the state of the three blockers named at `65d3c7e`:**

| blocker | state |
| --- | --- |
| frozen `WellSorted.all`/`.ex` too weak | **closed** — the guard repair, with junk-truth and sharpness machine-checked |
| no mixed-context cover, no `mul` normal form | `mul` normal form **closed** (`QE/MulNormalForm.lean`); the cover `qfq_cover` still open |
| the forward half of the parameter bridge | **closed** — `hasQE_of_hasQE_empty` |

and the frontier for the main theorem is `QFStep IsNontrivialVF Axioms.ACVF` (the one-element
back-and-forth step) or the §4 special transformations, with every input around it now available.

## `qfq_cover`: what the swarm left, and the real statement of the gap

Checked both leftovers before starting.

* **m4 left nothing usable for this.**  Its `out.lean`/`T1.lean` (777 lines) are a copy of
  `Assembly_val`'s realization prelude (`realize_tVFAdd`, `sortedHyps_realize`, `mem_ACVF_*`, …) in
  the `Transfer` namespace — plumbing for its `TransferWS` direction, and it never reported, so
  nothing was judged.  Not merged.
* **m6's `QFCoverMixed.lean` is the fragment layer, and it is green** (1263 lines, 0 errors, no
  `sorry`, `import Enc`).  Merged as `QE/QF2Fragment.lean`: `VFT2`/`RVT2`/`QF2`/`QFq2` over a *sorted*
  context `Fin n → SortTag` with an `RV`-sorted variable constructor (`RVT2.rvar`), their `val`/`Val`
  semantics, `tmSort_toLRV` for both, `realize_toRV`/`wellSorted_toRV` for both, closure under the
  connectives, `VFT2.val_mem`/`RVT2.val_mem`, and the junk conventions derived from `Axioms.ACVF`
  alone.  It stops exactly before the cover.

**The audit's statement of the gap is wrong, and this matters.**  `Missing.MixedContextCover`
(`.ultramath/smw1b0thh/m3/AvAudit.lean:158`) asks for a well-sorted `φ` to be matched by a
*parameter-free* `φ'` and an all-`VF` tuple `y`:

```
∃ φ' : Bf n, ∀ M ⊨ ACVF, ∀ v x, sorted → ∃ y (all VF), (φ.Realize v x ↔ φ'.Realize y)
```

Since `y` may depend on `(v, x)` and `φ'` cannot mention `v`, the only thing this can require of `φ'`
is that it have a true and a false instance — take `φ' := pVF (tv 0 …)`, which has both in every
model of `ACVF` — and it then holds for *every* `φ`.  So gap D as written is vacuous and is not the
content; "no mixed-context cover" was never the right name for the obstruction.  Not fixed in the
audit file (it is a swarm artifact); recorded here.

**The real target, now stated:** `QFRes2.qf2_cover` in `QE/QF2Cover.lean` — for a well-sorted
*quantifier-free* `φ : Bf n` over a sorted context `sn`, there is `q : QF2 sn` agreeing with `φ` at
every sorted tuple in every model of `ACVF`, i.e. the QF fragment is covered by the sorted-context
fragment.  The atom cases are a term extraction; `pVF`/`pRV`/`pUnits`/`pLe`/`pEq` map to
`inVF`/`inRV`/`unitRV`/`leRV`/`eqVF`, and the connectives to `QF2.imp`/`QF2.falsum`, so with
`RVT2.rvar` in the fragment the cover needs no normal form for its *statement* — the `mul` cancellation
(`QE/MulNormalForm.lean`) is what will be needed for the `RV`-term extraction, where a term built from
`rvMul`/`kAdd` must be flattened.

**One design fact paid for, so it is not paid again:** the proof-carrying extraction
`(t : Tm n) → TmSort sE sn t = some .vf → VFT2 sn` does **not** pass Lean's structural-recursion
check, because the sort hypothesis is consumed inside a `cases f` block and the residual goal is
`sizeOf (ts 0) < 1 + l` (`l` an arity, not a size).  The `Option`-valued extraction (`vfOpt`/`rvOpt`,
descending on `t` with no proof argument, soundness by a separate induction on `t`) is the way round;
`QE/QF2Cover.lean` states it that way.  Both remain `sorry`.

### `qf2_cover`: the term extraction is proved

`QE/QF2Cover.lean` (green, 1 `sorry` = `qf2_cover` itself): `vfOpt`, `rvOpt` and **both** soundness
theorems are proved — `vfOpt_sound`/`rvOpt_sound : TmSort sE sn t = some s → ∃ s', vfOpt sn t = some s'
∧ ∀ x, (Val s' x) = t.realize (…)`, axioms within {propext, Classical.choice, Quot.sound}.  The
`Option`-valued design was the right call: the proof-carrying version does not pass the termination
checker (recorded above), while this one descends on the term with no proof argument and needs the
sort hypothesis only in soundness.

Three things cost a round each, recorded so they are not rediscovered:

1. the encoding writes atoms as `rel R ts` for a general `ts`, while `pVF`/`pRVsort`/`pUnits`/`pLe`
   are the `![…]` abbreviations — so every `func` case must rewrite `ts` to `![ts 0]` /
   `![ts 0, ts 1]` before the realization lemma fires;
2. `rvMap`'s argument is a *VF* term, so `rvOpt_sound` must call `vfOpt_sound` (there is no mutual
   induction here, since `vfOpt` never recurses into `rvOpt`);
3. the arity-0 realization lemmas (`realize_tVFZero`, …) leave `M` undetermined under `.symm`, so
   they need `(M := M) (n := n)` explicitly or the instance search gets stuck.

Remaining for `qf2_cover`: the formula induction.  `QF2.Eval` is a pattern-matching `def`, so its
constructor equations are separate `rfl` lemmas, and `IsQF` is an inductive
(`falsum`/`of_isAtomic`/`imp`), with `BoundedFormula.not_all_isQF` excluding the quantifier case.
The atom realization lemmas need stating at general `ts` (`(rel Rel.memVF ts).Realize v x ↔
iVF ((ts 0).realize v)` and three companions), not via `pVF`.

### `qf2_cover` proved

`QE/QF2Cover.lean` is green with **no `sorry`**: `qf2_cover` and its `Eval` form `qf2_cover_eval`,
axioms within {propext, Classical.choice, Quot.sound}.  So the quantifier-free fragment over a sorted
context is covered by the sorted-context fragment `QF2` at sorted tuples in every model of `ACVF` —
the piece that `qfq_cover` needed and that the `mul` normal form was for.

Four obstacles, recorded in the file header so they are not repaid: atoms are `rel R ts` at general
`ts` (so each needs its own realization lemma, not `pVF`'s); `QF2.Eval` is a pattern-matching `def`
(hence separate `Iff.rfl` constructor equations); `IsQF` is an inductive with an impossible
`of_isAtomic` case at an implication (hence `isQF_imp_inv`); and a section variable that a statement
does not mention is **not** in scope for its proof, so the model-free existence of the extracted term
had to be obtained separately (`vfOpt_exists`, by instantiating the model-indexed soundness theorem at
a junk `LRV.Structure PUnit`), with `vfOpt_val` carrying the model inside its conclusion.

### Section 5 scaffold moved into the tree; `lake build` verified

`.ultramath/smw18ygko/m1/Sec5.lean` is now `QE/Sec5.lean` (1110 lines, standalone `import Mathlib`,
compiled here: exit 0, 0 errors, no `sorry`).  It could **not** be put in place of the library module
`SpecialTransformations/SpecialBijection.lean`: the file carries its own copy of `RV` (as `AGENTS.md`
§4 prescribes) and the two copies collide in one `lake build` — measured, `environment already
contains 'SpecialTransformations.RV' from SpecialTransformations.Basic`.  So the library stub stays,
and the content lives beside it; unifying the copies is Milestone 1–2 work.

`lake build` is green (8717 jobs, 14 s) with the stub restored, and the `QE/` directory is now
47 files, **all green**, 16 `sorry` warnings (2 of them the frozen Theorem 2.3 and 2 its copies in the
assembly).  `MILESTONES.md` carries the updated numbers.

### Milestone 1 correction, and `alg:ind:imag`'s blocker

**The milestone check under-reported Milestone 1.**  It said "no `vrv` exact sequence as a theorem";
that is false.  `Milestone0/accepted/IntendedModel.lean` (and five sibling snapshots:
`ACVF_fragment`, `ACVF_gamma_padic`, `ACVF_general_model`, `ACVF_general_model_gamma`,
`ACVF_residue_ops`) prove, for the intended model built from a Mathlib `Valuation`:
`vrv_mul : vrv (rvMul t s) = vrv t * vrv s`, `vrv_range` (`vrv` is onto the value group),
`vrv_kernel` (`vrv t = 1 ↔ t` is a residue unit), `vrv_rv`, and `rvLe` induced by `vrv`.  That *is*
`1 → Kˣ → RV → Γ → 0`.  `MILESTONES.md` is corrected.

**The abstract version is blocked, and this is a statement defect of the same species as the earlier
two.**  `gammaAxioms` link `Γ` to `RV` only through `gVrvMul` (guarded by `uUnits ⊓ uUnits`),
`gVrvEq` (kernel criterion) and `gLeVrv` (order).  Nothing makes `vrv` additive on all of
`RV ∖ {0}`, nothing says `vrv u = ⊤ → u = 0`, and nothing makes `vrv` surjective onto `Γ`.  So "the
exact sequence holds in every model of `ACVF00Γ`" is not derivable from the frozen axioms; the paper's
item 5 ("`Γ` *is* the quotient") is stronger than what was transcribed.  Recorded, not changed — the
axiomatisation is frozen and a change is the author's call.

**`alg:ind:imag` cannot be proved yet, and the reason is exact.**  `QE/Sec3_sat.lean`'s
`swl_alg_ind_image` needs exchange (the paper's proof: `a ∈ acl(t)` ⟹ `a ∈ acl(b)` for every `b` in
the `rv`-fibre of `t`; exchange gives `b ∈ acl(a)`, which the fibre's infiniteness against the
countability of `acl` of a finite set contradicts).  Exchange is `SP.swl_exchange` in
`QE/Sec3_frozen.lean`, still a frozen `sorry`, so any proof of `alg:ind:imag` today would carry
`sorryAx`.  The two halves of the paper's argument are in place — `QE/ParamBridgeRelabel.lean`'s
`wellSorted_relabel` is the parameter transport, and `QE/ParamBridge.lean`'s support machinery is what
counts the solutions — but exchange itself has to be proved first (it is Yin, QE:ACVF:min, Lemma 4.3,
i.e. the matroid property of `acl` in `ACVF`).

### §3: `exchange` moved to the monster model (it was frozen over arbitrary models)

`swl_exchange` was stated over an arbitrary `M ⊨ ACVF`.  That is the wrong setting: exchange is a
property of `acl` in a *saturated* model (it is what makes `acl` a pregeometry), and §3 of the paper is
over the monster model.  Withdrawn from `QE/Sec3_frozen.lean` (green, 4 `sorry`s) and restated in
`QE/Sec3_sat.lean` over `Sat.MonsterACVF` with `𝕄.Small` on both parameter sets (green, 8 `sorry`s).
Still a frozen target, so `alg:ind:imag` remains unprovable without `sorryAx` — but the statement is
now one that can be true.

So `alg:ind:imag` has exactly three inputs, in dependency order: exchange (must be proved from
`MonsterModel.realizes`/`exists_automorphism`; Yin QE:ACVF:min 4.3), the parameter transport (in
`QE/ParamBridgeRelabel.lean`, `wellSorted_relabel`), and the counting argument (`rv`-fibre infinite vs
`acl` of a finite set small — needs countability of the `L_RV` formula set).  Recorded in
`DECISION.md`.

## Correction, from the source: there is ONE route, and it goes through `L_v` QE

I had been treating "Route A" (`L_RV` direct, QF-type/Shoenfield) and "Route B" (`L_val` reduction,
`Assembly_val`) as rival proofs of `HasQE ACVF`.  That is wrong, and the source says so explicitly.

**1. `paper.tex` does not prove Theorem 2.3.**  It states it as `theorem[cite[Theorem 3.10]{Yin:QE:ACVF:min}]`
(`paper.tex:508`): the QE content is `qe.tex` (arXiv:1006.1393) Theorem 3.10.

**2. `qe.tex` §3 opens by reducing QE to Weispfenning's `L_v` theorem** (`qe.tex:549`):

> "In this section we shall use Shoenfield's test to show that `ACVF`, `ACVF†`, and `ACVF‡` all
> admit QE.  Our strategy is to **reduce the task to a case where we may apply Theorem 2.7**
> (`weis:qe`: *the theory of algebraically closed valued fields **as formulated in `L_v`** admits
> QE*)."

**3. The reduction is Remark `L:v:and:L:RV`** (`qe.tex:552`), and it is exactly the VF-generated
condition:

> "`L_RV` may be viewed as an expansion of `L_v`. … Let `f'` be an `L_RV`-isomorphism of two
> `L_RV`-substructures.  **If `K'` is VF-generated** then `f'` may also be treated as an
> `L_v`-isomorphism.  If `L` is sufficiently saturated then, by Theorem 2.7, `f'` may be extended to
> an `L_v`-monomorphism `f : K → L`, which is also an `L_RV`-monomorphism.  **Note that this procedure
> may fail if `K'` is not VF-generated, that is, if `rv(VF(K')) ≠ RV(K')`.**"

**4. Everything else in `qe.tex` §3 is the repair of the non-VF-generated case** — and it is exactly
the lemma set the tree already carries as `QE/Lemma32_root_lifting.lean` (`rv:root:lift:vf`),
`QE/Lemma35_divisible_hull.lean` (`lift:divisible_hull`), `QE/Lemma37_transcendental.lean`,
`QE/Lifting_transcendental.lean`, `QE/RV_henselian.lean`, plus `aclS:model` and
`algebraic:balls:definable:centers` from §4.  So the "non-VF-generated case" *is* the paper-specific
content, and it is where §3/§4's structure theory (and `alg:ind:imag`) is used.

**5. The tree already states the paper's route, faithfully.**  `QE/Reduction_assembly.lean`:

```
structure AlgIngredients : Prop where
  rv    : ∀ M ⊨ ACVF, RVeqRvVF M                       -- RV = rv(VF×) ∪ {0}   (PROVED: RVeqRvVF_of_model)
  prep  : ∀ M N hSat, PrepStep M N hSat                 -- Lemma 3.3 + henselization
  one   : ∀ M N hSat, OneStepVF M N hSat                -- Lemmas 3.4–3.8
  vfgen : ∀ M N, VFGenCase M N                          -- Remark 3.1 + Weispfenning's L_v QE   ← the person's point
theorem theorem_2_3_of_hypotheses (hShoen : ShoenfieldTest) (hAlg : AlgIngredients) : HasQE ACVF
```

So the frontier of the main route is `ShoenfieldTest` + `prep` + `one` + `vfgen`, and **`vfgen`
contains Weispfenning's `L_v` QE** — the `L_val` QE is not an alternative route but a load-bearing
input of the one route.  `theorem_2_3_of_three` already discharges the `rv` field.

**Consequences for the plan, and for what I have been doing.**

* The **criterion family** (`TransferWS`, `FragmentTransfer`, `QF2Fragment`, `QF2Cover`,
  `MulNormalForm`, `ParamBridge*`, `JunkTrue`, `FailProbe`) is a *third* formulation, equivalent to
  the target (`W1.hasQE_iff_qfTypeDetermines`, `Missing.nontrivialTransfer_iff_hasQEb`).  It is
  **check**, not route — it can validate, and pieces of it (`qf2_cover`, junk-truth) are reusable,
  but closing `QFStep` would not close Theorem 2.3 by the paper's argument.
* The **§3/§4 structure theory is on the critical path**, through `prep`/`one` (and `aclS:model`),
  not a side-quest.  `alg:ind:imag` matters because `aclS:model` needs it.
* `Assembly_val`'s `L_val` assembly (`hasQE_ACVF_val`, the Johnson/Chevalley/prime-models family) is
  the natural home of `vfgen`, i.e. of Weispfenning's theorem — which is where Route B's machinery
  actually belongs: as a *proof of `vfgen`*, not as a rival end-to-end route.
* **Keep both families alive** (author's instruction this session), but the priority order is now:
  `ShoenfieldTest` → `prep` → `one` → `vfgen`, with the criterion family as the independent check.

### The swap lemma exchange needs: Mathlib has no variable substitution

Checked in the pinned Mathlib (`Mathlib/ModelTheory/Syntax.lean`): the only substitutions on
`BoundedFormula` are

```
def subst  (φ : BoundedFormula α n) (f : α → L.Term β) : BoundedFormula β n      -- PARAMETERS only
def relabel (φ : BoundedFormula α n) (g : α → β ⊕ Fin m) : BoundedFormula β m    -- parameters → params/new vars
def castLE, liftAt, alls, ex                                                  -- no variable substitution
```

So there is **no** operation that substitutes a *variable* (`Fin n`), and therefore none that demotes a
variable to a parameter — which is exactly what exchange needs.  The swap is: promote the last `VF`
parameter to a second variable (`wellSorted_relabel` does this, it is in `QE/ParamBridgeRelabel.lean`),
interchange the two variables, then demote the second variable back into the last `VF` parameter slot.
The first step exists; steps two and three need a variable-level substitution that
`Mathlib` does not provide.

**So the swap lemma is a development, not a lemma**: a `BoundedFormula`/`Term` variable substitution
`Bf α (n+1) → Bf (α ⊕ Fin 1) n` (or a general variable renaming), with

* `TmSort` preservation under a *sort-preserving* variable substitution (term induction),
* `WellSorted` preservation (formula induction, with the `GuardTrue` field transported — `InAntecedent`
  and `GuardTrue` transport by their constructors, as `guardTrue_relabel` already shows for the
  parameter case),
* the realization lemma (a third induction, or a simultaneous one).

That is the missing infrastructure for `swl_exchange` and for `alg:ind:imag`; it is independent of
model theory and can be assigned as its own item.

### `inf:RV:def:gam` proved (§3, swarm `smw1jgnht` m7, accepted)

`QE/InfRVDefGam.lean` (green, no `sorry`, axioms within {propext, Classical.choice, Quot.sound}):
the paper's lemma at `paper.tex:746` — *`V = {γ : vrv⁻¹(γ) ∩ A` nonempty and finite`}` is finite and
definable* — in the `LRVΓ` expansion, from the paper's two uses of C-minimality (`hbdd`, the
compactness bound that produces the defining formula, and `hCM`, "by C-minimality again `V` is
finite", applied to `smallPart A` so it is not the conclusion).  This closes one of the two Section-3
items recorded as *unstatable* for lack of `Γ`-vocabulary; `aclS:model` is the remaining one, and it
is what `prep` in `Reduction_assembly` consumes.
