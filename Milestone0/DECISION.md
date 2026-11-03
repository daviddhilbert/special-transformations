# Milestone 0 — how `L_RV` is represented in Lean

Decision and evidence. Everything asserted below was checked in this repository's
environment (Lean 4.33.1, Mathlib prebuilt at `/opt/mathlib`); the Lean files named are the
artifacts, and each one elaborates with `lean <file>` and `import Mathlib` as its only
import.

## Decision

**Represent `L_RV` in Mathlib's one-sorted `FirstOrder.Language`, on a tagged carrier, with
`Γ` kept out of the syntax.** Concretely:

* the carrier is a disjoint union (`VF ⊕ RV`, or a three-way tag when `Γ` is adjoined);
* each sort is a unary relation symbol, and quantifiers over a sort are guarded by it;
* `Γ` is *not* a sort (see below): it is model data, or a definitional expansion by the
  definable quotient `RV/K^×`;
* the paper's partial `+`, `−` on `K` are total functions whose values off `K` are a fixed
  junk element, and the axioms are relativised to `K`.

Candidates (b) (vendor `Mathias-Stout/Many-sorted-model-theory`) and (c) (write a
many-sorted layer in-repo) are rejected, with reasons in "Why not (b)".

## Why (a)

1. **The API the later milestones need is Mathlib's, and only (a) has it.**
   `FirstOrder.Language`, `Structure`, `Term`, `BoundedFormula`, `BoundedFormula.IsQF`,
   `Theory`, `Theory.Model`, `Set.Definable`, `Language.DefinableSet` all exist there.
   Mathlib has *no* quantifier-elimination notion and *no* C-minimality
   (`grep -ri 'QuantifierElim'` and `CMinimal` over `/opt/mathlib/Mathlib`: no hits), so the
   two targets are new statements either way — but statements *about definable sets* are
   native to (a) and must be built from scratch in (b).

2. **The tagging is faithful, not a hack.** `Milestone0/Tagging.lean` builds many-sorted
   syntax with Tarski semantics and a translation into the tagged one-sorted language, and
   proves `BForm.realize_translate : (translate φ).Realize (tagFree v) (sigA xs) ↔
   Realize M v φ xs`, with the quantifier case `∀x^s` ↦ `∀x, S_s x → φ'` discharged by a
   genuine argument (`forall_sigma_eq` + `snoc_sigA`). The only hypothesis is that every
   sort is inhabited, which holds for `L_RV` (`0 ∈ VF`, `0, ∞ ∈ RV`). Axiom footprint:
   `propext, Classical.choice, Quot.sound`.

3. **It carries the whole milestone.** `Milestone0/Encoding.lean` (862 lines, two `sorry`s,
   both the targets) has: the twelve function and two relation symbols of Definition 2.1;
   `ACVF` as Definition 2.2 items 1–6; `ACVF(0,0)`; `ACVF_S(0,0)` as the constant expansion
   of `S` plus its atomic diagram; `HasQE` with Theorem 2.3 as `HasQE ACVF`; C-minimality
   with Theorem 2.8 as `∀ M, M ⊨ ACVF → IsCMinimal M`; and the mixed definable sets of
   Notation 2.10 on the index type `Fin n ⊕ Fin m`, which is exactly `VF^n × RV^m` with no
   junk values and no sort hypotheses.

4. **Partial symbols cost nothing.** `Milestone0/Partiality.lean` proves that totalising the
   paper's partial `+`, `−` with a junk value is conservative: a partial term is defined
   exactly when its totalised value differs from junk (`exists_iff_realize_ne_junk`), under
   two hypotheses (`JunkFresh`, `JunkProp`) that are each *necessary* (counterexamples
   included) and each *derivable* from Definition 2.1(2d) with junk `= ∞`
   (`spec_gives_hypotheses`), because `∞` is already a constant and the paper says the
   symbols "should all be relations". So (a) needs no extra axiom for partiality.

5. **The intended structure exists in Lean.** `Milestone0/RVModel.lean` builds the model
   over a Mathlib `Valuation K Γ₀`: `RV = Option (Kˣ ⧸ (1+𝔪))`, `rv`, `vrv`,
   `t ≤ s ↔ vrv s ≤ vrv t`; proves the RV-part of Definition 2.2 for it (group axioms,
   divisibility under `IsAlgClosed K`, `∞`/`0` augmentation, `≤` a preorder with `∞` top and
   `K^×` the class of `1`, `𝒪 = rv⁻¹(RV^{≥1})`, `𝔪 = rv⁻¹(RV^{>1})`, `ker vrv ≅ k^×`), and
   instantiates the axiomatisation at it (`rvGroupAxioms_intended`), which is the test that
   distinguishes a theory from a table.

6. **Theorem 2.8 has real mathematics behind it.** `Milestone0/Balls.lean` defines the
   valuation C-relation `C x y z := v (y - z) < v (x - y)`, proves the four C-relation
   axioms for it (`isCrelation_Crel`), the ball-nesting and `rv`-fibre lemmas, and the
   Boolean closure of ball combinations.

## Why not (b)

Measured, not assumed. `Mathias-Stout/Many-sorted-model-theory` at `4d15933` **does build**
in this environment after three or four mechanical Mathlib renames (two `Set.mem_setOf_eq →
Set.mem_ofPred_eq`, one `Set.coe_setOf → Set.coe_ofPred`, one `simp only` repair);
`lake build` then reports `Build completed successfully (3049 jobs)` against
`/opt/mathlib`. Three members independently attempted the port and two stopped one rename
short, so early reports that it "does not build" are wrong.

It is still the wrong dependency:

* **no definability layer** — `grep -ri definable` over its 23,222 lines returns nothing,
  while every remaining milestone is about definable subsets, dimensions, special
  bijections and Jacobians;
* **it replaces Mathlib's syntax** with its own `MSFirstOrder`, so `Set.Definable`,
  `IsQF`, `Theory.Model` and `Language.DefinableSet` are lost — the very API (a) is being
  chosen for;
* its concrete valued-field example is a *three*-sorted `VF / Γ∪{∞} / residue` language,
  not `L_RV`, so it does not even supply the paper's signature;
* the one thing it buys — sorted contexts `VF^n × RV^m` instead of a guarded tuple — is
  recovered in (a) by the index type `Fin n ⊕ Fin m`, as `Encoding.lean`'s downstream
  section shows.

Candidate (c) would re-derive (b)'s syntax inside the repository at a measured cost of
roughly 1.5–6k lines, for no gain over (a).

## The points that decide correctness (each one cost a member a rejection)

* **`Γ` is not a sort.** The paper treats it as imaginary: "syntactically any reference to
  `Γ` may be eliminated". An encoding may adjoin it, but then it is a definitional
  expansion (`RV/K^×` by the definable relation `t ~ s ↔ ∃u ∈ K^×, t = u·s`), and Theorem
  2.3 as printed concerns `L_RV` alone.
* ~~**`0` and `∞` are different points.**~~ **Superseded — this was a transcription error.** See
  the revision section below: `0` and `∞` are one element, `rv(0)`.  Kept for the record because
  the reasoning shows what a wrong transcription of (6) looks like.  `K = K^× ∪ {0}` uses the constant `0` as the
  residue field's zero; `∞ = rv(0_VF)` is the top of `≤` and is absorbing on `RV₀`
  (`t × ∞ = ∞` for all `t`), while `t × 0 = 0` only for `t ∈ K`. Identifying them — one
  member's first axiomatisation did — forces `0 = ∞`, and then `le_top` + `le_zero` +
  `0 ≠ 1` make the theory inconsistent, so both target theorems become vacuous. A referee
  proof of that inconsistency is what rejected the first version.
* **Guard the residue-field axioms by `x ≠ ∞`, not by the sort predicate.** The `RV` sort's
  carrier contains `0`, `K^×` *and* `∞`, so `∀x ∈ RV-sort` includes `∞`; the paper's field
  is `K = K^× ∪ {0} = RV-sort ∖ {∞}`. Asserting Definition 2.2(3) at `∞` — in particular
  "every nonzero element is invertible", together with `t × ∞ = ∞` and commutativity —
  derives `1 = ∞`, hence `0 = ∞` (via the same disjunction), and no intended model
  survives. The encoding therefore relativises every `K`-quantifier with `allSortedK` /
  `exSortedK` (`x ≠ ∞`). This was a genuine defect in the first committed version of
  `Encoding.lean`; it was found by a member proving the *negative* result
  (`¬ (K ⊕ RV₀) ⊨ ACVF` for any placement of the constants) and is fixed in
  `Axioms.kField`, `Axioms.acfSchemeK`, `Axioms.kAlgClosed`.
* **`K^×` is the class of `1`, not everything below `∞`.** The paper's `K^×` is the
  residue field's units — the subgroup `{x : vrv x = 1}`, which is *proper* as soon as `Γ` is
  nontrivial. An earlier sort axiom defined `K^×` as `RV-sort ∖ {0, ∞}`, i.e. the whole
  multiplicative group `RV^× = K^× · Γ`; combined with axiom (4) (`K^×` is the class of `1`)
  that puts every `x ∉ {0, ∞}` in the class of `1`, so `1 ≤ x ≤ 1` holds for all of them and
  the preorder — hence `Γ` — collapses to a point, contradicting the paper's standing
  hypothesis `Γ(S)` nontrivial. `sdUnits` now only says that the predicate lives on the `RV`
  sort; its content comes from `leClassOne`.
* **`K` is `K^× ∪ {0}`, not `RV ∖ {∞}`.** This is the subtlest of the repairs. Guarding the
  residue-field axioms by `t ≠ ∞` still over-asserts them: when `Γ` is nontrivial, the
  elements of `RV ∖ {0, ∞}` of value `≠ 1` are outside `K`, the residue operations are junk
  there, and the field axiom `t + 0 = t` together with invertibility then fails at such a
  `t` — so `t ≠ ∞` as a guard forces `Γ` trivial just as the original sort-predicate guard
  forced `0 = ∞`. Definition 2.1(d) is explicit: `K = K^× ∪ {0}`, with `K^×` the predicate
  of Definition 2.2(4), i.e. the class of `1`. Every `K`-quantifier is now guarded by
  `pInK t := pUnits t ⊔ t = 0`, and `sdKAdd`, `sdKNeg`, `sdKMul` and `rvMulZeroK` use it too.
  (`t ≠ ∞` remains in the file as `pK`, but is no longer used as a guard.)
* **`K` must be closed under `×`, not only under `+` and `−`.** The paper's `K = K^× ∪ {0}`
  is a field. With the field axioms guarded by `pK` but no closure axiom for `×`, a model may
  send the product of two elements of `K` to `∞`, and the axioms then constrain only those
  products that happen to land back in `K`. `sdKMul` now states the closure.
* **`rv` is onto the units only.** `rv : VF^× → RV^×` is surjective onto
  `RV^× = RV ∖ {0, ∞}`; the residue zero is *not* in its image (it is absorbing, hence not
  a group element). An axiom saying "every `t ≠ ∞` is `rv x`" excludes the intended model.
* **The ACF scheme must be the right scheme.** `acfScheme k` has to say "every monic
  polynomial of degree `k` has a root", i.e. the Horner form must be
  `x^k + a_{k-1}x^{k-1} + ⋯ + a_0`. A first version started the Horner fold at `x` rather
  than at `x + a_{k-1}`, which silently produced `x^{k+1} + a_{k-1}x^{k-1} + ⋯ + a_0` — a
  monic polynomial of degree `k+1` with zero `x^k` coefficient, so `acfScheme k` covered only
  a proper subclass (at `k = 1`, only the quadratics `x² + a_0`) and neither `VF` nor `K`
  was actually algebraically closed. Fixed in `LRV.hornerPoly`, with `hornerPoly_one` and
  `hornerPoly_two` as regression lemmas.
* **Orientation of `≤`.** With `t ≤ s ↔ vrv s ≤ vrv t`, the ultrametric inequality reads
  `rv a ≤ rv (a+b) ∨ rv b ≤ rv (a+b)`. The tempting "`val (a+b)` equals one of
  `val a`, `val b`" is strictly weaker and admits non-valuations.
* **Quantifier elimination is a statement about a theory**, `T ⊨ᵇ (φ ⇔ ψ)`, not a
  per-structure claim with parameters; C-minimality quantifies over all models of
  `ACVF_S(0,0)` and over parametrically definable sets produced by the syntax.

## The model (closed)

`accepted/ACVFModel.lean` proves `model_ACVF : (M K) ⊨ Axioms.ACVF` and
`exists_model_ACVF : ∃ M, LRV.Structure M ∧ M ⊨ ACVF`, at `K = ℂ` and
`M K = K ⊕ RV₀ K` with the **trivial valuation**: every element of `K` is a unit,
`𝒪 = ⊤`, `𝔪 = ⊥`, the residue field is `K` itself and `Γ` is trivial. It also proves
`model_ACVF00`. So `ACVF` and `ACVF(0,0)` are consistent, and Theorems 2.3 and 2.8 as
stated are not vacuous.

The trivial valuation is what makes this cheap: `K^× = RV ∖ {0, ∞}`, so the residue
field is `K` rather than the residue field of a valuation ring, and no integrality
argument is needed. `isAlgClosed_residueField` in `accepted/ResidueField.lean` covers the
general case.

What this does *not* give: a model of `ACVF_S(0,0)` with `Γ(S)` nontrivial, which is the
setting of the paper's theorems. That needs the general model over a nontrivial valuation,
of which `rvGroup` (`accepted/` — m8's block) and `vfAlgClosed`
(`accepted/VFAlgClosed.lean`) are done.

* **`rvSurj` is weaker than the paper's axiom (open, twelfth defect).** The encoding states
  `pUnits t → ∃ x, rv x = t`, i.e. `rv` is onto the class of `1`, which is the subgroup
  `K^× = ker(vrv)`. The paper's axiom is `rv : VF^× → RV^×` surjective onto
  `RV^× = RV ∖ {0, ∞}`, the *whole* multiplicative group, of which `K^×` is the proper
  subgroup of value `1`. So a model may contain elements of `RV ∖ {0, ∞}` that are not in the
  image of `rv`, and the QE reduction needs `RV = rv(VF^×) ∪ {0}` as an extra hypothesis
  (`.ultramath/smw081ptp/m1/Assembly.lean`, `AlgIngredients.rv`) because of it. Fixing it
  means guarding `rvSurj` by `t ≠ rvZero ∧ t ≠ rvInfty` instead of by `pUnits`; the intended
  model satisfies the stronger form, since `RV = Kˣ/(1+𝔪)` is by construction a quotient of
  `VF^×`. Not changed while the model artifacts in `accepted/` are proved against `d608de6`.

## Revision on the author's instruction: `0` and `∞` are one element

**There is one axiom set — the paper's.**  The two-constant form that this file recorded earlier
was a *transcription error*, not a different axiomatisation, and it is worth naming why it was
detectable: the intended structure has `rv(0) = 0 = ∞`, so a first-order theory that proves
`rv(0) ≠ ∞` (as the earlier form did, in `accepted/RepairedTheory.lean`) has no intended model.
A transcription that refutes its own intended model is simply wrong; nothing about the paper
changed.

The author has ruled on the convention: **there is no separate `0` in `RV`.**  Writing
`rv(0) = 0` makes `0` the absorbing element of `RV`, and the paper's `∞` is another name for
it.  This is also what the paper's axiom (2) requires: `(RV^×, 1, ×)` is a divisible abelian
*group*, and `RV^× = RV ∖ {∞}` — a set that is a group only if the removed element is the
absorbing one.  So `RV = {rv(0)} ∪ RV^×`, `K^× ⊆ RV^×`, `RV^×/K^× = Γ`.

This reverses the earlier repair recorded above as "`0` and `∞` are different points".  Applied
in this revision:

* `Fn.rvInfty` is deleted from the language: one constant, `rvZero`.  `tRVInfty`, `uRVInfty`
  and `iRVInfty` remain as *definitions* equal to `tRVZero`, `uRVZero`, `iRVZero`, so that the
  axioms and downstream files still read in the paper's notation.
* `rvSurj` is now the paper's surjectivity: `t ≠ rv(0) → ∃ x ∈ VF, rv x = t`.  It was guarded
  by `pUnits` (the class of `1`), which allowed `RV`-elements outside the image of `rv`.  With
  the corrected axiom, `RV = rv(VF^×) ∪ {0}` follows in the theory, so there are no such
  elements: the "junk" that the guarded axiom admitted is excluded by the axiom itself.
* `RVModel.lean`: the `RV`-carrier is the two-layer `RV = Option (RVUnit) = {rv(0)} ∪ RV^×`;
  `RVGroupAxioms` loses `zero_ne_infty`, `IsRVUnit t := t ≠ rvZero`, and the absorbing/top
  element in the axioms is `rvZero`.  `rvGroupAxioms_intended` compiles, i.e. the intended
  model satisfies the corrected RV layer with `0 = ∞`.
* sha256 of `Encoding.lean` after the revision, **final**:
  **`e4d1a5f49ece39598d59fdffd60f0402bc553a1ee6681c96add4afc729fd3408`**.  (Two intermediate
  states had `3c14aa7c…` and `63e92fca…`; the differences are docstrings only — the `K`-guard
  commentary, `RV₀`, `rv 0 = 0`, and finally the caution that `pK` (`t ≠ ∞ = 0`) is the group
  `RV^×`, *not* the residue field, which is `pInK`.  No definition or axiom has changed since
  `3c14aa7c…`, so every conversion made against any of the three hashes is against the same
  code.)
* Verified after the propagation: `make milestone0` (5 files), `make accepted` (14 files) and
  `make qe` (28 files) all exit 0 with no errors and no `sorry`; every `#print axioms` in all
  47 files is a subset of `{propext, Classical.choice, Quot.sound}`.
* **All twelve snapshots are converted.**  `accepted/ACVF_residue_ops.lean` was the last: the
  three-layer `rv0Mul`/`le0` became `abbrev`s of `rvMul`/`rvLe` on the two-layer carrier (so every
  statement naming them keeps its name and its meaning), the dead `fMap` clause for the deleted
  constructor is gone, `model_rvSurj` is the paper's surjectivity, and
  `model_ACVF_of_components` is byte-identical to the original.  Two mechanical passes of mine
  failed on it before this one worked; the reason is worth recording: the partial conversion had
  left `rv0Mul`/`le0` three-layer while the carrier had already moved, and a dead `fMap` clause
  made `fMap` itself a `sorry`, which cascaded into ~40 errors that looked like a dozen unrelated
  problems.

Still to propagate (in progress): the standalone copies of the encoding inside
`Milestone0/accepted/*.lean` and inside the `QE/` snapshots that embed it, then `make accepted`
and `make qe` against the new hash.  Each such file carries its own copy of `Fn`, the
`tRVInfty` definition, `rvSurj`, and — in the model files — the three-layer carrier
`RV0 = Option RV` with `cKZero ≠ cInfty`; the model files are the ones that need more than a
mechanical edit.

## Open (Milestone 1)

* **No proved model of the general `ACVF` over a nontrivial valuation.** `RVModel.lean` covers the RV-part; the field
  structure on `K` (transported from `ValuationSubring.ResidueField` along
  `(𝒪∖𝔪)/(1+𝔪) ≅ k^×`) and the `Γ` quotient are not constructed. Until one model exists,
  the two target theorems are statements that *could* be vacuous, and this is the first
  thing to close.
* **Theorems 2.3 and 2.8 are stated, not proved** — as this milestone requires.
  `Balls.lean` also carries one unproved auxiliary (`infinite_boolComb_contains_openBall`),
  labelled as such.
* **The files are standalone.** Each is `import Mathlib` with its own copies of the RV
  definitions, so they are not yet part of the `SpecialTransformations` library: their
  top-level names collide with `SpecialTransformations/Basic.lean`. Merging under one
  namespace is Milestone 1 work, as is wiring `Language.lean` and `Main.lean` to them.

## Files

| File | What it is | Checks |
| --- | --- | --- |
| `Encoding.lean` | `L_RV`, `ACVF`, `ACVF_S(0,0)`, QE and C-minimality targets, mixed definable sets | `lean`, 2 target `sorry`s |
| `RVModel.lean` | the intended structure over a Mathlib valuation; RV axioms instantiated | `lean`, no `sorry` |
| `Partiality.lean` | conservativity of junk-value totalisation for the partial symbols | `lean`, no `sorry` |
| `Tagging.lean` | many-sorted syntax and its satisfaction-preserving translation to the tagged language | `lean`, no `sorry` |
| `Balls.lean` | the valuation C-relation, ball combinatorics, C-minimality definitions | `lean`, 1 unproved auxiliary |
| `SPEC.md` | transcription of Definition 2.1, Definition 2.2, Theorems 2.3 and 2.8 from the arXiv sources, with line numbers | machine-checked tables |

## Thirteenth defect (found during the QE campaign): item 5 of Definition 2.2 is only half transcribed

Recorded here because it is a defect of the encoding, not of the mathematics, and because it
**refutes the frozen Theorem 2.3 statement**.  Full argument in `QE-PLAN.md`, last three
sections; the short form:

`qe.tex` Definition 2.2 item 5 says the quotient `RV / K^× = Γ ∪ {∞}` is a divisible *ordered*
abelian group whose ordering is induced by `≤` and whose group operation is induced by `×`.  The
encoding's `Axioms.leMulCompat` states this only for multipliers in `K^×` — the class of `1`,
which is the *identity* element of `Γ`:

```
leMulCompat : pRV a ⟹ pRV b ⟹ pRV c ⟹ (pUnits c ⟹ (pLe a b ⟹ pLe (a·c) (b·c)))
```

The missing case is `c` an arbitrary element of `RV^×`.  It is not derivable from the rest:
coarsening the order of any model along a monotone `f` with `f⁻¹ (f 0) = {0}` preserves every
axiom that mentions `≤`, and with `f = sign` the coarsened model is still a model of `Axioms.ACVF`
while the formula `θ (a, b) :≡ ∀ c (RV ∖ {0}), a·c ≤ b·c` defines the true order `γ_a ≤ γ_b`, which
no quantifier-free formula can define there (restricted to `γ_a, γ_b > 0` the only non-constant
atoms are finitely many lines through the origin, and a half-plane is not a Boolean combination of
those).  So the frozen `HasQE ACVF` is false, not merely hard.

The same slip — `pUnits` (`Kˣ`, the subgroup of value `1`) written where the paper has `RV^×` —
also affects item 2: `rvMulOne`, `rvMulInv`, `rvMulMem`, `rvDivisible` are all `pUnits`-guarded, so
the encoding axiomatises `Kˣ` as a group and never says that `RV^×` is one.  That is a fidelity gap,
but it is **not** needed for the QE transfer: stated with the guards on `a`, `b` dropped and only
`c ≠ 0` kept, item 5 alone carries `axScale` (`paperScale_of_vfPred_scale` in
`.ultramath/smw14elno/m1/Scale.lean` proves the two are equivalent), whereas a `pRV`-guarded form
would force `axScale`'s zero cases into a cancellation argument that needs the missing inverses.
So the minimal repair of item 5 is **one** sentence.  A separate gap, unrelated to it, is that the
frozen axioms admit trivially valued models while `L_val`'s `ACVF_val` requires `axNontrivial`; the
final theorem therefore needs a case split on triviality.

Two further defects of the same family were found later (swarm `smw1541fr`) and are recorded in
`QE-PLAN.md`: item 2's group laws are `pUnits`-guarded (so `RV^×` is never a group, and
`rv a = rv b` is not equivalent to any `v`-comparison), and — worse — `iKAdd`/`iKNeg` are not tied
to the field's addition at all, so twisting them by an automorphism of `(K^×, ·)` gives a model of
the frozen axioms in which `HasQE` fails for a reason disjoint from the order. **The frozen
`theorem_2_3_quantifier_elimination` is therefore false for at least two independent reasons**, and
the repair is four items: `leMulCompat` (item 5), `rvMulOne`/`rvMulInv` (item 2), and
`kAddLink`/`rvEqLink` plus junk conventions for the residue symbols.  All four await the ruling.

The repair restores the paper's item 5:

```lean
def leMulCompat : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv]
    (pRV &0 ⟹ (pRV &1 ⟹ (pRV &2 ⟹ (pLe &0 &1 ⇔ pLe (tRVMul &0 &2) (tRVMul &1 &2)))))
```

(`pRV &2` in place of `pUnits &2`, and `⇔` in place of `⟹`; the intended model satisfies it because
`vrv` is multiplicative and `Γ` is an ordered group, so `vrv (a·c) = vrv a · vrv c` and the Γ-order
is translation-invariant.)  This moves the frozen hash of `Milestone0/Encoding.lean` and needs the
same propagation as the `rvSurj` repair: every `QE/` and `accepted/` snapshot that carries a copy
of the axiom set, plus `RVModel.lean`'s `rvGroupAxioms_intended`.  **Not applied**: awaiting the
author's ruling.

## The repair, applied (author: "edit anything as you see fit")

The transcription defects recorded above are repaired in `Milestone0/Encoding.lean` **additively**:
no axiom is removed or weakened, so every theorem proved before the repair stays proved, and each
added sentence is true in the intended structure.  The new theory is `Axioms.repairRV`, included in
`ACVFpaper`:

| sentence | what the paper says | what the frozen axioms said |
| --- | --- | --- |
| `leMulCompatFull` | item 5: `RV/Kˣ = Γ` an **ordered** group, so `a ≤ b ↔ ac ≤ bc` for every `c ≠ rv 0` | `leMulCompat`, `pUnits c`-guarded — only the identity class of `Γ` |
| `rvMulOneRV`, `rvMulInvRV` | item 2: `(RV^×, 1, ×)` a divisible **group** | `rvMulOne`, `rvMulInv`, `pUnits`-guarded — only the subgroup `Kˣ` |
| `kAddLink`, `kNegLink` | items 3, 6: `K` is *the residue field* of `vv = vrv ∘ rv` | `kAdd`/`kNeg` constrained only inside `K`, never linked through `rv` |
| `rvEqLink` | `rv a = rv b ↔ v (a - b) > v b` | nothing |
| `kJunkZero`, `kNegJunkZero` | a fixed convention off `K` | the values off `K` were free |
| `axNontrivialRV` | the valuation is **nontrivial** (needed by Theorems 2.3 and 2.8) | no nontriviality sentence |

Each was necessary: for the first, the second and (jointly) the residue links there are explicit
models of the frozen axioms refuting Theorem 2.3 — a coarsened order, a twisted residue addition,
and a trivially valued field (which agrees with a nontrivially valued one on every quantifier-free
sentence) — recorded with their arguments in `QE-PLAN.md`.

```
sha256 of Milestone0/Encoding.lean after the repair: 2cc0d20fc272c75a8b5adff30ca2663f6722c27d3bbee2b6d840a27ec87daffe
```

`QE/Assembly_val.lean` carries the same axiom set, and with it the extraction is now
**unconditional**: `Transfer.model_ACVF_val_of_model (hM : M ⊨ Axioms.ACVF)` gives
`ValPM.ACVF_val` on the `VF` sort with no side hypotheses, and
`Transfer.paperScale_of_model`, `Transfer.hasNontrivVal_of_model` derive the two hypotheses that
were previously assumed.  The snapshots in `Milestone0/accepted/` and the older files in `QE/`
still carry their own copies of the *pre-repair* axiom set; since the repair only adds axioms, each
of them remains a true statement about the theory it states, and re-verifying them against the new
hash is bookkeeping to be done as they are next touched.
