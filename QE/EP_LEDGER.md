# Ledger: the two valuation-theory inequalities (direction `d4`, member `m3`, swarm `smw2ngn1z`)

Scope of this member: Lemma 3.6 (`lift:transcendental`, `qe.tex:732`) and the two Prestel–Engler
inequalities it and Lemma 3.4 consume. Registered direction `d4`: *Mathlib-side feasibility audit
and bridge ledger for the two inequalities, plus whatever Mathlib's vocabulary does support,
proved*.  The full Lemma 3.6 chain belongs to `d1` (`m8`), the non-vacuity audit to `d2` (`m4`);
nothing here overlaps them: no proof of Claim (⋆), no witness search.

## 1. Deliverables (all compile with `exit 0`, no `sorry`/`admit`/`native_decide`/`axiom`)

| file | content | status |
|---|---|---|
| `GammaTorsion.lean` | the **group step** of Lemma 3.6: `ratrank(Γ(T)/Γ(Ŝ)) = 0` + `Γ(Ŝ)` divisible ⇒ `Γ(T) = Γ(Ŝ)`, wired to the tree's `GammaHullInitialQ` / `GammaEqQ` / `Assembly.GammaDivisible` | proved |
| `EPQuotes.lean` | the two EP inequalities transcribed as `ClassicalProps`-style `Prop`s (`EP343_dimension_inequality`, `EP334_fundamental_inequality`) + consumer predicates + wiring + stress tests | quoted (per author ruling) + proved wiring |
| `Audit.lean` | compiling inventory of every Mathlib declaration the two inequalities touch, plus machine-checked availability of the residue-algebra structure `EP334` needs | inventory |
| `audit_out.txt` | the raw `#check` output of `Audit.lean` (103 lines, no errors) | evidence |

Compile command used (repo standard):

```
cd $R && LEAN_PATH=$R/.scratch2/sec3:$LEAN_PATH lean .ultramath/smw2ngn1z/m3/<FILE>.lean
```

(`EPQuotes.lean` and `Audit.lean` import only `Mathlib`; `GammaTorsion.lean` imports `GammaDiv`
and `M5Ledger` from `$R/.scratch2/sec3`.)

## 2. The group step of Lemma 3.6 — proved, and wired

Paper, `qe.tex:744-747`:

> By the dimension inequality of valuation theory (EP Thm 3.4.3), the rational rank of
> `Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` is 0.  Since `Γ(Ŝ)` is divisible, we actually have `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`.

That sentence is pure ordered-group algebra once the dimension inequality is granted:

* `RatRankZeroSet (K L : Set G) := ∀ q ∈ L, ∃ n, 0 < n ∧ q ^ n ∈ K` — rational rank 0 as
  torsion-ness, with the positive exponent required (`n = 0` would make it vacuous);
* `DivisibleSet K`, `pow_inj_of_pos` (powers injective in a linearly ordered commutative group);
* `subset_of_divisible_of_ratRankZero : DivisibleSet K → RatRankZeroSet K L → L ⊆ K`
  — the root `q^n ∈ K` must be `q` itself;
* `submodule_eq_top_of_forall_smul_mem` — the `ℚ`-vector-space form (`(n:ℚ) • v ∈ W` for some
  `n > 0` ⇒ `W = ⊤`), the shape a `Module.rank`-based statement of EP 3.4.3 would plug into.

Wiring to the tree (this is the part consumers want):

```
GammaDiv.gammaHullInitialQ_iff_image :
  GammaDiv.GammaHullInitialQ S T ↔ RatRankZeroSet (GammaDiv.GammaImage S) (GammaDiv.GammaImage T)

GammaTorsion.gammaEqQ_of_gammaDivisible_of_hullInitial :
  Assembly.GammaDivisible S → GammaDiv.GammaHullInitialQ S T → GammaDiv.GammaEqQ S T
```

The hypothesis `Assembly.GammaDivisible S` is the tree's own form of "`Γ(Ŝ)` is divisible"
(the `DivisibilityStep` predicate of `QE/M5Ledger.lean`); the conclusion `GammaEqQ S T` is
"every nonzero value class of `T` is the class of a nonzero element of `S`", i.e. the paper's
"for every `b ∈ VF(⟨Ŝ,e⟩)` there is an `a ∈ VF(Ŝ)` such that `vv(b/a) = 0`" at class level.
The converter `gammaImageDivisible_of_gammaDivisible` is the same transport as
`GammaDiv.exists_gamma_root_of_gammaDivisible_top` with `⊤` replaced by `S`.

**Stress test (machine-checked).** `exists_ratRankZero_not_subset`: `RatRankZeroSet` alone does
**not** imply `L ⊆ K` — witness `G = Multiplicative ℤ`, `K = {ofAdd (m+m)}`, `L = ⊤`.  So the
divisibility hypothesis is load-bearing; without `Γ(Ŝ)` divisible, Lemma 3.6's `Γ`-step fails
even when `Γ(T)` lies in the divisible hull of `Γ(Ŝ)`.  (Second sanity point: with `n = 0`
allowed in the definition the hypothesis would be vacuous, which is why the definition carries
`0 < n`.)

## 3. The two quotations

Both are `Prop`s, per the author ruling (Prestel–Engler quoted, never proved), in the vocabulary
the tree's Lemma 3.7/3.8 work already uses (`QE/Case38Value.lean`, `QE/Lemma37_transcendental.lean`):
`v : Valuation L Γ₀`, `K : Subfield L`, `Transcendental ↥K e`.

### 3.1 `EP343_dimension_inequality` (EP Thm 3.4.3, dimension/Abhyankar inequality)

Consumer shape of Lemma 3.6: if `L = K(e)` with `e` transcendental over `K` **and** `rv(e)`
transcendental over `k(K)`, then `ratrank(Γ(L)/Γ(K)) = 0`.

```
EP343_dimension_inequality : Prop :=
  ∀ {L} [Field L] {Γ₀} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)
    (K : Subfield L) (e : L),
    (∀ x : L, x ∈ IntermediateField.adjoin ↥K {e}) →
    Transcendental ↥K e →
    ResidueTranscendental v K e →
    ValueTorsionOver v K
```

with the following two predicates defined in the same file:

* `ValueTorsionOver v K := ∀ x : L, x ≠ 0 → ∃ n, 0 < n ∧ ∃ y : K, y ≠ 0, v (x^n) = v y`
  — "`Γ(L)/Γ(K)` torsion", the class-free form of rational rank 0;
* `ResidueTranscendental v K e := v e = 1 ∧ ∀ (n) (b : Fin (n+1) → K), (∀ i, v (b i) ≤ 1) →
  (∃ i, v (b i) = 1) → v (Σ_i b_i e^i) = 1` — "`rv(e)` transcendental over `k(K)`" in
  `O`-language: no nonzero polynomial over the residue field, lifted with unit coefficients,
  vanishes at `rv(e)`.  Correctness of that reading: all terms have value `≤ 1`, so the sum has
  value `≤ 1`; its residue vanishes iff the value is `< 1`.  `v e = 1` is part of the predicate
  because the paper's case has `e ∈ U(M)`.

`ResidueTranscendental` has content: `not_residueTranscendental_of_sub_lt_one` shows that if the
residue of `e` is the residue of a constant (`v e = 1`, `a ∈ K` a unit, `v (e - a) < 1`) then the
predicate fails.

### 3.2 `EP334_fundamental_inequality` (EP Thm 3.3.4, fundamental inequality)

Consumer shape of Lemmas 3.4/3.8: for a finite extension `L/K` of valued fields,
(1) the residue degree is at most the field degree, and (2) if the residue degree *is* the whole
field degree — the paper's situation in Lemma 3.4, `qe.tex:628`
`[K(⟨Ŝ,e⟩):K(Ŝ)] = [VF(⟨Ŝ,e⟩):VF(⟨Ŝ)]` — then the value group does not grow.

```
EP334_fundamental_inequality : Prop :=
  ∀ {K L} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {Γ₀ Γ₁} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
    (vK : Valuation K Γ₀) (vL : Valuation L Γ₁) [vK.HasExtension vL],
    Module.finrank (IsLocalRing.ResidueField vK.integer) (IsLocalRing.ResidueField vL.integer)
        ≤ Module.finrank K L
      ∧ (Module.finrank (ResidueField vK.integer) (ResidueField vL.integer) = Module.finrank K L →
          ∀ x : L, x ≠ 0 → ∃ n, 0 < n ∧ ∃ y : K, y ≠ 0, vL (x^n) = vL (algebraMap K L y))
```

Both conjuncts are corollaries of `[L:K] ≥ [k_L:k_K]·e·ratrank` with the ramification index
`e ≥ 1`.  Stated in two conjuncts rather than as `[L:K] ≥ [k_L:k_K]·e·r` because (a) no
ramification index exists in Mathlib, and (b) these are exactly the two consequences the two
consumers use.  **This is a specialization of the quoted theorem, and it is documented as such** —
the general form is not stated here, because the general form needs a rational-rank function on
value-group quotients and a ramification index, neither of which exists in Mathlib
(§4).

## 4. What Mathlib has and does not have (the audit)

Machine-checked inventory: `Audit.lean` (compiles, 0 errors; raw output `audit_out.txt`).

**Present and used:** `Valuation`, `Valuation.integer` (`= 𝒪`), `Valuation.valuationSubring`,
`Valuation.map_add` (`v (x+y) ≤ max`), `Valuation.Integers.isIntegral_iff_v_le_one`,
`Valuation.Integers.isIntegrallyClosed`, `Valuation.HasExtension` with
`val_map_le_iff` / `val_map_eq_one_iff`, `Valuation.HasExtension.instIsLocalHomValuationInteger`,
`IsLocalRing.ResidueField`, `IsLocalRing.residue`, `MonoidWithZeroHom.ValueGroup₀`,
`Valuation.restrict`, `Valuation.RankOne`, `Transcendental`, `IntermediateField.adjoin`,
`Module.finrank`, `Module.rank`, `FiniteDimensional`, `HenselianLocalRing`, `IsAlgClosed.lift`.

Crucially, `Valuation.HasExtension` makes the **residue field of the extension an algebra over
the residue field of the base** (`Audit.lean` §4 checks `Algebra (ResidueField vK.integer)
(ResidueField vL.integer)` by `inferInstance`, and
`algebraMap_residue_eq_residue_algebraMap` pins the map), so a residue degree
`Module.finrank k_K k_L` is statable — that is what `EP334` is written with.

**Absent** (searched by name and by concept over `Mathlib/`):

| concept | grep | hits |
|---|---|---|
| Abhyankar / dimension inequality | `grep -rli Abhyankar Mathlib/` | none |
| rational rank | `grep -rli "rational rank" Mathlib/` | none |
| dimension inequality | `grep -rli "dimension inequality" Mathlib/` | none |
| residue degree | `grep -rli "residue degree" Mathlib/` | none |
| `Module.rank` in valuation theory | `grep -rn "Module.rank" Mathlib/RingTheory/Valuation/` | none |
| Ostrowski's lemma on value extensions | `grep -rli Ostrowski Mathlib/` | only Ostrowski's theorem on absolute values of `ℚ` (`NumberTheory/Ostrowski.lean`) and Gelfand–Mazur |
| ramification index | `grep -rli ramification Mathlib/` | only Dedekind-domain ideal ramification (`RingTheory/DedekindDomain/...`), not valuation indices |
| fundamental inequality | `grep -rli "fundamental inequality" Mathlib/` | only analysis (Gronwall, multilinear) |

Also absent: the two EP 3.2 facts behind the paper's "clearly `e` is transcendental over
`VF(Ŝ)`" — *the residue of an algebraic element is algebraic over the residue field* and *the
value group extension of an algebraic extension is torsion*.

**Consequence for the project.** Neither inequality can be discharged inside Mathlib 4.33.1, and
neither can the two EP 3.2 facts.  They must enter `CaseSeparated` (and Lemma 3.4's slot) as named
quoted hypotheses — `EPQuotes.EP343_dimension_inequality` and
`EPQuotes.EP334_fundamental_inequality` are written for exactly that, in a vocabulary already in
use in the tree.

## 5. Wiring: quote ⇒ consumer

```
EPQuotes.valueTorsionOver_of_EP343 :
  EP343_dimension_inequality → (∀ x, x ∈ adjoin ↥K {e}) → Transcendental ↥K e →
  ResidueTranscendental v K e → ValueTorsionOver v K

EPQuotes.valueTorsionOver_of_EP334 :
  EP334_fundamental_inequality → (residue degree = field degree) →
  ∀ x ≠ 0, ∃ n > 0, ∃ y : K, y ≠ 0, vL (x^n) = vL (algebraMap K L y)
```

Composition with §2 (this is the full path to the paper's `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`):

```
EP343 → ValueTorsionOver → (classes of values) RatRankZeroSet → 
GammaDivisible (Γ(Ŝ)) → subset_of_divisible_of_ratRankZero → Γ(⟨Ŝ,e⟩) ⊆ Γ(Ŝ)
```

The only link **not** machine-checked in this directory is the last-but-one arrow at the level of
the frozen encoding: turning `ValueTorsionOver v K` (a Mathlib-valuation statement about a
`Subfield` of a `Field`) into `GammaDiv.GammaHullInitialQ S T` (a statement about
`LRV.Substructure`s of a model).  That link needs the encoding↔Mathlib valuation bridge
(`QE/ValueGroupBridge.lean`'s `vGammaValuation`, `QE/KOfBridge.lean`,
`QE/StandingField.lean`), and it is the natural next step; it is *not* claimed here.

## 6. What was not done (explicitly)

* No proof of Claim (⋆) or of `CaseSeparated` (that is `d1`).
* No satisfiability/counterexample audit of Lemma 3.6's hypotheses beyond the two stress tests in
  §2 (that is `d2`).
* No construction of residue fields as such: `ResidueTranscendental` is stated in `O`-language,
  and the equivalence with `Transcendental ↥(k(K)) (rv e)` is the standard residue-lifting
  argument, not formalized here.
* No general (non-specialized) statement of EP 3.3.4 with a ramification index and a rational
  rank; only the two consequences the paper's lemmas consume.
* The `b/b*` induction of Lemma 3.6 (the paper's three cases on `vv(b₀)` vs
  `vv(e·Σ_{j≥1} b_j e^{j-1})`) is not touched.

## 7. Verification transcript (real output)

```
$ cd $R && for f in GammaTorsion EPQuotes Audit; do
    LEAN_PATH=$R/.scratch2/sec3:$LEAN_PATH lean .ultramath/smw2ngn1z/m3/$f.lean; done
=== GammaTorsion
exit=0
errors: 0
sorry/admit/native_decide: 1        <- the single hit is the docstring line "No `sorry`, no `axiom`; ..."
axioms: 0 sorryAx lines
=== EPQuotes
exit=0
errors: 0
sorry/admit/native_decide: 1        <- same: docstring only
axioms: 0 sorryAx lines
=== Audit
exit=0
errors: 0
sorry/admit/native_decide: 0
axioms: 0 sorryAx lines
```

`#print axioms` of the proved theorems (`GammaTorsion.out`, `EPQuotes.out`), all
`{propext, Classical.choice, Quot.sound}`:

```
GammaTorsion.pow_inj_of_pos                            [propext, Classical.choice, Quot.sound]
GammaTorsion.subset_of_divisible_of_ratRankZero        [propext, Classical.choice, Quot.sound]
GammaTorsion.exists_ratRankZero_not_subset            [propext, Quot.sound]
GammaTorsion.submodule_eq_top_of_forall_smul_mem       [propext, Classical.choice, Quot.sound]
GammaTorsion.gammaImage_subset_of_divisible_of_hullInitial
                                                       [propext, Classical.choice, Quot.sound]
GammaTorsion.gammaEqQ_of_divisible_of_hullInitial     [propext, Classical.choice, Quot.sound]
GammaTorsion.gammaImageDivisible_of_gammaDivisible    [propext, Classical.choice, Quot.sound]
GammaTorsion.gammaEqQ_of_gammaDivisible_of_hullInitial [propext, Classical.choice, Quot.sound]
EPQuotes.valueTorsionOver_top                          [propext, Classical.choice, Quot.sound]
EPQuotes.ValueTorsionOver.mono                         [propext, Classical.choice, Quot.sound]
EPQuotes.not_residueTranscendental_of_sub_lt_one       [propext, Classical.choice, Quot.sound]
EPQuotes.valueTorsionOver_of_EP343                     [propext, Classical.choice, Quot.sound]
EPQuotes.valueTorsionOver_of_EP334                     [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `admit`, no `native_decide`, no new `axiom` in any of the three files; the two
quoted `Prop`s are `def`s (hypotheses of consumers), not axioms.

## 8. Addendum: the `VF`-sorted normalisation and the remaining stress tests

Three additions after the first verification pass (all in the same two files, same status:
`exit 0`, `0 errors`, axioms `⊆ {propext, Classical.choice, Quot.sound}`):

* **`GammaTorsion.exists_vf_class_witness`** — the paper's `VF`-sorted form of the value
  normalisation, which is what the polynomial induction on `Σ bᵢ eⁱ` consumes:

  ```
  Assembly.IsVFGen S → Assembly.GammaDivisible S → GammaDiv.HullInitialQ S T →
    ∀ t ∈ T (iRV t) (t ≠ 0), ∃ a, a ∈ S ∧ iVF a ∧ iRv a ∈ S ∧ iRv a ≠ 0 ∧
      ∀ (h : iRV (iRv a)) (h' : iRv a ≠ 0), gammaMk (mkR t ..) = gammaMk (mkR (iRv a) h h')
  ```

  i.e. *for every value class of `T` there is a `VF`-sorted element of `S` with that class* —
  the paper's "for every `b ∈ VF(⟨Ŝ,e⟩)` there is an `a ∈ VF(Ŝ)` such that `vv(b/a) = 0`", with
  the witness in the `VF` sort as the induction needs.  (`IsVFGen` is the tree's
  `rv(VF(S)) = RV(S)`; the two proof arguments of the class constructor are universally
  quantified so the statement is proof-irrelevant and needs no `rv`-membership lemma at the call
  site.)
* **`GammaTorsion.not_ratRankZeroSet_bot`** — `RatRankZeroSet` has content: in
  `G = Multiplicative ℤ` with `K = {1}` and `L = ⊤` it fails (the class of `1` has no positive
  power in `{1}`).
* **`GammaTorsion.ratRankZeroSet_self`** — it is satisfiable: `RatRankZeroSet K K`.
* **`EPQuotes.valueTorsionOver_of_value_surjective`** — a shortcut for consumers who can compute
  values exactly (`Γ(L) = Γ(K)`, no torsion): then `ValueTorsionOver` holds with exponent `1`, so
  neither quote of §3 is needed.  This covers the strict-triangle / dominant-term route of
  Lemmas 3.5 and 3.7.

Axiom prints added by these:

```
GammaTorsion.not_ratRankZeroSet_bot                  [propext, Classical.choice, Quot.sound]
GammaTorsion.ratRankZeroSet_self                      [propext]
GammaTorsion.exists_vf_class_witness                 [propext, Classical.choice, Quot.sound]
EPQuotes.valueTorsionOver_of_value_surjective        [propext, Classical.choice, Quot.sound]
```
