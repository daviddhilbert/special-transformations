# Model of `ACVF_S(0,0)` with `Γ(S)` nontrivial — target, instance, and landing guards

The target of the current milestone, and the checks that make it reachable. Written while the
model-building swarm runs; everything in the "verified" sections was run in this repository.

## The target

```
∃ (M : Type) (_ : LRV.Structure M) (S : LRV.Substructure M),
    M ⊨ SubstructureTheory.ACVF_S S ∧ Γ(S) nontrivial
```

`SubstructureTheory.ACVF_S S` is already defined in `Encoding.lean` as the constant expansion
of `ACVF(0,0)` by the atomic diagram of `S`, and `accepted/ACVFS_conservative.lean` proves
`M ⊨ ACVF00 → M ⊨ ACVF_S S` for **every** substructure `S`. So the open work is a model of
`ACVF(0,0)` with a nontrivial value group, plus the witness in `S`.

### `Γ(S)` nontrivial: the reading that is *not* vacuous

`Γ(S)` is not a sort, so it has to be expressed in the `RV` part of `S`. The obvious formula

```
∃ t, (S : Set M) t ∧ iRV t ∧ ¬ (iLe iRVOne t ∧ iLe t iRVOne)          -- VACUOUS
```

is **wrong**: in the trivial-valuation model the constant `∞ = rv 0` lies in every
substructure and is outside the class of `1`, so this holds for `S = ⊥` at `ℂ` and would
"satisfy" the milestone without any nontrivial value group. The correct statement excludes
the two points `0` and `∞` of the `RV` sort:

```
∃ t, (S : Set M) t ∧ iRV t ∧ t ≠ iRVZero ∧ t ≠ iRVInfty ∧ ¬ (iLe iRVOne t ∧ iLe t iRVOne)
```

i.e. `S` contains an element of `RV^×` outside the class of `1`. Equivalent, and the form a
witness at `ℂ_[p]` takes: `∃ x : VF, x ≠ 0 ∧ v x ≠ 1` with `rv x ∈ S`.

At the trivial valuation no `S` has nontrivial `Γ(S)`; this is what forces the model onto a
nontrivial valuation. (Recorded from a member's refutation of my first formulation, which is
also why `ACVF_S` alone does not make this milestone interesting.)

## The concrete instance: `ℂ_[p]` — and why it cannot carry `ACVF(0,0)`

Mathlib has the p-adic complex numbers, and they supply most of what the encoding needs.
`NumberTheory/Padics/Complex.lean`, with `p : ℕ` and `[Fact (Nat.Prime p)]`:

| Fact | Declaration | Verified here |
| --- | --- | --- |
| algebraically closed | `PadicComplex.isAlgClosed : IsAlgClosed ℂ_[p]` | instance synthesizes |
| characteristic zero | `PadicComplex.charZero : CharZero ℂ_[p]` | instance synthesizes |
| valued | `PadicComplex.valued : Valued ℂ_[p] ℝ≥0` | `(PadicComplex.valued p).v : Valuation ℂ_[p] ℝ≥0` typechecks against `[LinearOrderedCommGroupWithZero Γ₀]` |
| value group class | `LinearOrderedCommGroupWithZero ℝ≥0` | instance synthesizes (`Data/NNReal/Defs.lean`) |

**Nontriviality, which is what `Γ(S)` needs.** The valuation of `p` is `1/p`, and
`((p : ℝ≥0))⁻¹ < 1`, so `v p ≠ 1`:

```lean
example (p : ℕ) [hp : Fact (Nat.Prime p)] :
    (PadicComplex.valued p).v ((p : PadicAlgCl p) : PadicComplex p) ≠ 1
```

compiles (`PadicComplex.valuation_extends`, `PadicAlgCl.valuation_p`). So `Γ` is nontrivial at
`ℂ_[p]`.

**But `ℂ_[p]` is NOT a model of `ACVF(0,0)`.** The same computation, read the other way, is
fatal: `v p = 1/p < 1` puts `p` in the maximal ideal, so the residue field is `𝔽_p` —
characteristic `p`, not zero. In the encoding's vocabulary, with `t ≤ s ↔ vrv s ≤ vrv t`,

* `1 ≤ rv x` iff `v x ≤ 1`, and `rv x ≤ 1` iff `1 ≤ v x`;
* `pGtOne t := (1 ≤ t) ∧ ¬ (t ≤ 1)` iff `v t < 1`, i.e. `t` is in `𝔪` — matching the paper's
  `𝔪 = rv⁻¹(RV^{>1})`;
* `residueCharZero r := ¬ pGtOne (rv r)` therefore says `v r ≥ 1`, i.e. `r` is a unit of `𝒪`.

At `ℂ_[p]`, `v p = 1/p < 1`, so `pGtOne (rv p)` holds and `residueCharZero p` **fails**.

Consequences, recorded so they are not rediscovered:

* `ℂ_[p]` **does** model `ACVF` (the characteristic-free theory over which Theorems 2.3 and
  2.8 are stated) with a nontrivial `Γ`, so `ACVF ∪ atomicDiagram S` with `Γ(S)` nontrivial is
  reachable there.
* `ℂ_[p]` **does not** model `ACVF(0,0)`, hence not `SubstructureTheory.ACVF_S S` for any `S`,
  since that theory contains `ACVF00`.
* A concrete model of `ACVF_S(0,0)` with `Γ(S)` nontrivial needs an algebraically closed field
  of characteristic zero with a nontrivial valuation *and residue characteristic zero* — e.g.
  the Puiseux series over `ℂ`, or the algebraic closure of `ℂ(t)` at the `t`-adic valuation.
  Mathlib has neither: `Valuation.HasExtension` is a class with no existence theorem
  (`rg HasExtension /opt/mathlib/Mathlib` returns only `RingTheory/Valuation/Extension.lean`),
  and no `IsAlgClosed` type carries a nontrivial valuation with residue characteristic zero.

## Landing guards: what the accepted fragments are worth

`accepted/` files span five snapshots of the encoding. Checked here by `difflib` against the
frozen `Encoding.lean` (sha256 `78607b94c28343fc3aa5c260cb1f296063f579d5f38b5f14b260618827980be6`,
commit `d608de6`):

| File | Snapshot | Port cost |
| --- | --- | --- |
| `VFAlgClosed.lean` | current (`d608de6`) | none — the encoding block is byte-identical for the first 500 lines |
| `ACVFModel.lean` | current | `def LRV` → `abbrev LRV` only |
| `IntendedModel.lean` | `acf79f6` | 9 hunks, all in the `K`-guard (`kHyps`, `exSortedK`) and docstrings |
| `RepairedTheory.lean` | `acf79f6` | same 9 hunks |

Crucially, `IntendedModel.lean`'s `model_vfField` and `model_rvAxioms_all` mention neither
`kHyps` nor `allSortedK`, so they do **not** depend on the guard that changed after `acf79f6`
and port to the frozen axioms unchanged. `model_kField`/`model_kAlgClosed` in that file do
depend on it and must be redone.

## What is now verified (unconditional)

`accepted/ACVF_gamma_padic.lean`, at the frozen axioms `d608de6`:

* `model_ACVF_minus_kField [IsAlgClosed K] (v)` — six of the eight summands of `ACVF` at
  `C v = K ⊕ RV₀ v` for **arbitrary** `v`: `sortAxioms`, `vfField`, `vfAlgClosed`, `rvGroup`,
  `preorderRV`, `rvAxioms`;
* `ACVF_eq_FRAG_union : Axioms.ACVF = FRAG ∪ Axioms.kField ∪ Axioms.kAlgClosed` — the gap as a
  set equality;
* `exists_gamma_nontrivial (v) (x) (hx0 : x ≠ 0) (hx : v x < 1)` — `t = mkRV (some (rv x))`
  lies in `RV^×` and outside the class of `1`, in the **corrected** predicate;
* `exists_model_with_nontrivial_gamma (p)` — at `ℂ_[p]`, a structure with
  `M ⊨ FRAG ∪ atomicDiagram S` and `Γ(S)` nontrivial;
* `not_model_ACVF_S_padic` — `ℂ_[p]` has residue characteristic `p`, so `ACVF(0,0)`, hence
  `ACVF_S S`, fails there for **every** `S`.

So: `ACVF` minus the two residue-field summands is realised with a nontrivial value group, and
the `(0,0)` refinement is proved out of reach at the only concrete field Mathlib offers.

## The residue-field transport is in place

`accepted/ACVF_residue_ops.lean` reinterprets `kAdd`/`kNeg` on `C v` by the actual residue
field operations, transported along `ACVFResidue.kEquiv` (`kOf`, `ofK`, `kOf_ofK`, `ofK_inj`,
`iKAdd_ofK`, `iKNeg_ofK`, `iRVMul_ofK`), and proves `model_ACVF_of_components`: `(C v) ⊨ ACVF`
follows from exactly three obligations —

```
⊨ kField        ⊨ kAlgClosed        ∀ k ≥ 1, ⊨ rvDivisible k
```

It also proves the general criterion `model_residueCharZero_iff k : ⊨ residueCharZero k ↔ 1 ≤ v k`,
which together with `PadicComplex.valuation_p` gives `padicComplex_not_model_ACVF00` — the
clean form of the `ℂ_[p]` obstruction: residue characteristic zero is exactly "the valuation
of every positive integer is at least `1`", which the p-adic valuation fails at `p`.

## What is still missing

Of the eight blocks of `Axioms.ACVF` at the general carrier `K ⊕ RV₀ v`, four are done against
the current guard (`.ultramath/smw06c8tw/m7/ACVF_fragment.lean`): `sortAxioms` 16/16,
`preorderRV` 7/7, `vfField` 10/10, and `vfAlgClosed` (transported from
`accepted/VFAlgClosed.lean`). `model_ACVF_of_residue_blocks` reduces `(C v) ⊨ ACVF` to the
remaining four:

* `rvGroup` — proved at the general carrier in the previous swarm's `rv_divisible.lean`; its
  `rvMulZeroK` sentence now uses `pInK`, so that one sentence needs the re-base.
* `rvAxioms` — open; `rvZeroEq`, `rvEqInfty`, `rvMulHom`, `rvSurj`, `rvUltrametric`.
* `kField`, `kAlgClosed` — open. Residue field transported along `K^× ≃* k^×`
  (`accepted/ResidueField.lean`).
* The substructure `S` and its `Γ(S)` nontriviality — at `ℂ_[p]` for `ACVF`, not for
  `ACVF(0,0)` (see above).
