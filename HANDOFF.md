# Handoff: formalizing arXiv:1006.2467

## The paper

**Yimu Yin**, *Special transformations in algebraically closed valued fields*,
Annals of Pure and Applied Logic (2010). arXiv:1006.2467, math.LO, 29 pages.

It presents the first two of the three steps of the Hrushovski–Kazhdan
construction of motivic integration for theories `ACVF_S(0,0)`: algebraically
closed valued fields of pure characteristic 0, expanded by a `(VF, Γ)`-generated
substructure `S` in the two-sorted language `L_RV`.

The main mathematical objects:

- `RV = Kˣ/(1+M)` and the projection `rv : K → RV`;
- definable subsets of `VF^n × RV^m`;
- the categories `VF[k,·]` and `RV[k,·]`, their Grothendieck semigroups;
- the lifting map `L` from `RV`-objects to `VF`-objects;
- **special bijections** and **RV-pullbacks**;
- VF-, RV-, and Γ-Jacobians and volume-form categories.

The two steps formalized in this paper:

1. Every definable subset admits a special bijection to an RV-pullback
   (Theorem 5.5 / Corollary 5.6), hence `L` is surjective on isomorphism
   classes (Corollary 5.7).
2. Isomorphic `RV`-objects have isomorphic lifts (Theorem 7.6 / Corollary 7.7).

Section 10 refines the categories by volume forms and proves Theorem 10.4,
Theorem 10.5, and Corollary 10.6.

## Repository roles

- `special-transformations` (this repo): all paper-specific definitions and
  theorems.
- `hilbert-mathlib` (separate repo): reusable, paper-independent background.
  Nothing in this repo should be imported by the foundation repo.

At the moment the foundation is essentially empty, so this repo only depends on
Mathlib. Once the foundation has its first valued-field definitions, add:

```lean
require hilbert-mathlib from "../path/to/hilbert-mathlib"
```

and, for the public GitHub build, switch to a git requirement.

## What exists

- `SpecialTransformations/Basic.lean`: `RVUnit`, `RV`, `RV0`, `rv`.
- `SpecialTransformations/Language.lean` … `VolumeForms.lean`: module skeleton
  with the paper reference and TODO list for each section.
- `SpecialTransformations/Main.lean`: item-by-item target table (all “not started”).
- `blueprint/src/blueprint.tex`: minimal blueprint.

Everything compiles; no theorem is proved yet. `Basic.lean` is the only file
with real Lean content.

## Recommended next steps

### Milestone 0 — language and syntax

- Decide between Mathlib's one-sorted model theory and the many-sorted
  framework at <https://github.com/Mathias-Stout/Many-sorted-model-theory>
  (Apache-2.0).
- Define the sorts `VF`, `RV`, the symbols of `L_RV`, the theory `ACVF`, and
  `ACVF_S(0,0)`.
- State quantifier elimination (Theorem 2.3) and C-minimality (Theorem 2.8) as
  targets. Do not prove them yet.

### Milestone 1 — algebraic layer

- `vrv : RV → Γ ∪ {∞}` and the exact sequence
  `1 → Kˣ/(1+M) → RV → Γ → 0`.
- Balls, polydiscs, `rv`-balls, valuative center.
- `ValuationSubring.principalUnitGroup` is already in Mathlib; use it rather
  than redefining `1+M`.

### Milestone 2 — definable sets and dimensions

- Definability in a saturated model, `acl`, `dcl`.
- `dimVF`, `dimRV`, `dimfib`; Lemma 4.2/4.4/4.6.
- Categories `VF[k,·]`, `RV[k,·]`, the lift `L`, Grothendieck semigroups.

### Milestone 3 — special bijections

- Definition 5.1, Theorem 5.4/5.5, Corollary 5.6/5.7.
- This is the technical core; likely the first place to use a proof-search run.

### Milestone 4 — lifting functions

- Generalized Hensel (Lemma 7.2), Theorem 7.6, Corollary 7.7.

### Milestone 5 — differentiation and volume forms

- Definitions 9.1–9.14, Theorem 9.16, Theorems 10.4/10.5, Corollary 10.6.

## Reuse notes

- Mathlib already has `Valuation`, `ValuationSubring`, `principalUnitGroup`,
  `IsLocalRing.ResidueField`, and one-sorted model theory.
- For many-sorted model theory, `Mathias-Stout/Many-sorted-model-theory` is the
  closest existing Lean 4 project (Apache-2.0). Check whether it builds against
  Lean 4.33.1 before depending on it; otherwise copy the needed definitions with
  attribution.
- The paper's companion `arXiv:1006.1393` (quantifier elimination and minimality
  conditions) is the source for the model-theoretic facts quoted in Section 2.

## Practical commands

```bash
lake build
make check FILE=SpecialTransformations/Basic.lean
make sorry
```
