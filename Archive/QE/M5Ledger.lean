/-
# The Prestel–Engler / Marker ledger for Lemma 3.3 (`PrepStepSize`): five inputs, one assembly

Direction d5, swarm `smw2ioy2w` (merged, unchanged).  *This file proves no new mathematics*: it is the assembly
ledger by which the frozen `M7Paper.PrepStepSize` (`QE/PaperRoute.lean`) follows from the five
inputs into which `MILESTONES.md` §"Second axiom-of-quotation" decomposes Lemma 3.3 of
`refs/qe.tex` (l. 580):

> There is a monomorphism `f* : S* → N` extending `f` such that
> (1) `VF(S*) = VF(S)`, (2) `K(S*) = K(M)`, (3) `Γ(S*)` is the divisible hull of `Γ(S)`.

and `MILESTONES.md` l. 428–438 ("we fix two models `M`, `N ⊨ ACVF` with `N` `‖M‖⁺`-saturated"):

> After both rulings, **Lemma 3.3 (`PrepStepP` at SizeHyp pairs) decomposes as**:
> 1. `g : K(M) → K(N)` extending `f ↾ K(S)` — Marker (ACF extension of embeddings), quoted.
> 2. henselization of `VF(Ŝ)` + `K` and `Γ` preserved — Prestel-Engler, quoted.
> 3. adjoining representatives of all residue classes gives `K(S*) = K(M)` — construction.
> 4. `Γ(S*)` divisible via the (Prestel-Engler) divisible hull — construction-meets-quote.
> 5. extending the monomorphism — Marker (saturation realization), quoted.
> So what remains is the **assembly** of those five into the frozen `PrepStepP`/`PrepStepSize`
> statement, which is Lean work, not mathematics.

## What is delivered

Pair level (no size hypothesis, no saturation hypothesis — the honest core):

    prepStepP_of_ledger :
      ACFExtends → HenselizationExists M → ResidueStep → DivisibilityStep →
      SaturationRealization → Assembly.PrepStepP (M := M) (N := N)

Frozen shape (`QE/PaperRoute.lean`'s `M7Paper.PrepStepSize`, verbatim):

    prepStepSize_of_ledger : LedgerInput1 → … → LedgerInput5 → M7Paper.PrepStepSize

End-to-end wiring into the frozen route (`QE/M7Hensel.lean`):

    paper_theorem_2_3_sat_of_ledger :
      ShoenfieldTestSat → LedgerInput1 → … → LedgerInput5 → ImmediateLift →
      (Lemmas 3.4–3.8 at henselian domains) → HasQE Axioms.ACVF

**The recommended shape**, at the paper's own hypothesis instead of the frozen `SizeHyp` (§10b):

    paper_theorem_2_3_sat_of_ledger_paperHyp :
      ShoenfieldTestSat → (five inputs at PaperHyp) → OneStepSizeFree → HasQE Axioms.ACVF

which is `M7Paper.paper_theorem_2_3_sat` with the undischarged `PrepStepSize` replaced by the five
inputs, and needs neither `ImmediateLift` nor the one-step-at-henselian-domains hypothesis.

The chain that is proved (each input consumed, in this order):

| step | input | gives |
|---|---|---|
| 1 | `HenselizationExists M` (P–E, `QE/M7Hensel.lean`, reused verbatim) | `T₁ ⊇ S`, `Immediate S T₁`, `IsHenselianVF T₁`, `K`/`Γ` preserved |
| 2 | `SaturationRealization` (Marker, saturation) | `g₁ : T₁ ↪ N` extending `f` |
| 3 | `ACFExtends` (Marker, ACF+saturation) | `γ : K(M) →+* K(N)` extending `f` on `K(S)`; via `Immediate S T₁` also extending `g₁` on `K(T₁)` (`M7Hens.units_rv_mem`, `M7Hens.rv_eq_of_henselization`) |
| 4 | `ResidueStep` (paper, construction 3) at the henselian `T₁` | `T₂ ⊇ T₁`, `g₂` extending `g₁`, `KEqTop T₂`, `Γ(T₂) = Γ(T₁)`, `VF(T₂) = VF(T₁)`, `γ` realised by `g₂` on `Kˣ(T₂)` |
| 5 | `DivisibilityStep` (paper, construction 4) at `T₂`, which is still henselian by `M7Hens.henselian_congr` applied to `VF(T₂) = VF(T₁)` | `T₃ ⊇ T₂`, `g₃` extending `g₂`, `GammaDivisible T₃`, `Γ(T₃)` inside the hull of `Γ(T₂)` |
| — | `KEqTop_mono`, `Extends.comp` | `Standing T₃` and `g₃` extends `f` on `S` |

A remark on why the henselianity conjunct `VF(T₂) = VF(T₁)` is not decoration: `IsHenselianVF`
is **not** upward closed (henselianity is destroyed by enlarging the valued field non-immediately),
and `GammaDivisible` is not upward closed either (it quantifies over the *elements of the
substructure*).  So the two construction steps must each record what they preserve, and `VF`-equality
is exactly what carries henselianity from `T₁` to `T₂` (`M7Hens.henselian_congr`) — the paper's
Lemma 3.3(1), used for the reason the paper uses it.  `KEqTop` *is* upward closed
(`KEqTop_mono`), which is why only it is carried from `T₂` to `T₃`.

## Which conjuncts the assembly consumes

The assembly consumes: `Immediate` (`S ≤ T₁`, `K(T₁) = K(S)`), `IsHenselianVF T₁`, `KEqTop T₂`,
`GammaDivisible T₃` and the three embeddings.  It does *not* consume `ResidueStep`'s
`GammaEq S T`, `DivisibilityStep`'s `GammaHullInitial S T`, nor `ResidueStep`'s realisation of `γ`:
those are carried because they are the paper's own conclusions for those steps (Lemma 3.3(1)–(3))
and because they are what makes the inputs *non-vacuous* — without them `T = ⊤` would satisfy both
inputs (`bare_KEqTop_trivial`, `bare_gammaDivisible_trivial`).  A discharge that finds `Γ`-side
statements inconvenient may weaken `ResidueStep` to its `VF`-equality plus `KEqTop` content and
`DivisibilityStep` to `GammaDivisible`, *provided* it supplies a non-triviality argument for `T` by
another route; the ledger's proof is unaffected.  Input 5 (`SaturationRealization`) may likewise be
replaced by `M7Hens.ImmediateLift` (`QE/M7Hensel.lean`): the only place the ledger needs a
monomorphism it cannot get from inputs 3/4 is the henselization step, so the two routes are
interchangeable and both are proved (`HenselLift`, `prepStepP_of_ledger` / `prepStepP_of_ledger_hens`).
The Marker form is kept as the primary because `MILESTONES.md` lists it as one of the five.

## Stress tests required by the report standard

*(a) No input is its own conclusion; no input is vacuous.*

* The **bare** forms one would write first really are vacuous, machine-checked:
  `bare_KEqTop_trivial`, `bare_gammaDivisible_trivial` (`T := ⊤`, using
  `StandingTree.standing_top`), and `standing_top_trivial`: the frozen `Standing` half that
  Lemma 3.3 has to *produce* is already true of `⊤`.  So a residue step stated as
  `∀ S, ∃ T ⊇ S, KEqTop T` carries no content at all.  What rules `⊤` out of `ResidueStep` is the
  `GammaEq T₁ T₂` conjunct (`Γ` must not grow when residue representatives are adjoined — the
  `Kˣ`-part of `RV` is value-trivial) together with the `VF`-equality conjunct and the realisation of
  `γ`; in `DivisibilityStep`, the `GammaHullInitial` conjunct.  `GammaEq S ⊤` and
  `GammaHullInitial S ⊤` fail as soon as `Γ(S) ⊊ Γ(M)` (the paper's situation: `Γ(S)` is proper
  before the hull is taken, otherwise step 4 has nothing to do).
* `SaturationRealization` is not the conclusion: it mentions no closure predicate, and it is
  *inhabited* at `T = S` (`saturationRealization_refl`, the identity extension).
* `HenselizationExists` is inhabited at every already-henselian `S`
  (`M7Hens.henselian_self_immediate`, reused as `henselizationExists_of_henselian`), and `Immediate`
  forbids `T = ⊤`, so it is not "take `T = ⊤`" either.
* `ACFExtends` alone yields no substructure, no `Standing`, no embedding: it is a statement about
  `K(M) → K(N)` only.  Input 1 is *used*: `ResidueStep` carries `γ` in its conclusion, so deleting
  input 1 breaks the proof.

*(b) No impossible cardinality is forced.*  Machine-checked cardinality audit:

* the conclusion forces `#Kˣ(M) ≤ #N` (`M7Paper.prepStepP_forces_units_size`, reused as
  `ledger_forces_units_size`);
* `ACFExtends` forces `#K(M) ≤ #K(N)` (`acfExtends_field_size`: an injective ring hom out of a
  field);
* `SaturationRealization` forces `#M ≤ #N` (`saturationRealization_forces_size`: `T := ⊤`);
* `HenselizationExists` forces nothing (`Immediate` restricts `T` from above, not in size).
  Together: nothing beyond `SizeHypK := #M ≤ #N ∧ #K(M) ≤ #K(N)`, and `units_size_of_sizeHypK`
  proves `SizeHypK` implies the one inequality the *conclusion* forces, so the ledger is not
  cardinality-refutable at `SizeHypK` pairs.

  **FINDING (for the discharge step, and for the swarm).**  `SizeHyp := #M ≤ #N` alone does not
  imply `#K(M) ≤ #K(N)`: the paper gets that inequality from `‖M‖⁺`-saturation (`K(N)` is a
  saturated field, hence universal and homogeneous, so the partial embedding `K(S) → K(N)` extends
  to `K(M)`).  So `M7Paper.PrepStepSize`, whose guard is `SizeHyp` only, cannot be discharged at
  arbitrary model pairs from inputs 1 and 5 as stated: the residue-field inequality is real content
  that `SizeHyp` does not carry.  The corrected frozen shape is `PrepStepSizeK` (`SizeHypK` guard;
  `prepStepSizeK_of_ledger` below, same five inputs), or `PrepStepSize` with the saturation conjunct
  restored, i.e. `PaperHyp`.  This is the same *kind* of defect as the one `QE/PaperRoute.lean`
  machine-checked for the unrepaired `PrepStepP` (`prepStepP_forces_units_size`), one level down:
  there the forced inequality was about the source's value group, here it is about the source's
  residue field, and here it is *not* implied by the frozen guard.  The repair delivered here is
  §10b: state the ledger at `PaperHyp` (the paper's pair), where inputs 1 and 5 are true, and
  recover Proposition 3.9 / Theorem 2.3 from there (`paper_theorem_2_3_sat_of_ledger_paperHyp`);
  `PrepStepSizeK` is the minimal repair of the frozen shape.

*(c) Shape of the frozen obligation.*  `prepStepSize_of_ledger` is stated at `SizeHyp` pairs exactly
as `M7Paper.PrepStepSize` is, so it is not stronger in shape; it is weaker in that its premises are
the paper's five steps.

## What is *not* done here

Inputs 1, 3, 4, 5 are transcriptions (Marker / the paper's construction), not proofs; input 2 is the
existing `M7Hens.HenselizationExists`.  `ImmediateLift` and Lemmas 3.4–3.8 at henselian domains
enter only in the end-to-end wiring, which is `QE/M7Hensel.lean`'s
`paper_theorem_2_3_sat_of_hens` applied to the ledger; they are not reproved.  Nothing is proved
about Hahn fields or about saturation itself.  `QE/ClassicalProps.lean` was not extended because
this member may not write outside its own directory: the two new quotations (saturated-field
universality/homogeneity for inputs 1 and 5) are named in the docstrings of `ACFExtends` and
`SaturationRealization`, in `ClassicalProps`' style, for transcription by whoever owns that file.
-/
import M7Hensel
import PaperRoute
import StandingField

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations
namespace Milestone0
namespace M5Ledger

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-! ### 1. What is monotone and what is not (no hypotheses) -/

/-- `KEqTop` is upward closed: the units it quantifies over are absolute (elements of `M`), so
enlarging the substructure keeps them.  This is the *only* one of the three `Standing`-related
predicates that is. -/
theorem KEqTop_mono {S T : LRV.Substructure M} (hS : Assembly.KEqTop S) (h : S ≤ T) :
    Assembly.KEqTop T :=
  fun x hx => h (hS x hx)

/-- `g : T ↪[LRV] N` extends `f : S ↪[LRV] N` along `S ≤ T`. -/
def Extends {S T : LRV.Substructure M} (hST : S ≤ T) (g : T ↪[LRV] N)
    (f : S ↪[LRV] N) : Prop :=
  ∀ x : S, g ⟨(x : M), hST x.2⟩ = f x

/-- `Extends` is transitive along a two-step tower. -/
theorem Extends.comp {S T U : LRV.Substructure M} {hST : S ≤ T} {hTU : T ≤ U}
    {g : U ↪[LRV] N} {g' : T ↪[LRV] N} {f : S ↪[LRV] N}
    (hgg : Extends hTU g g') (hgf : Extends hST g' f) :
    Extends (hST.trans hTU) g f := by
  intro x
  have h1 : (⟨(x : M), (hST.trans hTU) x.2⟩ : U) = ⟨(x : M), hTU (hST x.2)⟩ := rfl
  rw [h1, hgg ⟨(x : M), hST x.2⟩, hgf x]

/-- `Extends` is reflexive. -/
theorem extends_refl {S : LRV.Substructure M} (f : S ↪[LRV] N) :
    Extends (le_rfl : S ≤ S) f f :=
  fun _ => rfl

/-- **Henselianity transfers across a `VF`-preserving enlargement** — the paper's mechanism for
"we may assume `(VF(Š), O(Š))` henselian" (Lemma 3.3(1) `VF(S*) = VF(S)` plus
Engler–Prestel Thm 4.1.3).  Note that henselianity is *not* upward closed: this needs the equality
of the `VF`-parts, and `M7Hens.henselian_congr` is the tree's version of that fact. -/
theorem IsHenselianVF.of_vf_eq {S T : LRV.Substructure M}
    (hvf : ∀ x : M, iVF x → (x ∈ T ↔ x ∈ S)) (hS : M7Hens.IsHenselianVF S) :
    M7Hens.IsHenselianVF T :=
  (M7Hens.henselian_congr (S := T) (T := S) hvf).mpr hS

/-! ### 2. The two value-group predicates of Lemma 3.3(3)

`Γ = RV / Kˣ` in the encoding, so "`Γ(T) = Γ(S)`" and "`Γ(T)` is contained in the divisible hull of
`Γ(S)`" are spelled with a unit `c` absorbing the residue: `iRVMul s c = t` says `[t] = [s]` in `Γ`,
and `rvPow t n = iRVMul s c` says `[t]ⁿ = [s]`. -/

/-- **`Γ(T) = Γ(S)`**: every nonzero `RV`-element of `T` has the value class of an element of `S`.
(The other inclusion is `S ≤ T`.)  This is the form of `M6L33.Immediate` that survives adjoining
*units*, which is exactly what the residue step does and why the residue step must not be stated as
`Immediate`. -/
def GammaEq (S T : LRV.Substructure M) : Prop :=
  ∀ t : M, t ∈ T → iRV t → t ≠ iRVZero →
    ∃ s c : M, s ∈ S ∧ iRV s ∧ s ≠ iRVZero ∧ iUnits c ∧ iRVMul s c = t

/-- **`Γ(T)` lies in the divisible hull of `Γ(S)`**: every value class of `T` has a positive power
in `Γ(S)`.  This is the initiality half of the Prestel–Engler `DivisibleHullExists` quotation
(`ClassicalProps.DivisibleHullExists`, its `∀ h, ∃ n > 0, n • h = j g` clause), transported to the
encoding.  Without it, `DivisibilityStep` would be satisfied by `T = ⊤`
(`bare_gammaDivisible_trivial`). -/
def GammaHullInitial (S T : LRV.Substructure M) : Prop :=
  ∀ t : M, t ∈ T → iRV t → t ≠ iRVZero →
    ∃ (n : ℕ) (s c : M), 0 < n ∧ s ∈ S ∧ iRV s ∧ s ≠ iRVZero ∧ iUnits c ∧
      Assembly.rvPow t n = iRVMul s c

section Inputs

variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-! ### 3. Input 1 — Marker: ACF extends embeddings (the map `K(M) → K(N)`) -/

/-- **Input 1** (Marker, *Model Theory*: ACF model completeness, plus saturated-field universality;
the paper's "First of all, there is a field homomorphism `g : K(M) → K(N)` extending
`f ↾ K(S)`").

`KOf M = {x : M // iUnits x ∨ x = iRVZero}` is the residue field as a Mathlib `Field`
(`QE/StandingField.lean`).  The statement: for every substructure `S` and monomorphism `f`, there is
a *field* homomorphism `K(M) → K(N)` agreeing with `f` on the units of `S`.

**Quotation status.**  `ClassicalProps.ACFExtendsAlgebraicEmbeddings` covers the *algebraic* part
only (`Algebra.IsAlgebraic K E`).  The transcendental part needs a size hypothesis — a transcendence
basis of `K(M)` over `K(S)` mapped into `K(N)` — which the paper supplies from `‖M‖⁺`-saturation of
`N`: `K(N)` is a saturated field, hence universal among fields of smaller cardinality and
homogeneous, so the given partial embedding extends.  This input is therefore a *saturation*
statement, not a pure ACF statement, and must be discharged at `PaperHyp` pairs; see the header,
stress test (b).

The agreement is stated in the carrier (`((γ …) : N) = f x`) rather than as an equality of `KOf N`
elements, so no `iUnits (f x)` transport lemma is needed. -/
def ACFExtends : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
    ∃ γ : StandingField.KOf M →+* StandingField.KOf N,
      ∀ (x : S) (hx : iUnits (x : M)),
        (γ ⟨(x : M), Or.inl hx⟩ : StandingField.KOf N).1 = f x

/-! ### 4. Input 2 — Prestel–Engler: the henselization (reused from the tree) -/

/-- **Input 2** is `M7Hens.HenselizationExists M` (`QE/M7Hensel.lean`), used verbatim: every
substructure has an immediate henselian extension, `M6L33.Immediate` being `RV`-invariance, i.e. `K`
and `Γ` preserved.  No new transcription: the ledger only records that this is one of the five
inputs and that it must be available at every `M ⊨ ACVF`. -/
abbrev HenselizationExists (M : Type) [LRV.Structure M] : Prop :=
  M7Hens.HenselizationExists M

/-! ### 5. Input 3 — the paper's construction: adjoining residue representatives -/

/-- **Input 3** (paper, Lemma 3.3 "adjoining representatives of all residue classes gives
`K(S*) = K(M)`", *construction*, not quoted).

Given a monomorphism `f : S ↪ N`, a field map `γ : K(M) → K(N)` extending it on the units of `S`
(input 1) and `(VF(S), O(S))` henselian (input 2), there are `T ⊇ S` and an extension
`g : T ↪ N` of `f` such that

* `KEqTop T` — every unit of `M` lies in `T`: the paper's `K(S*) = K(M)` (Lemma 3.3(2));
* `γ` is realised by `g` on the units of `T` — the paper's `f₁` is determined by `t·s ↦ g(t)f(s)`,
  so the residue-field part of the extended monomorphism *is* `γ`;
* `GammaEq S T` — adjoining residue representatives does not change `Γ` (representatives live in
  the `Kˣ`-part of `RV`, which is value-trivial);
* `VF(T) = VF(S)` — the paper's Lemma 3.3(1).  This is also what carries henselianity to the next
  step (`IsHenselianVF.of_vf_eq`).

Encoding caveat, recorded like `M7Hensel`'s for `ImmediateLift`: in the tagged one-sorted encoding
the closure of `S` under *ill-sorted* function symbols can in principle add `VF`-junk, so
`VF(T) = VF(S)` is a genuine constraint and not a formality (the paper's sorts are disjoint). -/
def ResidueStep : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (γ : StandingField.KOf M →+* StandingField.KOf N),
    (∀ (x : S) (hx : iUnits (x : M)),
      (γ ⟨(x : M), Or.inl hx⟩ : StandingField.KOf N).1 = f x) →
    M7Hens.IsHenselianVF S →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      Extends hST g f ∧ Assembly.KEqTop T ∧ GammaEq S T ∧
        (∀ x : M, iVF x → (x ∈ T ↔ x ∈ S)) ∧
        (∀ (x : T) (hx : iUnits (x : M)),
          (γ ⟨(x : M), Or.inl hx⟩ : StandingField.KOf N).1 = g x)

/-! ### 6. Input 4 — the paper's construction: the divisible hull of `Γ(S)` -/

/-- **Input 4** (paper, Lemma 3.3 "`Γ(S*)` divisible via the (Prestel–Engler) divisible hull",
*construction-meets-quote*).

From `S` with `K(S) = K(M)` (which the residue step has just arranged) and `(VF(S), O(S))`
henselian, there are `T ⊇ S` and an extension `g : T ↪ N` of `f` such that

* `GammaDivisible T` — `Γ(T)` is divisible, in the frozen `Assembly.GammaDivisible` form;
* `GammaHullInitial S T` — `Γ(T)` sits inside the *hull* of `Γ(S)` (the quotation's clamp; this is
  what forbids `T = ⊤`).

The henselianity hypothesis is what makes the algebraic case work: the paper's Lemmas 3.4 and 3.6
are stated at henselian `VF(Š)` (`refs/qe.tex` l. 640, l. 660), and `IsHenselianVF.of_vf_eq` carries
it up from `T₁`.  Note `GammaDivisible` is *not* upward closed, so it must be produced afresh at `T`. -/
def DivisibilityStep : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
    Assembly.KEqTop S → M7Hens.IsHenselianVF S →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      Extends hST g f ∧ Assembly.GammaDivisible T ∧ GammaHullInitial S T

/-! ### 7. Input 5 — Marker: saturation realisation -/

/-- **Input 5** (Marker, *Model Theory*: a `κ`-saturated structure is `κ`-homogeneous, so a partial
isomorphism of size `< κ` extends; here the paper's `‖M‖⁺`-saturation of `N` with `#T ≤ #M < ‖M‖⁺`).

`N` realises the type cutting out the graph of an embedding of any substructure `T ⊆ M` extending the
given one on `S`.  This is the input that supplies the monomorphism at each stage of the tower.  Its
size content is exactly `#M ≤ #N` (`saturationRealization_forces_size`), i.e. the frozen `SizeHyp`,
which the paper's `‖M‖⁺`-saturation supplies. -/
def SaturationRealization : Prop :=
  ∀ (S T : LRV.Substructure M) (f : S ↪[LRV] N) (hST : S ≤ T),
    ∃ g : T ↪[LRV] N, Extends hST g f

/-! ### 8. The assembly: the five inputs give `PrepStepP` at the pair -/

/-- **What inputs 2 and 5 jointly supply**: an immediate henselian extension of `S`, *together with*
an extension of `f` to it.  Factoring this out isolates the only place the ledger consumes either of
them, and makes the two routes (Marker's saturated realisation / Prestel–Engler's `ImmediateLift`)
interchangeable without redoing the argument. -/
def HenselLift : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (himm : M6L33.Immediate S T),
      Extends himm.1 g f ∧ M7Hens.IsHenselianVF T

/-- Inputs 2 and 5 give `HenselLift`. -/
theorem henselLift_of_saturation (h2 : HenselizationExists M)
    (h5 : SaturationRealization (M := M) (N := N)) : HenselLift (M := M) (N := N) := by
  intro S f
  obtain ⟨T, himm, hhen⟩ := h2 S
  obtain ⟨g, hag⟩ := h5 S T f himm.1
  exact ⟨T, g, himm, hag, hhen⟩

/-- Input 2 plus `M7Hens.ImmediateLift` (the Prestel–Engler route) give `HenselLift` too — the
statement of `ImmediateLift`'s conclusion is `Extends` by definition. -/
theorem henselLift_of_immediateLift (h2 : HenselizationExists M) (hL : M7Hens.ImmediateLift) :
    HenselLift (M := M) (N := N) := by
  intro S f
  obtain ⟨T, himm, hhen⟩ := h2 S
  obtain ⟨g, hag⟩ := hL M N S T f himm hhen
  exact ⟨T, g, himm, hag, hhen⟩

/-- **The ledger.**  `Assembly.PrepStepP (M := M) (N := N)` from inputs 1, 3, 4 and `HenselLift`.
The proof is the tower

    S --(henselize)--> T₁ --(residue reps)--> T₂ --(divisible hull)--> T₃

with the monomorphisms supplied at the bottom (input 5 / `ImmediateLift`) and carried along by inputs
3 and 4.  No size hypothesis and no saturation hypothesis appears in the statement: the inputs are
themselves the (putative) consequences of `PaperHyp`. -/
theorem prepStepP_of_henselLift (h1 : ACFExtends (M := M) (N := N))
    (hHL : HenselLift (M := M) (N := N)) (h3 : ResidueStep (M := M) (N := N))
    (h4 : DivisibilityStep (M := M) (N := N)) :
    Assembly.PrepStepP (M := M) (N := N) := by
  intro S f
  -- steps 1+2: an immediate henselian extension together with the monomorphism on it
  obtain ⟨T₁, g₁, himm, hag₁, hhen⟩ := hHL S f
  have hST₁ : S ≤ T₁ := himm.1
  -- step 3: the residue-field map (input 1)
  obtain ⟨γ, hγ⟩ := h1 S f
  -- it also extends `g₁` on the units of `T₁`, because `K(T₁) = K(S)` (`Immediate`)
  have hγ₁ : ∀ (x : T₁) (hx : iUnits (x : M)),
      (γ ⟨(x : M), Or.inl hx⟩ : StandingField.KOf N).1 = g₁ x := by
    intro x hx
    have hxrv : iRV (x : M) := M7Hens.units_rv_mem (M := M) hx
    have hxS : (x : M) ∈ S := (M7Hens.rv_eq_of_henselization (M := M) himm (x : M) hxrv).mp x.2
    have hstep : (γ ⟨(x : M), Or.inl hx⟩ : StandingField.KOf N).1
        = f ⟨(x : M), hxS⟩ := hγ ⟨(x : M), hxS⟩ hx
    have hag : f ⟨(x : M), hxS⟩ = g₁ x := by
      have h := hag₁ ⟨(x : M), hxS⟩
      have hxT : (⟨(x : M), hST₁ hxS⟩ : T₁) = x := Subtype.ext rfl
      rw [hxT] at h
      exact h.symm
    exact hstep.trans hag
  -- step 4: residue representatives (input 3) at the henselian `T₁`
  obtain ⟨T₂, g₂, hT₁T₂, hag₂, hKEq₂, _hΓ₂, hVF₂, _hγ₂⟩ := h3 T₁ g₁ γ hγ₁ hhen
  -- step 5: divisible hull (input 4) at `T₂`, still henselian because `VF(T₂) = VF(T₁)`
  obtain ⟨T₃, g₃, hT₂T₃, hag₃, hΓ₃, _hHull⟩ :=
    h4 T₂ g₂ hKEq₂ (IsHenselianVF.of_vf_eq hVF₂ hhen)
  -- conclusion
  refine ⟨T₃, g₃, hST₁.trans (hT₁T₂.trans hT₂T₃), ?_, ?_⟩
  · -- `g₃` extends `f` on `S`
    have h21 : Extends (hT₁T₂.trans hT₂T₃) g₃ g₁ := Extends.comp hag₃ hag₂
    exact Extends.comp h21 hag₁
  · -- `Standing T₃`
    exact ⟨KEqTop_mono hKEq₂ hT₂T₃, hΓ₃⟩

/-- **The ledger, Marker route**: inputs 1, 2, 3, 4, 5. -/
theorem prepStepP_of_ledger (h1 : ACFExtends (M := M) (N := N))
    (h2 : HenselizationExists M) (h3 : ResidueStep (M := M) (N := N))
    (h4 : DivisibilityStep (M := M) (N := N))
    (h5 : SaturationRealization (M := M) (N := N)) :
    Assembly.PrepStepP (M := M) (N := N) :=
  prepStepP_of_henselLift h1 (henselLift_of_saturation h2 h5) h3 h4

/-- **The ledger, Prestel–Engler route**: inputs 1, 2, 3, 4 and `M7Hens.ImmediateLift` in place of
input 5. -/
theorem prepStepP_of_ledger_hens (h1 : ACFExtends (M := M) (N := N))
    (h2 : HenselizationExists M) (h3 : ResidueStep (M := M) (N := N))
    (h4 : DivisibilityStep (M := M) (N := N)) (hL : M7Hens.ImmediateLift) :
    Assembly.PrepStepP (M := M) (N := N) :=
  prepStepP_of_henselLift h1 (henselLift_of_immediateLift h2 hL) h3 h4


end Inputs

/-! ### 9. The five inputs in the shape of the frozen route -/

/-- Input 1 at every `SizeHyp` pair. -/
def LedgerInput1 : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.SizeHyp M N → ACFExtends (M := M) (N := N)

/-- Input 2 at every model.  The binder shape is `M7Hens.paper_theorem_2_3_sat_of_hens`'s `hE`
deliberately, so one hypothesis serves both the ledger and the one-step. -/
def LedgerInput2 : Prop :=
  ∀ (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF], M7Hens.HenselizationExists M

/-- Input 3 at every `SizeHyp` pair. -/
def LedgerInput3 : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.SizeHyp M N → ResidueStep (M := M) (N := N)

/-- Input 4 at every `SizeHyp` pair. -/
def LedgerInput4 : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.SizeHyp M N → DivisibilityStep (M := M) (N := N)

/-- Input 5 at every `SizeHyp` pair. -/
def LedgerInput5 : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.SizeHyp M N → SaturationRealization (M := M) (N := N)

/-- **The frozen obligation**, from the five inputs.  This is `M7Paper.PrepStepSize` verbatim
(`QE/PaperRoute.lean`), i.e. Lemma 3.3 at `SizeHyp` pairs. -/
theorem prepStepSize_of_ledger (h1 : LedgerInput1) (h2 : LedgerInput2) (h3 : LedgerInput3)
    (h4 : LedgerInput4) (h5 : LedgerInput5) : M7Paper.PrepStepSize := by
  intro M N _ _ _hM _hN hSize S f
  exact prepStepP_of_ledger (h1 M N hSize) (h2 M) (h3 M N hSize) (h4 M N hSize) (h5 M N hSize) S f

/-- The residue-field-level size guard discussed in the header: `#M ≤ #N` (the frozen `SizeHyp`)
together with `#K(M) ≤ #K(N)`, which is what input 1 forces and what the frozen guard does not
supply. -/
def SizeHypK (M N : Type) [LRV.Structure M] [LRV.Structure N] : Prop :=
  M7Paper.SizeHyp M N ∧ Cardinal.mk (StandingField.KOf M) ≤ Cardinal.mk (StandingField.KOf N)

/-- **Corrected frozen obligation**: Lemma 3.3 at pairs whose *residue fields* are also size-ordered.
Same five inputs, guards at `SizeHypK`.  This is the shape dischargeable from the paper's hypotheses
without hidden content (see the header, stress test (b)). -/
def PrepStepSizeK : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    SizeHypK M N → Assembly.PrepStepP (M := M) (N := N)

theorem prepStepSizeK_of_ledger
    (h1 : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      SizeHypK M N → ACFExtends (M := M) (N := N))
    (h2 : LedgerInput2)
    (h3 : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      SizeHypK M N → ResidueStep (M := M) (N := N))
    (h4 : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      SizeHypK M N → DivisibilityStep (M := M) (N := N))
    (h5 : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      SizeHypK M N → SaturationRealization (M := M) (N := N)) : PrepStepSizeK := by
  intro M N _ _ _hM _hN hSize S f
  exact prepStepP_of_ledger (h1 M N hSize) (h2 M) (h3 M N hSize) (h4 M N hSize) (h5 M N hSize) S f

/-! ### 10. End-to-end wiring into the frozen route -/

/-- **Theorem 2.3 (`qe:acvf`) from the ledger.**  The ledger's `PrepStepSize` plugs into
`QE/M7Hensel.lean`'s `paper_theorem_2_3_sat_of_hens`, which consumes the two henselization inputs
(`LedgerInput2` and `ImmediateLift`) and Lemmas 3.4–3.8 at henselian domains.  `LedgerInput2` is
shared between the two: the ledger uses the henselization for `K`/`Γ`-preservation, the one-step uses
it for `Standing`-preservation, and `ImmediateLift` for the monomorphism. -/
theorem paper_theorem_2_3_sat_of_ledger (hShoen : M7Paper.ShoenfieldTestSat)
    (h1 : LedgerInput1) (h2 : LedgerInput2) (h3 : LedgerInput3) (h4 : LedgerInput4)
    (h5 : LedgerInput5) (hL : M7Hens.ImmediateLift)
    (hOne : ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF]
      [Q ⊨ Axioms.ACVF] (S : LRV.Substructure P) (f : S ↪[LRV] Q),
      Assembly.Standing S → M7Hens.IsHenselianVF S → ∀ m : P, iVF m →
        ∃ (T : LRV.Substructure P) (g : T ↪[LRV] Q) (hST : S ≤ T),
          (∀ x : S, g ⟨(x : P), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T) :
    HasQE Axioms.ACVF :=
  M7Hens.paper_theorem_2_3_sat_of_hens hShoen (prepStepSize_of_ledger h1 h2 h3 h4 h5) h2 hL hOne

/-! ### 10b. The same five inputs at the paper's own hypothesis (`M7Paper.PaperHyp`)

`SizeHyp` (§9) is the *frozen* guard.  The paper's guard is `N` `‖M‖⁺`-saturated, which
`QE/PaperRoute.lean` freezes as `PaperHyp M N = SaturatedFS N ∧ SizeHyp M N`, and it is exactly at
that guard that inputs 1 and 5 become available (header, stress test (b)).  This section therefore
provides the ledger at the paper's pair, and the paper's Proposition 3.9 and Theorem 2.3 from it, with
`OneStepSizeFree` (the frozen Lemmas 3.4–3.8) unchanged.  Note that this route needs *neither*
`ImmediateLift` nor the one-step-at-henselian-domains hypothesis of §10. -/

/-- Input 1 at `PaperHyp` pairs. -/
def LedgerInput1P : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.PaperHyp M N → ACFExtends (M := M) (N := N)

/-- Input 3 at `PaperHyp` pairs. -/
def LedgerInput3P : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.PaperHyp M N → ResidueStep (M := M) (N := N)

/-- Input 4 at `PaperHyp` pairs. -/
def LedgerInput4P : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.PaperHyp M N → DivisibilityStep (M := M) (N := N)

/-- Input 5 at `PaperHyp` pairs. -/
def LedgerInput5P : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.PaperHyp M N → SaturationRealization (M := M) (N := N)

/-- **Lemma 3.3 at the paper's pair**, from the five inputs. -/
def PrepStepPaper : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.PaperHyp M N → Assembly.PrepStepP (M := M) (N := N)

theorem prepStepPaper_of_ledger (h1 : LedgerInput1P) (h2 : LedgerInput2) (h3 : LedgerInput3P)
    (h4 : LedgerInput4P) (h5 : LedgerInput5P) : PrepStepPaper := by
  intro M N _ _ _hM _hN hP S f
  exact prepStepP_of_ledger (h1 M N hP) (h2 M) (h3 M N hP) (h4 M N hP) (h5 M N hP) S f

/-- **Proposition 3.9 at the paper's pair**, from Lemma 3.3 there and the frozen one-step
(`Assembly.prop39P_noVFGen`: the assembly of `PrepStepP` and `OneStepVFP` into a total embedding,
which never touches a saturation hypothesis). -/
theorem prop39Sat_of_prepStepPaper (hPrep : PrepStepPaper) (hOne : M7Paper.OneStepSizeFree) :
    M7Paper.Prop39Sat := by
  intro M N _ _ _hM _hN hP S f
  exact Assembly.prop39P_noVFGen (hPrep M N hP) (hOne M N) S f

/-- **Theorem 2.3 (`qe:acvf`) with the paper's hypotheses, the prep step decomposed into the five
inputs.**  Compare `M7Paper.paper_theorem_2_3_sat`, which has the undischarged `PrepStepSize`; the
only difference in the conclusion is that the `PrepStepSize` hypothesis has been replaced by the five
inputs of `MILESTONES.md` at the paper's pair. -/
theorem paper_theorem_2_3_sat_of_ledger_paperHyp (hShoen : M7Paper.ShoenfieldTestSat)
    (h1 : LedgerInput1P) (h2 : LedgerInput2) (h3 : LedgerInput3P) (h4 : LedgerInput4P)
    (h5 : LedgerInput5P) (hOne : M7Paper.OneStepSizeFree) : HasQE Axioms.ACVF :=
  hShoen (prop39Sat_of_prepStepPaper (prepStepPaper_of_ledger h1 h2 h3 h4 h5) hOne)

/-! ### 11. Stress tests -/

section StressTests

variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-! #### (a) The bare forms *are* vacuous — machine-checked -/

/-- The bare residue-step conclusion is satisfied by `T = ⊤`: a residue step stated without the
`Γ`-, `VF`- or embedding-conjunct carries no content. -/
theorem bare_KEqTop_trivial (S : LRV.Substructure M) :
    ∃ T : LRV.Substructure M, S ≤ T ∧ Assembly.KEqTop T :=
  ⟨⊤, le_top, fun _ _ => trivial⟩

/-- The bare divisibility conclusion is satisfied by `T = ⊤` (`StandingTree.standing_top`): this is
why `DivisibilityStep` carries `GammaHullInitial`. -/
theorem bare_gammaDivisible_trivial (S : LRV.Substructure M) :
    ∃ T : LRV.Substructure M, S ≤ T ∧ Assembly.GammaDivisible T :=
  ⟨⊤, le_top, (StandingTree.standing_top (M := M)).2⟩

/-- Even `Standing` is trivially reachable at `⊤`, so the content of `Assembly.PrepStepP` is *entirely*
in the embedding `T ↪[LRV] N` and in which `T` it is: a `T` that both carries `Standing` and embeds.
Recorded because it is the reason inputs 3 and 4 both carry embeddings rather than only closures. -/
theorem standing_top_trivial : Assembly.Standing (⊤ : LRV.Substructure M) :=
  StandingTree.standing_top

/-! #### (a′) The inputs are inhabited in the paper's setting -/

/-- `SaturationRealization` is not the conclusion: it mentions no closure predicate, and it holds
trivially at `T = S` (the identity extension). -/
theorem saturationRealization_refl (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    ∃ g : S ↪[LRV] N, Extends (le_rfl : S ≤ S) g f :=
  ⟨f, extends_refl f⟩

/-- `HenselizationExists` is inhabited at every already-henselian substructure.  (`Immediate` forbids
the trivial `T = ⊤` witness, so this is the honest non-vacuity statement.) -/
theorem henselizationExists_of_henselian {S : LRV.Substructure M}
    (h : M7Hens.IsHenselianVF S) : ∃ T, M6L33.Immediate S T ∧ M7Hens.IsHenselianVF T :=
  M7Hens.henselian_self_immediate h

/-! #### (b) The cardinality audit -/

/-- The conclusion's size content, through the ledger
(`M7Paper.prepStepP_forces_units_size`): the frozen `PrepStepP` forces `#Kˣ(M) ≤ #N`. -/
theorem ledger_forces_units_size (h1 : ACFExtends (M := M) (N := N))
    (h2 : HenselizationExists M) (h3 : ResidueStep (M := M) (N := N))
    (h4 : DivisibilityStep (M := M) (N := N))
    (h5 : SaturationRealization (M := M) (N := N)) (S : LRV.Substructure M)
    (f : S ↪[LRV] N) : Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N :=
  M7Paper.prepStepP_forces_units_size (prepStepP_of_ledger h1 h2 h3 h4 h5) S f

/-- Input 1's size content: an injective ring hom out of a field gives `#K(M) ≤ #K(N)`. -/
theorem acfExtends_field_size (h1 : ACFExtends (M := M) (N := N))
    (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    Cardinal.mk (StandingField.KOf M) ≤ Cardinal.mk (StandingField.KOf N) := by
  obtain ⟨γ, -⟩ := h1 S f
  exact Cardinal.mk_le_of_injective (RingHom.injective γ)

/-- Input 5's size content: extending along `S ≤ ⊤` gives an embedding `M ↪ N`, hence `#M ≤ #N`
(the frozen `M7Paper.SizeHyp`). -/
theorem saturationRealization_forces_size (h5 : SaturationRealization (M := M) (N := N))
    (S : LRV.Substructure M) (f : S ↪[LRV] N) : Cardinal.mk M ≤ Cardinal.mk N := by
  obtain ⟨g, -⟩ := h5 S ⊤ f le_top
  refine Cardinal.mk_le_of_injective (f := fun x : M => g ⟨x, trivial⟩) ?_
  intro a b hab
  exact Subtype.ext_iff.mp (Embedding.injective g hab)

/-- `SizeHypK` supplies the one inequality the conclusion forces.  So the ledger is *not*
cardinality-refutable at `SizeHypK` pairs. -/
theorem units_size_of_sizeHypK (h : SizeHypK M N) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N := by
  have hinj : Function.Injective
      (fun x : {x : M // iUnits x} => (⟨x.1, Or.inl x.2⟩ : StandingField.KOf M)) := by
    intro a b hab
    exact Subtype.ext (congrArg (fun y : StandingField.KOf M => y.1) hab)
  exact le_trans (Cardinal.mk_le_of_injective hinj)
    (le_trans h.2 (Cardinal.mk_subtype_le (fun x : N => iUnits x ∨ x = iRVZero)))

end StressTests

end M5Ledger
end Milestone0
end SpecialTransformations

#print axioms SpecialTransformations.Milestone0.M5Ledger.KEqTop_mono
#print axioms SpecialTransformations.Milestone0.M5Ledger.Extends.comp
#print axioms SpecialTransformations.Milestone0.M5Ledger.IsHenselianVF.of_vf_eq
#print axioms SpecialTransformations.Milestone0.M5Ledger.henselLift_of_saturation
#print axioms SpecialTransformations.Milestone0.M5Ledger.henselLift_of_immediateLift
#print axioms SpecialTransformations.Milestone0.M5Ledger.prepStepP_of_henselLift
#print axioms SpecialTransformations.Milestone0.M5Ledger.prepStepP_of_ledger
#print axioms SpecialTransformations.Milestone0.M5Ledger.prepStepP_of_ledger_hens
#print axioms SpecialTransformations.Milestone0.M5Ledger.prepStepSize_of_ledger
#print axioms SpecialTransformations.Milestone0.M5Ledger.prepStepSizeK_of_ledger
#print axioms SpecialTransformations.Milestone0.M5Ledger.paper_theorem_2_3_sat_of_ledger
#print axioms SpecialTransformations.Milestone0.M5Ledger.prepStepPaper_of_ledger
#print axioms SpecialTransformations.Milestone0.M5Ledger.prop39Sat_of_prepStepPaper
#print axioms SpecialTransformations.Milestone0.M5Ledger.paper_theorem_2_3_sat_of_ledger_paperHyp
#print axioms SpecialTransformations.Milestone0.M5Ledger.bare_KEqTop_trivial
#print axioms SpecialTransformations.Milestone0.M5Ledger.bare_gammaDivisible_trivial
#print axioms SpecialTransformations.Milestone0.M5Ledger.standing_top_trivial
#print axioms SpecialTransformations.Milestone0.M5Ledger.saturationRealization_refl
#print axioms SpecialTransformations.Milestone0.M5Ledger.henselizationExists_of_henselian
#print axioms SpecialTransformations.Milestone0.M5Ledger.ledger_forces_units_size
#print axioms SpecialTransformations.Milestone0.M5Ledger.acfExtends_field_size
#print axioms SpecialTransformations.Milestone0.M5Ledger.saturationRealization_forces_size
#print axioms SpecialTransformations.Milestone0.M5Ledger.units_size_of_sizeHypK
