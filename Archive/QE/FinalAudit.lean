/-
# ADVERSARIAL AUDIT OF `paper_theorem_FINAL` (direction **f6**)

`QE/FinalRoute.lean` states

    paper_theorem_FINAL : ShoenfieldTestSat → LedgerInput1P → LedgerInput2 → LedgerInput3P →
      LedgerInput4P → LedgerInput5P → M7OneStepPaper → HasQE Axioms.ACVF

and its own header says "it does not discharge any of the seven hypotheses" and that nothing in the
file "shows that `OneStepPaper` is not derivable from `h1`–`h5`".  This file runs the adversarial
audit of the seven and **does** find a collapse.  The verdict, machine-checked below:

## The finding

`Assembly.PrepStepP` and `Assembly.OneStepVFP` — the two frozen conclusions of the whole §3
decomposition — are both satisfied **with `T = ⊤`** at any pair of models, because

    M5Ledger.standing_top_trivial : Assembly.Standing (⊤ : LRV.Substructure M)

(`Γ(M)` is divisible and `K(⊤) = K(M)` trivially in a *model*; `QE/Standing.lean`,
`StandingTree.standing_top`).  All the frozen `Standing`-conclusions ask for is *some* `T ⊇ S` with
`Standing T` together with an embedding `T ↪[LRV] N` — there is no immediacy, no `VF`-clamp and no
hull-clamp in either statement.  Hence

* `Assembly.PrepStepP`  ⟸  `M5Ledger.SaturationRealization` (the whole content of input 5);
* `Assembly.OneStepVFP` ⟸  `M5Ledger.SaturationRealization`.

Consequently, at the paper's pairs, **input 5 alone gives Proposition 3.9**, and the FINAL reduces
to *two* hypotheses:

    paper_theorem_FINAL2 : ShoenfieldTestSat → LedgerInput5P → HasQE Axioms.ACVF

Hypotheses 1, 2, 3, 4 and 7 (`ACFExtends` at the paper's pairs, Prestel–Engler henselization,
the residue step, the divisible hull, and Lemmas 3.4–3.8) are **not used**: `paper_theorem_FINAL`
follows from `paper_theorem_FINAL2`, so the seven-fold hypothesis set shrinks to two, and
`M5Ledger`'s tower `S --henselize--> T₁ --residue reps--> T₂ --divisible hull--> T₃` is bypassed by
the one-step witness `T = ⊤` (this is the `bare_KEqTop_trivial` / `bare_gammaDivisible_trivial`
pattern of `M5Ledger` §11(a) — what those stress tests show for the *bare* forms also holds for the
frozen `PrepStepP`/`OneStepVFP` because `Standing ⊤` holds outright in a model of `ACVF`).

## Why this is not an artefact of a mis-statement, and what remains

`LedgerInput5P` is *not* weaker than the paper's conclusion: §3 below proves

    M5Ledger.LedgerInput5P ↔ M7Paper.Prop39Sat

(`SaturationRealization` at the paper's pairs is, by restriction of a total embedding to `T`,
*exactly* Proposition 3.9 `lrv:mono:lift`).  So the reduced FINAL is literally

    ShoenfieldTestSat → Prop39Sat → HasQE Axioms.ACVF

i.e. Shoenfield's criterion applied to the paper's Proposition 3.9 — the tree's formalisation of
"Marker: saturated ⟹ homogeneous" (input 5) already **is** the paper's conclusion.  The residual on
the paper's side is precisely: at a pair with `SaturatedFS N` and `#M ≤ #N`, every partial
monomorphism `S ↪ N` extends to a total one (`Prop39Sat`), together with the Marker quote
`Prop39Sat → HasQE`.  Nothing else in the seven is load-bearing.

The audit also records, machine-checked, *why the other hypotheses are not collapsed the same way*
(so that the collapse is attributed to the right place): §4 shows that the `⊤`-witness is
*excluded* for inputs 2, 3, 4 by their own clamps (`Immediate`, `VF(T) = VF(S)`, and
`GammaHullInitial`), and that the clamps are themselves satisfiable (`GammaHullInitial S S`), i.e.
the content of inputs 3/4 is real but unused, not vacuous.

## Hypothesis-by-hypothesis verdict

| # | hypothesis | verdict |
|---|---|---|
| 1 | `ShoenfieldTestSat` | **irreducible**: it is the only hypothesis mentioning `HasQE`.  Not touched by any degenerate witness (`HasQE` cannot be *produced* from `Prop39Sat` alone; see §5). |
| 2 | `LedgerInput1P` | **collapsed** (not needed): `paper_theorem_FINAL_of_input5` drops it.  `⊤`-discharge fails for it independently: a field embedding `K(M) →+* K(N)` is not a closure property (§6). |
| 3 | `LedgerInput2` | **collapsed** (not needed), same theorem.  Its own `⊤`-witness is excluded by `Immediate` (§4.2). |
| 4 | `LedgerInput3P` | **collapsed** (not needed), same theorem.  Its own `⊤`-witness is excluded by the `VF`-clamp (§4.1). |
| 5 | `LedgerInput4P` | **collapsed** (not needed), same theorem.  Its own `⊤`-witness is excluded by `GammaHullInitial`, whose weakest instantiation `GammaHullInitial S S` holds (§4.3), so its content is `GammaDivisible`, not the clamp. |
| 6 | `LedgerInput5P` | **the whole content**: `LedgerInput5P ↔ Prop39Sat` (§3), and the reduced FINAL is `ShoenfieldTestSat → LedgerInput5P → HasQE` (§2). |
| 7 | `M7OneStepPaper` | **collapsed** (not needed): `LedgerInput5P` alone gives `OneStepVFP` at every pair (§1.2, §2.2). |

## Cardinality audit of the full conjunction (§7)

At a `PaperHyp` pair the seven-fold conjunction's *only* cardinality content is `#M ≤ #N`, which the
gate already supplies; every inequality the audit can extract (`#K(M) ≤ #N`, `#Kˣ(M) ≤ #N`,
`#M ≤ #N`) is a consequence of `PaperHyp` alone, so no impossible size statement is forced.  The one
genuine size-forcing hypothesis, `SaturationRealization`, forces `#M ≤ #N` *without* a gate
(`M5Ledger.saturationRealization_forces_size`), which is machine-checked here as the refutation shape
`¬ SaturationRealization` whenever `#N < #M`: the gate is what keeps the hypothesis plausible, and it
is preserved by the collapse (the reduced FINAL still uses `LedgerInput5P`, i.e. still gated).

Everything is `exit 0`, no `sorry`/`admit`/`native_decide`, no new axiom, and every head theorem's
`#print axioms` is printed at the end.
-/
import FinalRoute
import M5Ledger
import MulNormalForm
import Lemma33

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations
namespace Milestone0
namespace FinalAudit

/-! ## 1. The `⊤` mechanism: what `Standing ⊤` buys -/

section TopMechanism

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- `Standing ⊤` is a theorem of `ACVF`, so the `⊤`-witness of `PrepStepP` is available.  Restated
here so that the audit is self-contained (identical to `M5Ledger.standing_top_trivial`). -/
theorem standing_top : Assembly.Standing (⊤ : LRV.Substructure M) :=
  StandingTree.standing_top

/-- **`PrepStepP` from saturation realisation.**  `PrepStepP` asks only for *some* `T ⊇ S` carrying
`Standing` together with an embedding `T ↪[LRV] N`; `T = ⊤` qualifies because `Standing ⊤` holds in
a model of `ACVF`.  So the frozen Lemma 3.3 conclusion follows from the single hypothesis that
extends `f` to `⊤` — i.e. from input 5 alone. -/
theorem prepStepP_of_saturationRealization
    (h5 : M5Ledger.SaturationRealization (M := M) (N := N)) :
    Assembly.PrepStepP (M := M) (N := N) := by
  intro S f
  obtain ⟨g, hag⟩ := h5 S ⊤ f le_top
  exact ⟨⊤, g, le_top, hag, standing_top⟩

/-- **`OneStepVFP` from saturation realisation**, by the same witness: `Standing ⊤` and `m ∈ ⊤`
are free.  So the frozen Lemmas 3.4–3.8 conclusion follows from input 5 alone as well. -/
theorem oneStepVFP_of_saturationRealization
    (h5 : M5Ledger.SaturationRealization (M := M) (N := N)) :
    Assembly.OneStepVFP (M := M) (N := N) := by
  intro S f _hStand m _hm
  obtain ⟨g, hag⟩ := h5 S ⊤ f le_top
  exact ⟨⊤, g, le_top, hag, trivial, standing_top⟩

/-- **Proposition 3.9 at the pair, from saturation realisation.**  Composed through the frozen join
`Assembly.prop39P_noVFGen`, which is the tree's own route from `PrepStepP` + `OneStepVFP` to the
total extension property. -/
theorem total_extension_of_saturationRealization
    (h5 : M5Ledger.SaturationRealization (M := M) (N := N)) (S : LRV.Substructure M)
    (f : S ↪[LRV] N) :
    ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x :=
  Assembly.prop39P_noVFGen (prepStepP_of_saturationRealization h5)
    (oneStepVFP_of_saturationRealization h5) S f

/-! ## 2. The collapse: the FINAL without hypotheses 1, 2, 3, 4 and 7 -/

/-- **`SaturationRealization` gives `PrepStepP` at every pair, hence Lemma 3.3 at the paper's
pairs from input 5 alone.** -/
theorem prepStepPaper_of_ledgerInput5P (h5 : M5Ledger.LedgerInput5P) :
    M5Ledger.PrepStepPaper := by
  intro M' N' _ _ _ _ hP S f
  exact prepStepP_of_saturationRealization (h5 M' N' hP) S f

/-- **Input 5 alone gives the one-step at the paper's pairs** — i.e. hypothesis 7 is unnecessary. -/
theorem oneStepPaper_of_ledgerInput5P (h5 : M5Ledger.LedgerInput5P) :
    FinalRoute.M7OneStepPaper := by
  intro M' N' _ _ _ _ hP S f hS m hm
  exact oneStepVFP_of_saturationRealization (h5 M' N' hP) S f hS m hm

/-- **Input 5 alone gives Proposition 3.9** (`lrv:mono:lift`) at the paper's pairs. -/
theorem prop39Sat_of_ledgerInput5P (h5 : M5Ledger.LedgerInput5P) : M7Paper.Prop39Sat := by
  intro M' N' _ _ _ _ hP S f
  exact total_extension_of_saturationRealization (h5 M' N' hP) S f

/-- **THE SIMPLIFIED FINAL** — `paper_theorem_FINAL` with five of its seven hypotheses deleted.
Only Shoenfield's criterion and the saturation-realisation input survive. -/
theorem paper_theorem_FINAL2 (hShoen : M7Paper.ShoenfieldTestSat)
    (h5 : M5Ledger.LedgerInput5P) : HasQE Axioms.ACVF :=
  hShoen (prop39Sat_of_ledgerInput5P h5)

/-- **The original FINAL, proved from two of its hypotheses.**  `h1`, `h2`, `h3`, `h4` and `hOne`
are bound and unused — this is the exact signature of `FinalRoute.paper_theorem_FINAL` with the same
conclusion, so the five hypotheses are redundant in the FINAL as compiled. -/
theorem paper_theorem_FINAL_of_input5 (hShoen : M7Paper.ShoenfieldTestSat)
    (h1 : M5Ledger.LedgerInput1P) (h2 : M5Ledger.LedgerInput2)
    (h3 : M5Ledger.LedgerInput3P) (h4 : M5Ledger.LedgerInput4P)
    (h5 : M5Ledger.LedgerInput5P) (hOne : FinalRoute.M7OneStepPaper) :
    HasQE Axioms.ACVF :=
  paper_theorem_FINAL2 hShoen h5

/-- The same at the packaged hypothesis set of `FinalRoute`: `FinalHyp → HasQE` only touches
`hShoen` and `h5`. -/
theorem paper_theorem_FINAL_flat_shrunk (h : FinalRoute.FinalHyp) : HasQE Axioms.ACVF :=
  paper_theorem_FINAL2 h.1 h.2.2.2.2.2.1

/-- Cross-check: the tree's own composition `prop39Sat_FINAL` already gives `Prop39Sat` from
`PrepStepPaper` + `OneStepPaper`, both of which are now consequences of input 5.  So the reduced
route and the compiled route agree at the join. -/
theorem prop39Sat_FINAL_of_input5 (h5 : M5Ledger.LedgerInput5P) : M7Paper.Prop39Sat :=
  FinalRoute.prop39Sat_FINAL (prepStepPaper_of_ledgerInput5P h5) (oneStepPaper_of_ledgerInput5P h5)

/-- **Type-level check that the telescope is the FINAL's own**: the tree's
`FinalRoute.paper_theorem_FINAL` has exactly the seven-hypothesis telescope written here (this
elaborates only if its binder list is this one), so the shrink below is a statement about the real
theorem and not about a copy. -/
theorem FINAL_telescope_matches :
    (∀ (hShoen : M7Paper.ShoenfieldTestSat) (h1 : M5Ledger.LedgerInput1P)
      (h2 : M5Ledger.LedgerInput2) (h3 : M5Ledger.LedgerInput3P)
      (h4 : M5Ledger.LedgerInput4P) (h5 : M5Ledger.LedgerInput5P)
      (hOne : FinalRoute.M7OneStepPaper), HasQE Axioms.ACVF) :=
  FinalRoute.paper_theorem_FINAL

/-- The same telescope, inhabited by the two-hypothesis proof: `h1`, `h2`, `h3`, `h4`, `hOne` are
never used.  Together with `FINAL_telescope_matches` this is the machine-checked statement that the
compiled FINAL has five redundant hypotheses. -/
theorem FINAL_telescope_matches_shrunk :
    (∀ (hShoen : M7Paper.ShoenfieldTestSat) (h1 : M5Ledger.LedgerInput1P)
      (h2 : M5Ledger.LedgerInput2) (h3 : M5Ledger.LedgerInput3P)
      (h4 : M5Ledger.LedgerInput4P) (h5 : M5Ledger.LedgerInput5P)
      (hOne : FinalRoute.M7OneStepPaper), HasQE Axioms.ACVF) :=
  paper_theorem_FINAL_of_input5

end TopMechanism

/-! ## 3. Sharpness: input 5 *is* Proposition 3.9

The collapse above is not an artefact of `PrepStepP`/`OneStepVFP` being weak in isolation: input 5
is *equivalent*, at the paper's pairs, to the paper's conclusion.  The missing direction is
restriction of a total embedding to a substructure (`Embedding.domRestrict`). -/

section Sharpness

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **The extension property at the pair implies `SaturationRealization`**: restrict the total
embedding to `T`.  This is the converse of §1.3 and it shows input 5 cannot be weakened by asking
only for the total extension. -/
theorem saturationRealization_of_total_extension
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
      ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x) :
    M5Ledger.SaturationRealization (M := M) (N := N) := by
  intro S T f _hST
  obtain ⟨g, hg⟩ := h S f
  exact ⟨g.domRestrict T, fun x => hg x⟩

/-- **Input 5 from Proposition 3.9**, at every pair: the gate of `LedgerInput5P` is `PaperHyp`, and
`Prop39Sat` supplies `PaperHyp`-uniform total extensions. -/
theorem ledgerInput5P_of_prop39Sat (h : M7Paper.Prop39Sat) : M5Ledger.LedgerInput5P := by
  intro M' N' _ _ _ _ hP
  exact saturationRealization_of_total_extension (fun S f => h M' N' hP S f)

/-- **INPUT 5 = PROPOSITION 3.9.**  At the paper's pairs, `SaturationRealization` and the paper's
`lrv:mono:lift` are the same statement.  Hence the FINAL's hypothesis 5 already contains the
paper's conclusion, which is why inputs 1–4 and the one-step gate are bypassed. -/
theorem ledgerInput5P_iff_prop39Sat :
    M5Ledger.LedgerInput5P ↔ M7Paper.Prop39Sat :=
  ⟨prop39Sat_of_ledgerInput5P, ledgerInput5P_of_prop39Sat⟩

/-- The reduced FINAL with `Prop39Sat` in place of `LedgerInput5P`.  This form has the whole
mathematical content in one place: it is Shoenfield's criterion (`ShoenfieldTestSat` unfolds to
`Prop39Sat → HasQE`, `M7Paper.ShoenfieldTestSat`) applied to the paper's Proposition 3.9. -/
theorem paper_theorem_FINAL3 (hShoen : M7Paper.ShoenfieldTestSat)
    (h39 : M7Paper.Prop39Sat) : HasQE Axioms.ACVF :=
  hShoen h39

/-- `FINAL3` is not an accidental weakening of `FINAL2`: by `ledgerInput5P_iff_prop39Sat` the two
reduced forms are inter-derivable, so §2's collapse is exact. -/
theorem FINAL2_iff_FINAL3 :
    (M7Paper.ShoenfieldTestSat → M5Ledger.LedgerInput5P → HasQE Axioms.ACVF) ↔
      (M7Paper.ShoenfieldTestSat → M7Paper.Prop39Sat → HasQE Axioms.ACVF) := by
  constructor
  · intro h hS h39
    exact h hS (ledgerInput5P_of_prop39Sat h39)
  · intro h hS h5
    exact h hS (prop39Sat_of_ledgerInput5P h5)

end Sharpness

/-! ## 4. Why the *other* hypotheses resist the `⊤` witness

The collapse of §2 goes through `PrepStepP`/`OneStepVFP` precisely because those statements carry no
clamp on `T`.  Inputs 2, 3 and 4 all do carry one, and the lemmas below machine-check that the
`⊤`-witness is excluded for each — so the collapse is *not* a consequence of those inputs being
trivially satisfiable, it is a consequence of them not being used. -/

section Clamps

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **Input 3's clamp excludes `T = ⊤`.**  `ResidueStep`'s conclusion contains
`∀ x, iVF x → (x ∈ T ↔ x ∈ S)` (the paper's `VF(T) = VF(S)`); read at `T = ⊤` it says that every
`VF`-element of `M` already lies in `S`, and a substructure containing every `VF`-element *is* the
whole model (`Assembly.eq_top_of_vf_all`).  So the residue step cannot be discharged by the `⊤`
trick. -/
theorem residueStep_vf_clause_at_top {S : LRV.Substructure M}
    (h : ∀ x : M, iVF x → (x ∈ (⊤ : LRV.Substructure M) ↔ x ∈ S)) : S = ⊤ :=
  Assembly.eq_top_of_vf_all S (fun x hx => (h x hx).1 trivial)

/-- **Input 2's clamp excludes `T = ⊤`.**  `M6L33.Immediate S T` says that no new `RV`-element is
added; at `T = ⊤` it says every `RV`-element of `M` is already in `S`.  So the henselization input is
not dischargeable at `⊤` either (and `Immediate` forbids `T = S` unless `S` is henselian —
`M5Ledger.henselizationExists_of_henselian`). -/
theorem immediate_top_iff {S : LRV.Substructure M} :
    M6L33.Immediate S ⊤ ↔ ∀ x : M, iRV x → x ∈ S := by
  constructor
  · intro h x hx
    exact h.2 x trivial hx
  · intro h
    exact ⟨fun _ _ => trivial, fun x _ hx => h x hx⟩

/-- **Input 4's hull clamp is satisfiable, so its content is `GammaDivisible`, not the clamp.**
`GammaHullInitial S S` is the weakest instantiation: `n = 1`, `s = t`, `c = 1`.  This is why
`M5Ledger.bare_gammaDivisible_trivial` (which `T = ⊤` satisfies) is not the statement of input 4:
the clamp is what forbids `⊤`, and it is satisfied at `T = S` where the divisibility of `Γ(S)` is the
real, unproven content. -/
theorem gammaHullInitial_self (S : LRV.Substructure M) : M5Ledger.GammaHullInitial S S := by
  intro t ht hrv h0
  refine ⟨1, t, iRVOne (M := M), by norm_num, ht, hrv, h0, StandingTree.rv_one_units, ?_⟩
  show iRVMul (Assembly.rvPow t 0) t = iRVMul t iRVOne
  rw [show Assembly.rvPow t 0 = iRVOne (M := M) from rfl,
    MulNormalForm.rv_mul_one_all hM hrv, MulNormalForm.rv_mul_one_right hM hrv]

/-- **The `⊤`-witness of `DivisibilityStep` would have to satisfy the clamp at `⊤`**, i.e. it would
assert that every value of `M` has a positive power in the hull of `Γ(S)`: precisely the half of
`GammaHullInitial` that is *not* automatic (`gammaHullInitial_self` is the `T = S` case, where the
witness is the trivial one and the content has moved to `GammaDivisible S`). -/
theorem gammaHullInitial_top_content {S : LRV.Substructure M}
    (h : M5Ledger.GammaHullInitial S ⊤) :
    ∀ t : M, iRV t → t ≠ iRVZero →
      ∃ (n : ℕ) (s c : M), 0 < n ∧ s ∈ S ∧ iRV s ∧ s ≠ iRVZero ∧ iUnits c ∧
        Assembly.rvPow t n = iRVMul s c :=
  fun t hrv h0 => h t trivial hrv h0

/-- **The paper's Lemma 3.3 is *not* vacuous at `⊤`** — which is exactly what distinguishes it from
the frozen `PrepStepP`.  Clause (1) of `M6L33.Lemma33Clauses` (`VF(T) = VF(S)`) at `T = ⊤` forces
`S = ⊤`: so the paper's clause set excludes the `⊤`-witness that `Assembly.PrepStepP` accepts.
`M6L33.prepStepP_of_paperLemma33` gives the other direction, so the two obligations have genuinely
different solution sets and the frozen `PrepStepP` is the one that is satisfiable at `⊤`.  This is
the machine-checked form of the report's recommendation to reinstate the clauses if the paper's
content is to remain visible. -/
theorem paperLemma33Clauses_top {S : LRV.Substructure M}
    (h : M6L33.Lemma33Clauses (M := M) S ⊤) : S = ⊤ :=
  Assembly.eq_top_of_vf_all S (fun x hx => (h.2.1 x hx).1 trivial)

end Clamps

/-! ## 5. Hypothesis 1 (`ShoenfieldTestSat`) — the irreducible one -/

section Shoenfield

/-- `ShoenfieldTestSat` unfolds to the criterion applied to `Prop39Sat`; nothing in the audit
produces `HasQE Axioms.ACVF`, so it cannot be collapsed by a witness.  Its shape is recorded so that
the reduced FINAL's residual is visible. -/
theorem shoenfield_unfold :
    M7Paper.ShoenfieldTestSat = (M7Paper.Prop39Sat → HasQE Axioms.ACVF) := rfl

/-- The reduced FINAL *is* the criterion applied: with both hypotheses in hand the proof is the
application, and the audit's collapse leaves nothing else.  (Same term as `paper_theorem_FINAL3`,
stated to exhibit the rfl-level content of the reduction.) -/
theorem reduced_final_is_the_criterion (hShoen : M7Paper.ShoenfieldTestSat)
    (h39 : M7Paper.Prop39Sat) : HasQE Axioms.ACVF :=
  hShoen h39

end Shoenfield

/-! ## 6. Hypothesis 2 (input 1, `ACFExtends`) — not a closure statement -/

section ACFExtends
variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- Input 1's conclusion is an *existence of a ring homomorphism*, not a closure property, so the
`⊤`/`⊥`/unit witnesses that collapse `PrepStepP` do not even have the right type for it.  Its
cardinality content is `#K(M) ≤ #K(N)` (`M5Ledger.acfExtends_field_size`); recorded here in the
audit's own numbering so that §7 can use it. -/
theorem input1_field_size (h : M5Ledger.ACFExtends (M := M) (N := N))
    (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    Cardinal.mk (StandingField.KOf M) ≤ Cardinal.mk (StandingField.KOf N) :=
  M5Ledger.acfExtends_field_size h S f

end ACFExtends

/-! ## 7. The cardinality stress suite on the full conjunction

The seven-fold conjunction is only ever applied at `PaperHyp` pairs.  The audit below shows that
every cardinality inequality extractable from it is a consequence of `PaperHyp` alone — in
particular nothing forces `#N ≤ #M`, `#M = #N`, or a contradiction.  The single hypothesis that
forces size *without* a gate is `SaturationRealization`, and it forces exactly the size half of
`PaperHyp`, which the reduced FINAL keeps. -/

section CardinalAudit

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- `#K(M) ≤ #M`: the residue field is a subtype of the carrier. -/
theorem kof_size_le (M' : Type) [LRV.Structure M'] [M' ⊨ Axioms.ACVF] :
    Cardinal.mk (StandingField.KOf M') ≤ Cardinal.mk M' :=
  Cardinal.mk_subtype_le (fun x => iUnits x ∨ x = iRVZero)

/-- **The gate is never cardinally empty**: the size half holds reflexively at the diagonal, so no
impossible size statement can be hidden in `PaperHyp`'s second conjunct alone. -/
theorem sizeHyp_self (M' : Type) : M7Paper.SizeHyp M' M' :=
  le_refl _

/-- **Every cardinality consequence of the seven, from the gate alone.**  This is the audit's
negative result: the seven-fold conjunction forces no size statement that `PaperHyp` does not
already force.  (Proof: all three are subtypes of `M` embedded into `N` via `#M ≤ #N`.) -/
theorem paperHyp_cardinal_content (hP : M7Paper.PaperHyp M N) :
    Cardinal.mk M ≤ Cardinal.mk N ∧
      Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N ∧
      Cardinal.mk (StandingField.KOf M) ≤ Cardinal.mk N := by
  refine ⟨hP.2, ?_, ?_⟩
  · exact le_trans (Cardinal.mk_subtype_le (fun x => iUnits x)) hP.2
  · exact le_trans (kof_size_le M) hP.2

/-- **The full conjunction's size content is the gate's size content.**  Taking the seven hypotheses
plus the gate at a pair yields nothing beyond `paperHyp_cardinal_content` — the audit's check that
the seven are jointly size-consistent. -/
theorem full_conj_cardinal_content (_h : FinalRoute.FinalHyp) (hP : M7Paper.PaperHyp M N) :
    Cardinal.mk M ≤ Cardinal.mk N ∧
      Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N ∧
      Cardinal.mk (StandingField.KOf M) ≤ Cardinal.mk N :=
  paperHyp_cardinal_content hP

/-- **The one hypothesis that forces size is input 5, and it is refutable without the gate**:
`SaturationRealization` yields `#M ≤ #N`, so at a pair with `#N < #M` it fails (any single partial
embedding `S ↪[LRV] N` is enough to run the argument).  This is the exact sense in which the
saturation input needs `PaperHyp`, and it survives the collapse of §2: the reduced FINAL still uses
`LedgerInput5P`, i.e. it is still gated. -/
theorem not_saturationRealization_of_lt (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (hlt : Cardinal.mk N < Cardinal.mk M) :
    ¬ M5Ledger.SaturationRealization (M := M) (N := N) := by
  intro h5
  exact absurd (M5Ledger.saturationRealization_forces_size (M := M) (N := N) h5 S f)
    (not_le.mpr hlt)

end CardinalAudit

/-! ## 8. The same collapse on the frozen `SizeHyp` route, and why the `PaperHyp` gate matters

`M5Ledger` also states the five inputs at the frozen §9 guard `SizeHyp` (`LedgerInput1` …
`LedgerInput5`), and those are the hypotheses of `M5Ledger.paper_theorem_2_3_sat_of_ledger`.  The
same `⊤` mechanism applies, so the §9 route also reduces to input 5 alone — but there input 5 is
*gated too weakly*: it forces `Hahn.OneStepSizeBounded`, which m7's Archimedean obstruction refutes.
So the §9 form of input 5 is a **false statement** (given m7's witness configuration), and this is
exactly the reason the FINAL must use the `PaperHyp`-gated `LedgerInput5P`.  The audit records both
halves: the reduction, and the refutation. -/

section LedgerRoute

/-- `LedgerInput5` (the §9 form) gives `M7Paper.PrepStepSize` on its own. -/
theorem prepStepSize_of_ledgerInput5 (h5 : M5Ledger.LedgerInput5) : M7Paper.PrepStepSize := by
  intro M' N' _ _ _ _ hSize S f
  exact prepStepP_of_saturationRealization (h5 M' N' hSize) S f

/-- `LedgerInput5` gives the size-bounded one-step `Hahn.OneStepSizeBounded` on its own. -/
theorem oneStepSizeBounded_of_ledgerInput5 (h5 : M5Ledger.LedgerInput5) :
    Hahn.OneStepSizeBounded := by
  intro M' N' _ _ _ _ hSize S f hS m hm
  exact oneStepVFP_of_saturationRealization (h5 M' N' hSize) S f hS m hm

/-- `LedgerInput5` gives `M7Paper.Prop39Size` (Proposition 3.9 at the frozen `SizeHyp` guard) on its
own. -/
theorem prop39Size_of_ledgerInput5 (h5 : M5Ledger.LedgerInput5) : M7Paper.Prop39Size := by
  intro M' N' _ _ _ _ hSize S f
  exact total_extension_of_saturationRealization (h5 M' N' hSize) S f

/-- **The §9 form of input 5 is refutable.**  It forces `Hahn.OneStepSizeBounded`, which
`Hahn.not_oneStepSizeBounded` refutes at any pair carrying a `RoomObstruction` into an Archimedean
target of at least `M`'s size (m7's witness pair `ℂ((t^{ℚ²}))`, `ℂ((t^ℚ))`).  So `LedgerInput5` is
*not* a consequence of `ACVF` at `SizeHyp` pairs, and the `PaperHyp` gate is not cosmetic — which is
why the reduced FINAL of §2 is stated with the `P`-form. -/
theorem not_ledgerInput5_of_roomObstruction {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : Hahn.RoomObstruction M N) (hArch : Hahn.ArchimedeanRV N)
    (hSize : M7Paper.SizeHyp M N) : ¬ M5Ledger.LedgerInput5 :=
  fun h5 => Hahn.not_oneStepSizeBounded h hArch hSize (oneStepSizeBounded_of_ledgerInput5 h5)

/-- `ShoenfieldTestSat` implies its `SizeHyp` form (a `PaperHyp` pair is `SizeHyp`). -/
theorem shoenfieldTestSize_of_shoenfieldTestSat (h : M7Paper.ShoenfieldTestSat) :
    M7Paper.ShoenfieldTestSize :=
  fun hSize => h (fun M N _ _ _ _ hP => hSize M N hP.2)

/-- **The §9/§10 route also reduces to two hypotheses** — the same collapse, one gate weaker.
(Read together with `not_ledgerInput5_of_roomObstruction`: this form is *vacuous* at m7's pair, which
is the precise sense in which the FINAL's `P`-form is the honest one.) -/
theorem paper_theorem_2_3_sat_of_input5 (hShoen : M7Paper.ShoenfieldTestSat)
    (h5 : M5Ledger.LedgerInput5) : HasQE Axioms.ACVF :=
  shoenfieldTestSize_of_shoenfieldTestSat hShoen (prop39Size_of_ledgerInput5 h5)

/-- And the §9 route's own statement, `M5Ledger.paper_theorem_2_3_sat_of_ledger`, with its five
inputs, `ImmediateLift` and the henselian-domain one-step reduced to input 5 alone: all seven of
its hypotheses except `hShoen` and `h5` are bound and unused. -/
theorem paper_theorem_2_3_sat_of_ledger_shrunk (hShoen : M7Paper.ShoenfieldTestSat)
    (h1 : M5Ledger.LedgerInput1) (h2 : M5Ledger.LedgerInput2) (h3 : M5Ledger.LedgerInput3)
    (h4 : M5Ledger.LedgerInput4) (h5 : M5Ledger.LedgerInput5)
    (hL : M7Hens.ImmediateLift)
    (hOne : ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF]
      [Q ⊨ Axioms.ACVF] (S : LRV.Substructure P) (f : S ↪[LRV] Q),
      Assembly.Standing S → M7Hens.IsHenselianVF S → ∀ m : P, iVF m →
        ∃ (T : LRV.Substructure P) (g : T ↪[LRV] Q) (hST : S ≤ T),
          (∀ x : S, g ⟨(x : P), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T) :
    HasQE Axioms.ACVF :=
  paper_theorem_2_3_sat_of_input5 hShoen h5

end LedgerRoute

end FinalAudit
end Milestone0
end SpecialTransformations

#print axioms SpecialTransformations.Milestone0.FinalAudit.standing_top
#print axioms SpecialTransformations.Milestone0.FinalAudit.prepStepP_of_saturationRealization
#print axioms SpecialTransformations.Milestone0.FinalAudit.oneStepVFP_of_saturationRealization
#print axioms SpecialTransformations.Milestone0.FinalAudit.total_extension_of_saturationRealization
#print axioms SpecialTransformations.Milestone0.FinalAudit.prepStepPaper_of_ledgerInput5P
#print axioms SpecialTransformations.Milestone0.FinalAudit.oneStepPaper_of_ledgerInput5P
#print axioms SpecialTransformations.Milestone0.FinalAudit.prop39Sat_of_ledgerInput5P
#print axioms SpecialTransformations.Milestone0.FinalAudit.paper_theorem_FINAL2
#print axioms SpecialTransformations.Milestone0.FinalAudit.paper_theorem_FINAL_of_input5
#print axioms SpecialTransformations.Milestone0.FinalAudit.paper_theorem_FINAL_flat_shrunk
#print axioms SpecialTransformations.Milestone0.FinalAudit.prop39Sat_FINAL_of_input5
#print axioms SpecialTransformations.Milestone0.FinalAudit.FINAL_telescope_matches
#print axioms SpecialTransformations.Milestone0.FinalAudit.FINAL_telescope_matches_shrunk
#print axioms SpecialTransformations.Milestone0.FinalAudit.saturationRealization_of_total_extension
#print axioms SpecialTransformations.Milestone0.FinalAudit.ledgerInput5P_of_prop39Sat
#print axioms SpecialTransformations.Milestone0.FinalAudit.ledgerInput5P_iff_prop39Sat
#print axioms SpecialTransformations.Milestone0.FinalAudit.paper_theorem_FINAL3
#print axioms SpecialTransformations.Milestone0.FinalAudit.FINAL2_iff_FINAL3
#print axioms SpecialTransformations.Milestone0.FinalAudit.residueStep_vf_clause_at_top
#print axioms SpecialTransformations.Milestone0.FinalAudit.immediate_top_iff
#print axioms SpecialTransformations.Milestone0.FinalAudit.paperLemma33Clauses_top
#print axioms SpecialTransformations.Milestone0.FinalAudit.gammaHullInitial_self
#print axioms SpecialTransformations.Milestone0.FinalAudit.gammaHullInitial_top_content
#print axioms SpecialTransformations.Milestone0.FinalAudit.shoenfield_unfold
#print axioms SpecialTransformations.Milestone0.FinalAudit.reduced_final_is_the_criterion
#print axioms SpecialTransformations.Milestone0.FinalAudit.input1_field_size
#print axioms SpecialTransformations.Milestone0.FinalAudit.kof_size_le
#print axioms SpecialTransformations.Milestone0.FinalAudit.sizeHyp_self
#print axioms SpecialTransformations.Milestone0.FinalAudit.paperHyp_cardinal_content
#print axioms SpecialTransformations.Milestone0.FinalAudit.full_conj_cardinal_content
#print axioms SpecialTransformations.Milestone0.FinalAudit.not_saturationRealization_of_lt
#print axioms SpecialTransformations.Milestone0.FinalAudit.prepStepSize_of_ledgerInput5
#print axioms SpecialTransformations.Milestone0.FinalAudit.oneStepSizeBounded_of_ledgerInput5
#print axioms SpecialTransformations.Milestone0.FinalAudit.prop39Size_of_ledgerInput5
#print axioms SpecialTransformations.Milestone0.FinalAudit.not_ledgerInput5_of_roomObstruction
#print axioms SpecialTransformations.Milestone0.FinalAudit.shoenfieldTestSize_of_shoenfieldTestSat
#print axioms SpecialTransformations.Milestone0.FinalAudit.paper_theorem_2_3_sat_of_input5
#print axioms SpecialTransformations.Milestone0.FinalAudit.paper_theorem_2_3_sat_of_ledger_shrunk
