/-
# g3 — The hull-collapse composition: what Proposition 3.9 costs, and what it does not

Swarm `smw2ku6gn`, member m3, direction d2/g3.  The question this file answers, machine-checked:

> `StandingHullRoute.prepStepP_iff_hullExtension` computes Proposition 3.9 through the *hull*.
> Is the hull-computed `Prop39Sat` derivable from `SaturationRealization` directly at gated pairs —
> and hence does `Prop39Sat` need the case lemmas 3.4/3.6 at all?

## The answers (machine-checked)

* **§1 `extendsHere_iff_hullExtension_and_oneStep`** — at a *fixed pair* of models, Proposition 3.9
  (`lrv:mono:lift`, the extension property) is **equivalent** to

      HullExtension  ∧  Assembly.OneStepVFP,      i.e.
      Lemma 3.3 (hull form)  ∧  Lemmas 3.4–3.8 (one-step)

  and `extendsHere_iff_hullExtension_and_cases` replaces the one-step by the paper's own case split
  (`M4Cases.Cases`: `lift:all:root` / `lift:divisible:hull` / new-`rv`).  No gate, no saturation and
  no size hypothesis appears in either direction.  **So the case lemmas enter at `OneStepVFP`, and
  nowhere else**: they are one of the two conjuncts, not a detour on the way to the hull.
  (This is the exact answer to "do the case lemmas enter only at smaller `S` via OneStepCases' Slot
  forms": they enter only as the one-step, which the hull route feeds to `prop39P_noVFGen`.)

* **§1.1 the collapse** — `extendsHere_of_satReal` : `SaturationRealization` alone gives the *total*
  extension, by `T = ⊤` (`M5Ledger`'s own `saturationRealization_forces_size` applies the hypothesis
  at `⊤`).  Hence `HullExtension` is *not needed* (`hullExtension_of_satReal`), the one-step is *not
  needed*, and `Assembly.PrepStepP`/`OneStepVFP`/`Standing ⊤` are all bypassed.  So
  `Prop39Sat` — the paper's Proposition 3.9 at the paper's own hypothesis — needs **no** case
  analysis once input 5 (Marker's saturated realisation) is granted.  The hull computation is a
  *decomposition of the conjunction*, not a proof of its content.

* **§2–§3 the honest-gate route** — at `relGate` (`M1Fix.SatRel ∧ #M ≤ #N`, `QE/ShoenfieldQuote.lean`)

      extendsAt_rel_iff_input5R : M5Shoenfield.ExtendsAt relGate ↔ M5Shoenfield.Input5R
      paper_theorem_rel_two      : ShoenfieldTestRel → Input5R → HasQE Axioms.ACVF

  and (`qfsat_of_satRel_of_qffinsat`, new here) `SatRel` + `QFFinSat` gives qf-type realisation
  pair-relatively, which yields

      paper_theorem_rel_of_qffinsat :
        ShoenfieldTestRel → (∀ relGate pairs, QFFinSat) → HasQE Axioms.ACVF.

* **§5 exactness** — `satReal_iff_hullExtension_and_oneStep` : input 5 is *equivalent* to Lemma 3.3
  (hull form) ∧ Lemmas 3.4–3.8 (one-step); hence `ledgerInput5P_iff_gated_hullExtension_and_oneStep`
  (the canonical frontier `Prop39Sat` ⟺ the paper's two §3 obligations at the paper's pairs) and
  `input5R_iff_gated_hullExtension_and_oneStep`.  The case lemmas are therefore not a way around
  input 5 — they are an equivalent rewriting of it, and `Prop39Sat` needs them exactly when input 5
  is not assumed.

## Where the hypotheses really go (the demand table, each row a theorem below)

| step | consumes |
|---|---|
| `prop39P_noVFGen` (the join) | nothing (`⊤`-witness of `PrepStepP`/`OneStepVFP`) |
| `extendsHere_iff_hullExtension_and_oneStep` | nothing |
| `extendsHere_of_satReal` | `SaturationRealization`, no gate |
| `qfsat_of_satRel_of_qffinsat` | `SatRel` + `QFFinSat`, no size |
| `extendsHere_forces_size` | — *produces* `#M ≤ #N` |
| `hullExtension_forces_units_size` | — *produces* `#Kˣ(M) ≤ #N` only |
| `extendsAt_rel_iff_input5R` | the gate indexes the hypotheses only: the proof is pointwise, and neither direction decomposes it |

Three machine-checked refutations show each gate conjunct is nevertheless load-bearing:

* **(no gate)** `not_extendsHere_of_archimedean` — at an Archimedean target carrying the
  infinitesimal configuration the extension property **fails** (`Hahn.not_embAt_of_infinitesimal`),
  so `ExtendsAt (fun _ _ _ _ => True)` is false (`not_forall_extendsHere_of_archimedean`) and
  `Prop39Sat` itself is refutable at any `PaperHyp` pair with such a configuration
  (`not_prop39Sat_of_archimedean_config`).  This is the exact interaction with `QE/HahnAnatomy.lean`
  §2 and with `FinalAudit` §4: the ⊤-witness is legitimate *because* Proposition 3.9 carries no
  clamp, and the paper's own gate does not exclude the configuration.
* **(size)** `FinalAudit.not_saturationRealization_of_lt` — dropping `#M ≤ #N` makes the conclusion
  produce it at every pair, hence refutable at pairs with `#N < #M`; the hull form produces only the
  *units* size, which is `M7Paper.prepStepP_forces_units_size`.
* **(finite satisfiability)** `not_finSat_at_pair_of_archimedean` — at a `SaturatedFS`
  Archimedean target with the configuration, `QFFinSat` **fails** (`Hahn.not_finSat_of_archimedean`),
  so the `QFFinSat`-at-`PaperHyp` hypothesis of `QE/QFRoute.lean` is not a theorem at every gated
  pair (`not_forall_qffinsat_at_paperGate`): the case lemmas cannot prove it globally, only under
  `¬ ArchimedeanRV N` (`not_archimedeanRV_of_paperHyp_of_config`) — or at the pairs where the paper's
  configuration does not occur.

Everything is `exit 0`, no `sorry`/`admit`/`native_decide`, no new axiom; the axiom audit is at the
end of the file.
-/
import FinalAudit
import SatReal
import ShoenfieldQuote
import HahnAnatomy
import StandingHull
import OneStepCases

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations
namespace Milestone0
namespace G3

/-! ## 1. Proposition 3.9 at a fixed pair, and its exact decomposition

`ExtendsHere` is `lrv:mono:lift` at one pair, with no gate: every embedding of a substructure of `M`
extends to an embedding of `M`.  This is the pair-level form of `M7Paper.Prop39Sat`. -/

section Pair

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-- **Proposition 3.9 at the pair** (`lrv:mono:lift`), off the gate. -/
def ExtendsHere (M N : Type) [LRV.Structure M] [LRV.Structure N] : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x

variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-! ### 1.1 The collapse: `SaturationRealization` gives it outright -/

/-- **Input 5 gives Proposition 3.9 at the pair, with no hull and no one-step.**  The whole proof is
`SaturationRealization` applied at `T = ⊤` (inside `FinalAudit`); `HullExtension`, `PrepStepP`,
`OneStepVFP` and `Standing ⊤` are all bypassed. -/
theorem extendsHere_of_satReal (h : M5Ledger.SaturationRealization (M := M) (N := N)) :
    ExtendsHere M N :=
  fun S f => FinalAudit.total_extension_of_saturationRealization h S f

/-- The converse: a total extension restricts to any `T ≥ S`, so input 5 is *not* weaker than the
extension property.  (This is `FinalAudit.saturationRealization_of_total_extension`.) -/
theorem satReal_of_extendsHere (h : ExtendsHere M N) :
    M5Ledger.SaturationRealization (M := M) (N := N) :=
  FinalAudit.saturationRealization_of_total_extension h

/-- **At a fixed pair, Proposition 3.9 *is* `SaturationRealization`** — the pair-level form of
`FinalAudit.ledgerInput5P_iff_prop39Sat`. -/
theorem extendsHere_iff_satReal :
    ExtendsHere M N ↔ M5Ledger.SaturationRealization (M := M) (N := N) :=
  ⟨satReal_of_extendsHere, extendsHere_of_satReal⟩

/-- The size content of the conclusion: any `ExtendsHere` forces `#M ≤ #N`.  This is why the gate's
size conjunct is a *consequence* of the conclusion rather than a consumption of the proof. -/
theorem extendsHere_forces_size (h : ExtendsHere M N) (S : LRV.Substructure M)
    (f : S ↪[LRV] N) : Cardinal.mk M ≤ Cardinal.mk N := by
  obtain ⟨g, _⟩ := h S f
  exact Cardinal.mk_le_of_injective (Embedding.injective g)

/-! ### 1.2 The hull form of Lemma 3.3

`HullExtension` is `StandingHullRoute.HullExtension`: every monomorphism out of `S` extends to the
*fixed* hull `M8Hull.standingHull S`.  (Restated here because `StandingHullRoute.lean` has no
compiled olean in the route's `LEAN_PATH`; the statement and the two equivalences are its own.) -/

/-- **Lemma 3.3, hull form**: every monomorphism `S ↪ N` extends to the standing hull of `S`. -/
def HullExtension (M N : Type) [LRV.Structure M] [LRV.Structure N]
    [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF] : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
    ∃ g : M8Hull.standingHull S ↪[LRV] N,
      ∀ x : S, g ⟨(x : M), M8Hull.le_standingHull S x.2⟩ = f x

/-- `HullExtension` gives the frozen `PrepStepP`: the hull is `Standing` and contains `S`. -/
theorem prepStepP_of_hullExtension (h : HullExtension (M := M) (N := N)) :
    Assembly.PrepStepP (M := M) (N := N) := by
  intro S f
  obtain ⟨g, hg⟩ := h S f
  exact ⟨M8Hull.standingHull S, g, M8Hull.le_standingHull S, hg, M8Hull.standing_standingHull S⟩

/-- Conversely, `PrepStepP` gives `HullExtension`: its witness `T` is `Standing` and contains `S`,
hence contains the hull, and the extension restricts. -/
theorem hullExtension_of_prepStepP (h : Assembly.PrepStepP (M := M) (N := N)) :
    HullExtension (M := M) (N := N) := by
  intro S f
  obtain ⟨T, g, hST, hagree, hStand⟩ := h S f
  have hle : M8Hull.standingHull S ≤ T := M8Hull.standingHull_le hST hStand
  refine ⟨g.comp (Substructure.inclusion hle), ?_⟩
  intro x
  have h1 : (Substructure.inclusion hle) ⟨(x : M), M8Hull.le_standingHull S x.2⟩
      = ⟨(x : M), hST x.2⟩ := rfl
  show g ((Substructure.inclusion hle) ⟨(x : M), M8Hull.le_standingHull S x.2⟩) = f x
  rw [h1]
  exact hagree x

/-- **`PrepStepP` is the hull extension statement** (`StandingHullRoute.prepStepP_iff_hullExtension`). -/
theorem prepStepP_iff_hullExtension :
    Assembly.PrepStepP (M := M) (N := N) ↔ HullExtension (M := M) (N := N) :=
  ⟨hullExtension_of_prepStepP, prepStepP_of_hullExtension⟩

/-- **The hull adds nothing once input 5 is granted**: `SaturationRealization` gives `HullExtension`
by applying the hypothesis at `T := standingHull S`.  (Compare `extendsHere_of_satReal`: the same
hypothesis gives the total extension at `T := ⊤`, which is strictly stronger and needs no hull.) -/
theorem hullExtension_of_satReal (h : M5Ledger.SaturationRealization (M := M) (N := N)) :
    HullExtension (M := M) (N := N) :=
  fun S f => h S (M8Hull.standingHull S) f (M8Hull.le_standingHull S)

/-- The total extension restricts to the hull, so the hull form is implied by Proposition 3.9. -/
theorem hullExtension_of_extendsHere (h : ExtendsHere M N) : HullExtension (M := M) (N := N) := by
  intro S f
  obtain ⟨g, hg⟩ := h S f
  exact ⟨g.domRestrict (M8Hull.standingHull S), fun x => hg x⟩

/-- **The size content of the hull form**: `HullExtension` forces only `#Kˣ(M) ≤ #N`, never
`#M ≤ #N`.  (Proof through `PrepStepP`, `M7Paper.prepStepP_forces_units_size`.)  This is the
machine-checked measure of the gap between the hull form and Proposition 3.9. -/
theorem hullExtension_forces_units_size (h : HullExtension (M := M) (N := N))
    (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N :=
  M7Paper.prepStepP_forces_units_size (prepStepP_of_hullExtension h) S f

/-! ### 1.3 The exact composition: Proposition 3.9 = Lemma 3.3 ∧ Lemmas 3.4–3.8 -/

/-- The one-step is implied by the extension property (`T = ⊤`, `Standing ⊤`).  So the one-step is
not an extra assumption on top of Proposition 3.9 — it is one of its two halves. -/
theorem oneStepVFP_of_extendsHere (h : ExtendsHere M N) :
    Assembly.OneStepVFP (M := M) (N := N) := by
  intro S f _hStand m _hm
  obtain ⟨g, hg⟩ := h S f
  exact ⟨⊤, g.domRestrict ⊤, fun _ _ => trivial, fun x => hg x, trivial, FinalAudit.standing_top⟩

/-- **Proposition 3.9 from the hull form and the one-step** — the `⊤`-join
(`Assembly.prop39P_noVFGen`), read as: the two frozen §3 conclusions compose to the paper's
Proposition 3.9 at the pair. -/
theorem extendsHere_of_hullExtension_of_oneStep (hHull : HullExtension (M := M) (N := N))
    (hOne : Assembly.OneStepVFP (M := M) (N := N)) : ExtendsHere M N :=
  fun S f => Assembly.prop39P_noVFGen (prepStepP_of_hullExtension hHull) hOne S f

/-- **THE COMPOSITION THEOREM.**  At a fixed pair of models of `ACVF`, Proposition 3.9 is
*equivalent* to Lemma 3.3 (hull form) together with the one-step obligation of Lemmas 3.4–3.8.
Neither direction uses a gate, a saturation hypothesis or a size hypothesis.  So the case lemmas are
exactly the missing conjunct when input 5 is not assumed — and exactly what input 5 makes
unnecessary (`extendsHere_of_satReal`). -/
theorem extendsHere_iff_hullExtension_and_oneStep :
    ExtendsHere M N ↔
      HullExtension (M := M) (N := N) ∧ Assembly.OneStepVFP (M := M) (N := N) :=
  ⟨fun h => ⟨hullExtension_of_extendsHere h, oneStepVFP_of_extendsHere h⟩,
    fun h => extendsHere_of_hullExtension_of_oneStep h.1 h.2⟩

/-- **The same identity with the paper's own case split**: Proposition 3.9 ⟺ Lemma 3.3 (hull form)
∧ `M4Cases.Cases` (`lift:all:root` ∧ `lift:divisible:hull` ∧ the new-`rv` branch).  This is where
`QE/OneStepCases.lean`'s Slot forms enter the composition — as the second conjunct, nothing else. -/
theorem extendsHere_iff_hullExtension_and_cases :
    ExtendsHere M N ↔
      HullExtension (M := M) (N := N) ∧ M4Cases.Cases (M := M) (N := N) := by
  constructor
  · intro h
    exact ⟨hullExtension_of_extendsHere h, M4Cases.cases_of_global_extension h⟩
  · rintro ⟨hHull, hCases⟩
    exact extendsHere_of_hullExtension_of_oneStep hHull (M4Cases.oneStepVFP_of_cases hCases)

end Pair

/-!
## 2. The honest gate: `relGate` and the two-hypothesis routes

`M5Shoenfield.relGate M N = M1Fix.SatRel M N ∧ #M ≤ #N` is the paper's §3.1 hypothesis
pair-relatively (`QE/ShoenfieldQuote.lean` §1).  Everything below is stated at that gate; the frozen
`paperGate` (`Assembly.SaturatedFS N ∧ #M ≤ #N`) is *smaller* (its saturation conjunct is the
`∀ M`-quantified one), so `paperGate → relGate` is `M5Shoenfield.paperGate_le_relGate`, and every
`paperGate` statement is recovered from the `relGate` one (§2.2).
-/

section Gates

/-- **The collapse at the honest gate**: `Input5R` (Marker's saturated realisation, gated at
`relGate`) gives the extension property at `relGate` — with no case analysis, no hull, and no
`Standing`.  Pointwise this is `extendsHere_of_satReal`. -/
theorem extendsAt_rel_of_input5R (h : M5Shoenfield.Input5R) :
    M5Shoenfield.ExtendsAt M5Shoenfield.relGate := by
  intro M N _ _ _ _ hR S f
  exact extendsHere_of_satReal (h M N hR) S f

/-- The converse: the extension property at `relGate` gives `Input5R` (restrict the total embedding
to `T`).  So at the honest gate, Marker's saturated realisation and the paper's Proposition 3.9 are
*the same statement* — the `relGate` form of `FinalAudit.ledgerInput5P_iff_prop39Sat`. -/
theorem input5R_of_extendsAt_rel (h : M5Shoenfield.ExtendsAt M5Shoenfield.relGate) :
    M5Shoenfield.Input5R := by
  intro M N _ _ _ _ hR
  exact satReal_of_extendsHere (fun S f => h M N hR S f)

/-- **`Input5R` ⟺ Proposition 3.9 at `relGate`.** -/
theorem extendsAt_rel_iff_input5R :
    M5Shoenfield.ExtendsAt M5Shoenfield.relGate ↔ M5Shoenfield.Input5R :=
  ⟨input5R_of_extendsAt_rel, extendsAt_rel_of_input5R⟩

/-- A `relGate` hypothesis is a `paperGate` hypothesis, so `Input5R` gives the frozen
`LedgerInput5P`.  (The converse is false and must be: `relGate` is the larger gate.) -/
theorem ledgerInput5P_of_input5R (h : M5Shoenfield.Input5R) : M5Ledger.LedgerInput5P :=
  fun M N _ _ _ _ hP => h M N (M5Shoenfield.paperGate_le_relGate M N hP)

/-- **THE TWO-HYPOTHESIS FINAL AT THE HONEST GATE.**  Shoenfield's test (quoted,
`M5Shoenfield.ShoenfieldTestRel`) plus Marker's saturated realisation at `relGate`
(`M5Shoenfield.Input5R`) give quantifier elimination.  The paper's Lemmas 3.3–3.9 are *derived*
inside (`extendsAt_rel_of_input5R`), not assumed: the case lemmas 3.4/3.6 do not occur. -/
theorem paper_theorem_rel_two (hQ : M5Shoenfield.ShoenfieldTestRel)
    (h5 : M5Shoenfield.Input5R) : HasQE Axioms.ACVF :=
  hQ (extendsAt_rel_of_input5R h5)

/-- The same two hypotheses with the frozen gate's criterion: `ShoenfieldTestSat +
Input5R`.  (`Input5R` implies the frozen `LedgerInput5P`, and `FinalAudit.paper_theorem_FINAL2`
consumes only the latter.) -/
theorem paper_theorem_sat_via_input5R (hShoen : M7Paper.ShoenfieldTestSat)
    (h5 : M5Shoenfield.Input5R) : HasQE Axioms.ACVF :=
  FinalAudit.paper_theorem_FINAL2 hShoen (ledgerInput5P_of_input5R h5)

/-- For the record, in the canonical frontier's own shape (`paperGate`): the frozen
`paper_theorem_FINAL2` is `ShoenfieldTestSat + LedgerInput5P`.  Nothing here changes it; it is
restated so that the two gates' versions can be compared side by side. -/
theorem paper_theorem_sat_two (hShoen : M7Paper.ShoenfieldTestSat)
    (h5 : M5Ledger.LedgerInput5P) : HasQE Axioms.ACVF :=
  FinalAudit.paper_theorem_FINAL2 hShoen h5

end Gates

/-!
## 3. Where the finite-satisfiability content enters

`M2Saturation.QFFinSat` is the finite satisfiability of the pushed type — the `ACVF` content
(`QE/SatReal.lean`, `QE/QFRoute.lean`).  `SatReal.qfsat_of_saturatedFS` turns it into qf-type
realisation only under the frozen `∀ M`-quantified `SaturatedFS N`.  At the honest gate the saturation
input is `M1Fix.SatRel M N`, and the bridge is the same one line: `SatRel` *is* "finitely satisfiable
⟹ realised" at the pair.  The lemma below is that bridge; it is what lets the `QFFinSat` route run at
`relGate` instead of `paperGate`.
-/

section FinSat

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-- **`SatRel` + `QFFinSat` ⟹ qf-type realisation, pair-relatively.**  `M1Fix.SatRel` realises a
pushed type from a finite-satisfiability hypothesis; `QFFinSat` supplies that hypothesis;
`Hahn.realizesAtomic_of_forall` reads the atomic type off the full realisation.  No `ACVF`, no size,
no `∀ M` gate. -/
theorem qfsat_of_satRel_of_qffinsat (hSat : M1Fix.SatRel M N)
    (hfin : M2Saturation.QFFinSat M N) : M2Saturation.QFSat M N :=
  fun S f m => by
    obtain ⟨b, hb⟩ := hSat S f m (hfin S f m)
    exact ⟨b, Hahn.realizesAtomic_of_forall S f m b hb⟩

end FinSat

section FinSatGate

/-- **The `QFFinSat`-gated input 5 at the honest gate**: finite satisfiability of the pushed types at
`relGate` pairs gives `Input5R`.  This is the `relGate` form of
`M2Saturation.ledgerInput5P_of_saturatedFS_finSat`, and it is *weaker* in hypotheses (it never asks
for `Assembly.SaturatedFS`). -/
theorem input5R_of_relGate_finSat
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → M2Saturation.QFFinSat M N) :
    M5Shoenfield.Input5R := by
  intro M N _ _ _ _ hR
  exact M2Saturation.satReal_of_qfsat
    (qfsat_of_satRel_of_qffinsat hR.1 (hfin M N hR))

/-- The extension property at `relGate` from `QFFinSat` there. -/
theorem extendsAt_rel_of_finSat
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → M2Saturation.QFFinSat M N) :
    M5Shoenfield.ExtendsAt M5Shoenfield.relGate :=
  extendsAt_rel_of_input5R (input5R_of_relGate_finSat hfin)

/-- **Theorem 2.3 from Shoenfield's test and finite satisfiability of the pushed types.**  Two
hypotheses: the quotation, and the `ACVF` content of the case lemmas in `QFFinSat` form.  Compared
with `QE/QFRoute.lean`'s `paper_theorem_2_3_sat_of_qf`, the inputs 2, 3, 4 and the one-step are gone
(`FinalAudit` §2 shows the collapse does not use them). -/
theorem paper_theorem_rel_of_qffinsat (hQ : M5Shoenfield.ShoenfieldTestRel)
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → M2Saturation.QFFinSat M N) :
    HasQE Axioms.ACVF :=
  hQ (extendsAt_rel_of_finSat hfin)

/-- The frozen-gate (`paperGate`) version of the same step, for comparison: the `QFFinSat` route at
`PaperHyp` collapses through `FinalAudit.paper_theorem_FINAL2`, i.e. the `QFFinSat` content *is* input
5 at the paper's gate. -/
theorem paper_theorem_sat_of_qffinsat (hShoen : M7Paper.ShoenfieldTestSat)
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M7Paper.PaperHyp M N → M2Saturation.QFFinSat M N) :
    HasQE Axioms.ACVF :=
  FinalAudit.paper_theorem_FINAL2 hShoen
    (M2Saturation.ledgerInput5P_of_saturatedFS_finSat hfin)

end FinSatGate

/-!
## 4. Stress tests: each gate conjunct is load-bearing, and the frontier is refutable without it

The three refutations below are the machine-checked evidence for the demand table in the header.
None of them needs a concrete model of `ACVF`: each is conditional on a configuration (an
infinitesimal over a substructure, `QE/HahnAnatomy.lean` §2) at a pair of models, which is exactly the
form in which `QE/HahnObstruction.lean` and `QE/HahnAnatomy.lean` record m7's obstruction.
-/

section Refutations

variable {M N : Type} [LRV.Structure M] [LRV.Structure N] [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **(no gate) Proposition 3.9 fails at an Archimedean target carrying the infinitesimal
configuration.**  A total extension `g` of `f` would give the embedding half `Hahn.EmbAt S f m` of the
one-step at `m` (`T = ⊤`), which `Hahn.not_embAt_of_infinitesimal` refutes.  So the extension property
is not a theorem at all pairs — the gate is not decoration. -/
theorem not_extendsHere_of_archimedean (hArch : Hahn.ArchimedeanRV N)
    {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmVF : iVF m) (hmS : m ∉ S) (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s) :
    ¬ ExtendsHere M N := by
  intro h
  obtain ⟨g, hg⟩ := h S f
  exact Hahn.not_embAt_of_infinitesimal hArch hsS hsRV hsne hsgt hmVF hmS hmgt hinf
    ⟨⊤, g.domRestrict ⊤, fun _ _ => trivial, fun x => hg x, trivial⟩

/-- The same at the empty gate: `M5Shoenfield.ExtendsAt (fun _ _ _ _ => True)` is false.  So no route
can drop the gate from Proposition 3.9 — in particular `M1Fix.Prop39FS`'s `SaturatedFS` and
`Prop39Sat`'s `PaperHyp` are both doing work, and the `⊤`-witness of `FinalAudit` §1 is legitimate
only because the *statement* carries no clamp (no `Immediate`, no `VF(T) = VF(S)`, no
`GammaHullInitial`), not because such clamps would be satisfiable at `⊤`. -/
theorem not_forall_extendsHere_of_archimedean (hArch : Hahn.ArchimedeanRV N)
    {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmVF : iVF m) (hmS : m ∉ S) (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s) :
    ¬ (∀ (M' N' : Type) [LRV.Structure M'] [LRV.Structure N']
        [M' ⊨ Axioms.ACVF] [N' ⊨ Axioms.ACVF], ExtendsHere M' N') :=
  fun h => not_extendsHere_of_archimedean (S := S) (f := f) hArch hsS hsRV hsne hsgt hmVF hmS hmgt hinf
    (h M N)

/-- **Proposition 3.9 at `relGate` fails at an Archimedean `SatRel` pair carrying the
configuration.**  Consequently `M5Shoenfield.Input5R` is *false* at such a pair: the honest gate's
saturation conjunct does not by itself exclude the configuration.  (The paper's *strong* saturation,
`Assembly.Saturated`, is what excludes it — via `Hahn.not_archimedeanRV_of_saturatedFS_of_config`
once finite satisfiability is granted; `SatRel` alone does not.) -/
theorem not_extendsAt_rel_of_archimedean_config (hSat : M1Fix.SatRel M N)
    (hsize : M7Paper.SizeHyp M N) (hArch : Hahn.ArchimedeanRV N)
    {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmVF : iVF m) (hmS : m ∉ S) (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s) :
    ¬ M5Shoenfield.ExtendsAt M5Shoenfield.relGate :=
  fun h => not_extendsHere_of_archimedean (S := S) (f := f) hArch hsS hsRV hsne hsgt hmVF hmS hmgt hinf
    (fun S f => h M N ⟨hSat, hsize⟩ S f)

/-- **The frozen `Prop39Sat` is refutable at a `PaperHyp` pair with an Archimedean target carrying
the configuration.**  So the canonical frontier `ShoenfieldTestRel + Prop39Sat` is *vacuous* at such
pairs, and `Prop39Sat` is not a theorem of `ACVF` at all paper pairs: the gate has to exclude the
configuration (which genuine saturation does, and `SaturatedFS` alone does not). -/
theorem not_prop39Sat_of_archimedean_config (hPaper : M7Paper.PaperHyp M N)
    (hArch : Hahn.ArchimedeanRV N)
    {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmVF : iVF m) (hmS : m ∉ S) (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s) :
    ¬ M7Paper.Prop39Sat :=
  fun h => not_extendsHere_of_archimedean (S := S) (f := f) hArch hsS hsRV hsne hsgt hmVF hmS hmgt hinf
    (fun S f => h M N hPaper S f)

/-- **(finite satisfiability) `QFFinSat` fails at a `SaturatedFS` Archimedean target with the
configuration.**  This is `Hahn.not_finSat_of_archimedean`, read as a statement about
`M2Saturation.QFFinSat` — the formula-level obligation the case lemmas would have to prove.  So the
case lemmas cannot be stated globally without `¬ ArchimedeanRV N`. -/
theorem not_finSat_at_pair_of_archimedean (hSat : Assembly.SaturatedFS N)
    (hArch : Hahn.ArchimedeanRV N) {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmRV : iRV m) (hmne : m ≠ iRVZero) (hmgt : ¬ iLe m iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow s n) m) :
    ¬ M2Saturation.QFFinSat M N :=
  fun h => Hahn.not_finSat_of_archimedean hSat hArch hsS hsRV hsne hsgt hmRV hmne hmgt hinf
    (h S f m)

/-- **(finite satisfiability, global form)** The `QFFinSat`-at-`PaperHyp` hypothesis of
`QE/QFRoute.lean`'s `paper_theorem_2_3_sat_of_qf` is **not** a theorem at every paper pair: at an
Archimedean `SaturatedFS` pair carrying the configuration it is false.  So the `QFFinSat` route is
conditional on the target's value group, and the honest residual at such pairs is `Prop39Sat` itself
(which fails too — `not_prop39Sat_of_archimedean_config`). -/
theorem not_forall_qffinsat_at_paperGate (hPaper : M7Paper.PaperHyp M N)
    (hArch : Hahn.ArchimedeanRV N) {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmRV : iRV m) (hmne : m ≠ iRVZero) (hmgt : ¬ iLe m iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow s n) m) :
    ¬ (∀ (M' N' : Type) [LRV.Structure M'] [LRV.Structure N']
        [M' ⊨ Axioms.ACVF] [N' ⊨ Axioms.ACVF],
        M7Paper.PaperHyp M' N' → M2Saturation.QFFinSat M' N') :=
  fun h => not_finSat_at_pair_of_archimedean (S := S) (f := f) hPaper.1 hArch hsS hsRV hsne hsgt hmRV hmne hmgt hinf
    (h M N hPaper)

/-- **The collapse is two-way at m7's configuration**: at a `PaperHyp` pair with an Archimedean target
carrying the infinitesimal configuration over a *`Standing`* substructure, `M5Ledger.LedgerInput5P`
**fails** — because `FinalAudit.oneStepPaper_of_ledgerInput5P` derives the paper-pair one-step from it,
and `Hahn.not_oneStepPaper_of_config` refutes that.  Read with `FinalAudit.ledgerInput5P_iff_prop39Sat`
and `extendsAt_rel_iff_input5R` this says: input 5, `Prop39Sat`, `Input5R` and the paper-pair one-step
all fail at the same pair.  So the `⊤`-collapse is not a way to satisfy the gate: no witness can
manufacture an embedding whose value group has no room. -/
theorem not_ledgerInput5P_of_config {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hPaper : M7Paper.PaperHyp M N) (hArch : Hahn.ArchimedeanRV N) (hStand : Assembly.Standing S)
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmVF : iVF m) (hmS : m ∉ S) (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s) :
    ¬ M5Ledger.LedgerInput5P :=
  fun h5 => Hahn.not_oneStepPaper_of_config (S := S) (f := f) hPaper hArch hStand hsS hsRV hsne hsgt
    hmVF hmS hmgt hinf (FinalAudit.oneStepPaper_of_ledgerInput5P h5)

end Refutations


section SatRelFinSat

variable {M N : Type} [LRV.Structure M] [LRV.Structure N] [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **The same refutation at the honest gate.**  `M1Fix.SatRel M N` is the pair-relative saturation
("finitely satisfiable ⟹ realised"), so the Archimedean obstruction to the configuration's type
applies at `SatRel` pairs without needing the frozen `∀ M`-quantified `Assembly.SaturatedFS`.  This is
`Hahn.not_finSat_of_archimedean` with the saturation hypothesis weakened from `SaturatedFS N` to
`SatRel M N` (the proof is that theorem's, with `hSat M S f m hfin` replaced by `hSat S f m hfin`). -/
theorem not_finSat_of_satRel_of_archimedean (hSat : M1Fix.SatRel M N)
    (hArch : Hahn.ArchimedeanRV N) {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmRV : iRV m) (hmne : m ≠ iRVZero) (hmgt : ¬ iLe m iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow s n) m) :
    ¬ M2Saturation.QFFinSat M N := by
  intro hfin
  obtain ⟨b, hb⟩ := hSat S f m (hfin S f m)
  have hbRV : iRV b := by
    have hφ : (Hahn.fRV (Hahn.varX S)).Realize (Realize.mv S m) := by
      simp [hmRV]
    simpa using hb (Hahn.fRV (Hahn.varX S)) hφ
  have hbne : b ≠ iRVZero := by
    have hφ : (Hahn.fNe (Hahn.varX S) Hahn.rvZeroTm).Realize (Realize.mv S m) := by
      simp [hmne]
    simpa using hb (Hahn.fNe (Hahn.varX S) Hahn.rvZeroTm) hφ
  have hbgt : ¬ iLe b iRVOne := by
    have hφ : (Hahn.fNotLe (Hahn.varX S) Hahn.rvOneTm).Realize (Realize.mv S m) := by
      simp [hmgt]
    simpa using hb (Hahn.fNotLe (Hahn.varX S) Hahn.rvOneTm) hφ
  have hbinf : ∀ n : ℕ, iLe (Assembly.rvPow (f ⟨s, hsS⟩) n) b := by
    intro n
    have hφ : (Hahn.fLe (Hahn.powTm (Hahn.varP ⟨s, hsS⟩) n) (Hahn.varX S)).Realize
        (Realize.mv S m) := by
      simp [Hahn.powTm_realize, hinf n]
    have h := hb (Hahn.fLe (Hahn.powTm (Hahn.varP ⟨s, hsS⟩) n) (Hahn.varX S)) hφ
    simpa [Hahn.powTm_realize] using h
  have hfsRV : iRV (f ⟨s, hsS⟩) := by
    have hφ : (Hahn.fRV (Hahn.varP ⟨s, hsS⟩)).Realize (Realize.mv S m) := by
      simp [hsRV]
    simpa using hb (Hahn.fRV (Hahn.varP ⟨s, hsS⟩)) hφ
  have hfsne : f ⟨s, hsS⟩ ≠ iRVZero := by
    have hφ : (Hahn.fNe (Hahn.varP ⟨s, hsS⟩) Hahn.rvZeroTm).Realize (Realize.mv S m) := by
      simp [hsne]
    simpa using hb (Hahn.fNe (Hahn.varP ⟨s, hsS⟩) Hahn.rvZeroTm) hφ
  have hfsgt : ¬ iLe (f ⟨s, hsS⟩) iRVOne := by
    have hφ : (Hahn.fNotLe (Hahn.varP ⟨s, hsS⟩) Hahn.rvOneTm).Realize (Realize.mv S m) := by
      simp [hsgt]
    simpa using hb (Hahn.fNotLe (Hahn.varP ⟨s, hsS⟩) Hahn.rvOneTm) hφ
  exact (Hahn.not_archimedeanRV_of_infinitesimalRoom hN hfsRV hbRV hbne hfsne hfsgt hbinf) hArch

/-- **`QFFinSat` fails at `relGate` pairs with an Archimedean target carrying the configuration**, so
the `QFFinSat`-at-`relGate` hypothesis of `paper_theorem_rel_of_qffinsat` is not a theorem at every
honest-gate pair. -/
theorem not_forall_qffinsat_at_relGate (hSat : M1Fix.SatRel M N) (hsize : M7Paper.SizeHyp M N)
    (hArch : Hahn.ArchimedeanRV N) {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmRV : iRV m) (hmne : m ≠ iRVZero) (hmgt : ¬ iLe m iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow s n) m) :
    ¬ (∀ (M' N' : Type) [LRV.Structure M'] [LRV.Structure N']
        [M' ⊨ Axioms.ACVF] [N' ⊨ Axioms.ACVF],
        M5Shoenfield.relGate M' N' → M2Saturation.QFFinSat M' N') :=
  fun h => not_finSat_of_satRel_of_archimedean (S := S) (f := f) hSat hArch hsS hsRV hsne hsgt
    hmRV hmne hmgt hinf (h M N ⟨hSat, hsize⟩)

end SatRelFinSat

/-!
## 5. The exactness of the paper's §3 decomposition

Composing §1.3 with §1.1 gives the strongest form of the answer to the direction's question:
**input 5 (Marker's saturated realisation) is *equivalent* to Lemma 3.3 (hull form) together with the
one-step Lemmas 3.4–3.8**, at a fixed pair and hence at the paper's pairs.  So the paper's §3 is not a
weaker or stronger statement than the saturation input the ledger consumes: it is that input, said in
two halves.  The case lemmas are therefore *necessary and sufficient* for Proposition 3.9 once the
hull form is granted — and unnecessary once input 5 is granted directly.
-/

section Exactness

variable {M N : Type} [LRV.Structure M] [LRV.Structure N] [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **Input 5 ⟺ Lemma 3.3 (hull) ∧ Lemma 3.4–3.8 (one-step)** at a fixed pair. -/
theorem satReal_iff_hullExtension_and_oneStep :
    M5Ledger.SaturationRealization (M := M) (N := N) ↔
      HullExtension (M := M) (N := N) ∧ Assembly.OneStepVFP (M := M) (N := N) :=
  extendsHere_iff_satReal.symm.trans extendsHere_iff_hullExtension_and_oneStep

/-- The same with the paper's case split in place of the one-step. -/
theorem satReal_iff_hullExtension_and_cases :
    M5Ledger.SaturationRealization (M := M) (N := N) ↔
      HullExtension (M := M) (N := N) ∧ M4Cases.Cases (M := M) (N := N) :=
  extendsHere_iff_satReal.symm.trans extendsHere_iff_hullExtension_and_cases

/-- **The canonical frontier, decomposed exactly**: `LedgerInput5P` (⟺ `Prop39Sat`, `FinalAudit` §3)
holds iff Lemma 3.3 in hull form and the one-step hold at every `PaperHyp` pair.  So the two frozen
§3 obligations are not a *sufficient* condition for input 5 — they are an equivalent rewriting of it,
and `FinalAudit` §1's `⊤`-witness is just the `←` direction's proof read at `T = ⊤`. -/
theorem ledgerInput5P_iff_gated_hullExtension_and_oneStep :
    M5Ledger.LedgerInput5P ↔
      ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
        M7Paper.PaperHyp M N →
          HullExtension (M := M) (N := N) ∧ Assembly.OneStepVFP (M := M) (N := N) := by
  constructor
  · intro h5 M N _ _ _ _ hP
    exact satReal_iff_hullExtension_and_oneStep.mp (h5 M N hP)
  · intro h M N _ _ _ _ hP
    exact satReal_iff_hullExtension_and_oneStep.mpr (h M N hP)

/-- The same at the honest gate: `Input5R` ⟺ the two §3 obligations at `relGate` pairs. -/
theorem input5R_iff_gated_hullExtension_and_oneStep :
    M5Shoenfield.Input5R ↔
      ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
        M5Shoenfield.relGate M N →
          HullExtension (M := M) (N := N) ∧ Assembly.OneStepVFP (M := M) (N := N) := by
  constructor
  · intro h5 M N _ _ _ _ hR
    exact satReal_iff_hullExtension_and_oneStep.mp (h5 M N hR)
  · intro h M N _ _ _ _ hR
    exact satReal_iff_hullExtension_and_oneStep.mpr (h M N hR)

/-- **The hull clause is vacuous at a `Standing` substructure**: `standingHull S = S` whenever `S` is
already `Standing` (minimality + containment).  Since `Assembly.OneStepVFP` applies *only* at
`Standing S`, the hull conjunct of §1.3 carries no element-adding content there: the two conjuncts
are genuinely different obligations, and it is the one-step that the case lemmas 3.4/3.6 must
discharge. -/
theorem standingHull_of_standing {S : LRV.Substructure M} (hS : Assembly.Standing S) :
    M8Hull.standingHull S = S :=
  le_antisymm (M8Hull.standingHull_le le_rfl hS) (M8Hull.le_standingHull S)

/-- **The canonical frontier, packaged under the target's own name.**  Shoenfield's test (quoted,
`M5Shoenfield.ShoenfieldTestRel`) and Marker's saturated realisation at the paper's pair-relative
hypothesis (`M5Shoenfield.Input5R`) give the frozen target
`theorem_2_3_quantifier_elimination : HasQE Axioms.ACVF`.  Both are quotations; everything else is
proved here and in the merged files (`extendsAt_rel_of_input5R`). -/
theorem theorem_2_3_quantifier_elimination_of_rel_quotes
    (hShoen : M5Shoenfield.ShoenfieldTestRel) (h5 : M5Shoenfield.Input5R) :
    HasQE Axioms.ACVF :=
  paper_theorem_rel_two hShoen h5

end Exactness

/-!
## 5b. The gates must match: which pairings of criterion and extension property compose

`relGate` is the *larger* gate (`paperGate → relGate`), so the extension property at `relGate` implies
the frozen `Prop39Sat`, while the criterion at `paperGate` (`ShoenfieldTestSat`) is stronger than the
quotation (`ShoenfieldTestRel`).  Consequently the two *matched* pairings are

* `ShoenfieldTestSat + Prop39Sat` — the frozen pairing (`FinalAudit.paper_theorem_FINAL3`);
* `ShoenfieldTestRel + Input5R` — the honest pairing (§2 above, `paper_theorem_rel_two`),

and the *mixed* pairing (quotation at `relGate` + extension property at `paperGate`) needs exactly
`M5Shoenfield.SatBridge` — the `∀ M`-quantifier-order upgrade `QE/ShoenfieldQuote.lean` §4 identifies as
the gap no book supplies.  Machine-checked below, so that a future final theorem cannot silently mix
them.
-/

section GateMatching

/-- The frozen pairing: criterion and extension property both at `paperGate`. -/
theorem paper_theorem_FINAL3' (hShoen : M7Paper.ShoenfieldTestSat)
    (h39 : M7Paper.Prop39Sat) : HasQE Axioms.ACVF :=
  hShoen h39

/-- **The frozen `Prop39Sat` gives the extension property at `relGate` exactly when the bridge holds,
and not otherwise in general** (the other direction, `ExtendsAt relGate → Prop39Sat`, is
`extendsAt_rel_of_input5R` + `ledgerInput5P_of_input5R`). -/
theorem extendsAt_rel_of_prop39Sat_of_bridge (hB : M5Shoenfield.SatBridge)
    (h39 : M7Paper.Prop39Sat) : M5Shoenfield.ExtendsAt M5Shoenfield.relGate := by
  intro M N _ _ _ _ hR S f
  exact h39 M N (hB M N hR) S f

/-- **The mixed pairing, with the bridge made explicit**: quotation at `relGate`, extension property at
`paperGate`, plus `SatBridge`.  Without `SatBridge` the implication is not available, because
`Prop39Sat` carries the `∀ M`-quantified `SaturatedFS` that the quotation does not spend. -/
theorem paper_theorem_rel_of_prop39Sat_of_bridge (hB : M5Shoenfield.SatBridge)
    (hQ : M5Shoenfield.ShoenfieldTestRel) (h39 : M7Paper.Prop39Sat) : HasQE Axioms.ACVF :=
  hQ (extendsAt_rel_of_prop39Sat_of_bridge hB h39)

/-- `SatBridge` is not needed for the frozen pairing, and `Input5R` is not needed for the honest one:
the two matched pairings above are both unconditional in their own gates.  The last cross-check:
`Input5R` gives the frozen extension property `Prop39Sat` (through `LedgerInput5P`), so the honest
pairing is at least as strong as the frozen conclusion. -/
theorem prop39Sat_of_input5R (h5 : M5Shoenfield.Input5R) : M7Paper.Prop39Sat :=
  FinalAudit.prop39Sat_of_ledgerInput5P (ledgerInput5P_of_input5R h5)

end GateMatching

/-! ## 6. Axiom audit -/

#print axioms SpecialTransformations.Milestone0.G3.extendsHere_of_satReal
#print axioms SpecialTransformations.Milestone0.G3.satReal_of_extendsHere
#print axioms SpecialTransformations.Milestone0.G3.extendsHere_iff_satReal
#print axioms SpecialTransformations.Milestone0.G3.extendsHere_forces_size
#print axioms SpecialTransformations.Milestone0.G3.prepStepP_of_hullExtension
#print axioms SpecialTransformations.Milestone0.G3.hullExtension_of_prepStepP
#print axioms SpecialTransformations.Milestone0.G3.prepStepP_iff_hullExtension
#print axioms SpecialTransformations.Milestone0.G3.hullExtension_of_satReal
#print axioms SpecialTransformations.Milestone0.G3.hullExtension_of_extendsHere
#print axioms SpecialTransformations.Milestone0.G3.hullExtension_forces_units_size
#print axioms SpecialTransformations.Milestone0.G3.oneStepVFP_of_extendsHere
#print axioms SpecialTransformations.Milestone0.G3.extendsHere_of_hullExtension_of_oneStep
#print axioms SpecialTransformations.Milestone0.G3.extendsHere_iff_hullExtension_and_oneStep
#print axioms SpecialTransformations.Milestone0.G3.extendsHere_iff_hullExtension_and_cases
#print axioms SpecialTransformations.Milestone0.G3.extendsAt_rel_of_input5R
#print axioms SpecialTransformations.Milestone0.G3.input5R_of_extendsAt_rel
#print axioms SpecialTransformations.Milestone0.G3.extendsAt_rel_iff_input5R
#print axioms SpecialTransformations.Milestone0.G3.ledgerInput5P_of_input5R
#print axioms SpecialTransformations.Milestone0.G3.paper_theorem_rel_two
#print axioms SpecialTransformations.Milestone0.G3.paper_theorem_sat_via_input5R
#print axioms SpecialTransformations.Milestone0.G3.paper_theorem_sat_two
#print axioms SpecialTransformations.Milestone0.G3.qfsat_of_satRel_of_qffinsat
#print axioms SpecialTransformations.Milestone0.G3.input5R_of_relGate_finSat
#print axioms SpecialTransformations.Milestone0.G3.extendsAt_rel_of_finSat
#print axioms SpecialTransformations.Milestone0.G3.paper_theorem_rel_of_qffinsat
#print axioms SpecialTransformations.Milestone0.G3.paper_theorem_sat_of_qffinsat
#print axioms SpecialTransformations.Milestone0.G3.not_extendsHere_of_archimedean
#print axioms SpecialTransformations.Milestone0.G3.not_forall_extendsHere_of_archimedean
#print axioms SpecialTransformations.Milestone0.G3.not_extendsAt_rel_of_archimedean_config
#print axioms SpecialTransformations.Milestone0.G3.not_prop39Sat_of_archimedean_config
#print axioms SpecialTransformations.Milestone0.G3.not_finSat_at_pair_of_archimedean
#print axioms SpecialTransformations.Milestone0.G3.not_forall_qffinsat_at_paperGate
#print axioms SpecialTransformations.Milestone0.G3.not_ledgerInput5P_of_config
#print axioms SpecialTransformations.Milestone0.G3.not_finSat_of_satRel_of_archimedean
#print axioms SpecialTransformations.Milestone0.G3.not_forall_qffinsat_at_relGate
#print axioms SpecialTransformations.Milestone0.G3.satReal_iff_hullExtension_and_oneStep
#print axioms SpecialTransformations.Milestone0.G3.satReal_iff_hullExtension_and_cases
#print axioms SpecialTransformations.Milestone0.G3.ledgerInput5P_iff_gated_hullExtension_and_oneStep
#print axioms SpecialTransformations.Milestone0.G3.input5R_iff_gated_hullExtension_and_oneStep
#print axioms SpecialTransformations.Milestone0.G3.standingHull_of_standing
#print axioms SpecialTransformations.Milestone0.G3.theorem_2_3_quantifier_elimination_of_rel_quotes
#print axioms SpecialTransformations.Milestone0.G3.paper_theorem_FINAL3'
#print axioms SpecialTransformations.Milestone0.G3.extendsAt_rel_of_prop39Sat_of_bridge
#print axioms SpecialTransformations.Milestone0.G3.paper_theorem_rel_of_prop39Sat_of_bridge
#print axioms SpecialTransformations.Milestone0.G3.prop39Sat_of_input5R

end G3
end Milestone0
end SpecialTransformations
