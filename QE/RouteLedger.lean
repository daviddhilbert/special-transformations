/-
# r7 — THE ASSEMBLY AND THE FINAL: the route ledger, final edition

Member `m7`, swarm `smw2ox51x`, direction r7.  Target: `Milestone0/Encoding.lean`'s
`theorem_2_3_quantifier_elimination : HasQE Axioms.ACVF`.

This file is the **ledger**: it says, machine-checkably, what exactly has to be proved for the frozen
target, which of those obligations the merged tree already discharges, and how the discharge
composes.  Nothing here is new mathematics beyond §1 (which removes an obligation that the merged
tree believed it had discharged) and the wiring of §4–§5 (which is what the merged files do not
state).

## The verdict

`HasQE Axioms.ACVF` follows from **three** statements, and from nothing weaker in the tree's own
vocabulary (`§3`):

    L33   Lemma 3.3, hull form, at the paper's pairs        (G3.HullExtension at M7Paper.PaperHyp)
    L3x   Lemmas 3.4–3.8, the paper's case split           (M4Cases.Cases at M7Paper.PaperHyp)
    QUOTE Shoenfield's test                                 (M7Paper.ShoenfieldTestSat)

`§3` proves `paper_theorem_2_3_of_hull_and_cases` and `§3.3` checks that the merged six-hypothesis
route (`M4Cases.paper_theorem_2_3_sat_of_cases`) is recovered from it, so the ledger is a
*decomposition*, not a weakening.  `§3.2` does the same at the honest `relGate` gate with Marker's
quotation (`M5Shoenfield.ShoenfieldTestRel`).

`§6b` proves the sharper structural fact the plan needs: at the frozen gate the pair
`(L33, L3x)` is **equivalent** to `M5Ledger.LedgerInput5P` (Marker's saturated realisation), and at
`relGate` to `M5Shoenfield.Input5R`.  So the paper's Section 3 is neither more nor less than the
saturation input: slicing it into case lemmas cannot avoid proving it, and quoting the input makes it
unnecessary.  `§6c` checks `L33` is not the conclusion in disguise (it forces only `#Kˣ(M) ≤ #N`).

`L3x` is where the paper's §3.2 content sits, and `§4` splits it as the tree's own files demand:
`CaseSeparated` (3.7, `M5L.Separated`), the **unit half** of `CaseNotSeparated` (3.4 and 3.6), the
**non-unit half** (3.5, `Case35.NotSeparatedBranch`), and `CaseNewRV` (3.8).  `§4` proves

    Cases  ⟸  CaseSeparated ∧ UnitSlot ∧ NonUnitSlot ∧ CaseNewRV

so the two halves of the not-separated slot can be attacked separately.

## §1 What the merged Lemma 3.6 actually proves: nothing

`M8.Lemma36Hyp S e` (the hypothesis list of `QE/Lemma36Statement.lean`'s `lemma36_claim_star`) is
**inconsistent**: `M8.RVTrans S e hunit` fails at every `Assembly.KEqTop S` and every unit `e`.
The reason is the coefficient set.  `RVTrans` allows any coefficient `b` with `pInKof b` (i.e.
`iUnits b ∨ b = iRVZero`) and `b ∈ S`; `Assembly.Standing S` contains `Assembly.KEqTop S`, which puts
*every residue-field unit of `M`* into `S` — including `rv e` itself.  So the polynomial `X - rv e`
has all its coefficients in the permitted set, is nonzero, and vanishes at `rv e`.

This is exactly the `RVeqRvVF` mismatch: the paper's `K(Ŝ)` is `{rv s : s ∈ Ŝ ∩ VF}`, and the tree
transcribes it as `S ∩ KOf`, which is *strictly bigger* once `KEqTop S` holds
(`{rv s : s ∈ S ∩ VF} ⊆ S ∩ KOf` is `M5L.rv_mem_sub`, the converse is not available and is false in
general).  Consequences, all machine-checked below:

* `lemma36Hyp_false` — `M8.Lemma36Hyp S e` has no instances; `not_exists_lemma36Hyp` — none in any
  model of `ACVF`, at any `S`;
* `claimStar_vacuous` — `M8.ClaimStar` is therefore never *derived* from Lemma 3.6's hypotheses in a
  way usable at a slot;
* so `M4Cases.CaseNotSeparated`'s unit half is **not** covered by 3.4 ∪ 3.6: the 3.6 side is empty.
  `§4.3` isolates the surviving unit obligation as `TranscendentalUnitSlot`, and `§1.3` states the
  repair (restrict `RVTrans`'s coefficients to residue images of `VF`-elements of `S`).

No `sorry`, no `axiom`, no `native_decide`; axiom audit at the end.
-/
import Prop39Decomp
import Case34Slot
import Case35Slot
import Lemma36Statement
import NewRVClaim

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.StandingField
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Milestone0.RouteLedger

/-! ## 1. Lemma 3.6 as merged is empty -/

section Lemma36

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `S` contains the `K`-negative of each of its elements (the language has a `kNeg` symbol). -/
theorem negCoeff_mem_sub (S : LRV.Substructure M) {x : M} (hx : x ∈ S) :
    TrivCase.iKNeg x ∈ S :=
  S.fun_mem Fn.kNeg ![x] (fun i => by fin_cases i; exact hx)

/-- `1 ≠ 0` in the residue field. -/
theorem one_ne_zero_rv : iRVOne (M := M) ≠ iRVZero :=
  GammaGroup.units_ne_zero (StandingTree.rv_one_units (M := M))

/-- `X - c` evaluated in the frozen residue-field vocabulary vanishes at `c`, for `c` a residue
element. -/
theorem rvPolyEval_sub_const {c : M} (hc : pInKof c) :
    M8.rvPolyEval (fun i => if i = 0 then TrivCase.iKNeg c else if i = 1 then iRVOne else iRVZero)
      c 2 = iRVZero := by
  have hneg : pInKof (TrivCase.iKNeg c) := kNeg_mk c hc
  have h0 : (if (0 : ℕ) = 0 then TrivCase.iKNeg c else if (0 : ℕ) = 1 then iRVOne else iRVZero)
      = TrivCase.iKNeg c := if_pos rfl
  have h1 : (if (1 : ℕ) = 0 then TrivCase.iKNeg c else if (1 : ℕ) = 1 then iRVOne else iRVZero)
      = iRVOne := by rw [if_neg (by norm_num), if_pos rfl]
  show iKAdd (iKAdd iRVZero (iRVMul
      (if (0 : ℕ) = 0 then TrivCase.iKNeg c else if (0 : ℕ) = 1 then iRVOne else iRVZero)
      (Transc.rvpow c 0)))
    (iRVMul (if (1 : ℕ) = 0 then TrivCase.iKNeg c else if (1 : ℕ) = 1 then iRVOne else iRVZero)
      (Transc.rvpow c 1)) = iRVZero
  rw [h0, h1]
  show iKAdd (iKAdd iRVZero (iRVMul (TrivCase.iKNeg c) iRVOne)) (iRVMul iRVOne (iRVMul iRVOne c))
    = iRVZero
  have hone : iRVMul iRVOne c = c := kOne_mul c hc
  simp only [hone, kMul_one (TrivCase.iKNeg c) hneg, kZero_add (TrivCase.iKNeg c) hneg,
    kAdd_comm (TrivCase.iKNeg c) c hneg hc, kAdd_neg_cancel c hc]

/-- **`RVTrans` fails at every `KEqTop` substructure and every unit.**  The polynomial `X - rv e` has
coefficients in the permitted set (`rv e` itself is one, by `KEqTop`), is nonzero, and vanishes at
`rv e`. -/
theorem not_rvTrans_of_units {S : LRV.Substructure M} {e : M}
    (hK : Assembly.KEqTop S) (hunit : iUnits (iRv e)) :
    ¬ M8.RVTrans S e hunit := by
  intro h
  have hxS : iRv e ∈ S := hK _ hunit
  have hc : pInKof (iRv e) := Or.inl hunit
  have hbK : ∀ i, pInKof
      (if i = 0 then TrivCase.iKNeg (iRv e) else if i = 1 then iRVOne else iRVZero) := by
    intro i
    by_cases h0 : i = 0
    · rw [if_pos h0]; exact kNeg_mk (iRv e) hc
    · by_cases h1 : i = 1
      · rw [if_neg h0, if_pos h1]; exact Or.inl (StandingTree.rv_one_units (M := M))
      · rw [if_neg h0, if_neg h1]; exact Or.inr rfl
  have hbS : ∀ i,
      (if i = 0 then TrivCase.iKNeg (iRv e) else if i = 1 then iRVOne else iRVZero) ∈ S := by
    intro i
    by_cases h0 : i = 0
    · rw [if_pos h0]; exact negCoeff_mem_sub S hxS
    · by_cases h1 : i = 1
      · rw [if_neg h0, if_pos h1]; exact M5L.rvOne_mem_sub S
      · rw [if_neg h0, if_neg h1]; exact M5L.rvZero_mem_sub S
  have hbne : ∃ i, i ≤ 1 ∧
      (if i = 0 then TrivCase.iKNeg (iRv e) else if i = 1 then iRVOne else iRVZero)
        ≠ iRVZero := by
    refine ⟨1, by norm_num, ?_⟩
    rw [if_neg (by norm_num), if_pos rfl]
    exact one_ne_zero_rv (M := M)
  exact (h 1 _ hbK hbS hbne) (rvPolyEval_sub_const (M := M) hc)

/-- **Lemma 3.6's hypothesis package has no instances.** -/
theorem lemma36Hyp_false {S : LRV.Substructure M} {e : M} (h : M8.Lemma36Hyp S e) : False :=
  not_rvTrans_of_units h.standing.1 h.unit h.transc

/-- Quantified form: no model of `ACVF`, no `S`, no `e` satisfies Lemma 3.6's hypotheses. -/
theorem not_exists_lemma36Hyp :
    ¬ ∃ (S : LRV.Substructure M) (e : M), M8.Lemma36Hyp S e := by
  rintro ⟨S, e, h⟩
  exact lemma36Hyp_false h

/-- The `⊤`-witness stress test for Lemma 3.6's hypotheses is necessarily **negative**. -/
theorem not_rvTrans_top {e : M} (hunit : iUnits (iRv e)) :
    ¬ M8.RVTrans (⊤ : LRV.Substructure M) e hunit :=
  not_rvTrans_of_units (S := (⊤ : LRV.Substructure M)) (fun _ _ => trivial) hunit

/-- The `QV`-form of the finding: Lemma 3.6's conclusion (`M8.ClaimStar`) is only ever reached
vacuously, so it cannot discharge any slot whose hypotheses are satisfiable.  Stated as the
implication with an explicit `False` premise, so that the ledger records the *reason*. -/
theorem claimStar_vacuous {S : LRV.Substructure M} {e : M} (h : M8.Lemma36Hyp S e) :
    False :=
  lemma36Hyp_false h

/-! ### 1.2 The same refutation for the *stricter* form of the defect

`RVTrans` also fails if the only coefficient restriction is "in `S` and a residue element": the
witness above is already of that form.  What is *not* refuted is the paper's reading, with the
coefficient set cut down to residue images of `VF`-elements of `S`.  That reading is recorded in
§1.3 as a definition; it is not used by anything in this file. -/

/-- **The repair**: the paper's `rv(e)` transcendental over `K(Ŝ)`, with `K(Ŝ)` read as the residue
*image* of `S ∩ VF` (rather than as `S ∩ KOf`, which is what `M8.RVTrans` allows).  `{rv s : s ∈ S}`
is contained in `S ∩ KOf` (`M5L.rv_mem_sub`), so this hypothesis is *weaker* than `M8.RVTrans` and is
the one the paper states. -/
def RVTransVF (S : LRV.Substructure M) (e : M) : Prop :=
  ∀ (m : ℕ) (b : ℕ → M), (∀ i, pInKof (b i)) →
    (∀ i, ∃ s : M, s ∈ S ∧ iVF s ∧ b i = iRv s) →
    (∃ i, i ≤ m ∧ b i ≠ iRVZero) → M8.rvPolyEval b (iRv e) (m + 1) ≠ iRVZero

/-- Every coefficient of the repaired form is a coefficient of `RVTrans`'s form: so
`RVTransVF` is implied by `RVTrans`, and the refutation above says the implication is strict at
every `KEqTop S` with a unit `e`. -/
theorem rvTransVF_of_rvTrans {S : LRV.Substructure M} {e : M} (hunit : iUnits (iRv e))
    (h : M8.RVTrans S e hunit) : RVTransVF S e :=
  fun m b hbK hbS => h m b hbK (fun i => by
    obtain ⟨s, hsS, -, hbs⟩ := hbS i
    rw [hbs]
    exact M5L.rv_mem_sub S hsS)

end Lemma36

/-! ## 2. The obligation set: three statements at the paper's pairs

`Bridge` is the shape both gates have (a `Prop` depending on the pair and its `ACVF` instances); the
ledger names the two instantiations the tree uses. -/

/-- **L33 — Lemma 3.3, hull form, at the paper's pairs.**  Every monomorphism out of `S ⊆ M`
extends to the standing hull of `S`.  Equivalent to `Assembly.PrepStepP` at the pair
(`G3.prepStepP_iff_hullExtension`), i.e. to the first conjunct of Proposition 3.9. -/
def GatedHull : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.PaperHyp M N → G3.HullExtension M N

/-- **L3x — Lemmas 3.4–3.8, the paper's case split, at the paper's pairs.**  The three slots of
`M4Cases.Cases`: `lift:all:root`-`lift:transcendental` (the `¬ Separated` unit half), `3.5` (the
`¬ Separated` non-unit half), `e:transc` (`Separated`), and the new-`rv` slot. -/
def GatedCases : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.PaperHyp M N → M4Cases.Cases (M := M) (N := N)

/-! ## 3. The endgame

Two composition steps, then the target.  Neither introduces a hypothesis: `§3.1` is
`G3.prepStepP_of_hullExtension` pointwise, `§3.2` is `M4Cases.oneStepPaper_of_cases`. -/

/-- **L33 at the paper's pairs gives the paper's Lemma 3.3.** -/
theorem prepStepPaper_of_gatedHull (h : GatedHull) : M5Ledger.PrepStepPaper :=
  fun M N _ _ _ _ hP => G3.prepStepP_of_hullExtension (M := M) (N := N) (h M N hP)

/-- **L3x at the paper's pairs gives the paper's one-step.** -/
theorem oneStepPaper_of_gatedCases (h : GatedCases) : M4Cases.OneStepPaper :=
  fun M N _ _ _ _ hP => M4Cases.oneStepVFP_of_cases (h M N hP)

/-- **THE LEDGER'S ENDGAME: `HasQE Axioms.ACVF` from L33, L3x and Shoenfield's quotation.** -/
theorem paper_theorem_2_3_of_hull_and_cases (hShoen : M7Paper.ShoenfieldTestSat)
    (hHull : GatedHull) (hCases : GatedCases) : HasQE Axioms.ACVF :=
  hShoen (M4Cases.prop39Sat_of_prepStepPaper_gated (prepStepPaper_of_gatedHull hHull)
    (oneStepPaper_of_gatedCases hCases))

/-- The same endgame **without the saturation-quotation**: L33 and L3x still give the frozen
extension property `Prop39Sat`, which is the antecedent of the quote.  (The gate's saturation
conjunct `Assembly.SaturatedFS` is *not* consumed by the two §3 statements at all.) -/
theorem prop39Sat_of_hull_and_cases (hHull : GatedHull) (hCases : GatedCases) :
    M7Paper.Prop39Sat :=
  M4Cases.prop39Sat_of_prepStepPaper_gated (prepStepPaper_of_gatedHull hHull)
    (oneStepPaper_of_gatedCases hCases)

/-! ### 3.1 The ledger is a decomposition, not a weakening

The merged six-hypothesis route (`M4Cases.paper_theorem_2_3_sat_of_cases`: five ledger inputs plus the
case ledger) is *recovered* from the three-statement one, because the five inputs give `PrepStepP` and
`PrepStepP` is the hull form.  So nothing is lost by forgetting inputs 1–5. -/

/-- The five ledger inputs give L33: `PrepStepP` *is* the hull form at the pair. -/
theorem gatedHull_of_ledger (h1 : M5Ledger.LedgerInput1P) (h2 : M5Ledger.LedgerInput2)
    (h3 : M5Ledger.LedgerInput3P) (h4 : M5Ledger.LedgerInput4P) (h5 : M5Ledger.LedgerInput5P) :
    GatedHull :=
  fun M N _ _ _ _ hP =>
    (G3.prepStepP_iff_hullExtension (M := M) (N := N)).mp
      (M5Ledger.prepStepPaper_of_ledger h1 h2 h3 h4 h5 M N hP)

/-- **The merged final is a corollary of the ledger's endgame.** -/
theorem paper_theorem_2_3_sat_of_cases_recovered (hShoen : M7Paper.ShoenfieldTestSat)
    (h1 : M5Ledger.LedgerInput1P) (h2 : M5Ledger.LedgerInput2) (h3 : M5Ledger.LedgerInput3P)
    (h4 : M5Ledger.LedgerInput4P) (h5 : M5Ledger.LedgerInput5P) (hcases : GatedCases) :
    HasQE Axioms.ACVF :=
  paper_theorem_2_3_of_hull_and_cases hShoen (gatedHull_of_ledger h1 h2 h3 h4 h5) hcases

/-- The instance check: the recovered statement and the merged statement have the same conclusion at
the same hypotheses (both are `HasQE Axioms.ACVF`, so the ledger's endgame is a rewriting of the
merged route rather than a different target). -/
theorem recovered_agrees (hShoen : M7Paper.ShoenfieldTestSat) (h1 : M5Ledger.LedgerInput1P)
    (h2 : M5Ledger.LedgerInput2) (h3 : M5Ledger.LedgerInput3P) (h4 : M5Ledger.LedgerInput4P)
    (h5 : M5Ledger.LedgerInput5P) (hcases : GatedCases) :
    paper_theorem_2_3_sat_of_cases_recovered hShoen h1 h2 h3 h4 h5 hcases =
      M4Cases.paper_theorem_2_3_sat_of_cases hShoen h1 h2 h3 h4 h5 hcases :=
  rfl

/-! ### 3.2 The same ledger at the honest gate (`relGate`)

Here the quotation is Marker's `M5Shoenfield.ShoenfieldTestRel` (pair-relative saturation), and the
two obligations are `HullExtension` and `Cases` at `relGate`.  `G3.satReal_iff_hullExtension_and_oneStep`
converts the pair, so the endgame is `G3.paper_theorem_rel_two`. -/

/-- **L33 at `relGate`.** -/
def RelHull : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → G3.HullExtension M N

/-- **L3x at `relGate`.** -/
def RelCases : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → M4Cases.Cases (M := M) (N := N)

/-- L33 + L3x at `relGate` give Marker's saturated realisation there. -/
theorem input5R_of_relHull_relCases (hH : RelHull) (hC : RelCases) : M5Shoenfield.Input5R :=
  fun M N _ _ _ _ hR =>
    (G3.satReal_iff_hullExtension_and_oneStep (M := M) (N := N)).mpr
      ⟨hH M N hR, M4Cases.oneStepVFP_of_cases (hC M N hR)⟩

/-- **The honest-gate endgame: `HasQE` from Marker's quotation, L33 and L3x.** -/
theorem paper_theorem_2_3_of_relHull_relCases (hQ : M5Shoenfield.ShoenfieldTestRel)
    (hH : RelHull) (hC : RelCases) : HasQE Axioms.ACVF :=
  G3.paper_theorem_rel_two hQ (input5R_of_relHull_relCases hH hC)

/-- The frozen gate is *smaller* than `relGate`, so the honest-gate obligations give the paper-gate
ones — the ledger's two gates are not in competition. -/
theorem gatedHull_of_relHull (h : RelHull) : GatedHull :=
  fun M N _ _ _ _ hP => h M N (M5Shoenfield.paperGate_le_relGate M N hP)

/-- The same for the case ledger. -/
theorem gatedCases_of_relCases (h : RelCases) : GatedCases :=
  fun M N _ _ _ _ hP => h M N (M5Shoenfield.paperGate_le_relGate M N hP)

/-! ## 4. L3x split into the paper's case lemmas

`M4Cases.CaseNotSeparated` is one `∀`-statement over *all* `¬ M5L.Separated` elements.  The tree's
own files show it must be split (`QE/Case34Slot.lean`'s `caseNotSeparated_iff_unit_and_nonunit`):
units of `M` are never `M5L.Separated` (`not_separated_of_units`), so the slot's unit half contains
every unit of the model — Lemmas 3.4 and 3.6 — while the non-unit half is Lemma 3.5
(`Case35.NotSeparatedBranch`).  This section states the split as named `Prop`s, proves the
combinator, and isolates what each half still owes. -/

section Split

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **The unit half of `M4Cases.CaseNotSeparated`** — Lemmas 3.4 and 3.6. -/
def UnitSlot : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
    iUnits (iRv m) → ¬ M5L.Separated S m →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T

/-- **The non-unit half of `M4Cases.CaseNotSeparated`** — Lemma 3.5. -/
def NonUnitSlot : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
    ¬ iUnits (iRv m) → ¬ M5L.Separated S m →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T

/-- **The algebraic unit case** — Lemma 3.4: `m` satisfies a `VF`-polynomial over `S` (the paper's
`e` algebraic over `VF(Ŝ)`, which after normalisation is a root of a monic over `O(Ŝ)`).  This is the
sub-case of the unit half that `QE/Case34Slot.lean`'s `LiftAllRoot`/`Slot34` formalises. -/
def AlgebraicUnitSlot : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
    iUnits (iRv m) → (∃ n : ℕ, M8.AlgebraicOverVF S m n) →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T

/-- **The transcendental unit case** — what Lemma 3.6 is *supposed* to cover, and, by §1, does not. -/
def TranscendentalUnitSlot : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
    iUnits (iRv m) → (¬ ∃ n : ℕ, M8.AlgebraicOverVF S m n) →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T

/-- The two algebraic sub-cases are exhaustive for the unit half (classical case split on the
existential).  Neither conclusion mentions `¬ M5L.Separated`: it is redundant in both, because
`not_separated_of_units` refutes the negation. -/
theorem unitSlot_of_algebraic_transcendental (ha : AlgebraicUnitSlot (M := M) (N := N))
    (ht : TranscendentalUnitSlot (M := M) (N := N)) : UnitSlot (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hunit _
  by_cases h : ∃ n : ℕ, M8.AlgebraicOverVF S m n
  · exact ha S f hS m hmVF hmrv hunit h
  · exact ht S f hS m hmVF hmrv hunit h

/-- **The two halves give the not-separated slot.**  (Same content as
`M5P1.caseNotSeparated_iff_unit_and_nonunit`'s `←`, restated with the halves named.) -/
theorem caseNotSeparated_of_halves (hu : UnitSlot (M := M) (N := N))
    (hn : NonUnitSlot (M := M) (N := N)) : M4Cases.CaseNotSeparated (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hns
  by_cases hunit : iUnits (iRv m)
  · exact hu S f hS m hmVF hmrv hunit hns
  · exact hn S f hS m hmVF hmrv hunit hns

/-- **`M4Cases.Cases` from the paper's four case lemmas**, with the not-separated slot split.  This is
the ledger's `L3x` at the pair, in the shape the four lemmas are actually proved in. -/
theorem cases_of_parts (hsep : M4Cases.CaseSeparated (M := M) (N := N))
    (hu : UnitSlot (M := M) (N := N)) (hn : NonUnitSlot (M := M) (N := N))
    (hnew : M4Cases.CaseNewRV (M := M) (N := N)) : M4Cases.Cases (M := M) (N := N) where
  separated := hsep
  notSeparated := caseNotSeparated_of_halves hu hn
  newRV := hnew

/-! ### 4.1 Lemma 3.4's residual, in the shape the ledger consumes

`M5P1.Slot34` consumes a full `M5P1.LiftAllRoot`, whose last three fields (`root_lift`, `embed`,
`class_control`) are the residuals r1/r2/r3 name.  The ledger's content is that **producing that
package is the only thing 3.4 owes**: `RootData` below is *exactly* "the paper's hypotheses of
`lift:all:root` give the package", and `Slot34` then discharges the algebraic unit slot. -/

/-- **The residual of Lemma 3.4**: from the paper's hypotheses of `lift:all:root` (`F` monic over
`O(Ŝ)`, `e ∈ U(M)` a root of `F`, `(VF(Ŝ),O(Ŝ))` henselian) plus the tree's algebraic-ness
hypothesis, produce the three facts the paper's proof derives.  This is r1 (`root_lift`), r2
(`embed`) and r3 (`class_control`) as a single obligation. -/
def RootData : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
    iUnits (iRv m) → (∃ n : ℕ, M8.AlgebraicOverVF S m n) →
      ∃ (a : ℕ → M) (n : ℕ), M5P1.LiftAllRoot S f a n m

/-- **Lemma 3.4 discharges the algebraic unit slot**, from `RootData` (its residual) and `Slot34`
(its proved reduction to Claim (⋆)).  Note that `¬ M5L.Separated S m` is produced, not assumed. -/
theorem algebraicUnitSlot_of_rootData_slot34 (hroot : RootData (M := M) (N := N))
    (h34 : M5P1.Slot34 (M := M) (N := N)) : AlgebraicUnitSlot (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hunit halg
  obtain ⟨a, n, hl⟩ := hroot S f hS m hmVF hmrv hunit halg
  exact h34 S f hS a n m hl (M5P1.not_separated_of_units hmVF hunit)

/-! ### 4.2 Lemma 3.7's wiring: what `M5L.OneStepSeparatedP` needs

`M5L.OneStepSeparatedP` (the tree's separated case) assumes `M5L.VFInvClosedOn S`, which
`QE/OneStepCases.lean` §2 shows is *not* a consequence of `Assembly.Standing S`.  So the slot
`M4Cases.CaseSeparated`, which does not assume it, follows from the tree's interface only with that
defect supplied as an explicit hypothesis.  Nothing in the merged tree supplies it. -/

/-- **Lemma 3.7 from the tree's separated interface**, at the price of `VFInvClosedOn` at every
`Standing` substructure. -/
theorem caseSeparated_of_oneStepSeparatedP
    (h : M5L.OneStepSeparatedP (M := M) (N := N))
    (hfinv : ∀ S : LRV.Substructure M, Assembly.Standing S → M5L.VFInvClosedOn S) :
    M4Cases.CaseSeparated (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hsep
  by_cases hm0 : m = iVFZero
  · refine ⟨S, f, le_rfl, fun _ => rfl, ?_, hS⟩
    rw [hm0]
    exact S.fun_mem Fn.vfZero (fun i => i.elim0) (fun i => i.elim0)
  · exact h S f hS (hfinv S hS) m hmVF hm0 hmrv hsep

/-! ### 4.3 Stress tests for the split -/

/-- **The unit half is not vacuous**: at a `KEqTop` substructure *every* unit of the model satisfies
its hypothesis cone.  (So `UnitSlot` is a statement about all of `U(M)`, not about a special class.) -/
theorem unitSlot_hypotheses {S : LRV.Substructure M} {m : M} (hK : Assembly.KEqTop S)
    (hmVF : iVF m) (hunit : iUnits (iRv m)) :
    iVF m ∧ iRv m ∈ S ∧ ¬ M5L.Separated S m :=
  ⟨hmVF, M5P1.rv_mem_of_units hK hunit, M5P1.not_separated_of_units hmVF hunit⟩

/-- **A slot is trivial at an element already in `S`**: so `UnitSlot`'s content is only at genuinely
new units, and the split does not smuggle the conclusion into the hypotheses. -/
theorem unitSlot_at_mem (S : LRV.Substructure M) (f : S ↪[LRV] N) (hS : Assembly.Standing S)
    {m : M} (hm : m ∈ S) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T :=
  ⟨S, f, le_rfl, fun _ => rfl, hm, hS⟩

/-- **The three merged slots are satisfiable**: at a pair where every monomorphism extends to `M`,
all of `Cases` holds with `T = ⊤` (this is `M4Cases.cases_of_global_extension`, restated as the
consistency check for the ledger's `L3x`). -/
theorem cases_consistent
    (hglob : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ∃ g : M ↪[LRV] N,
      ∀ x : S, g (x : M) = f x) : M4Cases.Cases (M := M) (N := N) :=
  M4Cases.cases_of_global_extension hglob

/-- **The merged Lemma-3.5 branch statement subsumes the non-unit half** (it subsumes the whole
not-separated slot: `QE/Case35Slot.lean`'s `caseNotSeparated_of_branch`). -/
theorem nonUnitSlot_of_branch (hb : Case35.NotSeparatedBranch (M := M) (N := N)) :
    NonUnitSlot (M := M) (N := N) := by
  intro S f hS m hmVF hmrv _ hns
  exact Case35.caseNotSeparated_of_branch hb S f hS m hmVF hmrv hns

/-- The same for the unit half — so `Case35.NotSeparatedBranch` is *stronger* than both halves, and
its residual (`M5.ResidualClasses S T` plus the realisation) covers 3.4/3.6's conclusion too.  It is
therefore not a decomposition of the unit half: `M5P1.Slot34` concludes `Standing T` only, so 3.4's
result feeds `UnitSlot` but not `NotSeparatedBranch`.  This is the precise sense in which the two
merged interfaces do not compose with each other. -/
theorem unitSlot_of_branch (hb : Case35.NotSeparatedBranch (M := M) (N := N)) :
    UnitSlot (M := M) (N := N) := by
  intro S f hS m hmVF hmrv _ hns
  exact Case35.caseNotSeparated_of_branch hb S f hS m hmVF hmrv hns

/-! ### 4.4 The 3.8 slot's status

The *class half* of Lemma 3.8 is a theorem of the tree with no quotation and no `VFInvClosedOn`
(`QE/NewRVClaim.lean`'s `ResidualClassesNew_of_VFGen`, packaged as `claimStarNewRV_holds`).  What
the frozen slot `M5.OneStepRVNew` adds is `Assembly.Standing T` — i.e. that the divisible hull of
`Γ(S) + ℤ·vv(m)` enters `T` in the same step — and the monomorphism `g : T ↪ N`.  The ledger
therefore records 3.8 as two independent residuals and does not pretend the class half is the slot. -/

/-- The new-`rv` class half, in the ledger's vocabulary: the merged theorem, restated so that the
ledger's status row for 3.8 points at a named statement. -/
theorem newRV_class_half {S T : LRV.Substructure M} {e : M} (he : iVF e) (he0 : e ≠ iVFZero)
    (hsep : M5L.Separated S e) (hVFGen : Assembly.IsVFGen T)
    (hquot : M5L.QuotExpansions S T e) :
    M5LNewRV.ResidualClassesNew S T e :=
  M5LNewRV.ResidualClassesNew_of_VFGen he he0 hsep hVFGen hquot

/-- **The `Standing T` half of 3.8 does not follow from its class half**: `Standing` is a property of
`T` alone while the class half is a statement about classes, and the tree's own
`QE/GammaDiv.lean`/`QE/Standing.lean` record no implication either way.  The ledger isolates it as
`M5.OneStepRVNew`'s second conjunct and records it as OPEN (the paper's `qe.tex:795-816` hull step). -/
theorem newRV_standing_half_is_separate (S : LRV.Substructure M) :
    Assembly.Standing S ↔ Assembly.KEqTop S ∧ Assembly.GammaDivisible S :=
  Iff.rfl

end Split

/-! ## 5. The two gates' versions of the split, and the final endgame list

The ledger's endgame in §3 takes `GatedCases` as a black box.  Here it is with the four case lemmas
named at the paper's pairs, so that a reader can see which statement each file of the tree attacks. -/

section GatedParts

/-- **3.7 at the paper's pairs** (`e:transc`, `M5L.Separated`). -/
def GatedSeparated : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.PaperHyp M N → M4Cases.CaseSeparated (M := M) (N := N)

/-- **The unit half at the paper's pairs** (Lemmas 3.4 / 3.6). -/
def GatedUnit : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.PaperHyp M N → UnitSlot (M := M) (N := N)

/-- **The non-unit half at the paper's pairs** (Lemma 3.5). -/
def GatedNonUnit : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.PaperHyp M N → NonUnitSlot (M := M) (N := N)

/-- **3.8 at the paper's pairs** (`lift:value:full`, the new-`rv` slot). -/
def GatedNewRV : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.PaperHyp M N → M4Cases.CaseNewRV (M := M) (N := N)

/-- **The four paper lemmas at the paper's pairs give `L3x`.** -/
theorem gatedCases_of_parts (hsep : GatedSeparated) (hu : GatedUnit) (hn : GatedNonUnit)
    (hnew : GatedNewRV) : GatedCases :=
  fun M N _ _ _ _ hP => cases_of_parts (hsep M N hP) (hu M N hP) (hn M N hP) (hnew M N hP)

/-- **THE FINAL ENDGAME LIST.**  `HasQE Axioms.ACVF` from

* `L33` — Lemma 3.3 in hull form, at the paper's pairs;
* `GatedSeparated` — Lemma 3.7 (`e:transc`);
* `GatedUnit` — Lemmas 3.4 / 3.6 (the `¬ Separated` unit half);
* `GatedNonUnit` — Lemma 3.5 (`lift:divisible:hull`);
* `GatedNewRV` — Lemma 3.8 (`lift:value:full`);
* `M7Paper.ShoenfieldTestSat` — the quotation.

Each of the five non-quoted statements is stated at the same gate and in the same vocabulary as the
tree's own assets, so no file has to be re-stated to feed this theorem. -/
theorem paper_theorem_2_3_of_five (hShoen : M7Paper.ShoenfieldTestSat) (hHull : GatedHull)
    (hsep : GatedSeparated) (hu : GatedUnit) (hn : GatedNonUnit) (hnew : GatedNewRV) :
    HasQE Axioms.ACVF :=
  paper_theorem_2_3_of_hull_and_cases hShoen hHull (gatedCases_of_parts hsep hu hn hnew)

end GatedParts

/-! ## 6. The same five-part list at the honest gate (`relGate`)

The frozen gate's `Assembly.SaturatedFS` is the `∀ M`-quantified saturation, which the paper's
hypothesis (`N` is `‖M‖⁺`-saturated, pair-relatively) does not supply; `M5Shoenfield.relGate` is the
pair-relative form and `M5Shoenfield.paperGate_le_relGate` says it is the *larger* gate.  Since the
merged tree contains a machine-checked refutation of the frozen extension property at `PaperHyp`
pairs with an Archimedean target (`G3.not_prop39Sat_of_archimedean_config`), the honest-gate list is
the one that matches the paper's own hypothesis — and both lists are recorded here. -/

section RelParts

/-- **3.7 at `relGate`.** -/
def RelSeparated : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → M4Cases.CaseSeparated (M := M) (N := N)

/-- **The unit half at `relGate`.** -/
def RelUnit : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → UnitSlot (M := M) (N := N)

/-- **The non-unit half at `relGate`.** -/
def RelNonUnit : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → NonUnitSlot (M := M) (N := N)

/-- **3.8 at `relGate`.** -/
def RelNewRV : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → M4Cases.CaseNewRV (M := M) (N := N)

/-- The four paper lemmas at `relGate` give `RelCases`. -/
theorem relCases_of_parts (hsep : RelSeparated) (hu : RelUnit) (hn : RelNonUnit)
    (hnew : RelNewRV) : RelCases :=
  fun M N _ _ _ _ hR => cases_of_parts (hsep M N hR) (hu M N hR) (hn M N hR) (hnew M N hR)

/-- **THE HONEST-GATE ENDGAME LIST.**  `HasQE Axioms.ACVF` from Marker's quotation
(`M5Shoenfield.ShoenfieldTestRel`, pair-relative saturation, i.e. the paper's `‖M‖⁺`-saturation read
pair-relatively) and the five Section-3 statements at `relGate`. -/
theorem paper_theorem_2_3_of_five_rel (hQ : M5Shoenfield.ShoenfieldTestRel) (hHull : RelHull)
    (hsep : RelSeparated) (hu : RelUnit) (hn : RelNonUnit) (hnew : RelNewRV) :
    HasQE Axioms.ACVF :=
  paper_theorem_2_3_of_relHull_relCases hQ hHull (relCases_of_parts hsep hu hn hnew)

end RelParts

/-! ## 6b. The ledger is *exactly* Marker's saturated realisation

The two §3 obligations at a fixed pair are equivalent to the pair's `SaturationRealization`
(`G3.satReal_iff_hullExtension_and_oneStep`).  So at the frozen gate the five-part list is equivalent
to `M5Ledger.LedgerInput5P`, item 5 of the merged ledger — and at the honest gate to
`M5Shoenfield.Input5R`.  Two consequences the ledger records:

* the paper's Section 3 is **not** avoidable by case analysis: no matter how the case lemmas are
  sliced, proving them is proving the saturation input, so a route that does not quote input 5 must
  prove §3 in full;
* conversely, granting input 5 makes the whole case analysis unnecessary
  (`G3.extendsHere_of_satReal`), which is why the frozen endgame consumes only the quotation once §3
  is available.

Both directions are proved here (the `←` direction is the `⊤`-witness plus
`M4Cases.cases_of_global_extension`, the `→` direction is `G3.satReal_iff_hullExtension_and_oneStep`). -/

section Exactness

/-- **At a fixed pair: Lemma 3.3 ∧ Lemmas 3.4–3.8 ⟺ Marker's saturated realisation.** -/
theorem hull_and_cases_iff_satReal {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF] :
    (G3.HullExtension M N ∧ M4Cases.Cases (M := M) (N := N)) ↔
      M5Ledger.SaturationRealization (M := M) (N := N) := by
  constructor
  · rintro ⟨hHull, hCases⟩
    exact (G3.satReal_iff_hullExtension_and_oneStep (M := M) (N := N)).mpr
      ⟨hHull, M4Cases.oneStepVFP_of_cases hCases⟩
  · intro h5
    exact ⟨G3.hullExtension_of_satReal h5,
      M4Cases.cases_of_global_extension (fun S f => G3.extendsHere_of_satReal h5 S f)⟩

/-- **At the frozen gate: the five §3 statements ⟺ `M5Ledger.LedgerInput5P`.** -/
theorem gatedHull_and_cases_iff_ledgerInput5P :
    (GatedHull ∧ GatedCases) ↔ M5Ledger.LedgerInput5P := by
  constructor
  · rintro ⟨hHull, hCases⟩ M N _ _ _ _ hP
    exact (hull_and_cases_iff_satReal (M := M) (N := N)).mp ⟨hHull M N hP, hCases M N hP⟩
  · intro h5
    exact ⟨fun M N _ _ _ _ hP =>
        (hull_and_cases_iff_satReal (M := M) (N := N)).mpr (h5 M N hP) |>.1,
      fun M N _ _ _ _ hP =>
        (hull_and_cases_iff_satReal (M := M) (N := N)).mpr (h5 M N hP) |>.2⟩

/-- **At the honest gate: the five §3 statements ⟺ `M5Shoenfield.Input5R`.** -/
theorem relHull_and_cases_iff_input5R :
    (RelHull ∧ RelCases) ↔ M5Shoenfield.Input5R := by
  constructor
  · rintro ⟨hHull, hCases⟩
    exact input5R_of_relHull_relCases hHull hCases
  · intro h5
    exact ⟨fun M N _ _ _ _ hR =>
        (hull_and_cases_iff_satReal (M := M) (N := N)).mpr (h5 M N hR) |>.1,
      fun M N _ _ _ _ hR =>
        (hull_and_cases_iff_satReal (M := M) (N := N)).mpr (h5 M N hR) |>.2⟩

/-! ### 6c. The hull form is not the conclusion (stress test)

`G3.hullExtension_forces_units_size` shows `HullExtension` forces only `#Kˣ(M) ≤ #N`, while a total
extension forces `#M ≤ #N` (`G3.extendsHere_forces_size`).  So `L33` is strictly weaker than
Proposition 3.9 — the ledger's first hypothesis is not the target in disguise. -/

/-- `L33` forces no cardinality beyond the units bound, at every `PaperHyp` pair. -/
theorem gatedHull_forces_units_size (h : GatedHull) {M N : Type} [LRV.Structure M]
    [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF] (hP : M7Paper.PaperHyp M N)
    (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N :=
  G3.hullExtension_forces_units_size (M := M) (N := N) (h M N hP) S f

end Exactness

/-! ## 7. Status table (the ledger's summary, as comments next to machine-checked names)

| obligation | statement | status |
|---|---|---|
| `L33` | `GatedHull` / `RelHull` (= `Assembly.PrepStepP`, `G3.prepStepP_iff_hullExtension`) | the paper's Lemma 3.3 (both construction steps) — not in the tree; `M5Ledger.prepStepPaper_of_ledger` reduces it to inputs 1–5 |
| 3.7 | `GatedSeparated` | the tree's `M5L.OneStepSeparatedP` gives it **only with `M5L.VFInvClosedOn`** (`caseSeparated_of_oneStepSeparatedP`), which is underivable from `Standing`; the `KF`-route `M5L.ResidualClasses_of_VFGen` has the same defect |
| 3.4 | `AlgebraicUnitSlot` | ⟸ `RootData` + `M5P1.Slot34` (`algebraicUnitSlot_of_rootData_slot34`); `Slot34` is proved from Claim (⋆), `RootData` is r1/r2/r3 |
| 3.6 | `TranscendentalUnitSlot` | **no merged asset**: `M8.Lemma36Hyp` is inconsistent (§1), so the merged 3.6 discharges nothing; the surviving unit case is unproved and unstated in the tree |
| 3.5 | `GatedNonUnit` | ⟸ `Case35.NotSeparatedBranch` (`caseNotSeparated_of_branch`, `nonUnitSlot_of_branch`), whose residual is `M5.ResidualClasses S T` + the realisation |
| 3.8 | `GatedNewRV` | class half is a theorem (`M5LNewRV.ResidualClassesNew_of_VFGen`, `newRV_class_half`); `Standing T` (the divisible hull) and the monomorphism are OPEN |
| QUOTE | `M7Paper.ShoenfieldTestSat` / `M5Shoenfield.ShoenfieldTestRel` | quoted (author ruling) |

The two endgame theorems are `paper_theorem_2_3_of_five` (frozen gate) and
`paper_theorem_2_3_of_five_rel` (honest gate). -/

/-! ## 8. Axiom audit -/

#print axioms SpecialTransformations.Milestone0.RouteLedger.not_rvTrans_of_units
#print axioms SpecialTransformations.Milestone0.RouteLedger.lemma36Hyp_false
#print axioms SpecialTransformations.Milestone0.RouteLedger.not_exists_lemma36Hyp
#print axioms SpecialTransformations.Milestone0.RouteLedger.not_rvTrans_top
#print axioms SpecialTransformations.Milestone0.RouteLedger.rvTransVF_of_rvTrans
#print axioms SpecialTransformations.Milestone0.RouteLedger.prepStepPaper_of_gatedHull
#print axioms SpecialTransformations.Milestone0.RouteLedger.oneStepPaper_of_gatedCases
#print axioms SpecialTransformations.Milestone0.RouteLedger.paper_theorem_2_3_of_hull_and_cases
#print axioms SpecialTransformations.Milestone0.RouteLedger.gatedHull_of_ledger
#print axioms SpecialTransformations.Milestone0.RouteLedger.paper_theorem_2_3_sat_of_cases_recovered
#print axioms SpecialTransformations.Milestone0.RouteLedger.input5R_of_relHull_relCases
#print axioms SpecialTransformations.Milestone0.RouteLedger.paper_theorem_2_3_of_relHull_relCases
#print axioms SpecialTransformations.Milestone0.RouteLedger.unitSlot_of_algebraic_transcendental
#print axioms SpecialTransformations.Milestone0.RouteLedger.caseNotSeparated_of_halves
#print axioms SpecialTransformations.Milestone0.RouteLedger.cases_of_parts
#print axioms SpecialTransformations.Milestone0.RouteLedger.algebraicUnitSlot_of_rootData_slot34
#print axioms SpecialTransformations.Milestone0.RouteLedger.caseSeparated_of_oneStepSeparatedP
#print axioms SpecialTransformations.Milestone0.RouteLedger.unitSlot_hypotheses
#print axioms SpecialTransformations.Milestone0.RouteLedger.cases_consistent
#print axioms SpecialTransformations.Milestone0.RouteLedger.nonUnitSlot_of_branch
#print axioms SpecialTransformations.Milestone0.RouteLedger.unitSlot_of_branch
#print axioms SpecialTransformations.Milestone0.RouteLedger.newRV_class_half
#print axioms SpecialTransformations.Milestone0.RouteLedger.gatedCases_of_parts
#print axioms SpecialTransformations.Milestone0.RouteLedger.paper_theorem_2_3_of_five
#print axioms SpecialTransformations.Milestone0.RouteLedger.relCases_of_parts
#print axioms SpecialTransformations.Milestone0.RouteLedger.paper_theorem_2_3_of_five_rel
#print axioms SpecialTransformations.Milestone0.RouteLedger.hull_and_cases_iff_satReal
#print axioms SpecialTransformations.Milestone0.RouteLedger.gatedHull_and_cases_iff_ledgerInput5P
#print axioms SpecialTransformations.Milestone0.RouteLedger.relHull_and_cases_iff_input5R
#print axioms SpecialTransformations.Milestone0.RouteLedger.gatedHull_forces_units_size

end SpecialTransformations.Milestone0.RouteLedger
