/-
# m4 / u4 — `RelNewRV` at the honest gate

Swarm `smw2qpqe7`, member `m4`, direction u4.  Object: the fifth part of
`QE/RouteLedger.lean`'s honest-gate endgame,

    RelNewRV  :=  ∀ relGate pairs, M4Cases.CaseNewRV (M := M) (N := N)
              =   ∀ relGate pairs, M5.OneStepRVNew (M := M) (N := N),

i.e. Lemma 3.8's `lift:value:full` slot: at a `Standing S`, a `VF`-element `m` whose `rv` is *new*
(`iRv m ∉ S`) must be absorbed into a `Standing T ⊇ S` carrying an embedding into `N` agreeing with
`f` on `S`.

## The answer

`QE/NewRVGlue.lean` proved (its §2–§4) that the slot is a **realisation** statement, not an
algebraic one: it is refuted at an Archimedean target carrying the infinitesimal configuration
(`not_caseNewRV_of_infinitesimal`), its only positive source in the tree is the total extension
property (`oneStepRVNew_of_total_extension`), and its target condition is exactly Γ-divisibility
(`oneStepRVNew_iff_gammaDivisible`).  This file supplies the missing parameter of that picture: the
**hypothesis** under which the positive source is available at the honest gate.

* **§1 `caseNewRV_of_satRel_of_finSat`** — the pair-level implication

      M1Fix.SatRel M N  →  M2Saturation.QFFinSat M N  →  M4Cases.CaseNewRV (M := M) (N := N)

  through the tree's own chain `G3.qfsat_of_satRel_of_qffinsat` (`SatRel` + `QFFinSat` ⟹ qf-type
  realisation), `M2Saturation.satReal_of_qfsat` (qf-type realisation ⟹ saturation realisation),
  `G3.extendsHere_of_satReal` (saturation realisation ⟹ total extension, at `T = ⊤`) and
  `NewRVGlue.oneStepRVNew_of_total_extension` (total extension ⟹ the slot, at `T = ⊤`,
  `StandingTree.standing_top`).  **No size hypothesis, no hull, no case analysis, and no use of the
  slot's own algebra: the whole content is the two hypotheses.**

* **§2 `relNewRV_of_finSat`** — the gate-level form:
  `(∀ relGate pairs, QFFinSat) → RelNewRV`.  So the *single* hypothesis of the `QFFinSat` route
  discharges part 5 of the five-part endgame, and §4 records the composition
  `ShoenfieldTestRel + RelFinSat + RelHull + RelSeparated + RelUnit + RelNonUnit → HasQE`: part 5 can
  be deleted from the endgame list once `RelFinSat` is a hypothesis.  The residual of `RelNewRV` is
  therefore **named**: it is `RelFinSat` (§0), the same statement that discharges input 5 at the
  honest gate (`G3.input5R_of_relGate_finSat`).

* **§3 `relNewRV_of_input5R`** — the frozen route's version: Marker's saturated realisation
  `M5Shoenfield.Input5R` already gives the slot (`NewRVGlue.cases_at_relGate_of_input5R`), which is
  the `←` direction of `RouteLedger.relHull_and_cases_iff_input5R`.  So the five parts are *not*
  independent of the saturation input; part 5 is a consequence of it.

* **§6 the slot's exact shape** — `caseNewRV_iff` identifies part 5 with **hull extension at the
  one-element enlargement** `stepHull S m := standingHull (closure (S ∪ {m}))`, i.e. with the same
  shape as part 1 (`G3.HullExtension`), read at `stepHull S m` instead of `standingHull S`.  Since
  `G3.HullExtension` quantifies over *all* substructures, this gives the sharpened residual
  `caseNewRV_of_hull_of_atomSat`:

      part 5  ⟸  part 1 (RelHull)  +  NewRVAtomSat

  where `NewRVAtomSat` is only "the atomic type of a new-`rv` `VF`-element over a `Standing S` is
  realised in `N`" — one atomic type per new-`rv` element, in form a much smaller statement than
  `RelFinSat`.  At the gate: `relNewRV_of_relHull_finSat : RelHull → RelFinSat → RelNewRV`.  So
  *given part 1*, part 5 costs only the one-element realisation; what `RelFinSat` pays beyond that
  is the compactness step `SatRel`, and `NewRVGlue.hull_demand_of_oneStepRVNew` (§5.8) shows the
  hull of §6 is exactly what makes the compactness step unavoidable.

## Stress tests (§5, §6.3, §7) — the hypotheses are not removable, and each tempting form is refuted

The route above consumes `SatRel` (the gate) and `QFFinSat` (the `ACVF` content).  Both are
load-bearing, machine-checked:

* **`not_forall_caseNewRV_of_satRel`** — `SatRel` **alone** does not give the slot at every pair:
  at an Archimedean target with the infinitesimal configuration the slot fails
  (`NewRVGlue.not_caseNewRV_of_infinitesimal`) while `SatRel` is exactly the pair-relative
  saturation the gate supplies.  So `QFFinSat` cannot be dropped from §1.
* **`not_relNewRV_of_config`** — `relGate` alone does **not** give `RelNewRV`: at a pair with
  `SatRel`, the size conjunct and an Archimedean target carrying the configuration, `RelNewRV` is
  *false*.  So part 5 is not implied by the gate.  (What this does **not** say is that parts 1–4
  hold at the configuration: `RouteLedger.relHull_and_cases_iff_input5R` says the five parts
  together *are* `Input5R`, and `G3.not_extendsAt_rel_of_archimedean_config` says `Input5R` fails at
  such a pair, so at a configuration pair at least one of the five must fail.  The machine-checked
  content here is that part 5 cannot be obtained from the gate, and §6 identifies what else it
  needs.)
* **`not_caseNewRV_unconditional`** — the slot is not a theorem of the tree's vocabulary at all
  (same configuration, empty gate), so no proof of `RelNewRV` can avoid an input of saturation type.
* **`finSat_forces_size`** — on this route the size conjunct of `relGate` is *produced*, not
  consumed: `SatRel + QFFinSat` give `#M ≤ #N` at any pair carrying a partial embedding.  So §1's
  hypotheses are weaker than `relGate` in that one respect, and the demand table of
  `QE/Prop39Decomp.lean` carries one more row that is not consumed anywhere on this route.
* **`not_relFinSat_of_archimedean`** — `RelFinSat` itself fails at Archimedean `relGate` pairs
  carrying the infinitesimal-room configuration (`G3.not_forall_qffinsat_at_relGate`), so part 5 and
  the `QFFinSat` hypothesis fail at the same pairs: §2's endgame is conditional exactly as
  `G3.paper_theorem_rel_of_qffinsat` is, and §1 says nothing where it does not apply.
* **`not_newRVAtomSat_of_config`** (§7.3) — the *weakest* named residual of part 5, §6.2's
  `NewRVAtomSat`, is refuted at the same configuration: the atomic type of the single new-`rv`
  element is already unrealisable there (`Hahn.not_embAt_of_infinitesimal`).  So the slot's failure
  at the configuration is not an artefact of the hull demand of §5.8.
* **`newRVAtomSat_of_global_extension`** (§7.2) — conversely `NewRVAtomSat` holds at every
  total-extension pair, so §6.2's hypothesis is not empty and `caseNewRV_of_hull_of_atomSat` is not
  a vacuously true implication.
* **`newRV_hull_demand`** — restates `NewRVGlue.hull_demand_of_oneStepRVNew` at the slot's own name:
  every witness `T` already contains the divisible hull of `Γ(S) + ℤ·vv(m)`.  This is why the slot
  cannot be discharged by `T = closure (S ∪ {m})` (`Realize.exists_oneStep`), i.e. why finite
  satisfiability alone, *without* the saturation step `SatRel`, has no chance: the one-step from
  `Realize.exists_oneStep` produces a substructure that is never `Standing` at a new-`rv` element.
* **`gatedNewRV_of_finSat`** (§7.1) — the frozen-gate twin of §2: the same `QFFinSat` hypothesis
  discharges part 5 in the `M7Paper.PaperHyp` endgame as well (there through
  `M2Saturation.qfsat_of_saturatedFS`), so neither gate's version of part 5 needs more.

No `sorry`, no `axiom`, no `native_decide`; axiom audit at the end of the file.
-/
import RouteLedger
import NewRVGlue

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.RelNewRVRoute

/-! ## 0. The residual, named

`RelFinSat` is the `QFFinSat` hypothesis of `QE/Prop39Decomp.lean`'s
`paper_theorem_rel_of_qffinsat`, at the honest gate.  §1–§2 show it discharges `RelNewRV`;
§5 shows that nothing weaker in the tree's vocabulary does. -/

/-- **The residual of the new-`rv` slot**: finite satisfiability of the pushed types at every
`relGate` pair.  This is the `ACVF` content of the paper's Lemmas 3.4–3.8 in formula form. -/
def RelFinSat : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → M2Saturation.QFFinSat M N

section Pair

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-! ## 1. The pair-level implication: `SatRel` + `QFFinSat` ⟹ the new-`rv` slot -/

/-- **`SatRel` + `QFFinSat` give `CaseNewRV`.**  The four links are the tree's own:
`G3.qfsat_of_satRel_of_qffinsat` (saturation + finite satisfiability ⟹ qf-type realisation),
`M2Saturation.satReal_of_qfsat` (qf-type realisation ⟹ saturation realisation, through the total
embedding), `G3.extendsHere_of_satReal` (`T = ⊤`), and `NewRVGlue.oneStepRVNew_of_total_extension`
(the total extension is a witness of the slot, again at `T = ⊤`).

Nothing of the slot's algebra is used: no `M5L.Separated`, no `ResidualClasses`, no `VFInvClosedOn`.
The size conjunct of `relGate` is not consumed either (§5, `finSat_forces_size`). -/
theorem caseNewRV_of_satRel_of_finSat (hSat : M1Fix.SatRel M N)
    (hfin : M2Saturation.QFFinSat M N) : M4Cases.CaseNewRV (M := M) (N := N) := by
  have hQ : M2Saturation.QFSat M N := G3.qfsat_of_satRel_of_qffinsat hSat hfin
  have hE : G3.ExtendsHere M N := G3.extendsHere_of_satReal (M2Saturation.satReal_of_qfsat hQ)
  exact NewRVGlue.oneStepRVNew_of_total_extension hE

/-- The same at the gate: only the `SatRel` conjunct of `relGate` is read. -/
theorem caseNewRV_of_relGate_of_finSat (hR : M5Shoenfield.relGate M N)
    (hfin : M2Saturation.QFFinSat M N) : M4Cases.CaseNewRV (M := M) (N := N) :=
  caseNewRV_of_satRel_of_finSat hR.1 hfin

/-! ## 2. The gate-level form: `RelFinSat` discharges part 5 of the endgame -/

end Pair

/-- **`RelFinSat` ⟹ `RelNewRV`.**  Part 5 of `QE/RouteLedger.lean`'s honest-gate endgame follows
from the single `QFFinSat` hypothesis of the `QFFinSat` route. -/
theorem relNewRV_of_finSat (hfin : RelFinSat) : RouteLedger.RelNewRV :=
  fun M N _ _ _ _ hR => caseNewRV_of_satRel_of_finSat hR.1 (hfin M N hR)

/-! ## 3. The frozen route's version: `Input5R` gives the slot -/

/-- **Marker's saturated realisation gives the new-`rv` slot.**  (The whole `Cases` ledger, in fact:
`NewRVGlue.cases_at_relGate_of_input5R`; the slot is its third field.)  So `RelNewRV` is a
*consequence* of `Input5R`, which is the other half of
`RouteLedger.relHull_and_cases_iff_input5R`. -/
theorem relNewRV_of_input5R (h5 : M5Shoenfield.Input5R) : RouteLedger.RelNewRV :=
  fun M N _ _ _ _ hR => (NewRVGlue.cases_at_relGate_of_input5R h5 hR).newRV

/-! ## 4. The endgame composition: part 5 is removable from the five-part list -/

/-- **The honest-gate endgame with part 5 discharged by `RelFinSat`.**  Compared with
`RouteLedger.paper_theorem_2_3_of_five_rel` the `RelNewRV` hypothesis is gone: the list is
`ShoenfieldTestRel + RelFinSat + RelHull + RelSeparated + RelUnit + RelNonUnit`.  Since
`RelFinSat` is one statement for *all* of the five parts' gates, the canonical single-hypothesis
form of the endgame (`G3.paper_theorem_rel_of_qffinsat`) dominates this one; it is recorded so that
the u6 matrix has a machine-checked row for part 5 that composes with the other members' rows. -/
theorem paper_theorem_2_3_of_finSat_and_four (hQ : M5Shoenfield.ShoenfieldTestRel)
    (hfin : RelFinSat) (hHull : RouteLedger.RelHull) (hsep : RouteLedger.RelSeparated)
    (hu : RouteLedger.RelUnit) (hn : RouteLedger.RelNonUnit) : HasQE Axioms.ACVF :=
  RouteLedger.paper_theorem_2_3_of_five_rel hQ hHull hsep hu hn (relNewRV_of_finSat hfin)

/-- The same with part 5 coming from the quotation route instead: the consistency check that the
two sources of the slot agree at the level of the endgame. -/
theorem paper_theorem_2_3_of_input5R_and_four (hQ : M5Shoenfield.ShoenfieldTestRel)
    (h5 : M5Shoenfield.Input5R) (hHull : RouteLedger.RelHull)
    (hsep : RouteLedger.RelSeparated) (hu : RouteLedger.RelUnit)
    (hn : RouteLedger.RelNonUnit) : HasQE Axioms.ACVF :=
  RouteLedger.paper_theorem_2_3_of_five_rel hQ hHull hsep hu hn (relNewRV_of_input5R h5)

/-! ## 5. Stress tests

The hypotheses of §1 are `M1Fix.SatRel M N` (the gate's saturation conjunct) and
`M2Saturation.QFFinSat M N` (the `ACVF` content).  §5.1–§5.4 show that `QFFinSat` is not removable
in the only direction that the tree can test; §5.5 shows that the *conclusion* of §1 is not absurd
(it holds at every total-extension pair); §5.6 shows that the size conjunct of `relGate` is
*produced* by §1's hypotheses rather than consumed; §5.7 shows that `RelFinSat` is itself not a
theorem at every gate pair, i.e. §2's endgame is conditional in exactly the way
`G3.paper_theorem_rel_of_qffinsat` is, and names the pairs where it is not applicable. -/

section Stress

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **The infinitesimal configuration of `QE/NewRVGlue.lean` §2**, bundled: an Archimedean target
`N`, a `Standing S` embedded in `N`, a positive `RV`-element `s ∈ S`, and a `VF`-element `m ∉ S`
whose `rv` is positive, infinitesimal below `s` and **new** (`iRv m ∉ S`).  This is the configuration
at which the new-`rv` slot is refutable; bundling it keeps the stress tests below readable. -/
structure NewRVConfig (M N : Type) [LRV.Structure M] [LRV.Structure N] where
  /-- the target's value group is Archimedean (`QE/HahnObstruction.lean` §2) -/
  arch : Hahn.ArchimedeanRV N
  /-- the domain substructure -/
  S : LRV.Substructure M
  /-- the partial embedding -/
  f : S ↪[LRV] N
  /-- the domain is `Standing` -/
  standing : Assembly.Standing S
  /-- the positive `RV` bound in `S` -/
  s : M
  s_mem : s ∈ S
  s_rv : iRV s
  s_ne : s ≠ iRVZero
  s_gt : ¬ iLe s iRVOne
  /-- the new-`rv` `VF`-element -/
  m : M
  m_vf : iVF m
  m_notMem : m ∉ S
  m_gt : ¬ iLe (iRv m) iRVOne
  m_inf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s
  /-- **`rv` is new**: the applicability condition of the slot itself -/
  m_rvnew : iRv m ∉ S

/-- **§5.1 the configuration refutes the slot** (`NewRVGlue.not_caseNewRV_of_infinitesimal`, at the
slot's own name `M4Cases.CaseNewRV`). -/
theorem not_caseNewRV_of_config (C : NewRVConfig M N) :
    ¬ M4Cases.CaseNewRV (M := M) (N := N) :=
  NewRVGlue.not_caseNewRV_of_infinitesimal (f := C.f) C.arch C.standing C.s_mem C.s_rv C.s_ne C.s_gt
    C.m_vf C.m_notMem C.m_gt C.m_inf C.m_rvnew

/-- **§5.2 `SatRel` alone is not enough.**  The tempting form "`M1Fix.SatRel` ⟹ the slot, at every
pair" — i.e. dropping `QFFinSat` from §1 — is **false**: at the configuration, `SatRel` gives no
witness of the slot, because a witness would realise the pushed infinitesimal type and
`Hahn.not_embAt_of_infinitesimal` refutes that at an Archimedean target.  So the `QFFinSat`
conjunct of §1 is load-bearing: it is exactly what the tree cannot derive from the gate, and it is
what §1 must consume. -/
theorem not_forall_caseNewRV_of_satRel (C : NewRVConfig M N) (hSat : M1Fix.SatRel M N) :
    ¬ (∀ (M' N' : Type) [LRV.Structure M'] [LRV.Structure N'] [M' ⊨ Axioms.ACVF] [N' ⊨ Axioms.ACVF],
        M1Fix.SatRel M' N' → M4Cases.CaseNewRV (M := M') (N := N')) :=
  fun h => not_caseNewRV_of_config C ((h M N) hSat)

/-- **§5.3 `relGate` alone is not enough either.**  At a pair carrying the configuration *and* the
gate, `RouteLedger.RelNewRV` is false: the gate is `SatRel` plus the size conjunct and neither
supplies a witness, while the slot is refuted at the pair.  Hence part 5 of the honest-gate endgame
is **not** implied by the gate, and in particular §5.2's defect is not repaired by the size
conjunct.  (Consequence: any proof of `RelNewRV` consumes a hypothesis whose content is beyond
`relGate` — the tree's candidate is `RelFinSat`, §2.) -/
theorem not_relNewRV_of_config (C : NewRVConfig M N) (hSat : M1Fix.SatRel M N)
    (hsize : M7Paper.SizeHyp M N) : ¬ RouteLedger.RelNewRV :=
  fun h => not_caseNewRV_of_config C (h M N ⟨hSat, hsize⟩)

/-- **§5.4 The slot is not a theorem of the tree's vocabulary at all.**  With no gate whatsoever the
universal statement is false, so no amount of algebra in `L_RV` alone produces it: the input must be
a saturation statement (`SatRel`, `QFFinSat`, `Input5R`, `SaturatedFS` — any of the tree's). -/
theorem not_caseNewRV_unconditional (C : NewRVConfig M N) :
    ¬ (∀ (M' N' : Type) [LRV.Structure M'] [LRV.Structure N'] [M' ⊨ Axioms.ACVF] [N' ⊨ Axioms.ACVF],
        M4Cases.CaseNewRV (M := M') (N := N')) :=
  fun h => not_caseNewRV_of_config C (h M N)

/-- **§5.5 The conclusion of §1 is consistent**: at a pair where every partial embedding extends
totally, the whole `M4Cases.Cases` ledger holds (`M4Cases.cases_of_global_extension`), hence the
slot.  So §1's conclusion is not absurd, and the hypothesis `QFFinSat`, which gives the total
extension through §1's chain, is a genuine sufficient condition. -/
theorem caseNewRV_of_global_extension
    (hglob : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ∃ g : M ↪[LRV] N,
      ∀ x : S, g (x : M) = f x) : M4Cases.CaseNewRV (M := M) (N := N) :=
  (M4Cases.cases_of_global_extension hglob).newRV

/-- **§5.6 The size conjunct of `relGate` is produced, not consumed.**  `SatRel` + `QFFinSat` give
`#M ≤ #N` at any pair carrying a partial embedding (`M2Saturation.qfsat_forces_size`, through
qf-type realisation).  So §1's hypotheses are strictly weaker than `relGate` in this one respect:
the gate's second conjunct is never read. -/
theorem finSat_forces_size (hSat : M1Fix.SatRel M N) (hfin : M2Saturation.QFFinSat M N)
    (S : LRV.Substructure M) (f : S ↪[LRV] N) : Cardinal.mk M ≤ Cardinal.mk N :=
  M2Saturation.qfsat_forces_size (G3.qfsat_of_satRel_of_qffinsat hSat hfin) S f

/-- **§5.7 `RelFinSat` is not a theorem at every gate pair.**  `QE/Prop39Decomp.lean`'s refutation,
read as a statement about §0's residual: at an Archimedean `relGate` pair carrying the
infinitesimal-room configuration, finite satisfiability of the pushed types fails
(`G3.not_finSat_of_satRel_of_archimedean`).  So §2's endgame is conditional exactly as
`G3.paper_theorem_rel_of_qffinsat` is: at such a pair nothing in §1 applies, and the slot is
correspondingly refuted (§5.1).  This is the exact sense in which the `QFFinSat` route and the
`oneStepRVNew_of_total_extension` route agree about *where* the obstruction sits. -/
theorem not_relFinSat_of_archimedean (hSat : M1Fix.SatRel M N) (hsize : M7Paper.SizeHyp M N)
    (hArch : Hahn.ArchimedeanRV N) {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmRV : iRV m) (hmne : m ≠ iRVZero) (hmgt : ¬ iLe m iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow s n) m) : ¬ RelFinSat :=
  fun h => G3.not_forall_qffinsat_at_relGate (f := f) hSat hsize hArch hsS hsRV hsne hsgt hmRV hmne hmgt
    hinf h

/-- **§5.8 The slot's own demand**, restated at the slot's name: every witness contains the whole
divisible hull of `Γ(S) + ℤ·vv(m)`.  So the one-step that finite satisfiability alone produces
(`Realize.exists_oneStep` at `T = closure (S ∪ {m})`) can never be a witness: `Standing` at a
new-`rv` element forces roots-up-to-units of every order.  This is why §1 needs `SatRel` (the
compactness step that produces a *total* extension) and not merely the realisation of one element. -/
theorem newRV_hull_demand (h : M4Cases.CaseNewRV (M := M) (N := N))
    {S : LRV.Substructure M} {f : S ↪[LRV] N} (hS : Assembly.Standing S) {m : M}
    (hmVF : iVF m) (hrvnew : iRv m ∉ S) (hrv0 : iRv m ≠ iRVZero) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧
        ∀ n : ℕ, 1 ≤ n → ∃ u c : M, u ∈ T ∧ iRV u ∧ u ≠ iRVZero ∧ c ∈ T ∧ iUnits c ∧
          Assembly.rvPow u n = iRVMul (iRv m) c :=
  NewRVGlue.hull_demand_of_oneStepRVNew h hS hmVF hrvnew hrv0

end Stress

/-! ## 6. The slot's exact shape: hull extension at the one-element enlargement

`G3.HullExtension` (part 1 of the endgame) and `M5.OneStepRVNew` (part 5) look like different kinds
of statement: part 1 extends an embedding along the *fixed* minimal `Standing` superset
`M8Hull.standingHull S`, part 5 asks for *some* `Standing T ⊇ S` containing a given element `m`.
This section shows they are the same shape: the minimal `Standing` superset of `S` containing `m` is
`stepHull S m := standingHull (closure (S ∪ {m}))`, and part 5 is exactly "every embedding of a
`Standing S` extends to `stepHull S m`" (§6.1, `caseNewRV_iff`).

Two consequences:

* **§6.2 a sharper residual.**  `G3.HullExtension` is quantified over *all* substructures, so it
  applies at `closure (S ∪ {m})`.  Hence

      part 5  ⟸  part 1  +  "the atomic type of a new-`rv` `VF`-element over a `Standing S` is
                              realised in `N`"

  (`caseNewRV_of_hull_of_atomSat`).  The second conjunct, `NewRVAtomSat`, is one atomic-type
  realisation per *new-`rv` element* — a strictly smaller statement, in form, than `RelFinSat`
  (§2), which asks for every *formula* of every pushed type.  So given part 1, part 5 does not need
  the full saturation input.  At the gate:
  `relNewRV_of_relHull_finSat : RelHull → RelFinSat → RelNewRV`.

* **§6.3 the residual `NewRVAtomSat` is still not removable**, and *why*: `Realize.exists_oneStep`
  turns one realised atomic type into an embedding of `closure (S ∪ {m})`, which is **not**
  `Standing` (`NewRVGlue.hull_demand_of_oneStepRVNew`): the slot needs the hull as well.  That is
  precisely what §6.2 spends part 1 on, and it is why `NewRVAtomSat` alone gives no slot (the
  finite-satisfiability route cannot produce a `Standing` witness, §5.8).

No `sorry`, no `axiom`; the axioms of §6 are audited with the rest at the end of the file. -/

section StepHull

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **The minimal `Standing` superset of `S` containing `m`.**  The hull computation of
`QE/StandingHull.lean` applied to the substructure generated by `S` and `m`. -/
noncomputable def stepHull (S : LRV.Substructure M) (m : M) : LRV.Substructure M :=
  M8Hull.standingHull (Substructure.closure LRV ((S : Set M) ∪ {m}))

theorem le_stepHull (S : LRV.Substructure M) (m : M) : S ≤ stepHull S m :=
  fun _ hx => M8Hull.le_standingHull _ (Substructure.subset_closure (Set.mem_union_left _ hx))

theorem mem_stepHull (S : LRV.Substructure M) (m : M) : m ∈ stepHull S m :=
  M8Hull.le_standingHull _ (Substructure.subset_closure (Set.mem_union_right _ (by simp)))

theorem standing_stepHull (S : LRV.Substructure M) (m : M) : Assembly.Standing (stepHull S m) :=
  M8Hull.standing_standingHull _

/-- `stepHull` is contained in every `Standing` superset of `S` containing `m`: it is the *minimal*
one. -/
theorem stepHull_le {S T : LRV.Substructure M} {m : M} (hST : S ≤ T) (hm : m ∈ T)
    (hT : Assembly.Standing T) : stepHull S m ≤ T := by
  have hcl : Substructure.closure LRV ((S : Set M) ∪ {m}) ≤ T := by
    refine Substructure.closure_le.mpr ?_
    rintro y (hy | hy)
    · exact hST hy
    · rw [Set.mem_singleton_iff] at hy
      exact hy ▸ hm
  exact (M8Hull.standingHull_mono hcl).trans (M8Hull.standingHull_le le_rfl hT)

/-- **§6.1 The new-`rv` slot is hull extension at the one-element enlargement.**  `CaseNewRV` is
*equivalent* to: every embedding of a `Standing S` extends to `stepHull S m`, for every `VF`-element
`m` with new `rv`.  So part 5 is the same kind of statement as part 1 (`G3.HullExtension`), read at
`stepHull S m` instead of `standingHull S`; what separates them is that `G3.HullExtension`'s
quantifier runs over *given* substructures only. -/
theorem caseNewRV_iff :
    M4Cases.CaseNewRV (M := M) (N := N) ↔
      ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
        iRv m ∉ S →
        ∃ g : stepHull S m ↪[LRV] N, ∀ x : S, g ⟨(x : M), le_stepHull S m x.2⟩ = f x := by
  constructor
  · intro h S f hS m hmVF hmrv
    obtain ⟨T, g, hST, hagree, hmT, hStand⟩ := h S f hS m hmVF hmrv
    have hstep : stepHull S m ≤ T := stepHull_le hST hmT hStand
    refine ⟨g.comp (Substructure.inclusion hstep), ?_⟩
    intro x
    have h1 : (Substructure.inclusion hstep) ⟨(x : M), le_stepHull S m x.2⟩
        = ⟨(x : M), hST x.2⟩ := rfl
    show g ((Substructure.inclusion hstep) ⟨(x : M), le_stepHull S m x.2⟩) = f x
    rw [h1]
    exact hagree x
  · intro h S f hS m hmVF hmrv
    obtain ⟨g, hg⟩ := h S f hS m hmVF hmrv
    exact ⟨stepHull S m, g, le_stepHull S m, hg, mem_stepHull S m, standing_stepHull S m⟩

/-- **§6.2 the atomic-type realisation the slot's residual really needs**: one realised atomic type
per new-`rv` `VF`-element over a `Standing` substructure.  (One atomic type, not every formula of
every pushed type: `RelFinSat` ⟹ this, `newRVAtomSat_of_finSat`.) -/
def NewRVAtomSat (M N : Type) [LRV.Structure M] [LRV.Structure N] : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∉ S →
    ∃ b : N, Realize.RealizesAtomic S f m b

/-- **§6.2 `HullExtension` + atomic realisation of the new-`rv` element ⟹ the slot.**  The realised
atomic type produces an embedding of `closure (S ∪ {m})` (`Realize.exists_oneStep`); the hull
extension, applied at that closure (it quantifies over *all* substructures), produces the embedding
of `stepHull S m = standingHull (closure (S ∪ {m}))` that §6.1 asks for.

So part 5 = part 1 + one-element atomic realisation.  The second conjunct is strictly smaller in
form than the saturation input; the first is exactly the hull form the endgame already lists. -/
theorem caseNewRV_of_hull_of_atomSat (hHull : G3.HullExtension (M := M) (N := N))
    (hatom : NewRVAtomSat (M := M) (N := N)) : M4Cases.CaseNewRV (M := M) (N := N) := by
  intro S f hS m hmVF hmrv
  have hmS : m ∉ S := fun h => hmrv (M5L.rv_mem_sub S h)
  obtain ⟨b, hb⟩ := hatom S f hS m hmVF hmrv
  obtain ⟨T, g, hST, hmT, hagree⟩ := Realize.exists_oneStep hb hmS
  obtain ⟨g', hg'⟩ := hHull T g
  exact ⟨M8Hull.standingHull T, g', fun _ hx => M8Hull.le_standingHull T (hST hx),
    fun x => (hg' ⟨(x : M), hST x.2⟩).trans (hagree x),
    M8Hull.le_standingHull T hmT, M8Hull.standing_standingHull T⟩

/-- **`RelFinSat` gives the atomic realisation of §6.2** (through qf-type realisation). -/
theorem newRVAtomSat_of_finSat (hSat : M1Fix.SatRel M N) (hfin : M2Saturation.QFFinSat M N) :
    NewRVAtomSat (M := M) (N := N) :=
  fun S f _ m _ _ => G3.qfsat_of_satRel_of_qffinsat hSat hfin S f m

end StepHull

/-- **§6.2 at the gate: part 1 + `RelFinSat` give part 5.**  This is the sharpened form of §2:
`RelNewRV` follows from the endgame's own hull part `RelHull` together with the same single
`QFFinSat` hypothesis.  (Also a cross-check of the endgame list: with part 1 granted, part 5 costs
only the one-element atomic realisation of §6.2.) -/
theorem relNewRV_of_relHull_finSat (hHull : RouteLedger.RelHull) (hfin : RelFinSat) :
    RouteLedger.RelNewRV :=
  fun M N _ _ _ _ hR =>
    caseNewRV_of_hull_of_atomSat (hHull M N hR) (newRVAtomSat_of_finSat hR.1 (hfin M N hR))

/-- **§6.3 the sharpened residual at the gate, named**: one realised atomic type per new-`rv`
`VF`-element over a `Standing` substructure, at every `relGate` pair.  `RelFinSat` implies it
(`relAtomSat_of_finSat`) and Marker's saturated realisation implies it (`relAtomSat_of_input5R`);
together with part 1 it gives part 5. -/
def RelAtomSat : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M5Shoenfield.relGate M N → NewRVAtomSat (M := M) (N := N)

/-- **§6.3 part 1 + the sharpened residual give part 5** (the gate form of
`caseNewRV_of_hull_of_atomSat`).  This is the sharpest sufficient condition for `RelNewRV` that this
file produces: the hull computation of the endgame's part 1 plus a single atomic type per
new-`rv` element. -/
theorem relNewRV_of_relHull_atomSat (hHull : RouteLedger.RelHull) (hatom : RelAtomSat) :
    RouteLedger.RelNewRV :=
  fun M N _ _ _ _ hR => caseNewRV_of_hull_of_atomSat (hHull M N hR) (hatom M N hR)

/-- `RelFinSat` gives the sharpened residual, so §2's route is the special case of §6.3 with
`RelHull` dropped. -/
theorem relAtomSat_of_finSat (hfin : RelFinSat) : RelAtomSat :=
  fun M N _ _ _ _ hR => newRVAtomSat_of_finSat hR.1 (hfin M N hR)

/-- Marker's saturated realisation gives the sharpened residual too. -/
theorem relAtomSat_of_input5R (h5 : M5Shoenfield.Input5R) : RelAtomSat :=
  fun M N _ _ _ _ hR S f _ m _ _ => M2Saturation.qfsat_of_satReal (h5 M N hR) S f m

/-! ## 7. The frozen gate, and the non-vacuity of §6's residual

The endgame has two gates (`QE/RouteLedger.lean` §5, §6).  §7.1 records the frozen-gate twin of
§2 (`GatedNewRV` from `QFFinSat` at `M7Paper.PaperHyp`), where the saturation conjunct is the
`∀ M`-quantified `Assembly.SaturatedFS` instead of `M1Fix.SatRel`; §7.2 checks that §6.2's residual
`NewRVAtomSat` is not vacuous — at a total-extension pair it holds. -/

section Frozen

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **§7.1 the frozen gate: `PaperHyp` + `QFFinSat` ⟹ the slot.**  Here the saturation input is
`Assembly.SaturatedFS N` (the first conjunct of `M7Paper.PaperHyp`), so
`M2Saturation.qfsat_of_saturatedFS` replaces `G3.qfsat_of_satRel_of_qffinsat`. -/
theorem caseNewRV_of_paperHyp_of_finSat (hP : M7Paper.PaperHyp M N)
    (hfin : M2Saturation.QFFinSat M N) : M4Cases.CaseNewRV (M := M) (N := N) :=
  NewRVGlue.oneStepRVNew_of_total_extension
    (G3.extendsHere_of_satReal
      (M2Saturation.satReal_of_qfsat (M2Saturation.qfsat_of_saturatedFS hP.1 hfin)))

/-- **§7.2 `NewRVAtomSat` is satisfiable**: at a pair where every partial embedding extends totally,
the atomic type of every element is realised (by the image of the element).  So §6.2's residual is
not an empty hypothesis, and `caseNewRV_of_hull_of_atomSat` is not a vacuous implication. -/
theorem newRVAtomSat_of_global_extension
    (hglob : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ∃ g : M ↪[LRV] N,
      ∀ x : S, g (x : M) = f x) : NewRVAtomSat (M := M) (N := N) := by
  intro S f _ m _ _
  obtain ⟨g, hg⟩ := hglob S f
  refine ⟨g m, ?_⟩
  have h := M2Saturation.realizesAtomic_of_extends (S := S) (T := ⊤) (f := f)
    (g := g.domRestrict ⊤) le_top (fun x => hg x) (Substructure.mem_top m)
  simpa using h

/-- **§7.3 §6.2's residual `NewRVAtomSat` is itself refuted at the configuration.**  A realised
atomic type of the new-`rv` element gives an embedding of `closure (S ∪ {m})` containing `m`
(`Realize.exists_oneStep`), i.e. the embedding half `Hahn.EmbAt S f m`, which
`Hahn.not_embAt_of_infinitesimal` refutes at an Archimedean target.  So the failure of part 5 at the
configuration is *not* attributable to the hull demand of §5.8: the atomic type of the single
new-`rv` element is already unrealisable there.  This is the sharpest form of the stress test — the
weakest named residual of part 5 fails exactly where the slot does. -/
theorem not_newRVAtomSat_of_config (C : NewRVConfig M N) :
    ¬ NewRVAtomSat (M := M) (N := N) := by
  intro h
  obtain ⟨b, hb⟩ := h C.S C.f C.standing C.m C.m_vf C.m_rvnew
  have hmS : C.m ∉ C.S := fun hmem => C.m_rvnew (M5L.rv_mem_sub C.S hmem)
  obtain ⟨T, g, hST, hmT, hagree⟩ := Realize.exists_oneStep hb hmS
  exact Hahn.not_embAt_of_infinitesimal (S := C.S) (f := C.f) C.arch C.s_mem C.s_rv C.s_ne C.s_gt
    C.m_vf C.m_notMem C.m_gt C.m_inf ⟨T, g, hST, hagree, hmT⟩

end Frozen

/-- **§7.1 at the gate: `QFFinSat` at `PaperHyp` discharges the frozen endgame's new-`rv` part.** -/
theorem gatedNewRV_of_finSat
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M7Paper.PaperHyp M N → M2Saturation.QFFinSat M N) : RouteLedger.GatedNewRV :=
  fun M N _ _ _ _ hP => caseNewRV_of_paperHyp_of_finSat hP (hfin M N hP)

/-- **§7.1 the frozen endgame with part 5 discharged by `QFFinSat`**: the frozen-gate analogue of
§4's `paper_theorem_2_3_of_finSat_and_four`, composing with `RouteLedger.paper_theorem_2_3_of_five`.
So the same single hypothesis removes the new-`rv` part from *both* endgame lists. -/
theorem paper_theorem_2_3_of_finSat_and_four_gated (hShoen : M7Paper.ShoenfieldTestSat)
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M7Paper.PaperHyp M N → M2Saturation.QFFinSat M N)
    (hHull : RouteLedger.GatedHull) (hsep : RouteLedger.GatedSeparated)
    (hu : RouteLedger.GatedUnit) (hn : RouteLedger.GatedNonUnit) : HasQE Axioms.ACVF :=
  RouteLedger.paper_theorem_2_3_of_five hShoen hHull hsep hu hn (gatedNewRV_of_finSat hfin)

end SpecialTransformations.Milestone0.RelNewRVRoute

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.caseNewRV_of_satRel_of_finSat
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.caseNewRV_of_relGate_of_finSat
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.relNewRV_of_finSat
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.relNewRV_of_input5R
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.paper_theorem_2_3_of_finSat_and_four
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.paper_theorem_2_3_of_input5R_and_four

#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.not_caseNewRV_of_config
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.not_forall_caseNewRV_of_satRel
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.not_relNewRV_of_config
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.not_caseNewRV_unconditional
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.caseNewRV_of_global_extension
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.finSat_forces_size
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.not_relFinSat_of_archimedean
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.newRV_hull_demand

#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.le_stepHull
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.mem_stepHull
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.standing_stepHull
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.stepHull_le
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.caseNewRV_iff
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.caseNewRV_of_hull_of_atomSat
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.newRVAtomSat_of_finSat
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.relNewRV_of_relHull_finSat

#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.caseNewRV_of_paperHyp_of_finSat
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.newRVAtomSat_of_global_extension
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.gatedNewRV_of_finSat

#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.not_newRVAtomSat_of_config

#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.paper_theorem_2_3_of_finSat_and_four_gated

#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.relNewRV_of_relHull_atomSat
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.relAtomSat_of_finSat
#print axioms SpecialTransformations.Milestone0.RelNewRVRoute.relAtomSat_of_input5R
