/-
# Shoenfield's test for quantifier elimination: transcription, fit, and the exact gap

Direction e1, swarm `smw2jkpn4` (member m5).  The frozen Theorem-2.3 route
(`QE/M5Ledger.lean` §10b, `paper_theorem_2_3_sat_of_ledger_paperHyp`) consumes as its first
hypothesis

    M7Paper.ShoenfieldTestSat  :=  M7Paper.Prop39Sat → HasQE Axioms.ACVF

and the paper takes this step in one sentence (`refs/qe.tex` l. 827: "This proposition and
Shoenfield's test immediately yield [QE]").  This file does three things.

## 1. The quotation

`ShoenfieldTestRel` (§3) is Shoenfield's test transcribed as a `Prop` in the `ClassicalProps`
style, at the frozen interface (language `L_RV`, theory `Axioms.ACVF`), in the *extension* form:

> if every embedding of a substructure of a model `M` of `T` into a model `N` of `T` that is
> `‖M‖⁺`-saturated extends to an embedding of all of `M`, then `T` has quantifier elimination.

Sources, quoted content only, never proved here:

* J. R. Shoenfield, *A theorem on quantifier elimination* (1971) — the original;
* D. Marker, *Model Theory: An Introduction*, Theorem 5.7 (cardinality form, with the
  proper-extension variant) and Theorem 5.4 / Corollary 3.1.6 (the common-substructure and
  back-and-forth forms);
* Z. Chatzidakis, *Model Theory* (CUP notes) 2.27 — the `ℵ₁`-saturated back-and-forth form.

`‖M‖⁺`-saturation is transcribed pair-relatively as `M1Fix.SatRel M N`: `QE/M1Fix.lean` §2 is where
the frozen, `∀ M`-quantified `Assembly.SaturatedFS` is compared with it, and the identification
`SaturatedFS N ↔ ∀ M, SatRel M N` is that file's `saturatedFS_iff`.

Why the extension form and not the amalgamation form (`QE/M1Fix.lean`'s `QFEAmalg`): (i) the
sentence of the paper consumes the extension statement `lrv:mono:lift` (Proposition 3.9), and the
ledger's `Prop39Sat` is exactly that statement; (ii) `QFEAmalg` is already wired to the frozen
target on its own (`M1Fix.hasQE_of_qfEAmalg`), so it does not need a transcription here — but it is
*not* a transcription of Shoenfield's test, it is the amalgamation criterion Marker derives from it,
and it bypasses Proposition 3.9 entirely.  Both are recorded; the ledger's route needs (i).

## 2. The fit, and the exact gap

The frozen `ShoenfieldTestSat` is `QEOfGate paperGate` with
`paperGate M N = M7Paper.PaperHyp M N = Assembly.SaturatedFS N ∧ #M ≤ #N` (§1, machine-checked as
`shoenfieldTestSat_iff_QEOfGate`).  The quote is `QEOfGate relGate` with
`relGate M N = M1Fix.SatRel M N ∧ #M ≤ #N`.  Then:

* **`paperGate → relGate` is a theorem** (`paperGate_le_relGate`), because `SaturatedFS N` is
  `∀ M, SatRel M N` (`M1Fix.saturatedFS_iff`).  Hence by gate monotonicity
  (`QEOfGate_of_le`) the frozen hypothesis *implies* the quote
  (`shoenfieldTestRel_of_shoenfieldTestSat`).  So the frozen input is *at least as strong* as
  Shoenfield's test.
* **The converse needs `relGate → paperGate`** (`SatBridge`, §4), which the machine-checked
  decomposition `satBridge_iff` identifies with the single statement

      SatRel M N → Assembly.SaturatedFS N,

  i.e. with the upgrade of the *pair-relative* saturation to the frozen `∀ M`-quantified one.  That
  is the whole gap, and it is not a statement any book supplies: `Assembly.SaturatedFS N` quantifies
  over models of unbounded cardinality, while `‖M‖⁺`-saturation is a property of the pair.
  (`QE/M1Fix.lean` §2 already says the frozen quantifier order is the wrong one; this file is where
  its effect on the *criterion* is isolated.)
* **The size conjunct is not the obstruction** (it is in `relGate` by construction); the obstruction
  is the quantifier order.  So the honest input to a route is the quote plus five inputs stated at
  `relGate`, not `ShoenfieldTestSat` (§6).

## 3. Consequence: which gate the route should use, machine-checked

§5 records that a criterion at a gate `G` collapses to the target as soon as no pair satisfies `G`:
`shoenfieldTestSat_iff_hasQE_of_noPaperHyp`.  Under the natural expectation
`¬ SaturatedFS N` for every set-sized `N` (a model cannot be `κ`-saturated for all `κ`; not
machine-checked here, cf. `QE/M1Fix.lean` §2 and direction e2), the frozen input 1 is literally
*equivalent* to the theorem it is used to prove (`shoenfieldTestSat_iff_hasQE_of_noSaturatedFS`).
So the frozen `PaperHyp` gate cannot be the place to consume the quotation.

§6 therefore re-runs the §10b ledger at `relGate`, with the same five inputs (bodies unchanged) and
the same `OneStepSizeFree`.  The trade-off is explicit, and it is why the choice matters: the inputs
at `relGate` are *stronger* statements than the frozen ones at `paperGate` (the gate is larger — it
drops the `∀ M`-quantified `SaturatedFS` and keeps the pair-relative saturation), which is exactly
what the paper proves: Lemmas 3.3–3.9 are proved at *every* pair with `‖M‖⁺`-saturation and never use
a size conjunct as a hypothesis.  The gate must be the same at both ends of the route; §10b picks
the criterion's gate (`paperGate`), at which the criterion is not Shoenfield's test, rather than the
paper's gate (`relGate`), at which it is.

    paper_theorem_2_3_rel : ShoenfieldTestRel → Input1R → LedgerInput2 → Input3R → Input4R →
                            Input5R → (OneStepVFP at relGate) → HasQE Axioms.ACVF

and from it derives, rather than assumes, the frozen input (`shoenfieldTestSat_of_relLedger_gated`)
and the frozen Proposition 3.9 at the paper's pair (`prop39Sat_of_relLedger_gated`).  (`..._of_free`
and the ungated `..._of_relLedger` take the frozen `OneStepSizeFree` instead, which m7 has refuted,
so the gated forms are the usable ones.)  Nothing new is proved
about `ACVF` here: every hypothesis of the repaired route is either the quotation, one of the five
paper/Marker/Prestel–Engler inputs, or the frozen one-step obligation.

No `sorry`, no `axiom`, no `native_decide`.
-/
import M5Ledger
import M1Fix

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations
namespace Milestone0
namespace M5Shoenfield

/-! ## 1. Pair hypotheses ("gates") as first-class objects

A gate is a property of a pair of `L_RV`-structures.  Stating a criterion, an input or a ledger at
a gate is what lets the *same* assembly be reused at the frozen `PaperHyp` and at the paper's own
saturation hypothesis; the whole e1 gap is then a statement about gates. -/

/-- A pair hypothesis: which pairs `(M, N)` count as "the paper's pair" `§3.1`. -/
abbrev Gate := ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N], Prop

/-- The frozen gate: `N` is `‖M‖⁺`-saturated in the `∀ M`-quantified reading
(`Assembly.SaturatedFS`) together with `#M ≤ #N`.  This is `M7Paper.PaperHyp`. -/
def paperGate : Gate := fun M N _ _ => M7Paper.PaperHyp M N

/-- The paper's `§3.1` hypothesis, pair-relatively: `N` is `‖M‖⁺`-saturated *at this pair*
(`M1Fix.SatRel M N`, the reading `QE/M1Fix.lean` §2 identifies as the one `‖M‖⁺`-saturation gives),
together with the size conjunct. -/
def relGate : Gate := fun M N _ _ => M1Fix.SatRel M N ∧ M7Paper.SizeHyp M N

/-- **`PaperHyp` implies the pair-relative hypothesis.**  The only content is that the frozen
`Assembly.SaturatedFS N` is `∀ M, SatRel M N` (`M1Fix.saturatedFS_iff`); the size conjunct is
shared.  This is the direction of gate inclusion that makes the frozen input *stronger* than the
quotation. -/
theorem paperGate_le_relGate :
    ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      paperGate M N → relGate M N := by
  intro M N _ _ _ _ hP
  exact ⟨(M1Fix.saturatedFS_iff).mp hP.1 M, hP.2⟩

/-- The same, spelled out at a fixed pair and against the frozen names, for reuse downstream. -/
theorem satRel_of_saturatedFS {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [M ⊨ Axioms.ACVF] (h : Assembly.SaturatedFS N) : M1Fix.SatRel M N :=
  (M1Fix.saturatedFS_iff).mp h M

/-! ## 2. The extension property and the criterion at a gate -/

/-- **The extension property at a gate**: every embedding of a substructure of `M` into `N` extends
to an embedding of all of `M`, for every pair admitted by `G`.  This is the conclusion of the
paper's Proposition 3.9 (`lrv:mono:lift`), and at `paperGate` it is `M7Paper.Prop39Sat` verbatim. -/
def ExtendsAt (G : Gate) : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    G M N → ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
      ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x

/-- **A criterion for quantifier elimination at a gate**: if the extension property holds at every
pair admitted by `G`, then `ACVF` admits quantifier elimination in `L_RV`.  This is the shape of
Shoenfield's test; which gate is used is the whole question. -/
def QEOfGate (G : Gate) : Prop := ExtendsAt G → HasQE Axioms.ACVF

/-- The frozen `Prop39Sat` **is** the extension property at the frozen gate (definitional). -/
theorem prop39Sat_iff_extendsAt_paperGate :
    M7Paper.Prop39Sat ↔ ExtendsAt paperGate :=
  Iff.rfl

/-- The frozen input 1 **is** the criterion at the frozen gate (definitional).  This is the
"definitional part" of the fit: `ShoenfieldTestSat`'s shape `Prop39Sat → HasQE` is exactly
Shoenfield's criterion shape, and nothing about the mathematics is hidden in the notation. -/
theorem shoenfieldTestSat_iff_QEOfGate :
    M7Paper.ShoenfieldTestSat ↔ QEOfGate paperGate :=
  Iff.rfl

/-- **Gate monotonicity of the criterion.**  If every `G`-pair is an `H`-pair, then the criterion
at `G` implies the criterion at `H`: the criterion at the *smaller* gate is the *stronger*
statement, because it asks the extension property to hold at fewer pairs.  (This is the abstract
form of the observation that makes the frozen input stronger than the quotation.) -/
theorem QEOfGate_of_le {G H : Gate}
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], G M N → H M N)
    (hQ : QEOfGate G) : QEOfGate H := by
  intro hExt
  refine hQ ?_
  intro M N _ _ _ _ hG S f
  exact hExt M N (h M N hG) S f

/-! ## 3. The quotation

Nothing below in this section is proved; the two `def`s are the book statement, and every later
theorem is wiring between them and the frozen names. -/

/-- **Shoenfield's test for quantifier elimination** (Shoenfield 1971; Marker, *Model Theory: An
Introduction*, Theorem 5.7 with Theorem 5.4; Chatzidakis 2.27), transcribed at the frozen interface.

*Content, as quoted.*  Let `T` be a satisfiable theory in a language `L` and `κ = card(L)`.  Then
`T` admits quantifier elimination if the following holds: whenever `A, B ⊨ T`, `B` is
`κ`⁺-saturated (Marker's small-model form) — or, in the form used here, `B` is `‖A‖⁺`-saturated for
the `A` at hand — and `f` is an `L`-embedding of a substructure of `A` into `B`, then `f` extends to
an `L`-embedding of `A` into `B`.

*Deviations from the printed statements, all in the direction of the paper's use.*
(Marker 5.7 states the *proper*-extension version, one element at a time; iterating it through a
well-ordering of `A` gives the total-extension version stated here, which is what Proposition 3.9
produces.)  (Marker's `κ = card(L)` restriction is a proof artefact: the transfinite induction only
needs `B` to be saturated for types over fewer than `‖A‖⁺` parameters, which is exactly
`‖A‖⁺`-saturation.)  (Saturation is measured in `L_RV` with parameters from the modelled sorts — the
paper's `‖M‖⁺`-saturation, transcribed pair-relatively by `M1Fix.SatRel`, see `QE/M1Fix.lean` §2.)

*Conclusion.* `SpecialTransformations.Milestone0.HasQE Axioms.ACVF` — the frozen target
(`Milestone0/Encoding.lean`), i.e. well-sorted quantifier elimination for `ACVF` in `L_RV`.-/
def ShoenfieldTestRel : Prop := QEOfGate relGate

/-- The same quotation with the size conjunct deleted (the criterion is insensitive to it: it is part
of the gate, and dropping it enlarges the gate).  Recorded so that the fit below does not depend on
which of the two size conventions the `‖M‖⁺`-saturation supplies. -/
def ShoenfieldTestSaturated : Prop :=
  QEOfGate (fun M N _ _ => M1Fix.SatRel M N)

/-- The size conjunct is not what the criterion spends: deleting it enlarges the gate, so the
criterion at the larger gate is the *weaker* statement and follows from `ShoenfieldTestRel`. -/
theorem shoenfieldTestSaturated_of_rel (h : ShoenfieldTestRel) : ShoenfieldTestSaturated :=
  QEOfGate_of_le (fun _ _ _ _ _ _ hM => hM.1) h

/-! ## 4. The fit theorem, and the exact gap

Machine-checked answer to the direction's question:

* `shoenfieldTestSat_iff_QEOfGate` — *definitional*: the frozen shape `Prop39Sat → HasQE` is
  Shoenfield's criterion shape.
* `paperGate_le_relGate` + `QEOfGate_of_le` — *proved*: the frozen saturation gate implies the
  pair-relative one, so the frozen input implies the quotation
  (`shoenfieldTestRel_of_shoenfieldTestSat`).
* `SatBridge` — *the extra named statement* needed for the converse, and `satBridge_iff` shows it is
  exactly `SatRel M N → Assembly.SaturatedFS N`, the upgrade of the pair-relative saturation to the
  frozen `∀ M`-quantified one.  No book states it; `QE/M1Fix.lean` §2 records why it is the wrong
  quantifier order. -/

/-- **The frozen input implies the quotation.**  Unconditional: no bridge is needed in this
direction, because `paperGate → relGate` is a theorem.  So `ShoenfieldTestSat` is at least as strong
as Shoenfield's test, and a proof of it would not be a proof of the book statement. -/
theorem shoenfieldTestRel_of_shoenfieldTestSat (h : M7Paper.ShoenfieldTestSat) :
    ShoenfieldTestRel :=
  QEOfGate_of_le (G := paperGate) (H := relGate)
    (fun M N _ _ _ _ hP => paperGate_le_relGate M N hP)
    (shoenfieldTestSat_iff_QEOfGate.mp h)

/-- **The gap, as a named statement**: the frozen gate contains the paper's pair-relative gate.  This
is the *only* thing missing for the converse of `shoenfieldTestRel_of_shoenfieldTestSat`, i.e. the
only thing missing for deriving the frozen input 1 from the quotation. -/
def SatBridge : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    relGate M N → paperGate M N

/-- **What the bridge really says**: `SatRel M N → Assembly.SaturatedFS N`.  The size conjunct is
supplied by `relGate` itself, so the bridge carries no cardinality content — it is purely the
quantifier-order upgrade `∀ M` of a pair-relative statement.  This is the machine-checked
enumeration the direction asks for: definitional / proved / extra. -/
theorem satBridge_iff :
    SatBridge ↔
      ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
        M7Paper.SizeHyp M N → M1Fix.SatRel M N → Assembly.SaturatedFS N := by
  constructor
  · intro hB M N _ _ _ _ hSize hSat
    exact (hB M N ⟨hSat, hSize⟩).1
  · intro h M N _ _ _ _ hR
    exact ⟨h M N hR.2 hR.1, hR.2⟩

/-- **The quotation gives the frozen input, given the bridge.** -/
theorem shoenfieldTestSat_of_quote_of_bridge (hQ : ShoenfieldTestRel) (hB : SatBridge) :
    M7Paper.ShoenfieldTestSat :=
  shoenfieldTestSat_iff_QEOfGate.mpr
    (QEOfGate_of_le (G := relGate) (H := paperGate) (fun M N _ _ _ _ hR => hB M N hR) hQ)

/-- With the bridge the two gates give the same criterion, so the fit is exact: the frozen input 1
and the quotation differ by `SatBridge` and by nothing else. -/
theorem shoenfieldTestSat_iff_quote_of_bridge (hB : SatBridge) :
    M7Paper.ShoenfieldTestSat ↔ ShoenfieldTestRel :=
  ⟨shoenfieldTestRel_of_shoenfieldTestSat, fun hQ => shoenfieldTestSat_of_quote_of_bridge hQ hB⟩

/-! ## 5. The frozen gate is empty wherever the frozen saturation fails

A criterion at a gate `G` says nothing when `G` has no instances: the implication
`ExtendsAt G → HasQE` then reduces to `HasQE`.  Spelled out for the frozen gate, this is the
machine-checked statement that input 1 of the `§10b` route is *the theorem itself* unless a
`PaperHyp` pair exists. -/

/-- If no pair satisfies the frozen gate, the frozen `Prop39Sat` is provable by ex falso — it carries
no mathematical content. -/
theorem prop39Sat_of_no_paperHyp
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N], ¬ paperGate M N) :
    M7Paper.Prop39Sat := by
  intro M N _ _ _ _ hP S f
  exact absurd hP (h M N)

/-- **The frozen input 1 collapses to the target** when the frozen gate is empty: the criterion is
then equivalent to `HasQE Axioms.ACVF` itself, so a proof of it proves nothing that was not already
the goal. -/
theorem shoenfieldTestSat_iff_hasQE_of_no_paperHyp
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N], ¬ paperGate M N) :
    (M7Paper.ShoenfieldTestSat ↔ HasQE Axioms.ACVF) :=
  ⟨fun hS => hS (prop39Sat_of_no_paperHyp h), fun hQE => fun _ => hQE⟩

/-- The same, from the natural cause: if `Assembly.SaturatedFS` holds of no structure at all, the
frozen gate is empty (take its first conjunct). -/
theorem prop39Sat_of_no_saturatedFS
    (h : ∀ (N : Type) [LRV.Structure N], ¬ Assembly.SaturatedFS N) :
    M7Paper.Prop39Sat := by
  refine prop39Sat_of_no_paperHyp (fun M N _ _ hP => ?_)
  exact h N hP.1

/-- **The circularity check**: under `¬ SaturatedFS` for every structure, the frozen input 1 of the
`§10b` route is equivalent to the frozen target.  Input 1 is therefore *not* a reduction of the
target unless the frozen gate is known to be inhabited — which the paper's `‖M‖⁺`-saturation is, and
the frozen `∀ M`-quantified reading is not (`QE/M1Fix.lean` §2). -/
theorem shoenfieldTestSat_iff_hasQE_of_no_saturatedFS
    (h : ∀ (N : Type) [LRV.Structure N], ¬ Assembly.SaturatedFS N) :
    (M7Paper.ShoenfieldTestSat ↔ HasQE Axioms.ACVF) :=
  shoenfieldTestSat_iff_hasQE_of_no_paperHyp (fun _ N _ _ hP => h N hP.1)

/-- **The bridge at the diagonal.**  `SatBridge` already at `M = N`: if `N` is pair-relatively
saturated over itself, the frozen `∀ M`-quantified `SaturatedFS N` follows.  So the bridge asserts
that a set-sized structure is `κ`-saturated for *every* `κ` — the standard obstruction which
`QE/M1Fix.lean` §2 records.  This is the reason the gap is not one a quotation can fill; it is not
refuted here only because refuting it needs a model of `Axioms.ACVF` (direction e6). -/
theorem satBridge_diagonal (hB : SatBridge) :
    ∀ (N : Type) [LRV.Structure N] [N ⊨ Axioms.ACVF], M1Fix.SatRel N N → Assembly.SaturatedFS N :=
  fun N _ _ hSat => (hB N N ⟨hSat, le_rfl⟩).1

/-- For contrast, the criterion at the empty gate is *exactly* the target (both directions), so the
collapse above is not an artefact of the frozen gate's size conjunct. -/
theorem qeOfGate_empty_iff : QEOfGate (fun _ _ _ _ => False) ↔ HasQE Axioms.ACVF :=
  ⟨fun hQ => hQ (fun M N _ _ _ _ h => absurd h (by simp)),
    fun hQE => fun _ => hQE⟩

/-! ## 6. The route at an explicit gate; the paper's own pair-relatively stated hypothesis

The `§10b` ledger (`QE/M5Ledger.lean`) is gate-polymorphic in its proof: its five inputs are pair
statements, and `prepStepP_of_ledger` only ever applies them at the pair it is given.  Re-running it
at `relGate` costs nothing and removes the two defects isolated above (the frozen gate's quantifier
order, and the collapse of §5): the criterion is then Shoenfield's test at the paper's hypothesis,
and the inputs are the paper's five steps stated at the paper's pair. -/

/-- **The ledger route at an arbitrary gate.**  This is `M5Ledger.paper_theorem_2_3_sat_of_ledger_paperHyp`
with the fixed gate `M7Paper.PaperHyp` replaced by a parameter `H`: the criterion at `H`, the five
inputs at `H`, and the frozen one-step obligation.  Every gate-specific statement in this file is an
instance, and a member who supplies the honest saturation predicate (direction e2) can plug it in
without touching the assembly. -/
theorem paper_theorem_2_3_of_gate (H : Gate) (hQ : QEOfGate H)
    (h1 : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      H M N → M5Ledger.ACFExtends (M := M) (N := N))
    (h2 : M5Ledger.LedgerInput2)
    (h3 : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      H M N → M5Ledger.ResidueStep (M := M) (N := N))
    (h4 : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      H M N → M5Ledger.DivisibilityStep (M := M) (N := N))
    (h5 : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      H M N → M5Ledger.SaturationRealization (M := M) (N := N))
    (hOne : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      H M N → Assembly.OneStepVFP (M := M) (N := N)) : HasQE Axioms.ACVF := by
  refine hQ ?_
  intro M N _ _ _ _ hH S f
  exact Assembly.prop39P_noVFGen
    (M5Ledger.prepStepP_of_ledger (h1 M N hH) (h2 M) (h3 M N hH) (h4 M N hH) (h5 M N hH))
    (hOne M N hH) S f

/-- The **one-step hypothesis is gated at the same gate as everything else**.  The ungated
`M7Paper.OneStepSizeFree` (`∀ M N, OneStepVFP`) implies the gated form, so nothing is lost; but the
gate is essential on the other side: swarm `smw2ioy2w`'s m7 machine-refuted the ungated obligation
(`Hahn.not_oneStepSizeFree`), and the final route (`smw2jkpn4`/m8) uses the `PaperHyp`-gated
`OneStepPaper`.  Recorded here so that a member can plug in either form. -/
theorem oneStep_gated_of_free (h : M7Paper.OneStepSizeFree) (H : Gate) :
    ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      H M N → Assembly.OneStepVFP (M := M) (N := N) :=
  fun _ _ _ _ _ _ _ => h _ _

/-- The gated one-step at the frozen gate is exactly the shape of m7's `OneStepPaper`
(`.ultramath/smw2ioy2w/m7/HahnObstruction.lean:417`), stated against `M7Paper.PaperHyp` directly. -/
theorem oneStep_gate_paperGate_iff :
    (∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
        paperGate M N → Assembly.OneStepVFP (M := M) (N := N)) ↔
      (∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
        M7Paper.PaperHyp M N → Assembly.OneStepVFP (M := M) (N := N)) :=
  Iff.rfl

/-- **Consistency with `§10b`**: at the frozen gate, the hypotheses of the gate-parameterized route are
`§10b`'s own — the five `LedgerInput*P` definitions are the `H := paperGate` instances, and the
criterion is `shoenfieldTestSat_iff_QEOfGate`.  So nothing is weakened by restating the ledger at a
gate. -/
theorem paper_theorem_2_3_sat_of_ledger_paperHyp_via_gate (hShoen : M7Paper.ShoenfieldTestSat)
    (h1 : M5Ledger.LedgerInput1P) (h2 : M5Ledger.LedgerInput2) (h3 : M5Ledger.LedgerInput3P)
    (h4 : M5Ledger.LedgerInput4P) (h5 : M5Ledger.LedgerInput5P)
    (hOne : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], M7Paper.PaperHyp M N → Assembly.OneStepVFP (M := M) (N := N)) :
    HasQE Axioms.ACVF :=
  paper_theorem_2_3_of_gate paperGate (shoenfieldTestSat_iff_QEOfGate.mp hShoen) h1 h2 h3 h4 h5 hOne

/-- **The frozen `§10b` statement is recovered** (the ungated `OneStepSizeFree` is stronger, so it
specialises to the gated hypothesis of `paper_theorem_2_3_sat_of_ledger_paperHyp_via_gate`).  This is
the machine-checked audit that the gate-parameterized route is not a weakening of `§10b`. -/
theorem paper_theorem_2_3_sat_of_ledger_paperHyp_via_gate' (hShoen : M7Paper.ShoenfieldTestSat)
    (h1 : M5Ledger.LedgerInput1P) (h2 : M5Ledger.LedgerInput2) (h3 : M5Ledger.LedgerInput3P)
    (h4 : M5Ledger.LedgerInput4P) (h5 : M5Ledger.LedgerInput5P)
    (hOne : M7Paper.OneStepSizeFree) : HasQE Axioms.ACVF :=
  paper_theorem_2_3_sat_of_ledger_paperHyp_via_gate hShoen h1 h2 h3 h4 h5
    (oneStep_gated_of_free hOne paperGate)

/-- Input 1 at `relGate`: Marker, ACF extension of embeddings (with the saturation-supplied
transcendental part — see `M5Ledger.ACFExtends`'s docstring). -/
def Input1R : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    relGate M N → M5Ledger.ACFExtends (M := M) (N := N)

/-- Input 3 at `relGate`: the paper's residue step (Lemma 3.3 (2), `K(S*) = K(M)`). -/
def Input3R : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    relGate M N → M5Ledger.ResidueStep (M := M) (N := N)

/-- Input 4 at `relGate`: the divisible hull of `Γ(S)` (Lemma 3.3 (3)). -/
def Input4R : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    relGate M N → M5Ledger.DivisibilityStep (M := M) (N := N)

/-- Input 5 at `relGate`: Marker, saturation realization of the monomorphism. -/
def Input5R : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    relGate M N → M5Ledger.SaturationRealization (M := M) (N := N)

/-- **Lemma 3.3 at `relGate`**, from the five inputs.  Identical proof to
`M5Ledger.prepStepPaper_of_ledger`; only the gate is different. -/
theorem prepStepR_of_ledger (h1 : Input1R) (h2 : M5Ledger.LedgerInput2) (h3 : Input3R)
    (h4 : Input4R) (h5 : Input5R) :
    ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      relGate M N → Assembly.PrepStepP (M := M) (N := N) := by
  intro M N _ _ _ _ hR S f
  exact M5Ledger.prepStepP_of_ledger (h1 M N hR) (h2 M) (h3 M N hR) (h4 M N hR) (h5 M N hR) S f

/-- **Proposition 3.9 at `relGate`**, from Lemma 3.3 there and the one-step obligation, the latter
gated at the same `relGate` (see `oneStep_gate_paperGate_iff` for why the gate must be carried). -/
theorem extendsAt_rel_of_prepStep
    (hPrep : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], relGate M N → Assembly.PrepStepP (M := M) (N := N))
    (hOne : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], relGate M N → Assembly.OneStepVFP (M := M) (N := N)) :
    ExtendsAt relGate := by
  intro M N _ _ _ _ hR S f
  exact Assembly.prop39P_noVFGen (hPrep M N hR) (hOne M N hR) S f

/-- **Theorem 2.3 (`qe:acvf`) at the paper's own hypothesis**, with Lemma 3.3 decomposed into the
five inputs and the one-step obligation as frozen.  This is the repaired form of
`M5Ledger.paper_theorem_2_3_sat_of_ledger_paperHyp`: the first hypothesis is the quotation
`ShoenfieldTestRel` instead of the frozen `ShoenfieldTestSat`.  (Both `§10b` and this are the
`H := paperGate` / `H := relGate` instances of `paper_theorem_2_3_of_gate`.) -/
theorem paper_theorem_2_3_rel (hQ : ShoenfieldTestRel) (h1 : Input1R)
    (h2 : M5Ledger.LedgerInput2) (h3 : Input3R) (h4 : Input4R) (h5 : Input5R)
    (hOne : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], relGate M N → Assembly.OneStepVFP (M := M) (N := N)) :
    HasQE Axioms.ACVF :=
  paper_theorem_2_3_of_gate relGate hQ h1 h2 h3 h4 h5 hOne

/-- The same, with the ungated `OneStepSizeFree` as hypothesis. -/
theorem paper_theorem_2_3_rel_of_free (hQ : ShoenfieldTestRel) (h1 : Input1R)
    (h2 : M5Ledger.LedgerInput2) (h3 : Input3R) (h4 : Input4R) (h5 : Input5R)
    (hOne : M7Paper.OneStepSizeFree) : HasQE Axioms.ACVF :=
  paper_theorem_2_3_rel hQ h1 h2 h3 h4 h5 (oneStep_gated_of_free hOne relGate)

/-- **The frozen Proposition 3.9 follows from the `relGate` route**, because `paperGate → relGate`
(`paperGate_le_relGate`).  So the repaired route loses nothing on the frozen side. -/
theorem prop39Sat_of_relLedger (h1 : Input1R) (h2 : M5Ledger.LedgerInput2) (h3 : Input3R)
    (h4 : Input4R) (h5 : Input5R) (hOne : M7Paper.OneStepSizeFree) :
    M7Paper.Prop39Sat := by
  intro M N _ _ _ _ hP S f
  exact extendsAt_rel_of_prepStep (prepStepR_of_ledger h1 h2 h3 h4 h5)
    (oneStep_gated_of_free hOne relGate) M N (paperGate_le_relGate M N hP) S f

/-- **The frozen input 1 is *derived*, not assumed**: the quotation plus the five inputs at the
paper's pair plus the frozen one-step obligation give `M7Paper.ShoenfieldTestSat`.  So the `§10b`
route can be run unchanged once the five inputs are stated at `relGate`. -/
theorem shoenfieldTestSat_of_relLedger (hQ : ShoenfieldTestRel) (h1 : Input1R)
    (h2 : M5Ledger.LedgerInput2) (h3 : Input3R) (h4 : Input4R) (h5 : Input5R)
    (hOne : M7Paper.OneStepSizeFree) : M7Paper.ShoenfieldTestSat :=
  fun _ => paper_theorem_2_3_rel_of_free hQ h1 h2 h3 h4 h5 hOne

/-- The **usable form** of the previous corollary: the one-step gated at `relGate` (m7 machine-refuted
the ungated `M7Paper.OneStepSizeFree`, so the gated hypothesis is the one a discharge can meet). -/
theorem prop39Sat_of_relLedger_gated (h1 : Input1R) (h2 : M5Ledger.LedgerInput2) (h3 : Input3R)
    (h4 : Input4R) (h5 : Input5R)
    (hOne : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], relGate M N → Assembly.OneStepVFP (M := M) (N := N)) :
    M7Paper.Prop39Sat := by
  intro M N _ _ _ _ hP S f
  exact extendsAt_rel_of_prepStep (prepStepR_of_ledger h1 h2 h3 h4 h5) hOne M N
    (paperGate_le_relGate M N hP) S f

/-- The **usable form** of the frozen input 1 derivation: quotation + five inputs + the `relGate`-gated
one-step. -/
theorem shoenfieldTestSat_of_relLedger_gated (hQ : ShoenfieldTestRel) (h1 : Input1R)
    (h2 : M5Ledger.LedgerInput2) (h3 : Input3R) (h4 : Input4R) (h5 : Input5R)
    (hOne : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], relGate M N → Assembly.OneStepVFP (M := M) (N := N)) :
    M7Paper.ShoenfieldTestSat :=
  fun _ => paper_theorem_2_3_rel hQ h1 h2 h3 h4 h5 hOne

/-! ## 7. Stress tests

*(a) The quotation is not its own conclusion.*  `ShoenfieldTestRel` is `ExtendsAt relGate → HasQE`,
and the antecedent is a statement about embeddings, not about formulas: given `HasQE` one cannot
recover it (`relGate` contains pairs with an arbitrary partial embedding).  Machine-checked
non-degeneracy: `paperGate_le_relGate` exhibits `relGate` as implied by the frozen gate, so `relGate`
is inhabited whenever the paper's frozen hypothesis is; and `qeOfGate_empty_iff` shows that the
collapse of `QEOfGate` to `HasQE` is exactly *emptiness* of the gate, i.e. the gate is where the
criterion's content lives.

*(b) No hidden cardinality.*  `relGate` carries `#M ≤ #N` explicitly, so nothing is forced that the
guard does not supply; the quotation is insensitive to it (`shoenfieldTestSaturated_of_rel`), and the
frozen gate implies the `relGate` gate (`paperGate_le_relGate`), so no new size content is added
relative to `§10b`.

*(c) The tempting stronger forms are refuted where they are false.*  `satBridge_iff` shows that the
only missing step between the quotation and the frozen input is the quantifier-order upgrade
`SatRel → SaturatedFS`; `shoenfieldTestSat_iff_hasQE_of_no_saturatedFS` shows that if the frozen gate
is empty then the frozen input is the target — so the frozen input is *not* a faithful transcription
of Shoenfield's test, and no amount of work on the five inputs can make it one. -/

end M5Shoenfield

end Milestone0
end SpecialTransformations

#print axioms SpecialTransformations.Milestone0.M5Shoenfield.paperGate_le_relGate
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.prop39Sat_iff_extendsAt_paperGate
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.shoenfieldTestSat_iff_QEOfGate
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.QEOfGate_of_le
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.shoenfieldTestSaturated_of_rel
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.shoenfieldTestRel_of_shoenfieldTestSat
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.satBridge_iff
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.shoenfieldTestSat_of_quote_of_bridge
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.shoenfieldTestSat_iff_quote_of_bridge
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.prop39Sat_of_no_paperHyp
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.shoenfieldTestSat_iff_hasQE_of_no_paperHyp
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.shoenfieldTestSat_iff_hasQE_of_no_saturatedFS
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.qeOfGate_empty_iff
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.satBridge_diagonal
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.paper_theorem_2_3_of_gate
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.oneStep_gated_of_free
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.oneStep_gate_paperGate_iff
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.paper_theorem_2_3_rel_of_free
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.paper_theorem_2_3_sat_of_ledger_paperHyp_via_gate
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.prepStepR_of_ledger
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.extendsAt_rel_of_prepStep
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.paper_theorem_2_3_rel
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.prop39Sat_of_relLedger
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.prop39Sat_of_relLedger_gated
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.shoenfieldTestSat_of_relLedger_gated
#print axioms SpecialTransformations.Milestone0.M5Shoenfield.shoenfieldTestSat_of_relLedger
