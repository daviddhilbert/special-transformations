/-
# u1 — `RelUnit`: the unit half of the six-part frontier, assembled and reduced

Member `m1`, swarm `smw2qpqe7`, direction `d1` (= u1).

## What the frontier asks for

`QE/RouteLedger.lean`'s `RelUnit` is `∀ M N, M5Shoenfield.relGate M N → UnitSlot M N`, where

    UnitSlot = ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M,
      iVF m → iRv m ∈ S → iUnits (iRv m) → ¬ M5L.Separated S m →
      ∃ T g hST, g extends f ∧ m ∈ T ∧ Assembly.Standing T

the unit half of the paper's `lift:all:root` + `lift:transcendental` pair (Lemmas 3.4 and 3.6).

## The verdict of this file

The unit half has **one** content: the realisation `f ↾ Ŝ` extends to `⟨Ŝ,m⟩ = closure (S ∪ {m})`.
Everything else in the slot (`T`, `m ∈ T`, `Standing T`, `¬ Separated`) is either conclusion-side
bookkeeping that any witness already satisfies, or class control that the paper's Claim (⋆) supplies.
Machine-checked:

* `slotConcl_iff_closureEmbedding` (§0, **no `ACVF`, no gate, no case split**): with `⟨Ŝ,m⟩` standing,
  the slot's conclusion at a point is *equivalent* to the closure embedding;
  `closureEmbedding_of_slotConcl` is the forward half with no hypothesis at all;
* `unitSlot_iff_no_separated` (§1): `¬ M5L.Separated` is derivable at a unit, so the unit half
  carries no separation content;
* `unitSlot_of_closure_parts` + `closureEmbedding_of_unitSlot` (§1): the unit slot is *equivalent* to
  `UnitClosureEmbedding ∧ UnitClosureStanding`, i.e. to the realisation plus Claim (⋆)'s class half;
* `algebraicUnitSlot_of_rootData` (§2): **3.4** = `RouteLedger.RootData`; `Slot34` is a consequence,
  not an extra hypothesis; and `RootData'` (below) shows its `iRv m ∈ S` row is redundant;
* `transcendentalUnitSlot_iff_of_claimStar`, `transcendentalUnitSlot_iff_paperClaimStar` (§3):
  granting 3.6's class half, the **3.6** side is *equivalent* to the realisation statement.  The
  frozen `M8.ClaimStar` keeps only the class half of the paper's Claim (⋆) — the map
  `f^* : ⟨Ŝ,e⟩ → N` is the half `QE/Lemma36Statement.lean` records as not formalised;
* `residualClasses_closure_of_residueTranscendental` + `transcendentalClaimStar_of_residueTranscendental`
  (§3b): 3.6's class half is *derived*, not assumed, from the paper's own hypotheses — residue
  transcendence (`M7.ResidueTranscendental` at `VGBridge.vGammaValuation`), `QuotExpansions`,
  `IsVFGen` at the closure and `VFInvClosedOn` — through `QE/UnitCase.lean`'s
  `ResidualClasses_of_VFGen_unit_min`, with no EP 3.4.3 and no `RVTrans`;
* `unitSlot_of_34_and_36` (§5) assembles `RootData → 3.6's ClaimStar → realisation → UnitSlot`,
  `unitSlot_of_34_and_36_paper` does it with the class half replaced by §3b's hypotheses, and
  `relUnit_of_parts` / `relUnit_of_gated_parts` give `RelUnit` (the gate is never consumed);
* `paper_theorem_2_3_of_parts` (§5c): the five-part endgame with `RelUnit` replaced by those three
  residuals;
* §4 records the **repair-free** route: `M8.Lemma36Hyp` is inconsistent
  (`merged_lemma36_hyp_no_instances`), so the class half must come from the repaired
  `RVTransVF`; the root hull is standing unconditionally, so the residual stated there
  (`UnitRootHullEmbedding`) needs no class control at all (`unitSlot_of_rootHullEmbedding`), at the
  price of being strictly stronger (`closureEmbedding_of_rootHullEmbedding`);
* §6 stress tests: the cone is inhabited (`unitHyp_at_keqTop`), the slot conclusion is satisfied at
  `N = M` and at old elements (`slotConcl_of_mem`, `closureEmbedding_of_mem`), the residual follows
  from a global extension (`closureEmbedding_of_global`), `Closure ⊤ m = ⊤` and
  `UnitClosureStanding` holds there (`closure_top`, `unitClosureStanding_top`).

## What remains (the honest residual list for `RelUnit`)

1. `RootData` — 3.4: monic `F` over `O(Ŝ)` with irreducible projection, the henselianity step
   (`embed`), and the class control.
2. 3.6's class half — either the abstract `TranscendentalClaimStar`, or (better, §3b) the paper's own
   hypothesis cone: residue transcendence + `QuotExpansions` + `IsVFGen (Closure S m)` +
   `VFInvClosedOn S`.  The `RVTransVF` repair of `M8.Lemma36Hyp` is *not* needed on this route,
   because `QE/UnitCase.lean` proves the class half from residue transcendence directly.
3. `TranscendentalRealisation` — the paper's `f^* : ⟨Ŝ,e⟩ → N`, i.e. the half of Claim (⋆) that the
   frozen `ClaimStar` omits.  This is the model-theoretic (saturation) content; it is not class
   bookkeeping, and it is the only place where the unit half ever needs the target model `N` beyond
   `f` itself.

No `sorry`, no `axiom`, no `native_decide`; axiom audit at the end.
-/
import RouteLedger
import RootHull
import Lemma36Statement
import UnitCase

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Milestone0.RelUnit

open SpecialTransformations.Milestone0.RouteLedger

/-! ## 0. The structural core: the slot's conclusion *is* the closure embedding

No `ACVF` instance, no gate, no case split: the two `Prop`s below live in an arbitrary pair of
`L_RV`-structures. -/

section Structural

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-- The paper's `⟨Ŝ,e⟩`: the `L_RV`-substructure of `M` generated by `S` and the single element
`m`.  (This is the frozen encoding's `Substructure.closure LRV (S ∪ {m})`.) -/
def Closure (S : LRV.Substructure M) (m : M) : LRV.Substructure M :=
  Substructure.closure LRV ((S : Set M) ∪ {m})

theorem le_closure (S : LRV.Substructure M) (m : M) : S ≤ Closure S m :=
  fun _ hx => Substructure.subset_closure (Or.inl hx)

theorem mem_closure_self (S : LRV.Substructure M) (m : M) : m ∈ Closure S m :=
  Substructure.subset_closure (Or.inr rfl)

theorem closure_le_iff {S : LRV.Substructure M} {m : M} {T : LRV.Substructure M} :
    Closure S m ≤ T ↔ ((S : Set M) ∪ {m}) ⊆ (T : Set M) :=
  Substructure.closure_le

/-- **The conclusion of the frozen slot**, at a point: some standing `T ⊇ S` containing `m`, with a
monomorphism `T ↪[LRV] N` extending `f`.  This is the codomain shared by `CaseSeparated`,
`CaseNotSeparated`, `UnitSlot`, `NonUnitSlot` and the three `RootHull` slots. -/
def SlotConcl (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M) : Prop :=
  ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
    (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T

/-- **The realisation half of Claim (⋆)**: `f` extends to `⟨Ŝ,m⟩ = closure (S ∪ {m})`.  In the
paper this is the map `f^* : ⟨Ŝ,e⟩ → N` (with `f^*(rv e) = f(rv e)`); it is the *only* field of
`M5P1.LiftAllRoot` that is not class/bookkeeping, and the only residual §1–§4 leave open. -/
def ClosureEmbedding (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M) : Prop :=
  ∃ g : Closure S m ↪[LRV] N,
    ∀ x : S, g ⟨(x : M), le_closure S m x.2⟩ = f x

/-- The forward direction needs no standing hypothesis at all: *any* slot witness restricts to the
closure.  (This is the half of the theorem above that carries the "nothing is lost" content.) -/
theorem closureEmbedding_of_slotConcl (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M)
    (h : SlotConcl S f m) : ClosureEmbedding S f m := by
  obtain ⟨T, g, hST, hagree, hmT, -⟩ := h
  have hsub : ((S : Set M) ∪ {m}) ⊆ (T : Set M) := by
    rintro x (hx | hx)
    · exact hST hx
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hmT
  have hle : Closure S m ≤ T := Substructure.closure_le.mpr hsub
  refine ⟨g.comp (Substructure.inclusion hle), ?_⟩
  intro x
  show g (Substructure.inclusion hle ⟨(x : M), le_closure S m x.2⟩) = f x
  exact hagree x

/-- **THE STRUCTURAL THEOREM.**  If `⟨Ŝ,m⟩` is standing, the slot's conclusion at the point is
*exactly* the closure embedding.

Forward: a witness `T` contains `S ∪ {m}`, hence contains `closure (S ∪ {m})`, and `g` restricts.
Backward: `T := ⟨Ŝ,m⟩` itself.  No `Separated`, no `ACVF`, no gate, no size hypothesis. -/
theorem slotConcl_iff_closureEmbedding (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M)
    (hStand : Assembly.Standing (Closure S m)) :
    SlotConcl S f m ↔ ClosureEmbedding S f m := by
  constructor
  · exact closureEmbedding_of_slotConcl S f m
  · rintro ⟨g, hagree⟩
    exact ⟨Closure S m, g, le_closure S m, hagree, mem_closure_self S m, hStand⟩

end Structural

/-! ## 1. The unit hypothesis cone, and the two halves of what 3.4/3.6 must supply -/

section Unit

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **The unit hypothesis cone**: the slot's hypotheses *minus* `¬ M5L.Separated`, which is
derivable from them (`M5P1.not_separated_of_units`, the paper's `vv(e) = 0`) and therefore carries no
content.  Lemmas 3.4 and 3.6 are exactly the algebraic / transcendental dichotomy of this cone. -/
def UnitHyp (S : LRV.Substructure M) (m : M) : Prop :=
  Assembly.Standing S ∧ iVF m ∧ iRv m ∈ S ∧ iUnits (iRv m)

/-- **The realisation residual of the unit half** (both halves of the paper's case split, at once):
every unit `m` of a standing `S`, with `rv m` old, has `f` extending to `⟨Ŝ,m⟩`. -/
def UnitClosureEmbedding : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M), UnitHyp S m → ClosureEmbedding S f m

/-- **The class/bookkeeping residual of the unit half**: `⟨Ŝ,m⟩` is standing at every unit.  This is
Claim (⋆)'s *class* half — `M5L.ResidualClasses S ⟨Ŝ,m⟩` — read through
`M5P1.standing_closure_of_classControl` (`unitClosureStanding_of_residualClasses`), and it is the
only place where 3.4's `class_control` / 3.6's `ClaimStar` are consumed. -/
def UnitClosureStanding : Prop :=
  ∀ (S : LRV.Substructure M) (m : M), UnitHyp S m → Assembly.Standing (Closure S m)

/-- **`¬ Separated` is free at a unit.**  So the frozen `UnitSlot` equals the slot with the
separation hypothesis dropped: the unit half carries no `Separated` content, and 3.4's attribution
to `CaseSeparated` (refuted in `QE/Case34Slot.lean` §1) would have been vacuous. -/
theorem unitSlot_iff_no_separated :
    UnitSlot (M := M) (N := N) ↔
      ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M), UnitHyp S m → SlotConcl S f m := by
  constructor
  · rintro h S f m ⟨hS, hmVF, hmrv, hunit⟩
    exact h S f hS m hmVF hmrv hunit (M5P1.not_separated_of_units hmVF hunit)
  · intro h S f hS m hmVF hmrv hunit _
    exact h S f m ⟨hS, hmVF, hmrv, hunit⟩

/-- **The unit slot from its two halves**: the realisation and the standing of `⟨Ŝ,m⟩`.  This is the
exact form of "3.4's and 3.6's Claim (⋆) ⇒ `UnitSlot`", with the class and realisation halves
separated. -/
theorem unitSlot_of_closure_parts (he : UnitClosureEmbedding (M := M) (N := N))
    (hs : UnitClosureStanding (M := M)) : UnitSlot (M := M) (N := N) := by
  rw [unitSlot_iff_no_separated]
  intro S f m hU
  exact (slotConcl_iff_closureEmbedding S f m (hs S m hU)).mpr (he S f m hU)

/-- **The realisation residual is necessary**: any `UnitSlot` yields the closure embedding at every
unit.  So §1 introduces no strengthening — the unit slot and the closure embedding are the same
obligation, modulo `UnitClosureStanding`. -/
theorem closureEmbedding_of_unitSlot (h : UnitSlot (M := M) (N := N)) :
    UnitClosureEmbedding (M := M) (N := N) := by
  intro S f m hU
  exact closureEmbedding_of_slotConcl S f m ((unitSlot_iff_no_separated.mp h) S f m hU)

/-- **Claim (⋆)'s class half gives the standing half** — so `UnitClosureStanding` is exactly the
residual that 3.4's `class_control` and 3.6's `ClaimStar` discharge. -/
theorem unitClosureStanding_of_residualClasses
    (h : ∀ (S : LRV.Substructure M) (m : M), UnitHyp S m →
      M5L.ResidualClasses S (Closure S m)) : UnitClosureStanding (M := M) :=
  fun S m hU => M5P1.standing_closure_of_classControl hU.1 (h S m hU)

end Unit

/-! ## 2. Lemma 3.4's content: `RootData` alone closes the algebraic slot

`QE/RouteLedger.lean` proves `algebraicUnitSlot_of_rootData_slot34`, taking both `RootData` and the
slot `Slot34` as hypotheses.  `Slot34` is *not* an extra input: `RootData` produces a full
`M5P1.LiftAllRoot`, whose `embed` and `class_control` fields are exactly what
`M5P1.slot_of_liftAllRoot` consumes.  So 3.4's entire residual is `RootData` — the paper's `F` monic
over `O(Ŝ)` with irreducible projection, the henselianity step, and the class control. -/

section Algebraic

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- `RootData` reads in the unit vocabulary of §1: its hypothesis list is `UnitHyp` plus
algebraicity. -/
theorem rootData_iff : RootData (M := M) (N := N) ↔
    ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ (m : M),
      iVF m → iRv m ∈ S → iUnits (iRv m) → (∃ n : ℕ, M8.AlgebraicOverVF S m n) →
        ∃ (a : ℕ → M) (n : ℕ), M5P1.LiftAllRoot S f a n m :=
  Iff.rfl

/-- **3.4's residual without its redundant row.**  `iRv m ∈ S` is *derivable* from `Standing S` and
`iUnits (iRv m)` (`M5P1.rv_mem_of_units`, the paper's `K(Ŝ) = K(M)`), so it can be dropped from
`RootData`'s hypothesis list at no cost.  (The row is kept in `UnitHyp` only because the frozen
slots carry it.) -/
def RootData' : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ (m : M), iVF m →
    iUnits (iRv m) → (∃ n : ℕ, M8.AlgebraicOverVF S m n) →
      ∃ (a : ℕ → M) (n : ℕ), M5P1.LiftAllRoot S f a n m

theorem rootData_iff_rootData' : RootData (M := M) (N := N) ↔ RootData' (M := M) (N := N) := by
  constructor
  · intro h S f hS m hmVF hunit halg
    exact h S f hS m hmVF (M5P1.rv_mem_of_units hS.1 hunit) hunit halg
  · intro h S f hS m hmVF _ hunit halg
    exact h S f hS m hmVF hunit halg

/-- **Lemma 3.4 discharges the algebraic unit slot from `RootData` alone** (no `Slot34`). -/
theorem algebraicUnitSlot_of_rootData (hroot : RootData (M := M) (N := N)) :
    AlgebraicUnitSlot (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hunit halg
  obtain ⟨a, n, hl⟩ := hroot S f hS m hmVF hmrv hunit halg
  exact M5P1.slot_of_liftAllRoot S f a n m hS hl

/-- **`M5P1.Slot34` is a theorem, not an obligation.**  `QE/RouteLedger.lean`'s status table lists
3.4 as "⟸ `RootData` + `M5P1.Slot34`"; but `Slot34` takes the *full* `M5P1.LiftAllRoot` (whose
`embed` and `class_control` fields are 3.4's derived conclusions) as a hypothesis, so it is the
projection `M5P1.slot_of_liftAllRoot` and needs no input of its own.  Hence 3.4 *is* `RootData`. -/
theorem slot34_holds : M5P1.Slot34 (M := M) (N := N) :=
  fun S f hS a n m hl _ => M5P1.slot_of_liftAllRoot S f a n m hS hl

/-- The `RouteLedger` reduction instantiated at the redundant hypothesis: 3.4 equals `RootData`. -/
theorem algebraicUnitSlot_of_rootData_via_slot34 (hroot : RootData (M := M) (N := N)) :
    AlgebraicUnitSlot (M := M) (N := N) :=
  RouteLedger.algebraicUnitSlot_of_rootData_slot34 hroot slot34_holds

/-- Conversely `M5P1.LiftAllRoot` supplies the closure embedding (its `embed` field), so the
algebraic residual `RootData` is *stronger* than what `UnitClosureEmbedding` needs on the algebraic
part — which locates 3.4's content precisely. -/
theorem closureEmbedding_of_liftAllRoot {S : LRV.Substructure M} {f : S ↪[LRV] N}
    {a : ℕ → M} {n : ℕ} {m : M} (h : M5P1.LiftAllRoot S f a n m) :
    ClosureEmbedding S f m := by
  obtain ⟨g, hagree⟩ := h.embed
  exact ⟨g, hagree⟩

/-- The algebraic half of the realisation residual, from 3.4's residual. -/
theorem algebraicClosureEmbedding_of_rootData (hroot : RootData (M := M) (N := N)) :
    ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M), UnitHyp S m →
      (∃ n : ℕ, M8.AlgebraicOverVF S m n) → ClosureEmbedding S f m := by
  intro S f m hU halg
  obtain ⟨a, n, hl⟩ := hroot S f hU.1 m hU.2.1 hU.2.2.1 hU.2.2.2 halg
  exact closureEmbedding_of_liftAllRoot hl

end Algebraic

/-! ## 3. Lemma 3.6's content: the transcendental unit slot is *exactly* the realisation

At a standing `S`, Claim (⋆)'s `RV` half implies its `Standing` half
(`M5P1.standing_closure_of_classControl`), so the merged `M8.ClaimStar` collapses to the class
computation.  Granting 3.6's conclusion in that form, the transcendental unit slot is
*equivalent* to the single realisation statement — no other content is left. -/

section Transcendental

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **Claim (⋆)'s two halves are one** at a standing `S`: `ClaimStar S m` is equivalent to its class
component `M5L.ResidualClasses S ⟨Ŝ,m⟩`.  (So the `Standing` conjunct of `M8.ClaimStar` is
redundant, and 3.6's usable conclusion is the class computation.) -/
theorem claimStar_iff_residualClasses {S : LRV.Substructure M} {m : M}
    (hS : Assembly.Standing S) :
    M8.ClaimStar S m ↔ M5L.ResidualClasses S (Closure S m) :=
  ⟨fun h => h.1, fun h => ⟨h, M5P1.standing_closure_of_classControl hS h⟩⟩

/-- **3.6's conclusion, in the form the unit slot consumes it**: at every transcendental unit `m` of
a standing `S`, Claim (⋆) holds.  This is the (only) positive content Lemma 3.6 owes the unit
half. -/
def TranscendentalClaimStar : Prop :=
  ∀ (S : LRV.Substructure M) (m : M), UnitHyp S m →
    (¬ ∃ n : ℕ, M8.AlgebraicOverVF S m n) → M8.ClaimStar S m

/-- **The transcendental realisation**: at every transcendental unit, `f` extends to `⟨Ŝ,m⟩`.
This is the paper's `f^* : ⟨Ŝ,e⟩ → N`. -/
def TranscendentalRealisation : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M), UnitHyp S m →
    (¬ ∃ n : ℕ, M8.AlgebraicOverVF S m n) → ClosureEmbedding S f m

/-- **3.6's Claim (⋆) together with the realisation gives the transcendental unit slot.** -/
theorem transcendentalUnitSlot_of_claimStar_realisation
    (hc : TranscendentalClaimStar (M := M)) (hr : TranscendentalRealisation (M := M) (N := N)) :
    TranscendentalUnitSlot (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hunit htr
  have hU : UnitHyp S m := ⟨hS, hmVF, hmrv, hunit⟩
  have hcc : M5L.ResidualClasses S (Closure S m) := (claimStar_iff_residualClasses hS).mp (hc S m hU htr)
  have hst : Assembly.Standing (Closure S m) := M5P1.standing_closure_of_classControl hS hcc
  exact (slotConcl_iff_closureEmbedding S f m hst).mpr (hr S f m hU htr)

/-- **The realisation half is necessary**: the transcendental slot already yields it. -/
theorem transcendentalRealisation_of_unitSlot (h : TranscendentalUnitSlot (M := M) (N := N)) :
    TranscendentalRealisation (M := M) (N := N) := by
  intro S f m hU htr
  exact closureEmbedding_of_slotConcl S f m (h S f hU.1 m hU.2.1 hU.2.2.1 hU.2.2.2 htr)

/-- **THE EXACT STATEMENT OF WHAT 3.6 LEAVES OPEN.**  Granting 3.6's Claim (⋆) at every
transcendental unit, the transcendental unit slot is *equivalent* to the realisation statement: no
class content, no `Standing`, no `Separated` hypothesis is left over. -/
theorem transcendentalUnitSlot_iff_of_claimStar (hc : TranscendentalClaimStar (M := M)) :
    TranscendentalUnitSlot (M := M) (N := N) ↔ TranscendentalRealisation (M := M) (N := N) :=
  ⟨transcendentalRealisation_of_unitSlot,
   transcendentalUnitSlot_of_claimStar_realisation hc⟩

/-- **The paper's Claim (⋆) in full**, at a transcendental unit: the frozen `M8.ClaimStar` (the
class computation plus `Standing`) **and** the realisation `f^* : ⟨Ŝ,e⟩ → N`.  The frozen encoding
keeps only the first half (`QE/Lemma36Statement.lean`'s docstring: "The `f*(rv(e)) = f(rv(e))` half
of Claim (⋆) — not formalised here"), so this is the missing half named. -/
def PaperClaimStar : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M), UnitHyp S m →
    (¬ ∃ n : ℕ, M8.AlgebraicOverVF S m n) → M8.ClaimStar S m ∧ ClosureEmbedding S f m

/-- **The paper's Claim (⋆) (both halves) gives the transcendental unit slot.** -/
theorem transcendentalUnitSlot_of_paperClaimStar (h : PaperClaimStar (M := M) (N := N)) :
    TranscendentalUnitSlot (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hunit htr
  have hU : UnitHyp S m := ⟨hS, hmVF, hmrv, hunit⟩
  obtain ⟨hcs, he⟩ := h S f m hU htr
  obtain ⟨g, hagree⟩ := he
  exact ⟨Closure S m, g, le_closure S m, hagree, mem_closure_self S m,
    M5P1.standing_closure_of_classControl hS hcs.1⟩

/-- Conversely the transcendental slot plus the class half gives the paper's Claim (⋆) — so
`PaperClaimStar` is *exactly* the transcendental unit slot, given the class half, and the
realisation is the only content of the paper's `f^*` that is not in the frozen `ClaimStar`. -/
theorem paperClaimStar_of_transcendentalUnitSlot (hc : TranscendentalClaimStar (M := M))
    (h : TranscendentalUnitSlot (M := M) (N := N)) : PaperClaimStar (M := M) (N := N) := by
  intro S f m hU htr
  exact ⟨hc S m hU htr, transcendentalRealisation_of_unitSlot h S f m hU htr⟩

/-- **THE EXACT STATEMENT FOR 3.6**: granting the *class* half of Claim (⋆) (the part the merged
`QE/Lemma36Statement.lean` set out to prove), the transcendental unit slot is *equivalent* to the
paper's realisation half.  Nothing else is left. -/
theorem transcendentalUnitSlot_iff_paperClaimStar (hc : TranscendentalClaimStar (M := M)) :
    TranscendentalUnitSlot (M := M) (N := N) ↔
      ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M), UnitHyp S m →
        (¬ ∃ n : ℕ, M8.AlgebraicOverVF S m n) → M8.ClaimStar S m → ClosureEmbedding S f m := by
  refine ⟨fun h S f m hU htr _ => transcendentalRealisation_of_unitSlot h S f m hU htr, ?_⟩
  intro h S f hS m hmVF hmrv hunit htr
  have hU : UnitHyp S m := ⟨hS, hmVF, hmrv, hunit⟩
  have hcs : M8.ClaimStar S m := hc S m hU htr
  obtain ⟨g, hagree⟩ := h S f m hU htr hcs
  exact ⟨Closure S m, g, le_closure S m, hagree, mem_closure_self S m,
    M5P1.standing_closure_of_classControl hS hcs.1⟩

/-- **The merged Lemma 3.6 derives nothing usable**: its hypothesis package has no instances
(`QE/RouteLedger.lean` §1: `M8.RVTrans` fails at every `KEqTop` substructure and every unit, because
the permitted coefficient set `S ∩ KOf` contains `rv e` itself).  So the *class* half `hc` of the
reduction above must come from the repaired statement (`RVTransVF`), not from the merged one. -/
theorem merged_lemma36_hyp_no_instances :
    ¬ ∃ (S : LRV.Substructure M) (e : M), M8.Lemma36Hyp S e :=
  RouteLedger.not_exists_lemma36Hyp

end Transcendental

/-! ## 3b. The transcendental class half from the paper's own hypotheses (no EP 3.4.3)

`QE/UnitCase.lean` proves the `Γ`-step of Lemma 3.6 in the unit branch without Engler–Prestel 3.4.3,
from **residue transcendence** (`M7.ResidueTranscendental` at the tree's own valuation
`VGBridge.vGammaValuation`).  That hypothesis — unlike `M8.RVTrans`, refuted at every `KEqTop`
substructure and every unit by `QE/RouteLedger.lean` §1 — is the paper's, and it is not vacuous
(`QE/UnitTranscendWitness.lean` exhibits a model with it).  The wrapper below reads it as the supply
for §3's `TranscendentalClaimStar`, so 3.6's *class* half costs exactly the paper's hypothesis cone
plus the bookkeeping rows at the closure — and nothing else. -/

section ClassHalf

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **Claim (⋆)'s class half at `⟨Ŝ,m⟩` from residue transcendence** (a direct reading of
`M8.ResidualClasses_of_VFGen_unit_min` at `T = Closure S m`, whose value computation comes from
`M8.ExpansionValMin_of_residueTranscendental`).  No `EPDimensionInequality`, no `RVTrans`. -/
theorem residualClasses_closure_of_residueTranscendental {S : LRV.Substructure M} {m : M}
    (hVFGen : Assembly.IsVFGen (Closure S m)) (hquot : M5L.QuotExpansions S (Closure S m) m)
    (hfinv : M5L.VFInvClosedOn S) (he : iVF m) (heu : iUnits (iRv m))
    (hT : M7.ResidueTranscendental (VGBridge.vGammaValuation (M := M)) (M8.KOfS S)
      (M8.vGamma_eq_one_of_units he heu)) :
    M5L.ResidualClasses S (Closure S m) :=
  M8.ResidualClasses_of_VFGen_unit_min (M8.ExpansionValMin_of_residueTranscendental he heu hT)
    heu hquot hfinv he hVFGen

/-- **3.6's class half (`TranscendentalClaimStar`) from the paper's hypotheses**: at every
transcendental unit, `rv m` residue-transcendental over `K(Ŝ)`, `VF(⟨Ŝ,m⟩)` a quotient field of
expansions of `m` (`QuotExpansions`), `⟨Ŝ,m⟩` `VF`-generated and `VF(Ŝ)` inverse closed. -/
theorem transcendentalClaimStar_of_residueTranscendental
    (hVFGen : ∀ (S : LRV.Substructure M) (m : M), UnitHyp S m →
      (¬ ∃ n : ℕ, M8.AlgebraicOverVF S m n) → Assembly.IsVFGen (Closure S m))
    (hquot : ∀ (S : LRV.Substructure M) (m : M), UnitHyp S m →
      (¬ ∃ n : ℕ, M8.AlgebraicOverVF S m n) → M5L.QuotExpansions S (Closure S m) m)
    (hfinv : ∀ (S : LRV.Substructure M) (m : M), UnitHyp S m →
      (¬ ∃ n : ℕ, M8.AlgebraicOverVF S m n) → M5L.VFInvClosedOn S)
    (htr : ∀ (S : LRV.Substructure M) (m : M) (hU : UnitHyp S m)
      (_hns : ¬ ∃ n : ℕ, M8.AlgebraicOverVF S m n),
      M7.ResidueTranscendental (VGBridge.vGammaValuation (M := M)) (M8.KOfS S)
        (M8.vGamma_eq_one_of_units hU.2.1 hU.2.2.2)) :
    TranscendentalClaimStar (M := M) := by
  intro S m hU hns
  have hres : M5L.ResidualClasses S (Closure S m) :=
    residualClasses_closure_of_residueTranscendental (hVFGen S m hU hns) (hquot S m hU hns)
      (hfinv S m hU hns) hU.2.1 hU.2.2.2 (htr S m hU hns)
  exact ⟨hres, M5P1.standing_closure_of_classControl hU.1 hres⟩

end ClassHalf

/-! ## 4. The repair-free route: the root hull is standing unconditionally

`QE/RouteLedger.lean` §1 proves `M8.Lemma36Hyp` inconsistent (`M8.RVTrans` fails at every `KEqTop`
substructure and every unit, because `S ∩ KOf` contains `rv e` itself), so the merged Lemma 3.6
derives nothing and §3's reduction is only as good as the repair of `RVTrans`.  The route below does
not need `ClaimStar` at all: `QE/RootHull.lean`'s root hull is `Standing` for free, so the residual
stated there costs no class control.  It is *strictly stronger* than the closure form
(`closureEmbedding_of_rootHullEmbedding`, and `closureEmbedding_of_mem` shows where the difference
lives). -/

section RootHullRoute

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **The repair-free unit residual**: `f` extends to the root hull of `S` at every unit `m`.
`Case35Hull.standing_rootHull` supplies `Standing (rootHull S m)` with no hypothesis, so this carries
no `ResidualClasses` and no `ClaimStar`. -/
def UnitRootHullEmbedding : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M), UnitHyp S m →
    Case35Hull.RootHullEmbedding (M := M) (N := N) S f m

/-- A root-hull embedding gives the slot conclusion (using `standing_rootHull`). -/
theorem slotConcl_of_rootHullEmbedding {S : LRV.Substructure M} {f : S ↪[LRV] N} {m : M}
    (hS : Assembly.Standing S) (h : Case35Hull.RootHullEmbedding (M := M) (N := N) S f m) :
    SlotConcl S f m := by
  obtain ⟨g, hagree⟩ := h
  exact ⟨Case35Hull.rootHull S m, g, Case35Hull.le_rootHull S m, hagree,
    Case35Hull.mem_rootHull_self S m, Case35Hull.standing_rootHull hS m⟩

/-- **The unit slot from the repair-free residual.** -/
theorem unitSlot_of_rootHullEmbedding (h : UnitRootHullEmbedding (M := M) (N := N)) :
    UnitSlot (M := M) (N := N) := by
  rw [unitSlot_iff_no_separated]
  intro S f m hU
  exact slotConcl_of_rootHullEmbedding hU.1 (h S f m hU)

/-- The root-hull residual gives the transcendental half without any `ClaimStar`. -/
theorem transcendentalUnitSlot_of_rootHullEmbedding
    (h : UnitRootHullEmbedding (M := M) (N := N)) :
    TranscendentalUnitSlot (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hunit _
  exact slotConcl_of_rootHullEmbedding hS (h S f m ⟨hS, hmVF, hmrv, hunit⟩)

/-- The root hull contains the closure, so the root-hull residual is *stronger* than the closure
form: it buys the `Standing` conjunct. -/
theorem closureEmbedding_of_rootHullEmbedding {S : LRV.Substructure M} {f : S ↪[LRV] N} {m : M}
    (h : Case35Hull.RootHullEmbedding (M := M) (N := N) S f m) :
    ClosureEmbedding S f m := by
  obtain ⟨g, hagree⟩ := h
  have hsub : ((S : Set M) ∪ {m}) ⊆ (Case35Hull.rootHull S m : Set M) := by
    rintro x (hx | hx)
    · exact Case35Hull.le_rootHull S m hx
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ Case35Hull.mem_rootHull_self S m
  have hle : Closure S m ≤ Case35Hull.rootHull S m := Substructure.closure_le.mpr hsub
  refine ⟨g.comp (Substructure.inclusion hle), ?_⟩
  intro x
  show g (Substructure.inclusion hle ⟨(x : M), le_closure S m x.2⟩) = f x
  exact hagree x

end RootHullRoute

/-! ## 5. The assembly: `RelUnit` from the ungated parts

The gate `M5Shoenfield.relGate` is *never* consumed by the unit half: `RootData`,
`TranscendentalClaimStar` and `TranscendentalRealisation` are statements about the pair alone, and
`UnitSlot`'s hypotheses carry their own saturation-free content.  So `RelUnit` follows from the
ungated parts, and a fortiori from anything stronger (e.g. `RootHullRealisation`). -/

section Assembly

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **THE UNIT HALF, assembled**: 3.4's residual `RootData` + 3.6's Claim (⋆) + the realisation
give `UnitSlot`. -/
theorem unitSlot_of_34_and_36 (h34 : RootData (M := M) (N := N))
    (hc : TranscendentalClaimStar (M := M)) (hr : TranscendentalRealisation (M := M) (N := N)) :
    UnitSlot (M := M) (N := N) :=
  RouteLedger.unitSlot_of_algebraic_transcendental (algebraicUnitSlot_of_rootData h34)
    (transcendentalUnitSlot_of_claimStar_realisation hc hr)

/-- **THE UNIT HALF FROM THE PAPER'S OWN HYPOTHESES** — the strongest assembled form in this file.
Residuals: (1) 3.4's `RootData` (algebraic branch: monic `F` over `O(Ŝ)`, henselianity, class
control); (2) the bookkeeping rows at the closure for the transcendental branch (`IsVFGen`,
`QuotExpansions`, `VFInvClosedOn`) *together with* the paper's residue-transcendence hypothesis, from
which `QE/UnitCase.lean` derives Claim (⋆)'s class half with no EP 3.4.3; (3) the realisation
`TranscendentalRealisation`. -/
theorem unitSlot_of_34_and_36_paper (h34 : RootData (M := M) (N := N))
    (hVFGen : ∀ (S : LRV.Substructure M) (m : M), UnitHyp S m →
      (¬ ∃ n : ℕ, M8.AlgebraicOverVF S m n) → Assembly.IsVFGen (Closure S m))
    (hquot : ∀ (S : LRV.Substructure M) (m : M), UnitHyp S m →
      (¬ ∃ n : ℕ, M8.AlgebraicOverVF S m n) → M5L.QuotExpansions S (Closure S m) m)
    (hfinv : ∀ (S : LRV.Substructure M) (m : M), UnitHyp S m →
      (¬ ∃ n : ℕ, M8.AlgebraicOverVF S m n) → M5L.VFInvClosedOn S)
    (htr : ∀ (S : LRV.Substructure M) (m : M) (hU : UnitHyp S m)
      (_hns : ¬ ∃ n : ℕ, M8.AlgebraicOverVF S m n),
      M7.ResidueTranscendental (VGBridge.vGammaValuation (M := M)) (M8.KOfS S)
        (M8.vGamma_eq_one_of_units hU.2.1 hU.2.2.2))
    (hr : TranscendentalRealisation (M := M) (N := N)) :
    UnitSlot (M := M) (N := N) :=
  unitSlot_of_34_and_36 h34
    (transcendentalClaimStar_of_residueTranscendental hVFGen hquot hfinv htr) hr

/-- The same with the class half moved out of 3.6 into `UnitClosureStanding`: the two residuals of
§1 are exactly `RootData`'s class control plus the realisation, on the algebraic side, and
`UnitClosureStanding` plus the realisation on the transcendental side. -/
theorem unitSlot_of_rootData_of_realisation (h34 : RootData (M := M) (N := N))
    (hs : UnitClosureStanding (M := M)) (hr : TranscendentalRealisation (M := M) (N := N)) :
    UnitSlot (M := M) (N := N) := by
  refine unitSlot_of_closure_parts ?_ hs
  intro S f m hU
  by_cases halg : ∃ n : ℕ, M8.AlgebraicOverVF S m n
  · exact algebraicClosureEmbedding_of_rootData h34 S f m hU halg
  · exact hr S f m hU halg

/-- **`RelUnit` from the ungated parts.** -/
theorem relUnit_of_parts
    (h34 : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      RootData (M := M) (N := N))
    (hc : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      TranscendentalClaimStar (M := M))
    (hr : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      TranscendentalRealisation (M := M) (N := N)) :
    RelUnit := by
  intro M N instM instN hM' hN' _
  exact unitSlot_of_34_and_36 (M := M) (N := N) (h34 M N) (hc M N) (hr M N)

/-- **`RelUnit` from the repair-free (`RootHull`) route** — no `ClaimStar`, hence no reliance on the
broken `M8.Lemma36Hyp`. -/
theorem relUnit_of_rootHull
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      UnitRootHullEmbedding (M := M) (N := N)) : RelUnit := by
  intro M N instM instN hM' hN' _
  exact unitSlot_of_rootHullEmbedding (M := M) (N := N) (h M N)

/-- **`RelUnit` from `Case35Hull.RootHullRealisation`** (the merged tree-wide residual): its units
alone suffice, and the gate is not needed. -/
theorem relUnit_of_rootHullRealisation (h : Case35Hull.RootHullRealisation) : RelUnit :=
  relUnit_of_rootHull (fun M N _ _ _ _ S f m hU => h M N S f hU.1 m hU.2.1)

/-- The gate-free form: if `UnitSlot` holds at *every* pair, `RelUnit` holds — the gate is inert. -/
theorem relUnit_of_ungated
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      UnitSlot (M := M) (N := N)) : RelUnit :=
  fun M N _ _ _ _ _ => h M N

/-! ### 5b. The gated form, and the frontier with `RelUnit` split -/

/-- **`RelUnit` from gated parts** — the form in which a gated proof of 3.4/3.6 would be fed (the
parts are still weaker than their gated versions, so this is the general consumption form). -/
theorem relUnit_of_gated_parts
    (h34 : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → RootData (M := M) (N := N))
    (hc : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → TranscendentalClaimStar (M := M))
    (hr : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → TranscendentalRealisation (M := M) (N := N)) :
    RelUnit := by
  intro M N instM instN hM' hN' hgate
  exact unitSlot_of_34_and_36 (M := M) (N := N) (h34 M N hgate) (hc M N hgate) (hr M N hgate)

/-- **`RelUnit` from a gated repair-free (root-hull) residual.** -/
theorem relUnit_of_gated_rootHull
    (hu : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → UnitRootHullEmbedding (M := M) (N := N)) : RelUnit := by
  intro M N instM instN hM' hN' hgate
  exact unitSlot_of_rootHullEmbedding (M := M) (N := N) (hu M N hgate)

end Assembly

/-! ### 5c. The frontier, with the unit part split into its residuals

Nothing new is used here: `QE/RouteLedger.lean`'s `paper_theorem_2_3_of_five_rel` with its `RelUnit`
hypothesis replaced by the residuals of §2–§4.  This is the machine-checked form of "`RelUnit` is the
only thing §2–§4 replace in the five-part list". -/

section Frontier

/-- **THE FIVE-PART ENDGAME, with `RelUnit` split** into 3.4's `RootData`, 3.6's class half, and the
transcendental realisation. -/
theorem paper_theorem_2_3_of_parts
    (hQ : M5Shoenfield.ShoenfieldTestRel) (hHull : RelHull) (hsep : RelSeparated)
    (hn : RelNonUnit) (hnew : RelNewRV)
    (h34 : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → RootData (M := M) (N := N))
    (hc : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → TranscendentalClaimStar (M := M))
    (hr : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → TranscendentalRealisation (M := M) (N := N)) :
    HasQE Axioms.ACVF :=
  RouteLedger.paper_theorem_2_3_of_five_rel hQ hHull hsep (relUnit_of_gated_parts h34 hc hr) hn hnew

/-- **The same, on the repair-free route**: the unit part is the root-hull embedding at units. -/
theorem paper_theorem_2_3_of_parts_rootHull
    (hQ : M5Shoenfield.ShoenfieldTestRel) (hHull : RelHull) (hsep : RelSeparated)
    (hn : RelNonUnit) (hnew : RelNewRV)
    (hu : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → UnitRootHullEmbedding (M := M) (N := N)) :
    HasQE Axioms.ACVF :=
  RouteLedger.paper_theorem_2_3_of_five_rel hQ hHull hsep (relUnit_of_gated_rootHull hu) hn hnew

end Frontier

/-! ## 6. Stress tests

Each of the tempting strengthenings / weakenings of §0–§5 is checked below, in the style the tree
uses (a machine-checked statement, not prose). -/

section Stress

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **The unit cone is inhabited, at every `KEqTop` substructure and every unit.**  So `UnitSlot` is
a statement about all of `U(M)` (`M5P1.rv_mem_of_units` supplies the `iRv m ∈ S` row for free). -/
theorem unitHyp_at_keqTop {S : LRV.Substructure M} (hS : Assembly.Standing S) {m : M}
    (hmVF : iVF m) (hunit : iUnits (iRv m)) : UnitHyp S m :=
  ⟨hS, hmVF, M5P1.rv_mem_of_units hS.1 hunit, hunit⟩

/-- **The slot's conclusion is not contradictory**: at any element already in `S` it holds with
`T = S`, `g = f`.  So `SlotConcl` (and hence every slot of `M4Cases.Cases`) is a satisfiable
predicate, and the residual is only about *new* units. -/
theorem slotConcl_of_mem (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (hS : Assembly.Standing S) {m : M} (hm : m ∈ S) : SlotConcl S f m :=
  ⟨S, f, le_rfl, fun _ => rfl, hm, hS⟩

/-- **The residual is trivial at old elements** — the closure of `S ∪ {m}` is `S` itself. -/
theorem closureEmbedding_of_mem (S : LRV.Substructure M) (f : S ↪[LRV] N) {m : M}
    (hm : m ∈ S) : ClosureEmbedding S f m := by
  have hle : Closure S m ≤ S := Substructure.closure_le.mpr (by
    rintro x (hx | hx)
    · exact hx
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hm)
  refine ⟨f.comp (Substructure.inclusion hle), ?_⟩
  intro x
  show f (Substructure.inclusion hle ⟨(x : M), le_closure S m x.2⟩) = f x
  rfl

/-- **The residual is consistent**: any global extension of `f` restricts to `⟨Ŝ,m⟩`.  So
`UnitClosureEmbedding` is implied by Proposition 3.9 at the pair and is not an unrelated
assertion. -/
theorem closureEmbedding_of_global
    (hglob : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ∃ g : M ↪[LRV] N,
      ∀ x : S, g (x : M) = f x)
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M) : ClosureEmbedding S f m := by
  obtain ⟨g, hg⟩ := hglob S f
  exact ⟨g.domRestrict (Closure S m), fun x => hg x⟩

/-- `Closure ⊤ m = ⊤`: adjoining an element to the top substructure changes nothing. -/
theorem closure_top (m : M) : Closure (⊤ : LRV.Substructure M) m = ⊤ := by
  refine le_antisymm le_top ?_
  intro x _
  exact Substructure.subset_closure (Or.inl trivial)

/-- **The class half is satisfiable at `⊤`**: `UnitClosureStanding`'s conclusion holds there. -/
theorem unitClosureStanding_top (m : M) (hU : UnitHyp (⊤ : LRV.Substructure M) m) :
    Assembly.Standing (Closure (⊤ : LRV.Substructure M) m) := by
  rw [closure_top]
  exact StandingTree.standing_top

/-- **`UnitClosureStanding` is not a restatement of `Standing S`**: it is a statement about a
*different* substructure (`⟨Ŝ,m⟩`), and the only inherited half is `KEqTop`
(`M5.KEqTop_mono`); the divisibility half is genuinely new.  Recorded as the exact content of the
predicate via `Case35Hull.standing_iff_rootClosedOn`: root closure, not class control. -/
theorem unitClosureStanding_iff_rootClosedOn (S : LRV.Substructure M) (m : M) :
    Assembly.Standing (Closure S m) ↔
      Assembly.KEqTop (Closure S m) ∧ Case35Hull.RootClosedOn (Closure S m) :=
  Case35Hull.standing_iff_rootClosedOn _

/-- **The gate is not needed for the unit half**: `UnitSlot` at the pair, with no `relGate`
hypothesis, is what the parts supply; recorded so that a consumer knows `RelUnit` cannot be blocked
by the gate's conjuncts. -/
theorem unitSlot_holds_ungated_from_parts (h34 : RootData (M := M) (N := N))
    (hc : TranscendentalClaimStar (M := M)) (hr : TranscendentalRealisation (M := M) (N := N)) :
    UnitSlot (M := M) (N := N) :=
  unitSlot_of_34_and_36 h34 hc hr

/-- **The residual list is consistent with the tree's `QFFinSat` route**: at a pair where the pushed
qf-types are finitely satisfiable, a *global* extension exists (`QE/Prop39Decomp.lean` §2), and then
the unit slot holds with `T = ⊤`.  So `RelUnit` is not an unrelated strengthening of the frontier's
other route; it is *weaker* than `QFFinSat` at `relGate` (which is the content of direction u6's
matrix, not of this file). -/
theorem unitSlot_of_extendsHere (h : G3.ExtendsHere M N) : UnitSlot (M := M) (N := N) := by
  intro S f _ m _ _ _ _
  obtain ⟨g, hg⟩ := h S f
  exact ⟨⊤, g.domRestrict ⊤, fun _ _ => trivial, fun x => hg x, trivial,
    StandingTree.standing_top⟩

theorem relUnit_of_qffinsat
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M5Shoenfield.relGate M N → M2Saturation.QFFinSat M N) : RelUnit := by
  intro M N instM instN hM' hN' hgate
  exact unitSlot_of_extendsHere (fun S f =>
    G3.extendsAt_rel_of_finSat hfin M N hgate S f)

end Stress

/-! ## 7. Axiom audit -/

#print axioms SpecialTransformations.Milestone0.RelUnit.closureEmbedding_of_slotConcl
#print axioms SpecialTransformations.Milestone0.RelUnit.slotConcl_iff_closureEmbedding
#print axioms SpecialTransformations.Milestone0.RelUnit.unitSlot_iff_no_separated
#print axioms SpecialTransformations.Milestone0.RelUnit.unitSlot_of_closure_parts
#print axioms SpecialTransformations.Milestone0.RelUnit.closureEmbedding_of_unitSlot
#print axioms SpecialTransformations.Milestone0.RelUnit.unitClosureStanding_of_residualClasses
#print axioms SpecialTransformations.Milestone0.RelUnit.rootData_iff_rootData'
#print axioms SpecialTransformations.Milestone0.RelUnit.algebraicUnitSlot_of_rootData
#print axioms SpecialTransformations.Milestone0.RelUnit.slot34_holds
#print axioms SpecialTransformations.Milestone0.RelUnit.algebraicUnitSlot_of_rootData_via_slot34
#print axioms SpecialTransformations.Milestone0.RelUnit.algebraicClosureEmbedding_of_rootData
#print axioms SpecialTransformations.Milestone0.RelUnit.claimStar_iff_residualClasses
#print axioms SpecialTransformations.Milestone0.RelUnit.transcendentalUnitSlot_of_claimStar_realisation
#print axioms SpecialTransformations.Milestone0.RelUnit.transcendentalRealisation_of_unitSlot
#print axioms SpecialTransformations.Milestone0.RelUnit.transcendentalUnitSlot_iff_of_claimStar
#print axioms SpecialTransformations.Milestone0.RelUnit.slotConcl_of_rootHullEmbedding
#print axioms SpecialTransformations.Milestone0.RelUnit.unitSlot_of_rootHullEmbedding
#print axioms SpecialTransformations.Milestone0.RelUnit.closureEmbedding_of_rootHullEmbedding
#print axioms SpecialTransformations.Milestone0.RelUnit.unitSlot_of_34_and_36
#print axioms SpecialTransformations.Milestone0.RelUnit.relUnit_of_parts
#print axioms SpecialTransformations.Milestone0.RelUnit.relUnit_of_rootHull
#print axioms SpecialTransformations.Milestone0.RelUnit.relUnit_of_rootHullRealisation
#print axioms SpecialTransformations.Milestone0.RelUnit.relUnit_of_ungated
#print axioms SpecialTransformations.Milestone0.RelUnit.unitHyp_at_keqTop
#print axioms SpecialTransformations.Milestone0.RelUnit.slotConcl_of_mem
#print axioms SpecialTransformations.Milestone0.RelUnit.closureEmbedding_of_mem
#print axioms SpecialTransformations.Milestone0.RelUnit.closureEmbedding_of_global
#print axioms SpecialTransformations.Milestone0.RelUnit.closure_top
#print axioms SpecialTransformations.Milestone0.RelUnit.residualClasses_closure_of_residueTranscendental
#print axioms SpecialTransformations.Milestone0.RelUnit.transcendentalClaimStar_of_residueTranscendental
#print axioms SpecialTransformations.Milestone0.RelUnit.unitSlot_of_34_and_36_paper
#print axioms SpecialTransformations.Milestone0.RelUnit.unitClosureStanding_top
#print axioms SpecialTransformations.Milestone0.RelUnit.transcendentalUnitSlot_of_paperClaimStar
#print axioms SpecialTransformations.Milestone0.RelUnit.paperClaimStar_of_transcendentalUnitSlot
#print axioms SpecialTransformations.Milestone0.RelUnit.transcendentalUnitSlot_iff_paperClaimStar
#print axioms SpecialTransformations.Milestone0.RelUnit.merged_lemma36_hyp_no_instances
#print axioms SpecialTransformations.Milestone0.RelUnit.relUnit_of_gated_parts
#print axioms SpecialTransformations.Milestone0.RelUnit.relUnit_of_gated_rootHull
#print axioms SpecialTransformations.Milestone0.RelUnit.paper_theorem_2_3_of_parts
#print axioms SpecialTransformations.Milestone0.RelUnit.paper_theorem_2_3_of_parts_rootHull
#print axioms SpecialTransformations.Milestone0.RelUnit.unitSlot_of_extendsHere
#print axioms SpecialTransformations.Milestone0.RelUnit.relUnit_of_qffinsat

end SpecialTransformations.Milestone0.RelUnit
