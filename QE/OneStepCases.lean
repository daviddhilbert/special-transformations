/-
# Direction e4: the paper's case split for Lemmas 3.4–3.8, and the assembly combinator

Member `m4`, swarm `smw2jkpn4`.  Reference: Yimu Yin, *Special transformations in algebraically
closed valued fields*, §3.1 (`refs/qe.tex`): at a fixed pair `M, N ⊨ ACVF` with `N` `‖M‖⁺`-saturated,
a fixed substructure `S ⊆ M` and a fixed monomorphism `f : S → N`, Lemmas 3.4–3.8 add one element
`m ∈ VF(M)` at a time, preserving the paper's two standing properties
(`Assembly.Standing S` = `K(Ŝ) = K(M)` plus `Γ(Ŝ)` divisible).  The frozen obligation is

    Assembly.OneStepVFP (M := M) (N := N)
      ∀ S f, Standing S → ∀ m, iVF m →
        ∃ T g hST, (∀ x : S, g ⟨x, hST x.2⟩ = f x) ∧ m ∈ T ∧ Standing T

and the swarm's surviving quantifier shape (`ultramath/smw2ioy2w/m7/HahnObstruction.lean`) is the
gate `OneStepPaper := ∀ M N, M7Paper.PaperHyp M N → OneStepVFP`.

## What this file does

**§1 The case split.**  At the fixed pair the paper's case analysis is exactly

* `m ∈ S` — nothing to do (`trivial_at_mem`, no hypothesis needed);
* `m ∉ S`, `rv m ∈ RV(S)` (no new `RV`-element), and `vv(m^k) ∉ Γ(Ŝ)` for `k > 0` — **Lemma 3.4
  (`lift:all:root`) / Lemma 3.6 (`lift:transcendental`)**, the *separated* case,
  `M5L.Separated S m` in `QE/M5L34_36.lean`'s transcription;
* `m ∉ S`, `rv m ∈ RV(S)`, **not** separated — Lemma 3.5 (`lift:divisible:hull`): `m^n = a ∈ VF(Ŝ)`,
  where the separation condition only has to hold for `0 < k < n`;
* `rv m ∉ RV(S)` — **Lemma 3.7 / Lemma 3.8 (`lift:value:full`)**: `Γ` grows, so `Standing T`
  additionally forces the divisible hull of `Γ(S) + ℤ·vv(m)` into `T` (`M5.OneStepRVNew`).  This is
  strictly stronger than the paper's per-element Claim (⋆), which only ever adds `e` with
  `rv(e) ∈ RV(S)` and re-hulls between phases; it is nevertheless the frozen obligation, and m7's
  gate is the frozen obligation.

`Cases` packages the three nontrivial branches as named hypotheses, and `oneStepVFP_of_cases`
assembles them into the frozen `OneStepVFP *at the fixed pair*, with **no gate of its own**: every
slot is a statement about this `M`, this `N`, and the `S, f, m` it is handed.  So the ledger
specialises directly under m7's `∀ M N, PaperHyp M N →` gate (`oneStepPaper_of_cases`) and feeds
`QE/M5Ledger.lean` §10b's paper-pair route (`paper_theorem_2_3_sat_of_cases`).

**§2 The separated slot is not the conclusion, and does not carry the tree's extra hypothesis.**
`QE/M5L34_36.lean`'s separated case (`M5L.OneStepSeparatedP`) assumes `M5L.VFInvClosedOn S`: every
`VF`-element of `S` whose `rv`-class lies in `S` has an inverse whose `rv`-class lies in `S`.  That
is **not** a consequence of `Standing S`: `S`'s `VF`-sort is a sub*ring* of `M` (the frozen language
`L_RV` has no inverse symbol on the `VF` sort, `Milestone0/Encoding.lean` `Fn`), `Kˣ ⊆ S` is free but
an inverse of a non-unit is not a term, and no axiom of `ACVF` produces one.  Since
`OneStepVFP`/`OneStepPaper` quantify over *arbitrary* `Standing S`, a case hypothesis with
`VFInvClosedOn` would be a strengthening, not a decomposition — the same defect that
`PrepStepP`'s missing size bound had.  The separated slot below therefore does **not** assume it;
`VFInvClosedOn` appears only in `cases_of_classStepP`, where it is part of the *tree's* sufficient
interface, not of the ledger.

**§3 The ledger is implied by the tree's own interfaces** (stress test (a): no slot is the
conclusion, and the ledger introduces nothing new):

* `cases_of_classStepP` — `M5L.ClassStepP` (the `Γ`-class form of Claim (⋆), `QE/M5L34_36.lean`)
  plus `M5.OneStepRVNew` discharge all three slots;
* `cases_of_stepObligation` — `M1QFStep.StepObligation` (atomic match + `RV`-control of the
  closure, `QE/M1QFStep.lean`) discharges all three slots.  This is the explicit mapping to
  `M1QFStep.StepObligation`: a proof of the obligation at every `(S, f, m)` is strictly more than the
  ledger asks for.

**§4 Stress tests.**

* (a) `trivial_at_mem`: for `m ∈ S` the conclusion holds with `T = S`, `g = f` — so the slots are
  needed only for genuinely new elements, and none of them is "the conclusion at the trivial point".
* (a′) `cases_of_classStepP`, `cases_of_stepObligation`: the slots are *implied* by interfaces that
  already exist in the tree, so the ledger cannot be stronger than what the tree already owes.
* (b) `standing_forces_units_size` (`QE/PaperRoute.lean`) shows that `Standing S` plus an embedding
  `S ↪ N` already forces `#Kˣ(M) ≤ #N`; the gate `PaperHyp` supplies it
  (`paperHyp_units_size`).  The slots contain no cardinality conjunct beyond that, and
  `gated_size` records the guard's two components.
* (b′) `oneStepPaper_of_free`: the gated shape is implied by the frozen ungated one, so the ledger
  is not weakened by the gate.

No `sorry`, no `axiom`, no `native_decide`; axiom audit at the end of the file.
-/
import M5Ledger
import M5L34_36
import M5OneStep
import M1QFStep

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SpecialTransformations.Milestone0
namespace M4Cases

open FirstOrder FirstOrder.Language

/-! ## 1. The three case hypotheses at a fixed pair -/

section FixedPair

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]

/-- **Lemmas 3.4 / 3.6 (`lift:all:root`, `lift:transcendental`), separated branch**, with the
tree's `M5L.VFInvClosedOn` hypothesis *removed*.

The element `m` is new, its `rv` is old (`iRv m ∈ S`), and `vv(m^k) ∉ Γ(Ŝ)` for `k > 0`
(`M5L.Separated S m`, the frozen transcription of the paper's separation hypothesis).  The slot asks
for the extension with `Standing T`; the paper's proof supplies it by the dominant-monomial
computation (`M5L.rvPoly_mem_of_separated`) plus `Standing`-preservation
(`M5.standing_of_RV_le`). -/
def CaseSeparated : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
    M5L.Separated S m →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T

/-- **Lemma 3.5 (`lift:divisible:hull`), not-separated branch**: `m` is new, its `rv` is old, but
some class of `m^k` (`k > 0`) times a class of `S` is a class of `S` — the paper's case
`m^n = a ∈ VF(Ŝ)`, where the separation condition is needed only up to `n`.  Same conclusion, and
again **no** `VFInvClosedOn`. -/
def CaseNotSeparated : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
    ¬ M5L.Separated S m →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T

/-- **Lemmas 3.7 / 3.8 (`lift:transcendental`, `lift:value:full`), new-`rv` branch**: the divisible
hull of `Γ(S) + ℤ·vv(m)` has to enter `T` in the same step, which is the frozen
`M5.OneStepRVNew`. -/
abbrev CaseNewRV : Prop := M5.OneStepRVNew (M := M) (N := N)

/-- The paper's case split for Lemmas 3.4–3.8 at the fixed pair `(M, N)`. -/
structure Cases : Prop where
  /-- Lemmas 3.4/3.6, separated.
  **ATTRIBUTION CORRECTION (QE/Case34Slot.lean, swarm smw2mluv7 m1, machine-checked):** this is NOT
  where Lemma 3.4 belongs — 3.4's hypothesis `e ∈ U(M)` makes `M5L.Separated` FALSE
  (`not_separated_of_units`), so the 3.4 data is never a `CaseSeparated` configuration
  (`liftAllRoot_not_separated`, `slot34_at_caseSeparated_hypotheses_vacuous`). The separated slot is
  the infinite-order configuration only (Lemma 3.7's hypothesis). Lemma 3.4 — and 3.6, also a unit
  case — live in `CaseNotSeparated`, which therefore splits into a unit half (3.4/3.6) and a
  non-unit half (3.5): `caseNotSeparated_iff_unit_and_nonunit`. A proof of only the `m^n = a` half is
  provably incomplete. -/
  separated : CaseSeparated (M := M) (N := N)
  /-- Lemma 3.5, not separated — and, per QE/Case34Slot.lean, also Lemmas 3.4 and 3.6 (the unit
  half): see `caseNotSeparated_iff_unit_and_nonunit`. -/
  notSeparated : CaseNotSeparated (M := M) (N := N)
  /-- Lemmas 3.7/3.8, `rv`-new. -/
  newRV : CaseNewRV (M := M) (N := N)

/-! ## 2. The combinator: the frozen one-step from the three branches -/

/-- **`m ∈ S` costs nothing**: `T = S`, `g = f`.  Recorded so that the case slots are applied only
at genuinely new elements — the stress test that no slot is the conclusion at the trivial point. -/
theorem exists_oneStep_of_mem (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (hS : Assembly.Standing S) {m : M} (hm : m ∈ S) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T :=
  ⟨S, f, le_rfl, fun _ => rfl, hm, hS⟩

/-- **The two `rv`-old branches give `M5.OneStepRVOld`.**  The case split is on
`M5L.Separated S m`; for `m ∈ S` no branch is used at all.  Note that neither branch mentions
`M5L.VFInvClosedOn`, unlike `QE/M5L34_36.lean`'s `oneStepRVOld_of_separated_and_rest`. -/
theorem oneStepRVOld_of_cases (hsep : CaseSeparated (M := M) (N := N))
    (hnotsep : CaseNotSeparated (M := M) (N := N)) : M5.OneStepRVOld (M := M) (N := N) := by
  intro S f hS m hmVF hmrv
  by_cases hm : m ∈ S
  · exact exists_oneStep_of_mem S f hS hm
  · by_cases hsep' : M5L.Separated S m
    · exact hsep S f hS m hmVF hmrv hsep'
    · exact hnotsep S f hS m hmVF hmrv hsep'

/-- **The frozen one-step at the fixed pair, from the paper's three cases.**  This is the
combinator: `M5.oneStepVFP_of_two_steps` (the `rv`-old / `rv`-new split) with its `rv`-old half
proved from the paper's two branches.  No size hypothesis, no saturation hypothesis, no
`∀ M ∀ N` gate appears here, so `oneStepPaper_of_cases` specialises it under m7's gate. -/
theorem oneStepVFP_of_cases (h : Cases (M := M) (N := N)) :
    Assembly.OneStepVFP (M := M) (N := N) :=
  M5.oneStepVFP_of_two_steps (oneStepRVOld_of_cases h.separated h.notSeparated) h.newRV

/-- The same at one element, in the shape `Assembly.OneStepVFP` unfolds to (for reading off which
slot is used where). -/
theorem exists_oneStep_of_cases (h : Cases (M := M) (N := N))
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (hS : Assembly.Standing S) (m : M) (hmVF : iVF m) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T :=
  oneStepVFP_of_cases h S f hS m hmVF

/-! ## 3. The ledger is implied by the tree's own interfaces

Both theorems below are *implications into* `Cases`, i.e. they show that the ledger asks for no more
than interfaces that already exist in the tree.  They are the (a)-stress test: no slot is the
conclusion in disguise, and the ledger is not a strengthening of the frozen obligation. -/

/-- **The ledger is satisfiable wherever Proposition 3.9 holds at the pair.**  If every
monomorphism out of a substructure of `M` extends to a total `M ↪[LRV] N`, then all three slots hold
with `T = ⊤` (`Assembly.Standing (⊤)` is `StandingTree.standing_top`).  So the slots are not
contradictory, and they are implied by the conclusion of Proposition 3.9 at the pair — the
`OneStepVFP`-analogue of `M1QF.Frozen.oneStepVFP_of_global_extension`. -/
theorem cases_of_global_extension
    (hglob : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ∃ g : M ↪[LRV] N,
      ∀ x : S, g (x : M) = f x) : Cases (M := M) (N := N) where
  separated := by
    intro S f _hS m _hmVF _hmrv _hsep
    obtain ⟨g, hg⟩ := hglob S f
    exact ⟨⊤, g.domRestrict ⊤, fun _ _ => trivial, fun x => hg x, trivial,
      StandingTree.standing_top⟩
  notSeparated := by
    intro S f _hS m _hmVF _hmrv _hnotsep
    obtain ⟨g, hg⟩ := hglob S f
    exact ⟨⊤, g.domRestrict ⊤, fun _ _ => trivial, fun x => hg x, trivial,
      StandingTree.standing_top⟩
  newRV := by
    intro S f _hS m _hmVF _hmrv
    obtain ⟨g, hg⟩ := hglob S f
    exact ⟨⊤, g.domRestrict ⊤, fun _ _ => trivial, fun x => hg x, trivial,
      StandingTree.standing_top⟩

/-- **The ledger is implied by `M5.OneStepRVOld`** — the tree's two-piece decomposition of the
frozen one-step (`QE/M5OneStep.lean` §2).  The separated / not-separated split is a *sub-split* of the
`rv`-old case, so it loses nothing: whatever proves the `rv`-old case proves both slots. -/
theorem cases_of_oneStepRVOld (hold : M5.OneStepRVOld (M := M) (N := N))
    (hnew : CaseNewRV (M := M) (N := N)) : Cases (M := M) (N := N) where
  separated := by
    intro S f hS m hmVF hmrv _hsep
    exact hold S f hS m hmVF hmrv
  notSeparated := by
    intro S f hS m hmVF hmrv _hnotsep
    exact hold S f hS m hmVF hmrv
  newRV := hnew

/-- **The separated slot in `RV`-control form** (`M5.RVStepP`'s conclusion): if the case produces the
extension with `RV(T) ⊆ S` — the sharp form of Claim (⋆) — then `Standing T` follows by
`M5.standing_of_RV_le`.  Stated so that the slot can be discharged in the vocabulary in which
`QE/M5L34_36.lean` §2 proves Claim (⋆). -/
theorem caseSeparated_of_RVControl
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      iRv m ∈ S → M5L.Separated S m →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧
          (∀ y : M, y ∈ T → iRV y → y ∈ S)) :
    CaseSeparated (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hsep
  obtain ⟨T, g, hST, hagree, hmT, hRV⟩ := h S f hS m hmVF hmrv hsep
  exact ⟨T, g, hST, hagree, hmT, M5.standing_of_RV_le hST hS hRV⟩

/-- **The separated slot in `Γ`-class form** (`M5L.ResidualClasses`, the form `QE/M5L34_36.lean` §2d
establishes it in): if the case produces the extension with the class computation
`∀ y ∈ T, ∃ s ∈ S, Cls y s`, then `Standing T` follows by `M5L.standing_of_ClassControl`. -/
theorem caseSeparated_of_ResidualClasses
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      iRv m ∈ S → M5L.Separated S m →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ M5L.ResidualClasses S T) :
    CaseSeparated (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hsep
  obtain ⟨T, g, hST, hagree, hmT, hcc⟩ := h S f hS m hmVF hmrv hsep
  exact ⟨T, g, hST, hagree, hmT, M5L.standing_of_ClassControl hST hS hcc⟩

/-- **`M5L.ClassStepP` plus the new-`rv` case discharge the ledger.**  `ClassStepP` is the
`Γ`-class form of Claim (⋆) for *every* new `VF`-element (`QE/M5L34_36.lean` §1b); it implies both
`rv`-old slots, because `Standing T` then follows from the class computation by
`M5L.standing_of_ClassControl`. -/
theorem cases_of_classStepP (hcls : M5L.ClassStepP (M := M) (N := N))
    (hnew : CaseNewRV (M := M) (N := N)) : Cases (M := M) (N := N) where
  separated := by
    intro S f hS m hmVF _hmrv _hsep
    obtain ⟨T, g, hST, hagree, hmT, hcc⟩ := hcls S f hS m hmVF
    exact ⟨T, g, hST, hagree, hmT, M5L.standing_of_ClassControl hST hS hcc⟩
  notSeparated := by
    intro S f hS m hmVF _hmrv _hnotsep
    obtain ⟨T, g, hST, hagree, hmT, hcc⟩ := hcls S f hS m hmVF
    exact ⟨T, g, hST, hagree, hmT, M5L.standing_of_ClassControl hST hS hcc⟩
  newRV := hnew

/-- **`M1QFStep.StepObligation` discharges the ledger** — the explicit mapping to
`M1QFStep.StepObligation`.  A `StepObligation (S, f, m)` is an atomic match `n ∈ N` for `m` over
`f '' S` plus `RV`-control `RV(⟨S, m⟩) ⊆ S`.  `atomicAgree` gives, through
`M1QF.exists_embedding_closure_of_atomic`, an embedding `⟨S, m⟩ ↪ N` extending `f`
(`QE/M1QFStep.lean` §1–§2), and `RV`-control gives `Standing ⟨S, m⟩` by
`M1QF.Frozen.standing_of_RV_le`.  So *every* slot of `Cases` follows from the obligation, whatever
the relationship of `m` to `S`. -/
theorem oneStepAt_of_obligation
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      M1QF.Frozen.StepObligation S f m)
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (hS : Assembly.Standing S) (m : M) (hmVF : iVF m) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T := by
  obtain ⟨n, hagree, hRV⟩ := h S f hS m hmVF
  obtain ⟨g, hincl, -⟩ := M1QF.exists_embedding_closure_of_atomic S f
    (fun _ : Unit => m) (fun _ => n) hagree
  refine ⟨Substructure.closure LRV ((S : Set M) ∪ Set.range (fun _ : Unit => m)), g,
    fun x hx => Substructure.subset_closure (Or.inl hx), ?_, ?_, ?_⟩
  · intro x
    exact hincl x
  · exact Substructure.subset_closure (Or.inr ⟨(), rfl⟩)
  · exact M1QF.Frozen.standing_of_RV_le (fun x hx => Substructure.subset_closure (Or.inl hx)) hS hRV

/-- **The obligation discharges the ledger.** -/
theorem cases_of_stepObligation
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      M1QF.Frozen.StepObligation S f m) : Cases (M := M) (N := N) where
  separated := by
    intro S f hS m hmVF _hmrv _hsep
    exact oneStepAt_of_obligation h S f hS m hmVF
  notSeparated := by
    intro S f hS m hmVF _hmrv _hnotsep
    exact oneStepAt_of_obligation h S f hS m hmVF
  newRV := by
    intro S f hS m hmVF _hmrv
    exact oneStepAt_of_obligation h S f hS m hmVF

end FixedPair

/-! ## 4. The gated route: m7's `OneStepPaper` and `QE/M5Ledger.lean` §10b -/

/-- **Lemmas 3.4–3.8 at the paper's pairs** — verbatim the body of
`.ultramath/smw2ioy2w/m7/HahnObstruction.lean`'s `OneStepPaper` (the swarm's surviving quantifier
shape), restated here so that this file depends only on the merged tree. -/
def OneStepPaper : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.PaperHyp M N → Assembly.OneStepVFP (M := M) (N := N)

/-- **The gated one-step from the case ledger.**  The ledger is demanded at the paper's pairs only;
by `oneStepVFP_of_cases` it needs no hypothesis of its own, so the gate is the only quantifier
restriction. -/
theorem oneStepPaper_of_cases
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M7Paper.PaperHyp M N → Cases (M := M) (N := N)) : OneStepPaper :=
  fun M N _ _ _ _ hP => oneStepVFP_of_cases (h M N hP)

/-- **The gate is a weakening of the frozen shape** (`M7Paper.OneStepSizeFree`): the frozen
ungated obligation implies the gated one.  (That the converse fails is m7's refutation, which this
file does not reprove.) -/
theorem oneStepPaper_of_free (h : M7Paper.OneStepSizeFree) : OneStepPaper :=
  fun M N _ _ _ _ _ => h M N

/-- **Proposition 3.9 at the paper's pairs, from the ledger's prep step and the gated one-step.**
This is `QE/M5Ledger.lean`'s `prop39Sat_of_prepStepPaper` with `M7Paper.OneStepSizeFree` weakened to
the gated shape: `Assembly.prop39P_noVFGen` never touches a saturation hypothesis, so it can use the
one-step only at the pair it is applied at. -/
theorem prop39Sat_of_prepStepPaper_gated (hPrep : M5Ledger.PrepStepPaper)
    (hOne : OneStepPaper) : M7Paper.Prop39Sat := by
  intro M N _ _ _hM _hN hP S f
  exact Assembly.prop39P_noVFGen (hPrep M N hP) (hOne M N hP) S f

/-- **Theorem 2.3 (`qe:acvf`) from the five ledger inputs and the case ledger.**  §10b's
paper-pair route with the one-step hypothesis supplied by §2 instead of `OneStepSizeFree`. -/
theorem paper_theorem_2_3_sat_of_cases (hShoen : M7Paper.ShoenfieldTestSat)
    (h1 : M5Ledger.LedgerInput1P) (h2 : M5Ledger.LedgerInput2)
    (h3 : M5Ledger.LedgerInput3P) (h4 : M5Ledger.LedgerInput4P) (h5 : M5Ledger.LedgerInput5P)
    (hcases : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], M7Paper.PaperHyp M N → Cases (M := M) (N := N)) :
    HasQE Axioms.ACVF :=
  hShoen (prop39Sat_of_prepStepPaper_gated
    (M5Ledger.prepStepPaper_of_ledger h1 h2 h3 h4 h5) (oneStepPaper_of_cases hcases))

/-! ## 5. The cardinality audit (stress test (b))

`Assembly.Standing S` already contains every unit of `M` (`KEqTop`), so an embedding `S ↪[LRV] N`
forces `#Kˣ(M) ≤ #N`; that is the only cardinality content anywhere near the ledger, the gate
`M7Paper.PaperHyp` supplies it, and no slot of `Cases` adds a cardinality conjunct. -/

section Size

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- The guard's two components: `N` is `SaturatedFS` and `#M ≤ #N`. -/
theorem gated_size (h : M7Paper.PaperHyp M N) :
    Assembly.SaturatedFS N ∧ M7Paper.SizeHyp M N := h

/-- The guard supplies `#M ≤ #N`. -/
theorem paperHyp_size (h : M7Paper.PaperHyp M N) : Cardinal.mk M ≤ Cardinal.mk N :=
  M7Paper.sizeHyp_of_paperHyp h

/-- The guard supplies the bound that `Standing` plus an embedding needs — so the case slots are
satisfiable-at-`PaperHyp` as far as cardinality is concerned. -/
theorem paperHyp_units_size (h : M7Paper.PaperHyp M N) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N :=
  M7Paper.paperHyp_supplies_units_size h

/-- The same bound, as forced by the one-step's *own* hypothesis `Standing S` and any embedding
`S ↪[LRV] N` (`QE/PaperRoute.lean`): the ledger cannot be refuted by a cardinality argument that
does not already refute the frozen obligation. -/
theorem standing_forces_units_size (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (hS : Assembly.Standing S) : Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N :=
  M7Paper.standing_forces_units_size S f hS

end Size

end M4Cases
end SpecialTransformations.Milestone0

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.M4Cases.exists_oneStep_of_mem
#print axioms SpecialTransformations.Milestone0.M4Cases.oneStepRVOld_of_cases
#print axioms SpecialTransformations.Milestone0.M4Cases.oneStepVFP_of_cases
#print axioms SpecialTransformations.Milestone0.M4Cases.exists_oneStep_of_cases
#print axioms SpecialTransformations.Milestone0.M4Cases.cases_of_global_extension
#print axioms SpecialTransformations.Milestone0.M4Cases.cases_of_oneStepRVOld
#print axioms SpecialTransformations.Milestone0.M4Cases.caseSeparated_of_RVControl
#print axioms SpecialTransformations.Milestone0.M4Cases.caseSeparated_of_ResidualClasses
#print axioms SpecialTransformations.Milestone0.M4Cases.cases_of_classStepP
#print axioms SpecialTransformations.Milestone0.M4Cases.oneStepAt_of_obligation
#print axioms SpecialTransformations.Milestone0.M4Cases.cases_of_stepObligation
#print axioms SpecialTransformations.Milestone0.M4Cases.oneStepPaper_of_cases
#print axioms SpecialTransformations.Milestone0.M4Cases.oneStepPaper_of_free
#print axioms SpecialTransformations.Milestone0.M4Cases.prop39Sat_of_prepStepPaper_gated
#print axioms SpecialTransformations.Milestone0.M4Cases.paper_theorem_2_3_sat_of_cases
#print axioms SpecialTransformations.Milestone0.M4Cases.gated_size
#print axioms SpecialTransformations.Milestone0.M4Cases.paperHyp_size
#print axioms SpecialTransformations.Milestone0.M4Cases.paperHyp_units_size
#print axioms SpecialTransformations.Milestone0.M4Cases.standing_forces_units_size
