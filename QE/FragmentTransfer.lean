/-
**The fragment transfer, composed** — merged from swarm `smw1bwjo2` m8 (direction d5), accepted
after compiling and reading it here.  `import Enc` only; 0 errors, no `sorry`, axioms within
{propext, Classical.choice, Quot.sound}.

The result: `TransferComp.transferAtWS_of_qfStep : QFStep P T → TransferAtWS P T`, and hence
`TransferComp.nontrivialTransferWS_ACVF_of_qfStep`.  So the whole remaining content of
`QE/TransferWS.lean`'s `NontrivialTransferWS Axioms.ACVF` is one hypothesis, `QFStep`: *for a sorted
element of one model there is a sorted element of the other whose well-sorted quantifier-free type at
the extended tuple matches*.  That is the one-element extension (back-and-forth) step — the paper's
§3/§4 effectiveness content — and it is not the conclusion in disguise: it quantifies only over
quantifier-free formulas and only at one added element.

The induction is `BoundedFormula.rec` with the sorted context and the two tuples in the motive, which
is the only shape that works (`WellSorted` is an indexed family, so one cannot usefully induct on the
derivation).  The `all` case splits the bound value by `sortEval s`: outside the sort it closes with
the junk-truth of the repaired `GuardTrue` (see `QE/JunkTrue.lean`), inside it uses `QFStep` and the
induction hypothesis, both directions (`step` is obtained from `step'` by applying `QFStep` with the
models swapped).

`transferAtWS_all_ACVF_of_qfStep` takes `AllNontrivial Axioms.ACVF` as a hypothesis; the tree proves
it (`QE/Assembly_val.lean`, `TrivialHalf.allNontrivial_ACVF`), so that antecedent is discharged and
only `QFStep` remains.  Note that the copied `IsNontrivialVF` uses `x ≠ iRVZero`, matching
`QE/TransferWS.lean`'s frozen statement rather than `Assembly_val`'s `x ≠ iVFZero`; the two agree for
`x ∈ VF` given `sdDisjoint`.

Check with `.scratch2/sec3/` (a compiled `Enc`): copy this file there and
`LEAN_PATH=$PWD:$LEAN_PATH lean` it.
-/
import Enc

/-
# The composition: the well-sorted fragment transfer from the QF-type step

This file carries direction **d4 (composition)** of swarm `smw1bwjo2`.

`QE/TransferWS.lean` freezes `NontrivialTransferWS Axioms.ACVF` as the target: two models of
`ACVF` whose valuation is nontrivial, at sort-respecting tuples, that agree on every well-sorted
*quantifier-free* formula, agree on every well-sorted formula.  Here that statement is **composed**
from two ingredients:

* `LRV.GuardTrue`'s junk-truth, proved here in full (`guardTrue_realize`), with no model axiom —
  it is the purely syntactic statement that a guarded body is true at carrier elements outside the
  sort;
* `QFStep`, the one-element extension property of a well-sorted quantifier-free type ("the
  back-and-forth step"): for a sorted element of one model there is an element of the same sort in
  the other model whose extended QF type matches.

The induction is on the formula structure, with the `WellSorted` derivation consumed at each node;
`BoundedFormula.all` ranges over the *whole* one-sorted carrier, so the `all` case splits the bound
value by whether it lies in the sort: inside, `QFStep` + the induction hypothesis; outside, the
junk-truth lemma.  That split is the reason the guard repair exists (`Milestone0/DECISION.md`).

Nothing here needs `TmSort` soundness, and nothing here restates a theorem of the tree: the
conclusion is stated for an arbitrary theory `T` and an arbitrary class of models `P`, and the
`all` case is the only place where the two ingredients meet.
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations
namespace Milestone0
open LRV

namespace TransferComp

/-! ## 1. The junk-truth semantics of the guard

`guardAtom s i` is `sortPredG s (var i)`, so it realises to `sortEval s` of the `i`-th component;
`InAntecedent` puts that atom among the top-level conjuncts of the antecedent, so an antecedent
that has it is *false* off the sort, and a body whose antecedent has it is *true* off the sort. -/

variable {M : Type*} [LRV.Structure M]

/-- The guard atom «the `i`-th variable lies in the sort `s`» realises to the sort predicate. -/
theorem realize_guardAtom {α : Type} {n : ℕ} (s : SortTag) (i : Fin n) (v : α → M)
    (T : Fin n → M) :
    (guardAtom s i : LRV.BoundedFormula α n).Realize v T ↔ sortEval s (T i) := by
  cases s <;> simp [guardAtom, sortPredG, pVFG, pRVG, sortEval]

/-- **Junk-false**: a formula with the guard atom among its top-level conjuncts is false at a tuple
whose `i`-th component is outside the sort `s`.  No well-sortedness, no model axiom. -/
theorem inAntecedent_not_realize {α : Type} {n : ℕ} {s : SortTag} {i : Fin n}
    {η : LRV.BoundedFormula α n} (h : InAntecedent s i η) (v : α → M) (T : Fin n → M)
    (hi : ¬ sortEval s (T i)) : ¬ η.Realize v T := by
  induction h with
  | atom => exact fun hc => hi ((realize_guardAtom s i v T).mp hc)
  | and_left _ ih => exact fun hc => ih (BoundedFormula.realize_inf.mp hc).1
  | and_right _ ih => exact fun hc => ih (BoundedFormula.realize_inf.mp hc).2

/-- **Junk-true**: a `GuardTrue` body is true at a tuple whose `i`-th component is outside the sort
`s` — the lemma the guard repair exists to make provable.  Again no well-sortedness and no model
axiom: `BoundedFormula.all` ranges over the whole carrier, and this is exactly what makes that
harmless for a guarded body. -/
theorem guardTrue_realize {α : Type} (s : SortTag) :
    ∀ {n : ℕ} {i : Fin n} {χ : LRV.BoundedFormula α n}, GuardTrue s i χ →
      ∀ (v : α → M) (T : Fin n → M), ¬ sortEval s (T i) → χ.Realize v T := by
  intro n i χ h
  induction h with
  | imp hη =>
      intro v T hi
      rw [BoundedFormula.realize_imp]
      exact fun hc => absurd hc (inAntecedent_not_realize hη v T hi)
  | all hχ ih =>
      intro v T hi
      rw [BoundedFormula.realize_all]
      intro a
      exact ih v (Fin.snoc T a) (by simpa [Fin.snoc_castSucc] using hi)

/-- **Junk-truth in the tree's packaging** (`W1.JunkTrueAt`,
`.ultramath/smw19wtoj/m1/W1.lean:502`): a `GuardTrue` body is true at every carrier element
outside its sort, in every model of `Axioms.ACVF`, at every tuple.  The model hypothesis is unused
— this is a theorem about the encoding alone, which is what makes it available to the composition
before any valuation theory is in place. -/
def JunkTrueAt (s : SortTag) (n : ℕ) (χ : Bf (n + 1)) : Prop :=
  ∀ (M : Type) [LRV.Structure M], M ⊨ Axioms.ACVF → ∀ (T : Fin n → M) (a : M),
    ¬ sortEval s a → χ.Realize (default : Empty → M) (Fin.snoc T a)

theorem junkTrueAt_of_guardTrue {n : ℕ} {s : SortTag} {χ : Bf (n + 1)}
    (hj : GuardTrue s (Fin.last n) χ) : JunkTrueAt s n χ := by
  intro M _ _ T a ha
  exact guardTrue_realize s hj (default : Empty → M) (Fin.snoc T a)
    (by simpa [Fin.snoc_last] using ha)

/-! ## 2. The composition -/

/-- The valuation is nontrivial in the paper's sense (verbatim from `QE/TransferWS.lean`). -/
def IsNontrivialVF (M : Type) [LRV.Structure M] : Prop :=
  ∃ x : M, iVF x ∧ x ≠ iRVZero ∧ ¬ iLe (iRv iRVOne) (iRv x)

/-- **The back-and-forth step on well-sorted quantifier-free types.**  Two models of `T` in the
class `P` that agree on all well-sorted QF formulas at sorted tuples: for every element of the sort
`s` on the left there is an element of the same sort on the right such that the *extended* tuples
still agree on all well-sorted QF formulas.

This is the only ingredient of `TransferAtWS` that is not combinatorics: it is the statement that
a QF type of a sorted element is realised in the other model, i.e. the saturation content that the
tree takes from `Milestone0/Saturation.lean` in the monster-model setting.  It is *not* the
conclusion: it says nothing about formulas with quantifiers. -/
def QFStep (P : (M : Type) → [LRV.Structure M] → Prop) (T : LRV.Theory) : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (M : Type) [LRV.Structure M] [Nonempty M], M ⊨ T → P M →
  ∀ (N : Type) [LRV.Structure N] [Nonempty N], N ⊨ T → P N →
  ∀ (v : α → M) (xs : Fin n → M) (w : α → N) (ys : Fin n → N),
    (∀ a, sortEval (sα a) (v a)) → (∀ i, sortEval (sn i) (xs i)) →
    (∀ a, sortEval (sα a) (w a)) → (∀ i, sortEval (sn i) (ys i)) →
    (∀ ψ : LRV.BoundedFormula α n, WellSorted sα sn ψ → ψ.IsQF →
      (ψ.Realize v xs ↔ ψ.Realize w ys)) →
    ∀ (s : SortTag) (x : M), sortEval s x → ∃ y : N, sortEval s y ∧
      (∀ ψ : LRV.BoundedFormula α (n + 1), WellSorted sα (Fin.snoc sn s) ψ → ψ.IsQF →
        (ψ.Realize v (Fin.snoc xs x) ↔ ψ.Realize w (Fin.snoc ys y)))

/-- The transfer hypothesis at a class of models `P`, over the fragment (verbatim from
`QE/TransferWS.lean`). -/
def TransferAtWS (P : (M : Type) → [LRV.Structure M] → Prop) (T : LRV.Theory) : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (M : Type) [LRV.Structure M] [Nonempty M], M ⊨ T → P M →
  ∀ (N : Type) [LRV.Structure N] [Nonempty N], N ⊨ T → P N →
  ∀ (v : α → M) (xs : Fin n → M) (w : α → N) (ys : Fin n → N),
    (∀ a, sortEval (sα a) (v a)) → (∀ i, sortEval (sn i) (xs i)) →
    (∀ a, sortEval (sα a) (w a)) → (∀ i, sortEval (sn i) (ys i)) →
    (∀ ψ : LRV.BoundedFormula α n, WellSorted sα sn ψ → ψ.IsQF →
      (ψ.Realize v xs ↔ ψ.Realize w ys)) →
    ∀ φ : LRV.BoundedFormula α n, WellSorted sα sn φ →
      (φ.Realize v xs ↔ φ.Realize w ys)

/-- **The nontrivial half of the transfer, over the fragment** (verbatim from
`QE/TransferWS.lean`). -/
def NontrivialTransferWS (T : LRV.Theory) : Prop := TransferAtWS IsNontrivialVF T

/-- Appending a sorted element to sorted tuples keeps them sorted. -/
theorem sorted_snoc {M : Type} [LRV.Structure M] {n : ℕ} {sn : Fin n → SortTag}
    {xs : Fin n → M} {s : SortTag} {x : M}
    (hxs : ∀ i, sortEval (sn i) (xs i)) (hx : sortEval s x) :
    ∀ i, sortEval ((Fin.snoc sn s : Fin (n + 1) → SortTag) i)
      ((Fin.snoc xs x : Fin (n + 1) → M) i) := by
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simpa [Fin.snoc_last] using hx
  · intro j
    simpa [Fin.snoc_castSucc] using hxs j

section Composition

variable {α : Type} {sα : α → SortTag} {P : (M : Type) → [LRV.Structure M] → Prop}
variable {T : LRV.Theory} {M : Type} [LRV.Structure M] [Nonempty M]
variable {N : Type} [LRV.Structure N] [Nonempty N]
variable {v : α → M} {w : α → N}


/-- The induction: agreement on well-sorted quantifier-free formulas at sorted tuples propagates to
every well-sorted formula. -/
theorem agreement_aux (hstep : QFStep P T) (hM : M ⊨ T) (hPM : P M) (hN : N ⊨ T) (hPN : P N)
    (hv : ∀ a, sortEval (sα a) (v a)) (hw : ∀ a, sortEval (sα a) (w a)) :
    ∀ {n : ℕ} (φ : LRV.BoundedFormula α n) (sn : Fin n → SortTag)
      (xs : Fin n → M) (ys : Fin n → N),
      WellSorted sα sn φ → (∀ i, sortEval (sn i) (xs i)) → (∀ i, sortEval (sn i) (ys i)) →
      (∀ ψ : LRV.BoundedFormula α n, WellSorted sα sn ψ → ψ.IsQF →
        (ψ.Realize v xs ↔ ψ.Realize w ys)) →
      (φ.Realize v xs ↔ φ.Realize w ys) := by
  intro n φ
  refine BoundedFormula.rec (motive := fun (m : ℕ) (φ : LRV.BoundedFormula α m) =>
      ∀ (sn : Fin m → SortTag) (xs : Fin m → M) (ys : Fin m → N),
        WellSorted sα sn φ → (∀ i, sortEval (sn i) (xs i)) → (∀ i, sortEval (sn i) (ys i)) →
        (∀ ψ : LRV.BoundedFormula α m, WellSorted sα sn ψ → ψ.IsQF →
          (ψ.Realize v xs ↔ ψ.Realize w ys)) →
        (φ.Realize v xs ↔ φ.Realize w ys)) ?_ ?_ ?_ ?_ ?_ φ
  · intro _ sn xs ys hW _ _ hQF
    exact hQF BoundedFormula.falsum hW BoundedFormula.IsQF.falsum
  · intro _ t₁ t₂ sn xs ys hW _ _ hQF
    exact hQF (.equal t₁ t₂) hW (BoundedFormula.IsAtomic.equal t₁ t₂).isQF
  · intro _ l R ts sn xs ys hW _ _ hQF
    exact hQF (.rel R ts) hW (BoundedFormula.IsAtomic.rel R ts).isQF
  · intro _ a b iha ihb sn xs ys hW hxs hys hQF
    cases hW with
    | imp _ hWa hWb =>
      have ha := iha sn xs ys hWa hxs hys hQF
      have hb := ihb sn xs ys hWb hxs hys hQF
      rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp]
      exact ⟨fun h hbw => hb.mp (h (ha.mpr hbw)), fun h haw => hb.mpr (h (ha.mp haw))⟩
  · intro k χ ih sn xs ys hW hxs hys hQF
    cases hW with
    | @all _ _ s _ hχ _hg hj =>
      -- the QF step, in the direction that produces an element of `N`
      have step : ∀ (x : M), sortEval s x → ∃ y : N, sortEval s y ∧
          (∀ ψ : LRV.BoundedFormula α (k + 1), WellSorted sα (Fin.snoc sn s) ψ → ψ.IsQF →
            (ψ.Realize v (Fin.snoc xs x) ↔ ψ.Realize w (Fin.snoc ys y))) :=
        fun x hx => @hstep α sα k sn M _ _ hM hPM N _ _ hN hPN v xs w ys hv hxs hw hys hQF s x hx
      -- and in the direction that produces an element of `M`
      have step' : ∀ (y : N), sortEval s y → ∃ x : M, sortEval s x ∧
          (∀ ψ : LRV.BoundedFormula α (k + 1), WellSorted sα (Fin.snoc sn s) ψ → ψ.IsQF →
            (ψ.Realize v (Fin.snoc xs x) ↔ ψ.Realize w (Fin.snoc ys y))) :=
        fun y hy => by
          obtain ⟨x, hx, hq⟩ := @hstep α sα k sn N _ _ hN hPN M _ _ hM hPM w ys v xs hw hys hv hxs
            (fun ψ hψ hq' => (hQF ψ hψ hq').symm) s y hy
          exact ⟨x, hx, fun ψ hψ hq' => (hq ψ hψ hq').symm⟩
      rw [BoundedFormula.realize_all, BoundedFormula.realize_all]
      constructor
      · intro h b
        by_cases hb : sortEval s b
        · obtain ⟨a, ha, hagree⟩ := step' b hb
          exact (ih (Fin.snoc sn s) (Fin.snoc xs a) (Fin.snoc ys b) hχ
            (sorted_snoc hxs ha) (sorted_snoc hys hb) hagree).mp (h a)
        · exact guardTrue_realize s hj w (Fin.snoc ys b) (by simpa [Fin.snoc_last] using hb)
      · intro h a
        by_cases ha : sortEval s a
        · obtain ⟨b, hb, hagree⟩ := step a ha
          exact (ih (Fin.snoc sn s) (Fin.snoc xs a) (Fin.snoc ys b) hχ
            (sorted_snoc hxs ha) (sorted_snoc hys hb) hagree).mpr (h b)
        · exact guardTrue_realize s hj v (Fin.snoc xs a) (by simpa [Fin.snoc_last] using ha)

end Composition

/-- **The composition**: the QF-type step and junk-truth together give the fragment transfer at every
sort-respecting tuple. -/
theorem transferAtWS_of_qfStep {P : (M : Type) → [LRV.Structure M] → Prop} {T : LRV.Theory}
    (hstep : QFStep P T) : TransferAtWS P T := by
  intro α sα n sn M _ _ hM hPM N _ _ hN hPN v xs w ys hv hxs hw hys hQF φ hφ
  exact agreement_aux hstep hM hPM hN hPN hv hw φ sn xs ys hφ hxs hys hQF

/-- **The transfer at every model of the theory**, when the hypothesis class is the whole theory.
`QE/Assembly_val.lean` proves exactly this hypothesis for `Axioms.ACVF`
(`TrivialHalf.allNontrivial_ACVF : ∀ M, M ⊨ ACVF → IsNontrivialVF M`), so the nontrivial transfer
is the transfer.  This is the form a fragment quantifier-elimination proof consumes: the frozen
`HasQE` has no hypothesis class. -/
theorem transferAtWS_true_of_allP {P : (M : Type) → [LRV.Structure M] → Prop} {T : LRV.Theory}
    (hAll : ∀ (M : Type) [LRV.Structure M], M ⊨ T → P M) (h : TransferAtWS P T) :
    TransferAtWS (fun _ _ => True) T := by
  intro α sα n sn M _ _ hM _ N _ _ hN _ v xs w ys hv hxs hw hys hQF φ hφ
  exact h α sα n sn M hM (hAll M hM) N hN (hAll N hN) v xs w ys hv hxs hw hys hQF φ hφ

/-- **The transitive conclusion for `ACVF`**: since every model of `Axioms.ACVF` is nontrivially
valued, the QF-type step gives the fragment transfer at *all* models of `ACVF`. -/
theorem transferAtWS_all_ACVF_of_qfStep
    (hAll : ∀ (M : Type) [LRV.Structure M], M ⊨ Axioms.ACVF → IsNontrivialVF M)
    (hstep : QFStep IsNontrivialVF Axioms.ACVF) : TransferAtWS (fun _ _ => True) Axioms.ACVF :=
  transferAtWS_true_of_allP hAll (transferAtWS_of_qfStep hstep)

/-- **The nontrivial half of Theorem 2.3 over the fragment, from the QF-type step.**  With
`QFStep IsNontrivialVF Axioms.ACVF` — the back-and-forth step for well-sorted quantifier-free types
in nontrivial `ACVF` models — the frozen target `NontrivialTransferWS Axioms.ACVF` follows. -/
theorem nontrivialTransferWS_ACVF_of_qfStep
    (hstep : QFStep IsNontrivialVF Axioms.ACVF) : NontrivialTransferWS Axioms.ACVF :=
  transferAtWS_of_qfStep hstep

#print axioms TransferComp.nontrivialTransferWS_ACVF_of_qfStep
#print axioms TransferComp.transferAtWS_of_qfStep
#print axioms TransferComp.transferAtWS_all_ACVF_of_qfStep
#print axioms TransferComp.transferAtWS_true_of_allP
#print axioms TransferComp.guardTrue_realize
#print axioms TransferComp.inAntecedent_not_realize
#print axioms TransferComp.junkTrueAt_of_guardTrue

end TransferComp

end Milestone0
end SpecialTransformations
