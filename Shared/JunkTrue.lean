module

/-
**Junk-truth of the repaired guard** — merged from swarm `smw1bwjo2` m5 (direction d2), accepted
after compiling and reading it here.  `import Enc` only; 0 errors, no `sorry`, axioms within
{propext, Classical.choice, Quot.sound}.

What it supplies, and why it is the payload of the guard repair (`DECISION.md` §"The guard repair"):

* `Junk.guardAtom_realize` — the guard atom realises to `sortEval`; this is the only place where the
  semantics of the encoding's sort predicates enters;
* `Junk.junkFalse` / `Junk.junkTrue` — the dual inductions: a top-level conjunct of an antecedent is
  *false* off the sort, and a `GuardTrue` body is *true* off the sort.  Neither needs `WellSorted`
  and neither needs a model axiom;
* `Junk.all_realize_iff_sorted` — at a junk-true body the encoding's unguarded `∀` (over the whole
  one-sorted carrier) *is* the paper's guarded `∀ x ∈ s`: the `.all` step of any fragment transfer;
* `Junk.JunkTrueAt` and `junkTrueAt_of_guardTrue` / `junkTrueAt_guard` / `junkTrueAt_sortedHyps` —
  the named consequence in the shape a transfer consumes, non-vacuous on the paper's own body shape
  `sortedHyps ⟹ ψ`, which is what the author's ruling required the repaired predicate to admit;
* `Junk.not_wellSorted_all_witnessG` and its three companions — machine-checked sharpness: the
  junk-sensitivity witness of `QE/HANDOFF.md` satisfies `GuardsLast`, has a well-sorted body, and is
  rejected by the repaired `WellSorted` *because of* the `GuardTrue` field.

Check with `.scratch2/sec3/` (a compiled `Enc`): copy this file there and
`LEAN_PATH=$PWD:$LEAN_PATH lean` it.
-/
/-
  Direction d2 of swarm `smw1bwjo2`: **the junk-truth semantics of the guard repair.**

  `Milestone0/Encoding.lean` (sha256 `86d7ea7e…`) encodes the two sorts of `L_RV` on one carrier,
  so `BoundedFormula.all` ranges over the *whole* carrier, not just the tag `s` of a guarded
  quantifier.  The author's repair adds to the `WellSorted.all` constructor the field

      (hj : GuardTrue s (Fin.last n) χ)

  (`GuardTrue` = "the sort predicate of the bound variable is a top-level conjunct of the body's
  antecedent, or the body is a universal that inherits that property").  This file proves that the
  syntactic condition does its job.

  ## What is proved (all in `namespace SpecialTransformations.Milestone0.Junk`)

  * `guardAtom_realize` — the guard atom `xᵢ ∈ s` realizes to `sortEval s (x i)`.  This is the only
    place where the semantics of the encoding's sort predicates enters.
  * `junkFalse` — a formula with the guard atom among its top-level conjuncts is **false** at a
    tuple whose `i`-th entry is outside the sort `s`.
  * `junkTrue` — a `GuardTrue` formula is **true** at such a tuple.
    Both are proved in *stronger* form than the direction statement asks: neither needs
    `WellSorted` and neither needs the tuple to respect the sort signature `sn`; `WellSorted` is
    what makes the guard atom *available* at a quantifier (`WellSorted.all`'s `hj` field), not what
    makes the induction go through.  `inAntecedent_junkFalse`/`guardTrue_junkTrue` are the
    `WellSorted`-carrying restatements in the exact `Fin.snoc`/`Fin.last` shape the direction asks
    for (the `WellSorted` hypotheses are carried, and unused).
  * `all_realize_iff_sorted` — the semantic form of the repair: at a junk-true body the encoding's
    unguarded `∀` is the paper's guarded `∀ x ∈ s`.  This is the `.all` step of any induction on
    `WellSorted` derivations.
  * `snoc_sorted` — the transport of sorted tuples under `Fin.snoc`, the companion input of the same
    step.
  * `JunkTrueAt s n χ` — the named consequence (`DECISION.md`, constraint 1; `W1.lean` uses the
    name): every `WellSorted` + `GuardTrue` body is junk-true in every model of `ACVF`, in the shape
    a fragment transfer needs.  `junkTrueAt_of_guardTrue` derives it from the `hj` field alone;
    `junkTrueAt_of_wellSorted` states it for a `WellSorted` body; `forall_realize_iff_sorted` is
    the `∀`-form, model-theoretically.  Non-vacuous instances: `junkTrueAt_guard` and
    `junkTrueAt_sortedHyps` (the paper's own body shape `sortedHyps ⟹ ψ`, with no condition on `ψ`).
    `guardTrue_junkTrue` is the general-`α` form, for a transfer whose induction is over an
    arbitrary parameter type rather than `Empty`.
  * Sharpness (`witnessG*`): the witness of `QE/HANDOFF.md`'s junk-sensitivity experiment,
    `((x ∈ VF) ⟹ ⊥) ⟹ (x = 0_VF)`, is shown to satisfy `GuardsLast` and to *fail* `GuardTrue`
    (for every sort tag), while being `WellSorted` as a body.  Hence
    `¬ WellSorted sα sn (.all witnessG)`: under the pre-repair predicate, which required only
    `GuardsLast`, the witness was admitted; the new `GuardTrue` field is exactly what rejects it.

  Neither `d1`'s sort soundness nor any model-theoretic hypothesis is used: junk-truth is
  syntactic-semantic and holds in every `L_RV`-structure.  `M ⊨ Axioms.ACVF` is carried in
  `JunkTrueAt` only so that the statement is usable verbatim where only models of `ACVF` occur.

  Self-contained: `import Enc` only.  Check with

      LEAN_PATH=<repo>/.scratch2/sec3:$LEAN_PATH lean JunkTrue.lean

  (`.scratch2/sec3/Enc.olean` is a build of `Milestone0/Encoding.lean` at sha `86d7ea7e…`).
-/
public import Enc

@[expose] public section

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace SpecialTransformations
namespace Milestone0

open LRV

namespace Junk

/-! ## 1. Realizing the guard atom -/

section Guard

variable {M : Type*} [LRV.Structure M]

/-- `Realize` of a relation atom, at the encoding's relation type.  Stated with `L := LRV` written
out because `Rel` is `LRV.Relations` only definitionally, and the rewrite tactics do not unify at
that transparency. -/
theorem realize_relG {α : Type} {m l : ℕ} (R : Rel l)
    (ts : Fin l → LRV.Term (α ⊕ Fin m)) (v : α → M) (x : Fin m → M) :
    (BoundedFormula.rel (L := LRV) R ts).Realize v x ↔
      Structure.RelMap (L := LRV) R (fun i => (ts i).realize (Sum.elim v x)) :=
  Iff.rfl

theorem relMap_congr {l : ℕ} {R : Rel l} {f g : Fin l → M} (h : f = g) :
    Structure.RelMap (L := LRV) R f ↔ Structure.RelMap (L := LRV) R g := by
  rw [h]

/-- `xᵢ ∈ VF` realizes to `iVF (x i)`. -/
theorem pVFG_realize_var {α : Type} {m : ℕ} (i : Fin m) (v : α → M) (x : Fin m → M) :
    (LRV.pVFG (Term.var (Sum.inr i)) : LRV.BoundedFormula α m).Realize v x ↔ iVF (x i) := by
  simp only [LRV.pVFG, FirstOrder.Language.Relations.boundedFormula₁,
    FirstOrder.Language.Relations.boundedFormula, realize_relG, iVF]
  refine relMap_congr ?_
  funext j
  fin_cases j
  rfl

/-- `xᵢ ∈ RV` realizes to `iRV (x i)`. -/
theorem pRVG_realize_var {α : Type} {m : ℕ} (i : Fin m) (v : α → M) (x : Fin m → M) :
    (LRV.pRVG (Term.var (Sum.inr i)) : LRV.BoundedFormula α m).Realize v x ↔ iRV (x i) := by
  simp only [LRV.pRVG, FirstOrder.Language.Relations.boundedFormula₁,
    FirstOrder.Language.Relations.boundedFormula, realize_relG, iRV]
  refine relMap_congr ?_
  funext j
  fin_cases j
  rfl

/-- **The guard atom realizes to `sortEval` at the corresponding entry of the tuple.** -/
theorem guardAtom_realize {α : Type} {m : ℕ} (s : SortTag) (i : Fin m)
    (v : α → M) (x : Fin m → M) :
    (LRV.guardAtom s i : LRV.BoundedFormula α m).Realize v x ↔ sortEval s (x i) := by
  cases s with
  | vf => exact pVFG_realize_var i v x
  | rv => exact pRVG_realize_var i v x

/-! ## 2. The two dual inductions

`a ⊓ b` is `¬(a → ¬b)` in the encoding, so `BoundedFormula.realize_inf` is the only semantic input
beyond the guard atom itself.  Neither direction needs `WellSorted`: `InAntecedent` and `GuardTrue`
are purely syntactic families, and both inductions only ask that the `i`-th entry of the tuple be
outside the sort. -/

/-- **Junk-false**: if the guard atom `xᵢ ∈ s` is a top-level conjunct of `η`, then `η` fails at any
tuple whose `i`-th entry is outside `s`. -/
theorem junkFalse {α : Type} {m : ℕ} {s : SortTag} {i : Fin m} {η : LRV.BoundedFormula α m}
    (h : InAntecedent s i η) (v : α → M) (x : Fin m → M) (hx : ¬ sortEval s (x i)) :
    ¬ η.Realize v x := by
  revert v x hx
  induction h with
  | atom =>
      intro v x hx hr
      exact hx ((guardAtom_realize s i v x).mp hr)
  | and_left h ih =>
      intro v x hx hr
      exact ih v x hx (BoundedFormula.realize_inf.mp hr).1
  | and_right h ih =>
      intro v x hx hr
      exact ih v x hx (BoundedFormula.realize_inf.mp hr).2

/-- **Junk-true**: a `GuardTrue` formula holds at any tuple whose `i`-th entry is outside `s`. -/
theorem junkTrue {α : Type} {m : ℕ} {s : SortTag} {i : Fin m} {χ : LRV.BoundedFormula α m}
    (h : GuardTrue s i χ) (v : α → M) (x : Fin m → M) (hx : ¬ sortEval s (x i)) :
    χ.Realize v x := by
  revert v x hx
  induction h with
  | imp hη =>
      intro v x hx hr
      exact absurd hr (junkFalse hη v x hx)
  | all hχ ih =>
      intro v x hx
      rw [BoundedFormula.realize_all]
      intro y
      refine ih v (Fin.snoc x y) ?_
      rwa [Fin.snoc_castSucc]

/-! ## 3. The guarded quantifier, and the tuple transport that comes with it -/

/-- **The semantic form of `GuardTrue`.**  For a junk-true body, the encoding's unguarded universal
is the paper's guarded one.  (The reverse implication needs no hypothesis on `χ`.) -/
theorem all_realize_iff_sorted {α : Type} {n : ℕ} {s : SortTag}
    {χ : LRV.BoundedFormula α (n + 1)} (hj : GuardTrue s (Fin.last n) χ)
    (v : α → M) (x : Fin n → M) :
    (BoundedFormula.all χ).Realize v x ↔ ∀ a : M, sortEval s a → χ.Realize v (Fin.snoc x a) := by
  rw [BoundedFormula.realize_all]
  refine ⟨fun h a _ => h a, fun h a => ?_⟩
  by_cases ha : sortEval s a
  · exact h a ha
  · exact junkTrue hj v (Fin.snoc x a) (by rwa [Fin.snoc_last])

/-- **Sorted tuples are closed under `Fin.snoc`**: the companion of `WellSorted.all`. -/
theorem snoc_sorted {n : ℕ} {sn : Fin n → SortTag} {s : SortTag} {T : Fin n → M} {a : M}
    (hT : ∀ i, sortEval (sn i) (T i)) (ha : sortEval s a) :
    ∀ i, sortEval ((Fin.snoc sn s : Fin (n + 1) → SortTag) i)
      ((Fin.snoc T a : Fin (n + 1) → M) i) := by
  intro i
  by_cases h : i.val < n
  · rw [← Fin.castSucc_castLT i h, Fin.snoc_castSucc, Fin.snoc_castSucc]
    exact hT _
  · rw [Fin.eq_last_of_not_lt h, Fin.snoc_last, Fin.snoc_last]
    exact ha

/-- `junkFalse` in the `Fin.snoc`/`Fin.last` shape of the direction statement, with the
`WellSorted` hypothesis carried (unused) and the tuple respecting `sn`. -/
theorem inAntecedent_junkFalse {α : Type} {n : ℕ} {sα : α → SortTag} {sn : Fin n → SortTag}
    {s : SortTag} {η : LRV.BoundedFormula α (n + 1)}
    (_hws : WellSorted sα (Fin.snoc sn s) η) (h : InAntecedent s (Fin.last n) η)
    (v : α → M) (T : Fin n → M) (_hT : ∀ i, sortEval (sn i) (T i)) (a : M)
    (ha : ¬ sortEval s a) : ¬ η.Realize v (Fin.snoc T a) :=
  junkFalse h v (Fin.snoc T a) (by rwa [Fin.snoc_last])

/-- `junkTrue` in the `Fin.snoc`/`Fin.last` shape of the direction statement. -/
theorem guardTrue_junkTrue {α : Type} {n : ℕ} {sα : α → SortTag} {sn : Fin n → SortTag}
    {s : SortTag} {χ : LRV.BoundedFormula α (n + 1)}
    (_hws : WellSorted sα (Fin.snoc sn s) χ) (h : GuardTrue s (Fin.last n) χ)
    (v : α → M) (T : Fin n → M) (_hT : ∀ i, sortEval (sn i) (T i)) (a : M)
    (ha : ¬ sortEval s a) : χ.Realize v (Fin.snoc T a) :=
  junkTrue h v (Fin.snoc T a) (by rwa [Fin.snoc_last])

end Guard

/-! ## 4. The named consequence `JunkTrueAt`

Model-theoretic form, with `ACVF` and the empty parameter type: this is the hypothesis on quantifier
bodies that an induction on `WellSorted` derivations needs.  It follows from the `hj` field alone, so
every guarded quantifier of the fragment supplies it. -/

/-- **The junk-truth property of a quantifier body.**  `χ` holds at every tuple whose last entry is
outside the sort `s`, in every model of `ACVF`. -/
def JunkTrueAt (s : SortTag) (n : ℕ) (χ : Bf (n + 1)) : Prop :=
  ∀ (M : Type) [LRV.Structure M], M ⊨ Axioms.ACVF → ∀ (T : Fin n → M) (a : M),
    ¬ sortEval s a → χ.Realize (default : Empty → M) (Fin.snoc T a)

/-- **`JunkTrueAt` from the syntactic condition alone** — this is the field `hj` of
`WellSorted.all`. -/
theorem junkTrueAt_of_guardTrue {n : ℕ} {s : SortTag} {χ : Bf (n + 1)}
    (hj : GuardTrue s (Fin.last n) χ) : JunkTrueAt s n χ := by
  intro M inst hM T a ha
  exact @junkTrue (M := M) inst Empty _ s (Fin.last n) χ hj default (Fin.snoc T a)
    (by rwa [Fin.snoc_last])

/-- **`JunkTrueAt` for a body that is `WellSorted` and `GuardTrue`** — the exact data a
`WellSorted.all` node carries.  The `WellSorted` hypothesis is not needed by the proof; it is
carried so that this is the statement a fragment transfer consumes. -/
theorem junkTrueAt_of_wellSorted {n : ℕ} {s : SortTag} (sn : Fin n → SortTag)
    {χ : Bf (n + 1)} (_hws : WellSorted (fun a => nomatch a) (Fin.snoc sn s) χ)
    (hj : GuardTrue s (Fin.last n) χ) : JunkTrueAt s n χ :=
  junkTrueAt_of_guardTrue hj

/-- **Non-vacuity**: the simplest junk-true body, `(x ∈ s) ⟹ ψ`, for an arbitrary consequent. -/
theorem junkTrueAt_guard {n : ℕ} {s : SortTag} {ψ : Bf (n + 1)} :
    JunkTrueAt s n (guardAtom s (Fin.last n) ⟹ ψ) :=
  junkTrueAt_of_guardTrue (GuardTrue.of_inAntecedent InAntecedent.atom)

/-- **The paper's own guard shape**: `(⋀ i, xᵢ ∈ ssᵢ) ⟹ ψ` is junk-true, with no condition
whatsoever on the consequent `ψ`.  This is the body shape of every guarded quantifier of `ACVF`'s
axioms (`allSorted`/`exSorted`/`allSortedK`/`exSortedK`), so every such quantifier supplies
`JunkTrueAt` for its body. -/
theorem junkTrueAt_sortedHyps {n : ℕ} {s : SortTag} (sn : Fin n → SortTag) {ψ : Bf (n + 1)} :
    JunkTrueAt s n (sortedHyps (Fin.snoc sn s) ⟹ ψ) := by
  have h := occurs_sortedHyps (Fin.snoc sn s) (Fin.last n)
  rw [Fin.snoc_last] at h
  exact junkTrueAt_of_guardTrue (GuardTrue.of_inAntecedent h)

/-- The `∀`-form of `JunkTrueAt`, model-theoretically: at a junk-true body the encoding's unguarded
quantifier is the paper's guarded one. -/
theorem forall_realize_iff_sorted {n : ℕ} {s : SortTag} {χ : Bf (n + 1)}
    (hj : GuardTrue s (Fin.last n) χ) :
    ∀ (M : Type) [LRV.Structure M], ∀ (T : Fin n → M),
      (BoundedFormula.all χ).Realize (default : Empty → M) T ↔
        ∀ a : M, sortEval s a → χ.Realize (default : Empty → M) (Fin.snoc T a) := by
  intro M inst T
  exact @all_realize_iff_sorted (M := M) inst Empty n s χ hj default T

/-! ## 5. Sharpness: `GuardsLast` does not imply `GuardTrue`

The witness of the junk-sensitivity experiment recorded in `QE/HANDOFF.md`:
`∀x (((x ∈ VF) ⟹ ⊥) ⟹ (x = 0_VF))`.  Its body satisfies `GuardsLast` — the guard atom `x ∈ VF`
sits behind a further implication, which is what the *pre-repair* predicate accepted — but it does
not satisfy `GuardTrue`, and the repaired `WellSorted` therefore rejects the quantifier. -/

/-- The junk-sensitive witness of `QE/HANDOFF.md`, at a general parameter type:
`((x ∈ VF) ⟹ ⊥) ⟹ (x = 0_VF)`. -/
def witnessG {α : Type} : LRV.BoundedFormula α 1 :=
  (pVFG (Term.var (Sum.inr (Fin.last 0))) ⟹ ⊥) ⟹
    pEqG (Term.var (Sum.inr (Fin.last 0))) (Term.func Fn.vfZero (fun i => i.elim0))

/-- The witness at the empty parameter type. -/
def junkWitness : Bf 1 := witnessG (α := Empty)

/-- The witness's body is `GuardsLast`-guarded (this is what the pre-repair predicate asked). -/
theorem witnessG_guardsLast {α : Type} : GuardsLast SortTag.vf (Fin.last 0) (witnessG (α := α)) := by
  show Occurs (Fin.last 0) SortTag.vf
      (pVFG (Term.var (Sum.inr (Fin.last 0))) ⟹ ⊥) ∨
    GuardsLast SortTag.vf (Fin.last 0) (pVFG (Term.var (Sum.inr (Fin.last 0))) ⟹ ⊥) ∨
    GuardsLast SortTag.vf (Fin.last 0)
      (pEqG (Term.var (Sum.inr (Fin.last 0))) (Term.func Fn.vfZero (fun i => i.elim0)))
  exact Or.inr (Or.inl (Or.inl InAntecedent.atom))

/-- The witness's body is **not** junk-true, for any sort tag: the guard atom is not a top-level
conjunct of the antecedent `(x ∈ VF) ⟹ ⊥`. -/
theorem witnessG_not_guardTrue {α : Type} (s : SortTag) :
    ¬ GuardTrue s (Fin.last 0) (witnessG (α := α)) := by
  intro h
  cases h with
  | imp hη =>
    rcases InAntecedent.shape hη with h1 | ⟨a, b, h1⟩
    · cases s <;>
        (simp only [guardAtom, sortPredG, pVFG, pRVG,
          FirstOrder.Language.Relations.boundedFormula₁,
          FirstOrder.Language.Relations.boundedFormula] at h1
         cases h1)
    · simp only [pVFG, FirstOrder.Language.Relations.boundedFormula₁,
        FirstOrder.Language.Relations.boundedFormula] at h1
      simp only [Min.min, BoundedFormula.not] at h1
      cases h1

/-- The witness's body is well-sorted as a body (at the extended context `Fin.snoc sn .vf`). -/
theorem witnessG_wellSorted {α : Type} (sα : α → SortTag) (sn : Fin 0 → SortTag) :
    WellSorted sα (Fin.snoc sn SortTag.vf) (witnessG (α := α)) := by
  refine WellSorted.imp _ (WellSorted.imp _ ?_ (WellSorted.falsum _)) ?_
  · exact wellSorted_pVFG sα _ (t := Term.var (Sum.inr (Fin.last 0)))
      (by rw [tmSort_var_inr, Fin.snoc_last])
  · exact wellSorted_pEqG sα _ (t := Term.var (Sum.inr (Fin.last 0)))
      (u := Term.func Fn.vfZero (fun i => i.elim0))
      (by rw [tmSort_var_inr, Fin.snoc_last]) (tmSort_vfZero sα _)

/-- **The repair is exactly what rejects the witness**: the quantified witness is not a well-sorted
formula of the repaired fragment, and the `GuardTrue` field of `WellSorted.all` is the obstruction. -/
theorem not_wellSorted_all_witnessG {α : Type} (sα : α → SortTag) (sn : Fin 0 → SortTag) :
    ¬ WellSorted sα sn (.all (witnessG (α := α))) := by
  intro h
  cases h with
  | all sn' hχ hg hj => exact witnessG_not_guardTrue _ hj

end Junk

#print axioms SpecialTransformations.Milestone0.Junk.guardAtom_realize
#print axioms SpecialTransformations.Milestone0.Junk.junkFalse
#print axioms SpecialTransformations.Milestone0.Junk.junkTrue
#print axioms SpecialTransformations.Milestone0.Junk.all_realize_iff_sorted
#print axioms SpecialTransformations.Milestone0.Junk.snoc_sorted
#print axioms SpecialTransformations.Milestone0.Junk.inAntecedent_junkFalse
#print axioms SpecialTransformations.Milestone0.Junk.guardTrue_junkTrue
#print axioms SpecialTransformations.Milestone0.Junk.junkTrueAt_of_guardTrue
#print axioms SpecialTransformations.Milestone0.Junk.junkTrueAt_of_wellSorted
#print axioms SpecialTransformations.Milestone0.Junk.junkTrueAt_guard
#print axioms SpecialTransformations.Milestone0.Junk.junkTrueAt_sortedHyps
#print axioms SpecialTransformations.Milestone0.Junk.forall_realize_iff_sorted
#print axioms SpecialTransformations.Milestone0.Junk.witnessG_guardsLast
#print axioms SpecialTransformations.Milestone0.Junk.witnessG_not_guardTrue
#print axioms SpecialTransformations.Milestone0.Junk.witnessG_wellSorted
#print axioms SpecialTransformations.Milestone0.Junk.not_wellSorted_all_witnessG

end Milestone0
end SpecialTransformations
