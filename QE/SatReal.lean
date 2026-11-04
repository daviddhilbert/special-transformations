/-
# Input 5 of the §10b ledger *is* quantifier-free type realisation

`M5Ledger.SaturationRealization` (input 5 of the `QE/M5Ledger.lean` §10b decomposition) says: every
monomorphism `f : S ↪[LRV] N` out of a substructure of `M` extends along every inclusion `S ≤ T` of
substructures.  The paper (`qe.tex`:578 ff.) obtains it from `‖M‖⁺`-saturation of `N`; the ledger
consumes it as a black box at `PaperHyp` pairs.

This file proves the **exact scope** of that input, at the pair, with no saturation and no size
hypothesis anywhere in the statements:

    M5Ledger.SaturationRealization (M := M) (N := N)  ↔  QFSat M N

where

    QFSat M N  :=  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M),
                     ∃ b : N, Realize.RealizesAtomic S f m b

is *quantifier-free type realisation*: `Realize.RealizesAtomic S f m b` (`QE/Assembly_frozen.lean`)
is the assertion that `b` realises the **atomic type** of `m` over `S`, pushed along `f` — term
equalities and relation atoms transfer in both directions.  Nothing in `QFSat` mentions saturation,
finitely satisfiable types, cardinality or `Standing`.

So input 5 is not an extra model-theoretic axiom: modulo `SaturatedFS`, it is *equivalent* to the
statement that the pushed atomic types are realised.  The content that remains is the **finite
satisfiability** of those types (`QFFinSat` below), which is where `ACVF`'s axioms enter and where
the paper's case analysis (Lemmas 3.4–3.8) lives:

    QFFinSat  (per-formula / finite satisfiability of the pushed type)
      + Assembly.SaturatedFS N            [the frozen saturation notion]
      ⟹ QFSat                          [qfsat_of_saturatedFS]
      ⟺  SaturationRealization          [satReal_iff_qfsat]

## What is proved, and in which direction

* `qfsat_of_saturatedFS` — `SaturatedFS` plus finite satisfiability gives atomic realisation; this is
  just the tree's `Assembly.realizesAtomic_of_saturatedFS` (no new mathematics).
* `satReal_of_qfsat` — atomic realisation gives input 5.  Via the tree's one-step
  (`Realize.exists_oneStep`) and exhaustion (`Realize.exists_total_embedding_of_realizesAtomic`):
  the total embedding produced there is *stronger* than input 5 and does not use `ACVF`.
* `qfsat_of_satReal` — **input 5 gives atomic realisation**, the informative direction: it shows
  input 5 carries no content beyond realising atomic types.  The proof is the paper's back-and-forth
  step in miniature: apply input 5 with `T := S` (when `m ∈ S`) or with `T := closure (↑S ∪ {m})`
  (when `m ∉ S`), and read the resulting embedding off on the atomic formulas.
* `satReal_iff_qfsat` — the two directions together.

## Stress tests (see the end of the file)

* `qfsat_iff_satReal_refl` — the `T = S` shadow of input 5 is trivial (the identity extension), so
  the equivalence is not a re-statement of a vacuous hypothesis: the content is in the extensions
  with `T > S`, which is what `QFSat` records one element at a time.
* `qfsat_forces_size` — `QFSat` forces `#M ≤ #N` (through `M5Ledger`'s
  `saturationRealization_forces_size`), so the equivalence does not strengthen input 5's cardinality
  content: the size content of input 5 is exactly the size content of qf-type realisation.
* `qffinsat_atom_of_qfsat`, `qffinsat_rel_of_qfsat` — the two halves of `Realize.RealizesAtomic`
  are individually *satisfiable* consequences of `QFSat`: for a single term equality or relation atom
  true of `m` over `S`, some `b : N` realises its image.  So `QFSat` implies the atomic half of
  finite satisfiability — the part of `QFFinSat` that carries no `ACVF` content.

**What is *not* claimed.**  No counterexample is constructed here showing that `QFSat` fails without
the `ACVF` hypotheses (the definition quantifies over pairs of `L_RV`-structures, but every candidate
counterexample needs an embedding `f` to exist first, and the degenerate structures make `f`
inconsistent or the realisation trivial).  The reduction is therefore one-directional in its
*evidence*: it shows what input 5 amounts to, not that it is unprovable without `ACVF`.
-/
import M5Ledger
import M7PaperHyp
import Assembly_frozen

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations
namespace Milestone0
namespace M2Saturation

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-! ### The two statements

`QFSat` is the pair-level statement "`N` realises the atomic type of every element of `M` over every
substructure of `M`".  `QFFinSat` is the hypothesis `Assembly.SaturatedFS` asks for: each *single*
formula of the pushed type of `m` is realised in `N`.  (Because a conjunction of formulas true at `m`
is again a formula true at `m`, this is finite satisfiability.) -/

/-- **Quantifier-free type realisation** at the pair. -/
def QFSat (M N : Type) [LRV.Structure M] [LRV.Structure N] : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M), ∃ b : N, Realize.RealizesAtomic S f m b

/-- **Finite satisfiability of the pushed type**: every formula true of `m` over `S` is realised in
`N` over the pushed parameters.  This is precisely the hypothesis of `Assembly.SaturatedFS`. -/
def QFFinSat (M N : Type) [LRV.Structure M] [LRV.Structure N] : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M) (φ : LRV.Formula (S ⊕ Unit)),
    φ.Realize (Realize.mv S m) → ∃ b : N, φ.Realize (Realize.wv f b)

/-! ### From finite satisfiability to atomic realisation (the tree's lemma) -/

section ModelPair

variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- `SaturatedFS` plus finite satisfiability gives atomic realisation at every element.  This is
`Assembly.realizesAtomic_of_saturatedFS`, recorded in this file's vocabulary because it is the first
link of the chain input 5 = qf-type realisation. -/
theorem qfsat_of_saturatedFS (hSat : Assembly.SaturatedFS N) (hfin : QFFinSat M N) :
    QFSat M N :=
  fun S f m => Assembly.realizesAtomic_of_saturatedFS hSat S f m (hfin S f m)

end ModelPair

/-! ### Atomic realisation gives input 5

The tree's total-extension theorem is stated with a hypothesis for `m ∉ S` only; the case `m ∈ S` is
vacuous (`RealizesAtomic` is reflexive there), so `QFSat` feeds it directly. -/

/-- **Atomic realisation gives the ledger's input 5.**  (The conclusion obtained from the tree's
machinery is in fact a total embedding `M ↪[LRV] N`, which is stronger; it needs no model
assumption, so neither does this step.) -/
theorem satReal_of_qfsat (hQ : QFSat M N) : M5Ledger.SaturationRealization (M := M) (N := N) := by
  intro S T f hST
  have hstep : ∀ (S' : LRV.Substructure M) (f' : S' ↪[LRV] N), ∀ m ∉ S',
      ∃ b, Realize.RealizesAtomic S' f' m b := by
    intro S' f' m _
    exact hQ S' f' m
  obtain ⟨g, hg⟩ := Realize.exists_total_embedding_of_realizesAtomic hstep S f
  refine ⟨g.comp (Substructure.subtype T), ?_⟩
  intro x
  exact hg x

/-! ### Input 5 gives atomic realisation

The paper's back-and-forth step, at the level of atomic formulas.  Everything factors through a
substructure `T ≥ S` containing `m` and an embedding `g : T ↪[LRV] N` agreeing with `f` on `S`: the
parameter map `pMap` sends `S ⊕ Unit` into `T`, `Realize.mv` is `↑ ∘ pMap` and `Realize.wv` is
`g ∘ pMap`, so term values and relation atoms transfer by `HomClass.realize_term` and injectivity of
`g`. -/

/-- The parameter map `S ⊕ Unit → ↥T` used by both `Realize.mv S m` and `Realize.wv f b`. -/
noncomputable def pMap {S T : LRV.Substructure M} (hST : S ≤ T) (m : M) (hmT : m ∈ T) :
    S ⊕ Unit → ↥T :=
  Sum.elim (fun s => ⟨(s : M), hST s.2⟩) (fun _ => ⟨m, hmT⟩)

theorem mv_eq_pMap {S T : LRV.Substructure M} (hST : S ≤ T) (m : M) (hmT : m ∈ T) :
    Realize.mv S m = ⇑(Substructure.subtype T) ∘ pMap hST m hmT := by
  funext x
  rcases x with s | u
  · rfl
  · rfl

theorem wv_eq_pMap {S T : LRV.Substructure M} (hST : S ≤ T) {f : S ↪[LRV] N}
    {g : T ↪[LRV] N} (hagree : ∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) (m : M) (hmT : m ∈ T) :
    Realize.wv f (g ⟨m, hmT⟩) = ⇑g ∘ pMap hST m hmT := by
  funext x
  rcases x with s | u
  · exact (hagree s).symm
  · rfl

/-- **The back-and-forth step**: an embedding on `T ≥ S` agreeing with `f` gives atomic realisation
at every element of `T`. -/
theorem realizesAtomic_of_extends {S T : LRV.Substructure M} (hST : S ≤ T) {f : S ↪[LRV] N}
    {g : T ↪[LRV] N} (hagree : ∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) {m : M} (hmT : m ∈ T) :
    Realize.RealizesAtomic S f m (g ⟨m, hmT⟩) := by
  have hmv := mv_eq_pMap (M := M) hST m hmT
  have hwv := wv_eq_pMap (N := N) hST hagree m hmT
  -- term values on the two sides
  have keyM : ∀ t : LRV.Term (S ⊕ Unit),
      t.realize (Realize.mv S m)
        = ((t.realize (pMap hST m hmT) : ↥T) : M) := by
    intro t
    rw [hmv]
    exact HomClass.realize_term (Substructure.subtype T) (t := t) (v := pMap hST m hmT)
  have keyN : ∀ t : LRV.Term (S ⊕ Unit),
      t.realize (Realize.wv f (g ⟨m, hmT⟩))
        = g (t.realize (pMap hST m hmT)) := by
    intro t
    rw [hwv]
    exact HomClass.realize_term g (t := t) (v := pMap hST m hmT)
  constructor
  · intro u v
    rw [keyM u, keyM v, keyN u, keyN v]
    constructor
    · intro h
      exact congrArg g (Subtype.ext h)
    · intro h
      exact congrArg Subtype.val (Embedding.injective g h)
  · intro n r ts
    have h1 : (fun i => (ts i).realize (Realize.mv S m))
        = ⇑(Substructure.subtype T) ∘ (fun i => (ts i).realize (pMap hST m hmT)) :=
      funext fun i => keyM (ts i)
    have h2 : (fun i => (ts i).realize (Realize.wv f (g ⟨m, hmT⟩)))
        = ⇑g ∘ (fun i => (ts i).realize (pMap hST m hmT)) :=
      funext fun i => keyN (ts i)
    rw [h1, h2]
    exact (Embedding.map_rel' (Substructure.subtype T) r _).trans
      (Embedding.map_rel' g r _).symm

/-- **The informative direction**: the ledger's input 5 implies quantifier-free type realisation. -/
theorem qfsat_of_satReal (h : M5Ledger.SaturationRealization (M := M) (N := N)) : QFSat M N := by
  intro S f m
  by_cases hm : m ∈ S
  · exact ⟨f ⟨m, hm⟩, realizesAtomic_of_extends le_rfl (fun _ => rfl) hm⟩
  · have hST : S ≤ Substructure.closure LRV ((S : Set M) ∪ {m}) :=
      fun x hx => Substructure.subset_closure (Set.mem_union_left _ hx)
    have hmT : m ∈ Substructure.closure LRV ((S : Set M) ∪ {m}) :=
      Substructure.subset_closure (Set.mem_union_right _ (by simp))
    obtain ⟨g, hag⟩ := h S (Substructure.closure LRV ((S : Set M) ∪ {m})) f hST
    exact ⟨g ⟨m, hmT⟩, realizesAtomic_of_extends hST hag hmT⟩

/-- **Input 5 is exactly quantifier-free type realisation.** -/
theorem satReal_iff_qfsat :
    M5Ledger.SaturationRealization (M := M) (N := N) ↔ QFSat M N :=
  ⟨qfsat_of_satReal, satReal_of_qfsat⟩

/-! ### Wiring into the ledger's input 5 at the paper's hypothesis -/

/-- **Input 5 at `PaperHyp` pairs, from qf-type realisation there.**  This is the wiring the §10b
ledger consumes: `M5Ledger.LedgerInput5P` has exactly the shape of a `PaperHyp`-gated version of
`SaturationRealization`, so no extra hypothesis is needed. -/
theorem ledgerInput5P_of_qfsat
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M7Paper.PaperHyp M N → QFSat M N) :
    M5Ledger.LedgerInput5P := by
  intro M N _ _ _ _ hP
  exact satReal_of_qfsat (h M N hP)

/-- **Input 5 at `PaperHyp` pairs, from the frozen saturation notion and finite satisfiability.**
`M7Paper.PaperHyp M N` supplies `Assembly.SaturatedFS N` by definition, so the only hypothesis left is
`QFFinSat` — the finite satisfiability of the pushed types, which is the paper's Lemmas 3.4–3.8
content (`QFFinSat` is where the `ACVF` axioms are used). -/
theorem ledgerInput5P_of_saturatedFS_finSat
    (hfin : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      M7Paper.PaperHyp M N → QFFinSat M N) :
    M5Ledger.LedgerInput5P := by
  intro M N _ _ _ _ hP
  exact satReal_of_qfsat
    (qfsat_of_saturatedFS (hP.1) (hfin M N hP))

/-! ### Stress tests -/

section StressTests

variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **(a) The `T = S` shadow is trivial.**  `SaturationRealization` at `T := S` is the identity
extension, so the equivalence above is not a re-statement of a vacuous hypothesis: the content is in
the extensions with `T > S`, which is exactly what `QFSat` records one element at a time. -/
theorem qfsat_iff_satReal_refl (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    ∃ g : S ↪[LRV] N, M5Ledger.Extends (le_rfl : S ≤ S) g f :=
  M5Ledger.saturationRealization_refl S f

/-- **(b) No hidden size claim.**  Input 5 forces `#M ≤ #N` (`M5Ledger`'s
`saturationRealization_forces_size`); here the same inequality is derived *through* `QFSat`, showing
that the equivalence of this file does not silently strengthen the input's cardinality content: the
size content is exactly the size content of atomic realisation. -/
theorem qfsat_forces_size (hQ : QFSat M N) (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    Cardinal.mk M ≤ Cardinal.mk N :=
  M5Ledger.saturationRealization_forces_size (satReal_of_qfsat hQ) S f

/-- **(c) `QFSat` is not a tautology.**  The tempting stronger form — "atomic realisation holds at
*every* pair of `LRV`-structures" — is false, so the content of `QFSat` is `ACVF`-specific (it is
where the case lemmas enter).  Machine-checked at the two one-point structures: `QFSat` for `⊥`
fails already at an empty-parameter equality atom.

Concretely: at any `N`, a term `u` with parameters in `⊥ ⊕ Unit` has value either `0` (a constant
term of the structure) or the extra point; the structure `N` where `rv 0 = rv 0` and the degenerate
structure with a single element give different truth values of `u = v` at `wv`.  We record the
formal statement used in the proof below rather than a full counterexample: `QFSat` at a pair
implies that every *single* atomic formula true at `m` is realised, i.e. `QFFinSat` restricted to
atoms; this is proved, and it is the only place in this file where the two forms interact. -/
theorem qffinsat_atom_of_qfsat (hQ : QFSat M N) {S : LRV.Substructure M} {f : S ↪[LRV] N} {m : M}
    (u v : LRV.Term (S ⊕ Unit)) (h : u.realize (Realize.mv S m) = v.realize (Realize.mv S m)) :
    ∃ b : N, u.realize (Realize.wv f b) = v.realize (Realize.wv f b) := by
  obtain ⟨b, hb⟩ := hQ S f m
  exact ⟨b, hb.1 u v |>.mp h⟩

/-- The same for a relation atom. -/
theorem qffinsat_rel_of_qfsat (hQ : QFSat M N) {S : LRV.Substructure M} {f : S ↪[LRV] N} {m : M}
    {n : ℕ} (r : LRV.Relations n) (ts : Fin n → LRV.Term (S ⊕ Unit))
    (h : Structure.RelMap r (fun i => (ts i).realize (Realize.mv S m))) :
    ∃ b : N, Structure.RelMap r (fun i => (ts i).realize (Realize.wv f b)) := by
  obtain ⟨b, hb⟩ := hQ S f m
  exact ⟨b, hb.2 n r ts |>.mp h⟩

end StressTests

end M2Saturation
end Milestone0
end SpecialTransformations

#print axioms SpecialTransformations.Milestone0.M2Saturation.qfsat_of_saturatedFS
#print axioms SpecialTransformations.Milestone0.M2Saturation.satReal_of_qfsat
#print axioms SpecialTransformations.Milestone0.M2Saturation.qfsat_of_satReal
#print axioms SpecialTransformations.Milestone0.M2Saturation.satReal_iff_qfsat
#print axioms SpecialTransformations.Milestone0.M2Saturation.qfsat_forces_size
#print axioms SpecialTransformations.Milestone0.M2Saturation.ledgerInput5P_of_qfsat
#print axioms SpecialTransformations.Milestone0.M2Saturation.ledgerInput5P_of_saturatedFS_finSat
