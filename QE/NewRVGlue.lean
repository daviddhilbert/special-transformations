/-
# CaseNewRV (`M5.OneStepRVNew`) and the tree's interfaces: the glue is realisation, not algebra

Member `m6`, swarm `smw2mluv7`, direction d8.  Object: the frozen new-`rv` case
`M4Cases.CaseNewRV = M5.OneStepRVNew` (`QE/OneStepCases.lean`), the only case slot of
`M4Cases.Cases` no board direction covers, together with the three merged algebraic fragments
that Lemma 3.7/3.8 of Yin's §3.1 are supposed to contribute:

* `QE/Lemma37.lean` (`YinLemma37`) — the value half `vv(b(e)) = vv(b*(d))` under `Γ(Ŝ)` divisible;
* `QE/Lemma38RV.lean` (`YinLemma38`) — the residue half, `SameRV` transfer for expansions;
* `QE/Case38Value.lean` (`YinLemma38Case`) — the pair-level package `lemma38_transfer`.

## The answers (machine-checked below)

* **§1 `stepObligation_rv_mem`** — `M1QF.Frozen.StepObligation S f m` *forces* `iRv m ∈ S`: its
  `RV`-control clause applies to the `RV`-element `iRv m` of the generated substructure.  Hence
  `not_stepObligation_of_newRV`: the interface is unsatisfiable on the new-`rv` branch, and
  `not_stepObligationHypothesis_of_newRV`: the hypothesis of `M4Cases.cases_of_stepObligation` —
  `∀ S f, Standing S → ∀ m, iVF m → StepObligation S f m` — is *inconsistent* at every pair
  carrying a new-`rv` element (a `Standing S` embedded in `N` and a `VF` `m` with `iRv m ∉ S`).
  So that "interface closure" discharges the new-`rv` slot only vacuously; it is an interface for
  the `rv`-old world.
* **§1b `classStepP_rv_mem`** — the same for `M5L.ClassStepP`, the `Γ`-class form of Claim (⋆):
  `KEqTop S` plus `M5L.mem_of_cls_mem` turn the class control into `iRv m ∈ S`.  So the paper's
  Claim (⋆), read in the frozen encoding, is an `rv`-*old* statement — which is exactly why the
  fragments (whose Claim (⋆) is `RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv(e)⟩ ⊆ RV(S)`, control, not growth, with
  `rv(e) ∈ RV(S)`) live on the old-`rv` side of the frozen split.
* **§2 `not_oneStepRVNew_of_infinitesimal`** — at a `Standing S` carrying the infinitesimal
  configuration and a new-`rv` element `m`, `M5.OneStepRVNew` **fails** (embedding half:
  `Hahn.not_embAt_of_infinitesimal`).  So `CaseNewRV` is not provable from any hypotheses
  compatible with the configuration: the missing input is realisation of the pushed type
  (saturation, `M2Saturation.QFSat` / `M5Shoenfield.Input5R`), not value/residue algebra.
* **§3 `hull_demand_of_standing`** — conversely the slot's *conclusion* carries a demand the
  fragments also do not prove: every witness `T` (being `Standing`) contains, for every `n ≥ 1`,
  an `n`-th root-up-to-units of `iRv m` — the whole divisible hull of `Γ(S) + ℤ·vv(m)`
  (`QE/M5OneStep.lean`'s prose, made a theorem).
* **§4 `oneStepRVNew_of_total_extension`** — the one positive source: the total-extension
  property at the pair (saturation / Proposition 3.9) yields the branch outright; and
  `oneStepRVNew_iff_gammaDivisible` shows the branch's only target condition is Γ-divisibility
  (the hull), which is equally unobtainable at the configuration
  (`not_oneStepRVNewGam_of_infinitesimal`).

## The fragments are not consumed anywhere in the merged tree

`grep -l "^import Lemma38RV$" QE/*.lean` gives `QE/Case38Value.lean` only, and
`grep -l "^import Case38Value$" QE/*.lean` gives nothing; no file outside
`Lemma37` / `Lemma37_transcendental` / `Lemma38RV` / `Case38Value` even mentions a `YinLemma37` /
`YinLemma38` declaration.  So the chain terminates in `Case38Value.lean` and the frozen route never
reads it: the fragments have *no* consumer in the merged tree, and §1–§2 say they cannot acquire one
on the new-`rv` side (their Claim (⋆) is `rv`-old control, and the new-`rv` slot is a realisation
statement).  The missing consumer is Remark 3.1's `L_v → L_RV` conversion; the route bypasses it by
taking realisation (`Input5R`) as a hypothesis.

## Where the fragments land (a reading of §1–§2, not a Lean statement)

The fragments are conditional on an existing partner `d ∈ N` with `v' d = v e` (and, for the
residue half, `SameRV v e d`): they compute what `d` must look like (`Γ`, `RV` of `⟨Ŝ,e⟩`), they do
not produce it.  §2 shows no production is possible at Archimedean targets; §1 shows the tree's
`RV`-control interfaces cannot even *state* the new-`rv` case.  This is the exact glue: the
fragments are the paper's phase-2 bookkeeping, `CaseNewRV` is the phase boundary (the frozen slot
asks for the hull in the same step, strictly more than the paper's per-element Claim (⋆)), and the
only interface that crosses the boundary is realisation (saturation).  No `sorry`, no `axiom`,
no `native_decide`; axiom audit at the end.
-/
import M1QFStep
import M5L34_36
import HahnAnatomy
import OneStepCases
import Prop39Decomp

set_option autoImplicit false
set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Milestone0.NewRVGlue

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-! ## 1. `RV`-membership in the generated substructure, and what the tree's interfaces owe -/

/-- `iRv m` lies in every substructure containing `m` (closure under `Fn.rvMap`). -/
theorem iRv_mem_sub {S : LRV.Substructure M} {m : M} (hm : m ∈ S) : iRv m ∈ S :=
  M5L.rv_mem_sub S hm

/-- `iRv m` lies in the substructure generated by `S` and `m`. -/
theorem iRv_mem_closure (S : LRV.Substructure M) (m : M) :
    iRv m ∈ Substructure.closure LRV ((S : Set M) ∪ Set.range (fun _ : Unit => m)) :=
  iRv_mem_sub (Substructure.subset_closure (Or.inr ⟨(), rfl⟩))

/-- **`StepObligation` forces `iRv m ∈ S`.**  The `RV`-control clause
`∀ y ∈ closure (S ∪ {m}), iRV y → y ∈ S` is applied to `y = iRv m`, which lies in the closure
(closure under `Fn.rvMap`) and is an `RV`-element in every model of `ACVF`
(`Transfer.rv_mem`).  So the tree's `StepObligation` is an interface for the `rv`-*old* branch
only: nothing weaker than `iRv m ∈ S` can satisfy it. -/
theorem stepObligation_rv_mem {S : LRV.Substructure M} {f : S ↪[LRV] N} {m : M}
    (h : M1QF.Frozen.StepObligation S f m) (hm : iVF m) : iRv m ∈ S := by
  obtain ⟨n, _hagree, hRV⟩ := h
  exact hRV (iRv m) (iRv_mem_closure S m) (Transfer.rv_mem hM hm)

/-- **`StepObligation` is unsatisfiable in the new-`rv` branch.** -/
theorem not_stepObligation_of_newRV {S : LRV.Substructure M} {f : S ↪[LRV] N} {m : M}
    (hm : iVF m) (hrv : iRv m ∉ S) : ¬ M1QF.Frozen.StepObligation S f m :=
  fun h => hrv (stepObligation_rv_mem h hm)

/-- **The hypothesis of `M4Cases.cases_of_stepObligation` is inconsistent at every new-`rv`
configuration.**  A `Standing` substructure `S` with an embedding `f : S ↪[LRV] N` and a
`VF`-element `m` with `iRv m ∉ S` cannot carry the obligation at `m`.  (`S = ⊤` has no such `m`,
and no such configuration is needed for the empty model; the point is that the interface is a
statement about the `rv`-old world, not a decomposition of `OneStepVFP`.) -/
theorem not_stepObligationHypothesis_of_newRV
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      M1QF.Frozen.StepObligation S f m)
    {S : LRV.Substructure M} {f : S ↪[LRV] N} (hS : Assembly.Standing S) {m : M}
    (hm : iVF m) (hrv : iRv m ∉ S) : False :=
  not_stepObligation_of_newRV hm hrv (h S f hS m hm)

/-! ### 1b. The same for the `Γ`-class form of Claim (⋆), `M5L.ClassStepP`

`ClassStepP`'s conclusion controls the `RV`-elements of `T` *up to `Γ`-classes in `S`*.  With
`KEqTop S`, `M5L.mem_of_cls_mem` turns that into membership in `S`, so the interface forces
`iRv m ∈ S` for every `VF` `m` — again an `rv`-old statement. -/

/-- **`ClassStepP` forces `iRv m ∈ S`.** -/
theorem classStepP_rv_mem (hcls : M5L.ClassStepP (M := M) (N := N))
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (hS : Assembly.Standing S) {m : M}
    (hm : iVF m) : iRv m ∈ S := by
  obtain ⟨T, _g, _hST, _hagree, hmT, hcc⟩ := hcls S f hS m hm
  obtain ⟨s, hsS, hsRV, hcl⟩ := hcc (iRv m) (iRv_mem_sub hmT) (Transfer.rv_mem hM hm)
  exact M5L.mem_of_cls_mem hM hS.1 (Transfer.rv_mem hM hm) hsRV hcl hsS

/-- **`ClassStepP` is unsatisfiable in the new-`rv` branch too.** -/
theorem not_classStepP_of_newRV (hcls : M5L.ClassStepP (M := M) (N := N))
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (hS : Assembly.Standing S) {m : M}
    (hm : iVF m) (hrv : iRv m ∉ S) : False :=
  hrv (classStepP_rv_mem hcls S f hS hm)

/-- **The paper's Claim (⋆), in `Γ`-class form, is an `rv`-old statement.**  If every `RV`-element
of `T ⊇ S` is class-equal to an element of `S` (`M5L.ResidualClasses`, the paper's
`RV(⟨Ŝ,e⟩) ⊆ Γ(S)`), then *every* `VF`-element of `T` has its `rv` in `S`.  So a case lemma that
establishes Claim (⋆) and nothing else can never produce the frozen new-`rv` branch, whose very
hypothesis is `iRv m ∉ S`. -/
theorem residualClasses_rv_mem {S T : LRV.Substructure M} (hST : S ≤ T)
    (hK : Assembly.KEqTop S) (hcc : M5L.ResidualClasses S T) {m : M} (hmT : m ∈ T)
    (hmVF : iVF m) : iRv m ∈ S :=
  M5L.RVControl_of_ClassControl hST hK hcc (iRv m) (iRv_mem_sub hmT) (Transfer.rv_mem hM hmVF)

/-! ## 2. The new-`rv` branch fails at an Archimedean target carrying the configuration -/

/-- **The frozen new-`rv` branch (`CaseNewRV`) is *false* at an Archimedean target carrying the
infinitesimal configuration.**  A witness `T, g` of the branch is in particular the embedding half
`Hahn.EmbAt S f m`, which `Hahn.not_embAt_of_infinitesimal` refutes: `iRv m` is positive and
infinitesimal below the positive `s ∈ S`, so its pushed type is not realised over `f '' S` in an
Archimedean `Γ(N)`.

The hypothesis `hrvnew` is what makes the slot *applicable*: `OneStepRVNew` is only demanded at
new-`rv` elements.  The refutation therefore says exactly that the branch's only possible input is
type realisation (saturation, `Input5R`), and that no combination of value/residue computations can
produce the branch at such a pair. -/
theorem not_oneStepRVNew_of_infinitesimal
    (hArch : Hahn.ArchimedeanRV N)
    {S : LRV.Substructure M} {f : S ↪[LRV] N} (hS : Assembly.Standing S)
    {s : M} (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    {m : M} (hmVF : iVF m) (hmS : m ∉ S)
    (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s)
    (hrvnew : iRv m ∉ S) :
    ¬ M5.OneStepRVNew (M := M) (N := N) := by
  intro h
  obtain ⟨T, g, hST, hagree, hmT, _hStandT⟩ := h S f hS m hmVF hrvnew
  exact Hahn.not_embAt_of_infinitesimal hArch hsS hsRV hsne hsgt hmVF hmS hmgt hinf
    ⟨T, g, hST, hagree, hmT⟩

/-! ## 3. The divisible-hull demand forced on every witness -/

/-- **The `Γ`-hull demand of the new-`rv` branch.**  Every `Standing` substructure `T` containing
`m` contains, for every `n ≥ 1`, an `n`-th root (up to a unit coefficient) of the class of
`iRv m`: `u ∈ T` with `rvPow u n = rv(m) · c`, `c` a unit of `M`.  Applied to the target condition
`Standing T` of the slot's conclusion, this is the machine-checked form of "the whole divisible
hull of `Γ(S) + ℤ·vv(m)` has to enter `T` in the same step". -/
theorem hull_demand_of_standing {T : LRV.Substructure M} (hT : Assembly.Standing T)
    {m : M} (hmVF : iVF m) (hmT : m ∈ T) (hrv0 : iRv m ≠ iRVZero) :
    ∀ n : ℕ, 1 ≤ n → ∃ u c : M, u ∈ T ∧ iRV u ∧ u ≠ iRVZero ∧ c ∈ T ∧ iUnits c ∧
      Assembly.rvPow u n = iRVMul (iRv m) c :=
  fun n hn => hT.2 (iRv m) (iRv_mem_sub hmT) (Transfer.rv_mem hM hmVF) hrv0 n hn

/-- **`CaseNewRV`'s conclusion carries the hull demand.**  Whatever `T, g` a proof of the slot
produces, the `Standing`-ness of `T` forces the divisible hull inside it: so the slot is strictly
stronger than "add `m`", and any proposal that omits the hull cannot be a witness. -/
theorem hull_demand_of_oneStepRVNew (h : M5.OneStepRVNew (M := M) (N := N))
    {S : LRV.Substructure M} {f : S ↪[LRV] N} (hS : Assembly.Standing S) {m : M}
    (hmVF : iVF m) (hrvnew : iRv m ∉ S) (hrv0 : iRv m ≠ iRVZero) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧
        ∀ n : ℕ, 1 ≤ n → ∃ u c : M, u ∈ T ∧ iRV u ∧ u ≠ iRVZero ∧ c ∈ T ∧ iUnits c ∧
          Assembly.rvPow u n = iRVMul (iRv m) c := by
  obtain ⟨T, g, hST, hagree, hmT, hStandT⟩ := h S f hS m hmVF hrvnew
  exact ⟨T, g, hST, hagree, hmT, hull_demand_of_standing hStandT hmVF hmT hrv0⟩

/-! ## 4. The positive source, and stress tests -/

/-- **The new-`rv` branch with the target's `KEqTop` removed.**  Since `KEqTop` is monotone in the
substructure (`M5.KEqTop_mono`), the *only* target condition the new-`rv` branch carries is
`Assembly.GammaDivisible T` — i.e. exactly the divisible hull of `Γ(S) + ℤ·vv(m)`.  This is the
sharp form of "the slot's content beyond the embedding is the hull": whatever the fragments
compute about values and residues, the branch's target obligation is this predicate, and nothing
in the tree discharges it at a new-`rv` element. -/
def OneStepRVNewGam : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
    iRv m ∉ S →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.GammaDivisible T

/-- **`CaseNewRV`'s target condition is exactly Γ-divisibility.** -/
theorem oneStepRVNew_iff_gammaDivisible :
    M5.OneStepRVNew (M := M) (N := N) ↔ OneStepRVNewGam (M := M) (N := N) := by
  constructor
  · intro h S f hS m hm hrv
    obtain ⟨T, g, hST, hagree, hmT, hStand⟩ := h S f hS m hm hrv
    exact ⟨T, g, hST, hagree, hmT, hStand.2⟩
  · intro h S f hS m hm hrv
    obtain ⟨T, g, hST, hagree, hmT, hgam⟩ := h S f hS m hm hrv
    exact ⟨T, g, hST, hagree, hmT, ⟨M5.KEqTop_mono hST hS.1, hgam⟩⟩

/-- **(e) a tempting repair is still false: dropping `Standing T` for the hull condition does not
help.**  The Γ-divisibility form of the branch fails at the same configuration, so it is the
*realisation* half (the embedding `g`), not the target condition, that is unobtainable there. -/
theorem not_oneStepRVNewGam_of_infinitesimal
    (hArch : Hahn.ArchimedeanRV N)
    {S : LRV.Substructure M} {f : S ↪[LRV] N} (hS : Assembly.Standing S)
    {s : M} (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    {m : M} (hmVF : iVF m) (hmS : m ∉ S)
    (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s)
    (hrvnew : iRv m ∉ S) :
    ¬ OneStepRVNewGam (M := M) (N := N) :=
  fun h => not_oneStepRVNew_of_infinitesimal (f := f) hArch hS hsS hsRV hsne hsgt hmVF hmS hmgt hinf hrvnew
    (oneStepRVNew_iff_gammaDivisible.mpr h)

/-- **The new-`rv` branch from the total extension property** (saturation, Proposition 3.9 at the
pair): take `T = ⊤`, whose `Standing` is `StandingTree.standing_top`.  This pins the direction in
which the branch is available — the branch is not proved by algebra, it is a corollary of
realisation. -/
theorem oneStepRVNew_of_total_extension
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ∃ g : M ↪[LRV] N,
      ∀ x : S, g (x : M) = f x) :
    M5.OneStepRVNew (M := M) (N := N) := by
  intro S f _hS m _hmVF _hrvnew
  obtain ⟨g, hg⟩ := h S f
  exact ⟨⊤, g.domRestrict ⊤, fun _ _ => trivial, fun x => hg x, trivial,
    StandingTree.standing_top⟩

/-- **(a) `iRv m ∉ S` is not removable from §1**: at `m ∈ S` the obligation *is* satisfiable
(`M1QF.Frozen.stepObligation_of_mem`, the atomic match is `f` itself), so §1 isolates the new-`rv`
branch and nothing else. -/
theorem stepObligation_of_mem' {S : LRV.Substructure M} (f : S ↪[LRV] N) {m : M}
    (hm : m ∈ S) : M1QF.Frozen.StepObligation S f m :=
  M1QF.Frozen.stepObligation_of_mem S f hm

/-- **(b) the new-`rv` branch only ever applies at a proper substructure**: no `RV`-element is
outside `⊤`, so `hrvnew` of §2 is a properness condition and cannot be met at `S = ⊤`. -/
theorem not_rv_notMem_top {m : M} : ¬ iRv m ∉ (⊤ : LRV.Substructure M) :=
  fun h => h (Substructure.mem_top _)

/-- **(c) the hull demand is not vacuous**: at `T = ⊤` it holds for `m = 1` and every `n`, so the
conclusion of §3 is satisfiable (and `Γ(⊤)` is divisible at every model,
`StandingTree.standing_top`). -/
theorem hull_demand_top_instance (n : ℕ) (hn : 1 ≤ n) :
    ∃ u c : M, u ∈ (⊤ : LRV.Substructure M) ∧ iRV u ∧ u ≠ iRVZero ∧
      c ∈ (⊤ : LRV.Substructure M) ∧ iUnits c ∧
      Assembly.rvPow u n = iRVMul (iRv (iVFOne (M := M))) c :=
  hull_demand_of_standing (StandingTree.standing_top (M := M))
    (Transfer.vf_one_mem (M := M) hM) (Substructure.mem_top _)
    (by rw [RVCalc.rv_one (M := M) hM]; exact RVCalc.rv_one_ne_zero (M := M) hM) n hn

/-- **(d) the side condition `iRv m ≠ iRVZero` of §3 is not a gap**: `iRv m = 0` with `iVF m`
forces `m = 0 ∈ S`, so at the excluded class the element is old and no hull is owed. -/
theorem eq_vfZero_of_rv_eq_zero {m : M} (hmVF : iVF m) (h : iRv m = iRVZero) :
    m = iVFZero :=
  RVCalc.vf_eq_zero_of_rv_eq_zero hM hmVF h

/-- **(f) the refutation is not a size artefact**: `Standing S` plus the embedding `S ↪[LRV] N`
already forces `#Kˣ(M) ≤ #N` (`Hahn.config_forces_units_size`), the cardinality bound that genuine
`‖M‖⁺`-saturation supplies.  So the configuration of §2 lives in size-consistent territory: it is
the realisation half that fails, not the cardinality. -/
theorem config_forces_units_size' (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (hS : Assembly.Standing S) : Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N :=
  Hahn.config_forces_units_size S f hS

/-- **(g) the refutation at the slot's own name**: `M4Cases.CaseNewRV` (the new-`rv` slot of
`QE/OneStepCases.lean`) is false at the configuration, with the same hypotheses as §2 plus the
applicability condition `iRv m ∉ S`. -/
theorem not_caseNewRV_of_infinitesimal
    (hArch : Hahn.ArchimedeanRV N)
    {S : LRV.Substructure M} {f : S ↪[LRV] N} (hS : Assembly.Standing S)
    {s : M} (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    {m : M} (hmVF : iVF m) (hmS : m ∉ S)
    (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s)
    (hrvnew : iRv m ∉ S) :
    ¬ M4Cases.CaseNewRV (M := M) (N := N) :=
  not_oneStepRVNew_of_infinitesimal (f := f) hArch hS hsS hsRV hsne hsgt hmVF hmS hmgt hinf hrvnew

/-- **(h) the whole ledger `M4Cases.Cases` fails at the configuration** — so no slot of `Cases` is
an assumption that could be discharged at such a pair: `Cases → OneStepVFP`
(`M4Cases.oneStepVFP_of_cases`), and the one-step is refuted there
(`Hahn.not_oneStepVFP_of_infinitesimal'`). -/
theorem not_cases_of_infinitesimal
    (hArch : Hahn.ArchimedeanRV N)
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (hS : Assembly.Standing S)
    (s : M) (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (m : M) (hmVF : iVF m) (hmS : m ∉ S)
    (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s)
    (hC : M4Cases.Cases (M := M) (N := N)) : False :=
  Hahn.not_oneStepVFP_of_infinitesimal' hArch S f hS s hsS hsRV hsne hsgt m hmVF hmS hmgt hinf
    (M4Cases.oneStepVFP_of_cases hC)

/-- **(i) at the honest gate the slot is *supplied*, not assumed.**  `M5Shoenfield.Input5R` —
Marker's saturated realisation at `relGate`, the second hypothesis of `G3.paper_theorem_rel_two` —
gives the *whole* `M4Cases.Cases` ledger at every `relGate` pair (total extension at the pair, then
`M4Cases.cases_of_global_extension`), hence in particular `CaseNewRV`.  So the final theorem never
needs the case audit as an extra hypothesis; and by §2 the slot is false at the configuration
without that realisation input.  This is the exact sense in which the fragments and the case split
are *not* on the critical path of the honest-gate final. -/
theorem cases_at_relGate_of_input5R (h5 : M5Shoenfield.Input5R) {M N : Type}
    [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
    (hR : M5Shoenfield.relGate M N) : M4Cases.Cases (M := M) (N := N) :=
  M4Cases.cases_of_global_extension
    (fun S f => G3.extendsAt_rel_of_input5R h5 M N hR S f)

end NewRVGlue
end SpecialTransformations.Milestone0

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.NewRVGlue.iRv_mem_sub
#print axioms SpecialTransformations.Milestone0.NewRVGlue.iRv_mem_closure
#print axioms SpecialTransformations.Milestone0.NewRVGlue.stepObligation_rv_mem
#print axioms SpecialTransformations.Milestone0.NewRVGlue.not_stepObligation_of_newRV
#print axioms SpecialTransformations.Milestone0.NewRVGlue.not_stepObligationHypothesis_of_newRV
#print axioms SpecialTransformations.Milestone0.NewRVGlue.classStepP_rv_mem
#print axioms SpecialTransformations.Milestone0.NewRVGlue.not_classStepP_of_newRV
#print axioms SpecialTransformations.Milestone0.NewRVGlue.residualClasses_rv_mem
#print axioms SpecialTransformations.Milestone0.NewRVGlue.not_oneStepRVNew_of_infinitesimal
#print axioms SpecialTransformations.Milestone0.NewRVGlue.hull_demand_of_standing
#print axioms SpecialTransformations.Milestone0.NewRVGlue.hull_demand_of_oneStepRVNew
#print axioms SpecialTransformations.Milestone0.NewRVGlue.oneStepRVNew_iff_gammaDivisible
#print axioms SpecialTransformations.Milestone0.NewRVGlue.not_oneStepRVNewGam_of_infinitesimal
#print axioms SpecialTransformations.Milestone0.NewRVGlue.oneStepRVNew_of_total_extension
#print axioms SpecialTransformations.Milestone0.NewRVGlue.stepObligation_of_mem'
#print axioms SpecialTransformations.Milestone0.NewRVGlue.not_rv_notMem_top
#print axioms SpecialTransformations.Milestone0.NewRVGlue.hull_demand_top_instance
#print axioms SpecialTransformations.Milestone0.NewRVGlue.config_forces_units_size'
#print axioms SpecialTransformations.Milestone0.NewRVGlue.not_caseNewRV_of_infinitesimal
#print axioms SpecialTransformations.Milestone0.NewRVGlue.not_cases_of_infinitesimal
#print axioms SpecialTransformations.Milestone0.NewRVGlue.cases_at_relGate_of_input5R
#print axioms SpecialTransformations.Milestone0.NewRVGlue.eq_vfZero_of_rv_eq_zero
