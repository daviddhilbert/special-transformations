/-
# r4 — Lemma 3.5's surviving branch (`CaseNotSeparated`), and where the `Γ`-content actually is

Member `m1`, swarm `smw2ox51x`.  Direction `d6` (= r4).

## What this file is for

The merged `QE/Case35Slot.lean` (direction p5) reduces the not-separated slot to
`Case35.NotSeparatedBranch`, whose conclusion is `M5L.ResidualClasses S T` — the frozen form of the
paper's Claim (⋆), `RV(⟨Ŝ,e⟩) ⊆ RV(S)` in class form.  Two things are wrong with taking that as
*the* obligation, and both are machine-checked in the merged tree:

* `Case35.notSeparated_class_form` + `Case35.notSeparated_class_form_concl_witness`: the branch's
  hypothesis `RVOldClass S m` is **implied by the slot's own hypothesis** `iRv m ∈ S`
  (`rvOldClass_of_rv_mem` below) — so the hypothesis adds nothing;
* `Case35.not_residualClasses_of_perturbation`: at the slot's *own* hypotheses a sub-regime exists
  (perturbations `m = y + ε` with `y ∈ S ∩ VF` and `ε` of a class that is not an old class) on
  which `ResidualClasses S T` is **false for every** `T ⊇ S ∪ {m}`.

So the class-control conclusion is not the shape a branch statement can have.  This file supplies
the correct one, and proves that the `Γ`/`Γ`-divisibility bookkeeping of the frozen slot costs
nothing once the extension is allowed to be the *divisible hull* rather than `closure (S ∪ {m})`.

## Contents

**§1 `RootClosedOn`** — the class-level form of `Assembly.GammaDivisible`:
every nonzero `RV`-class of `T` has an `n`-th root *inside* `T` (`Cls (rvPow u n) t`).
`gammaDivisible_of_rootClosedOn`, `rootClosedOn_of_gammaDivisible` and
`standing_iff_rootClosedOn` show that `Assembly.Standing T = KEqTop T ∧ RootClosedOn T`, i.e. the
new predicate is *exactly* the frozen one, not a strengthening.

**§2 `Γ(M)` is divisible, so roots exist in `M`** (`exists_cls_root`, from
`GammaDiv.gamma_divisible`, hypothesis-free in the tree).

**§3 the root hull `rootHull S m`** — the `ω`-iterate of "adjoin all roots of all `RV`-classes",
starting at `closure (S ∪ {m})`.  It is a substructure of `M` containing `S` and `m`, and it is
`RootClosedOn` (`rootClosedOn_rootHull`).  Consequently `Assembly.Standing (rootHull S m)` holds
for **every** standing `S` and **every** `m ∈ VF(M)`, in the not-separated case, in the separated
case and in the new-`rv` case alike (`standing_rootHull`).

**§4 the branch statements that survive.**  With §3, the frozen slots reduce to the *embedding*
obligation alone: `CasesNotSeparatedRealise`, `CaseSeparatedRealise`, `CaseNewRVRealise` all have
the shape "`f` extends to `rootHull S m ↪[LRV] N`", with no `Γ`, no `ResidualClasses`, no
`RVOldClass`, and no `Standing T` conjunct.  `cases_of_rootHullEmbedding`,
`oneStepVFP_of_rootHullEmbedding`, `caseNotSeparated_of_branchRealise` and
`oneStepPaper_of_rootHullEmbedding` are the machine-checked chains.

**§5 stress tests**: the tree's `ResidualClasses` branch *implies* the new one
(`rootClosedOn_of_ResidualClasses`), so the new branch is strictly weaker; the residual is
satisfiable at `N = M` (`rootHullEmbedding_self`) and at `S = ⊤` (`rootHull_top`); the cardinality
content is unchanged (`rootHull_embedding_units_size`); and the reduction is not a restatement of
its own conclusion (`rootHullEmbedding_of_mem`).

No `sorry`, no `axiom`, no `native_decide`; axiom audit at the end.
-/
import OneStepCases
import M5L34_36
import GammaDiv
import Case35Slot
import Lemma36Audit
import OldRVClaim

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Milestone0.RVCalc
open SpecialTransformations.Milestone0.Transc

namespace SpecialTransformations.Milestone0.Case35Hull

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ## 1. `RootClosedOn`: the class-level form of `Assembly.GammaDivisible` -/

/-- **`T` is closed under `n`-th roots of its `RV`-classes.**  For every nonzero `RV`-element `t` of
`T` and every `n ≥ 1` there is `u ∈ T` whose `n`-th `RV` power has the same `Γ`-class as `t`.

This is the *class-level* form of `Assembly.GammaDivisible T`, which asks for the sharper
`rvPow u n = t · c` with `c` a unit of `T`; the two are equivalent modulo `KEqTop T`
(`gammaDivisible_of_rootClosedOn`, `rootClosedOn_of_gammaDivisible`).  The class-level form is the
one that is closed under adjoining roots, which is what §3 needs. -/
def RootClosedOn (T : LRV.Substructure M) : Prop :=
  ∀ t : M, t ∈ T → iRV t → t ≠ iRVZero → ∀ n : ℕ, 1 ≤ n →
    ∃ u : M, u ∈ T ∧ iRV u ∧ u ≠ iRVZero ∧ Transc.Cls (Assembly.rvPow u n) t

/-- A unit on the right does not change the `Γ`-class. -/
theorem cls_mul_unit_right {t c : M} (ht : iRV t) (ht0 : t ≠ iRVZero) (hc : iRV c)
    (hcU : iUnits c) : Transc.Cls (iRVMul t c) t := by
  have hone : Transc.Cls c iRVOne := Lemma36AuditACVF.units_cls_one hcU
  have h := Transc.cls_mul_left hM (a := c) (b := iRVOne) (c := t) hc
    (Transfer.rv_one_mem (M := M) hM) ht hone
  rwa [MulNormalForm.rv_mul_one_right hM ht] at h

/-- **`RootClosedOn` + `KEqTop` gives the frozen `GammaDivisible`.**  The `n`-th root `u ∈ T` and
`cls_ratio_units` supply the unit `c`; `KEqTop T` puts it in `T`. -/
theorem gammaDivisible_of_rootClosedOn {T : LRV.Substructure M} (hK : Assembly.KEqTop T)
    (h : RootClosedOn T) : Assembly.GammaDivisible T := by
  intro t htT htRV ht0 n hn
  obtain ⟨u, huT, huRV, hu0, hcls⟩ := h t htT htRV ht0 n hn
  obtain ⟨c, hcRV, hcU, heq⟩ :=
    M5L.cls_ratio_units hM (GammaDiv.rvPow_mem huRV n) htRV hcls ht0
  exact ⟨u, c, huT, huRV, hu0, hK c hcU, hcU, heq⟩

/-- **The frozen `GammaDivisible` implies `RootClosedOn`**: its witnesses already realise the
class. -/
theorem rootClosedOn_of_gammaDivisible {T : LRV.Substructure M}
    (h : Assembly.GammaDivisible T) : RootClosedOn T := by
  intro t htT htRV ht0 n hn
  obtain ⟨u, c, huT, huRV, hu0, -, hcU, hpow⟩ := h t htT htRV ht0 n hn
  refine ⟨u, huT, huRV, hu0, ?_⟩
  rw [hpow]
  exact cls_mul_unit_right htRV ht0 (Jm2.iRV_of_inK (Or.inl hcU)) hcU

/-- **`Assembly.Standing T` is exactly `KEqTop T` plus `RootClosedOn T`** — so §1's predicate is the
frozen one and not a strengthening of it. -/
theorem standing_iff_rootClosedOn (T : LRV.Substructure M) :
    Assembly.Standing T ↔ Assembly.KEqTop T ∧ RootClosedOn T :=
  ⟨fun h => ⟨h.1, rootClosedOn_of_gammaDivisible h.2⟩,
   fun h => ⟨h.1, gammaDivisible_of_rootClosedOn h.1 h.2⟩⟩

/-- `RootClosedOn` is **not** monotone in the substructure: a larger `T` has new `RV`-classes whose
roots need not lie in it.  (Recorded here as a negative remark: the correct monotonicity statement
is `RootClosedOn S → S ≤ T → (∀ t ∈ T, iRV t → ∃ s ∈ S, Cls t s) → RootClosedOn T`, which is
`rootClosedOn_of_residualClasses` in §5.) -/
theorem rootClosedOn_of_close {S T : LRV.Substructure M} (hS : Assembly.Standing S) (hST : S ≤ T)
    (hres : M5L.ResidualClasses S T) : RootClosedOn T := by
  apply rootClosedOn_of_gammaDivisible
  exact M5L.standing_of_ClassControl hST hS hres |>.2

/-! ## 2. `Γ(M)` is divisible: roots exist in the model -/

/-- **Every nonzero `Γ`-class of `M` has an `n`-th root realised in `M`.**  This is
`GammaDiv.gamma_divisible` (`Γ(M)` is a divisible ordered abelian group, hypothesis-free) read
through the quotient map `gammaMk`. -/
theorem exists_cls_root {t : M} (ht : iRV t) (ht0 : t ≠ iRVZero) {n : ℕ} (hn : 1 ≤ n) :
    ∃ u : M, iRV u ∧ u ≠ iRVZero ∧ Transc.Cls (Assembly.rvPow u n) t := by
  obtain ⟨b, hb⟩ := GammaDiv.gamma_divisible (M := M) n hn
    (GammaGroup.gammaMk (GammaDiv.mkR t ht ht0))
  obtain ⟨a, ha⟩ := GammaGroup.gammaMk_surjective b
  have hpow : GammaGroup.gammaMk (a ^ n) = GammaGroup.gammaMk (GammaDiv.mkR t ht ht0) := by
    rw [← GammaDiv.gammaMk_pow, ha, hb]
  -- move `hpow` to the `rvPow` spelling without rewriting inside an `RVStar` literal
  have h1 : GammaGroup.gammaMk (GammaDiv.mkR (a ^ n).1 (a ^ n).2.1 (a ^ n).2.2)
      = GammaGroup.gammaMk (GammaDiv.mkR t ht ht0) := by
    rw [GammaDiv.mkR_self]
    exact hpow
  have hkey : GammaGroup.gammaMk (GammaDiv.mkR (Assembly.rvPow a.1 n)
        (GammaDiv.rvPow_mem a.2.1 n) (GammaDiv.rvPow_ne_zero a.2.1 a.2.2 n))
      = GammaGroup.gammaMk (GammaDiv.mkR t ht ht0) :=
    (GammaDiv.gammaMk_congr (a ^ n).2.1 (a ^ n).2.2
      (GammaDiv.rvPow_mem a.2.1 n) (GammaDiv.rvPow_ne_zero a.2.1 a.2.2 n)
      (GammaDiv.rvStar_pow_val a n)).symm.trans h1
  refine ⟨a.1, a.2.1, a.2.2, ?_⟩
  exact GammaGroup.gammaMk_eq_iff_le.mp hkey

/-- `⊤` is root closed (every class of `M` has its roots in `M`). -/
theorem rootClosedOn_top : RootClosedOn (⊤ : LRV.Substructure M) :=
  fun t _ ht ht0 n hn => by
  obtain ⟨u, huRV, hu0, hcls⟩ := exists_cls_root ht ht0 hn
  exact ⟨u, trivial, huRV, hu0, hcls⟩

/-! ## 3. The root hull: `closure (S ∪ {m})` made root closed by `ω`-iteration -/

/-- The generators of the next stage: the previous stage together with *all* roots of all of its
nonzero `RV`-classes.  (Taking all roots rather than a chosen one keeps the definition free of
`Classical.choose`, and is what makes `rootClosedOn_rootHull` immediate.) -/
def step (T : LRV.Substructure M) : Set M :=
  (T : Set M) ∪ {u : M | ∃ t ∈ (T : Set M), iRV t ∧ t ≠ iRVZero ∧ ∃ n : ℕ, 1 ≤ n ∧
    iRV u ∧ u ≠ iRVZero ∧ Transc.Cls (Assembly.rvPow u n) t}

/-- The stages of the root hull, starting at `closure (S ∪ {m})`. -/
noncomputable def stage (S : LRV.Substructure M) (m : M) : ℕ → LRV.Substructure M
  | 0 => Substructure.closure LRV ((S : Set M) ∪ {m})
  | (k + 1) => Substructure.closure LRV (step (stage S m k))

/-- The root hull of `S` at `m`: the union of the stages. -/
noncomputable def rootHull (S : LRV.Substructure M) (m : M) : LRV.Substructure M :=
  ⨆ k, stage S m k

theorem stage_le_succ (S : LRV.Substructure M) (m : M) (k : ℕ) :
    stage S m k ≤ stage S m (k + 1) :=
  fun _ hx => Substructure.subset_closure (Or.inl hx)

theorem stage_mono (S : LRV.Substructure M) (m : M) : Monotone (stage S m) := by
  intro i j hij
  induction hij with
  | refl => exact le_rfl
  | @step j _ ih => exact le_trans ih (stage_le_succ S m j)

theorem stage_zero_le (S : LRV.Substructure M) (m : M) : S ≤ stage S m 0 :=
  fun _ hx => Substructure.subset_closure (Or.inl hx)

/-- `S` sits inside the root hull. -/
theorem le_rootHull (S : LRV.Substructure M) (m : M) : S ≤ rootHull S m :=
  fun x hx => le_iSup (fun k => stage S m k) 0 (stage_zero_le S m hx)

/-- The new element sits inside the root hull. -/
theorem mem_rootHull_self (S : LRV.Substructure M) (m : M) : m ∈ rootHull S m :=
  le_iSup (fun k => stage S m k) 0 (Substructure.subset_closure (Or.inr rfl))

/-- Membership in the root hull is membership in some finite stage. -/
theorem mem_rootHull {S : LRV.Substructure M} {m x : M} :
    x ∈ rootHull S m ↔ ∃ k, x ∈ stage S m k := by
  have hd : Directed (· ≤ ·) (stage S m) := fun i j =>
    ⟨max i j, stage_mono S m (le_max_left i j), stage_mono S m (le_max_right i j)⟩
  exact Substructure.mem_iSup_of_directed (L := LRV) (M := M) (S := stage S m) hd

/-- **The root hull is root closed.** -/
theorem rootClosedOn_rootHull (S : LRV.Substructure M) (m : M) : RootClosedOn (rootHull S m) := by
  intro t htT htRV ht0 n hn
  obtain ⟨k, hk⟩ := mem_rootHull.mp htT
  obtain ⟨u, huRV, hu0, hcls⟩ := exists_cls_root htRV ht0 hn
  have hu : u ∈ stage S m (k + 1) :=
    Substructure.subset_closure (Or.inr ⟨t, hk, htRV, ht0, n, hn, huRV, hu0, hcls⟩)
  exact ⟨u, le_iSup (fun k => stage S m k) (k + 1) hu, huRV, hu0, hcls⟩

/-- **The root hull is standing**, wherever `S` is: `KEqTop` is monotone and `GammaDivisible`
follows from root closedness. -/
theorem standing_rootHull {S : LRV.Substructure M} (hS : Assembly.Standing S) (m : M) :
    Assembly.Standing (rootHull S m) :=
  (standing_iff_rootClosedOn _).mpr
    ⟨M5.KEqTop_mono (le_rootHull S m) hS.1, rootClosedOn_rootHull S m⟩

/-! ## 4. The branch statements that survive, and the chains into the frozen slots -/

section Slots

variable {N : Type} [LRV.Structure N] [hN : N ⊨ Axioms.ACVF]

/-- **The embedding obligation at the root hull.**  `f : S ↪[LRV] N` extends to the root hull of
`S` at `m`.  This is the *whole* of what the frozen not-separated slot still owes once the `Γ`
bookkeeping is moved into §3. -/
def RootHullEmbedding (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M) : Prop :=
  ∃ g : rootHull S m ↪[LRV] N, ∀ x : S, g ⟨(x : M), le_rootHull S m x.2⟩ = f x

/-- **`CaseNotSeparated` from the embedding obligation alone.**  No `ResidualClasses`, no
`RVOldClass`, no `Γ`-divisibility: `standing_rootHull` supplies `Standing (rootHull S m)` outright,
and `rootHull S m` contains `m` by construction. -/
theorem caseNotSeparated_of_rootHullEmbedding
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      RootHullEmbedding (M := M) (N := N) S f m) :
    M4Cases.CaseNotSeparated (M := M) (N := N) := by
  intro S f hS m _hmVF _hmrv _hnotsep
  obtain ⟨g, hagree⟩ := h S f hS m _hmVF
  exact ⟨rootHull S m, g, le_rootHull S m, hagree, mem_rootHull_self S m,
    standing_rootHull hS m⟩

/-- **The separated slot from the same obligation** — the reduction is *independent of the case
split*: the frozen `Standing T` conjunct never uses `M5L.Separated`. -/
theorem caseSeparated_of_rootHullEmbedding
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      RootHullEmbedding (M := M) (N := N) S f m) :
    M4Cases.CaseSeparated (M := M) (N := N) := by
  intro S f hS m _hmVF _hmrv _hsep
  obtain ⟨g, hagree⟩ := h S f hS m _hmVF
  exact ⟨rootHull S m, g, le_rootHull S m, hagree, mem_rootHull_self S m,
    standing_rootHull hS m⟩

/-- **The new-`rv` slot from the same obligation.** -/
theorem caseNewRV_of_rootHullEmbedding
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      RootHullEmbedding (M := M) (N := N) S f m) :
    M4Cases.CaseNewRV (M := M) (N := N) := by
  intro S f hS m _hmVF _hmrv
  obtain ⟨g, hagree⟩ := h S f hS m _hmVF
  exact ⟨rootHull S m, g, le_rootHull S m, hagree, mem_rootHull_self S m,
    standing_rootHull hS m⟩

/-- **All three branches at once.** -/
theorem cases_of_rootHullEmbedding
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      RootHullEmbedding (M := M) (N := N) S f m) :
    M4Cases.Cases (M := M) (N := N) where
  separated := caseSeparated_of_rootHullEmbedding h
  notSeparated := caseNotSeparated_of_rootHullEmbedding h
  newRV := caseNewRV_of_rootHullEmbedding h

/-- **The frozen one-step from the embedding obligation.** -/
theorem oneStepVFP_of_rootHullEmbedding
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      RootHullEmbedding (M := M) (N := N) S f m) :
    Assembly.OneStepVFP (M := M) (N := N) :=
  M4Cases.oneStepVFP_of_cases (cases_of_rootHullEmbedding h)

/-! ## 4b. The exact restatement of the slot: `Standing` splits into a free half and a contentful half

`Assembly.Standing T = KEqTop T ∧ RootClosedOn T` (§1) and `KEqTop T` is *automatic* from
`Standing S` for any `T ⊇ S` (`M5.KEqTop_mono`).  So the frozen one-step is **equivalent** to the
same statement with `Standing T` replaced by `RootClosedOn T` — the `Kˣ`-half of the conclusion is
free, and only the root-closure half carries content. -/

/-- The frozen one-step with the conclusion's `Standing T` split into its two halves; the free half
(`KEqTop`) is dropped. -/
def OneStepRootClosed : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ RootClosedOn T

/-- **The frozen one-step is exactly its root-closed form.** -/
theorem oneStepVFP_iff_rootClosed :
    Assembly.OneStepVFP (M := M) (N := N) ↔ OneStepRootClosed (M := M) (N := N) := by
  constructor
  · intro h S f hS m hmVF
    obtain ⟨T, g, hST, hagree, hmT, hT⟩ := h S f hS m hmVF
    exact ⟨T, g, hST, hagree, hmT, (standing_iff_rootClosedOn T).mp hT |>.2⟩
  · intro h S f hS m hmVF
    obtain ⟨T, g, hST, hagree, hmT, hT⟩ := h S f hS m hmVF
    exact ⟨T, g, hST, hagree, hmT,
      (standing_iff_rootClosedOn T).mpr ⟨M5.KEqTop_mono hST hS.1, hT⟩⟩

/-- The root-hull embedding obligation implies the root-closed form of the slot. -/
theorem oneStepRootClosed_of_rootHullEmbedding
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      RootHullEmbedding (M := M) (N := N) S f m) :
    OneStepRootClosed (M := M) (N := N) := by
  intro S f hS m hmVF
  obtain ⟨g, hagree⟩ := h S f hS m hmVF
  exact ⟨rootHull S m, g, le_rootHull S m, hagree, mem_rootHull_self S m,
    rootClosedOn_rootHull S m⟩

end Slots

end SpecialTransformations.Milestone0.Case35Hull

namespace SpecialTransformations.Milestone0.Case35Hull

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]


/-! ## 5. The exponent-one branch, stated at the corrected strength

The merged `QE/Case35Slot.lean` states the not-separated branch as
`Case35.NotSeparatedBranch`, whose hypothesis is `Case35.RVOldClass S m` and whose conclusion is
`M5L.ResidualClasses S T`.  Two machine-checked facts make that shape unusable as *the* obligation,
and the replacement below is what survives.

1. **The hypothesis is free.**  `rvOldClass_of_rv_mem` shows `Case35.RVOldClass S m` follows from
   the slot's own hypothesis `iRv m ∈ S` (with `m ≠ 0`), via
   `Case35.notSeparated_class_form_concl_witness`; and under `Standing S` plus
   `Assembly.IsVFGen S` the *converse* holds too (`Case35.notSeparated_iff_RVOldClass`).  So the
   exponent-one hypothesis is exactly the slot's hypothesis at the VF-generated points, and
   carries no information of its own.
2. **The class conclusion is refutable at admissible points.**
   `Case35.not_residualClasses_of_perturbation`: if `m = y + ε` with `y ∈ S ∩ VF` and `ε` of a class
   that is not an old class, then **no** `T ⊇ S ∪ {m}` satisfies `ResidualClasses S T`, while the
   slot's hypotheses (`Standing S`, `iVF m`, `iRv m ∈ S`, `¬ Separated S m`) all hold
   (`Case35.perturbation_rv_mem`).

The conclusion that survives is `RootHullEmbedding`: no class control at all, only the embedding of
the *root hull*, whose `Standing` is a theorem (§3). -/

section Branch

variable {N : Type} [LRV.Structure N] [hN : N ⊨ Axioms.ACVF]

/-- The exponent-one hypothesis of the branch is implied by the slot's own hypothesis. -/
theorem rvOldClass_of_rv_mem {S : LRV.Substructure M} {m : M} (hmVF : iVF m)
    (hm0 : m ≠ iVFZero) (hmrv : iRv m ∈ S) : Case35.RVOldClass S m :=
  Case35.notSeparated_class_form_concl_witness hmVF hm0 hmrv

/-- Under `Standing S` and VF-generation, the exponent-one hypothesis is *exactly* the slot's
(`¬ M5L.Separated S m`). -/
theorem rvOldClass_iff_notSeparated {S : LRV.Substructure M} (hS : Assembly.Standing S)
    (hgen : Assembly.IsVFGen S) {m : M} (hmVF : iVF m) (hm0 : m ≠ iVFZero) (hmrv : iRv m ∈ S) :
    Case35.RVOldClass S m ↔ ¬ M5L.Separated S m :=
  (Case35.notSeparated_iff_RVOldClass hS hgen hmVF hm0 hmrv).symm

/-- **The surviving not-separated branch statement.**  Hypothesis: the slot's, in its exponent-one
form (`Case35.RVOldClass`, which is free) — kept for fidelity to the paper's `lift:divisible:hull`
branch.  Conclusion: the embedding of the root hull, i.e. *only* the realisation half. -/
def NotSeparatedBranchRealise : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
    iRv m ∈ S → Case35.RVOldClass S m → RootHullEmbedding (M := M) (N := N) S f m

/-- **The exponent-one branch implies the frozen not-separated slot.** -/
theorem caseNotSeparated_of_branchRealise (hb : NotSeparatedBranchRealise (M := M) (N := N)) :
    M4Cases.CaseNotSeparated (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hnot
  by_cases hm0 : m = iVFZero
  · exact ⟨S, f, le_rfl, fun _ => rfl, by
      rw [hm0]
      exact S.fun_mem Fn.vfZero (fun i => i.elim0) (fun i => i.elim0), hS⟩
  · obtain ⟨g, hagree⟩ := hb S f hS m hmVF hmrv (rvOldClass_of_rv_mem hmVF hm0 hmrv)
    exact ⟨rootHull S m, g, le_rootHull S m, hagree, mem_rootHull_self S m,
      standing_rootHull hS m⟩

/-- The branch statement, in the paper's `iRv m ∈ S`-free shape (the slot's hypotheses minus the
case split). -/
theorem cases_of_rootHullEmbedding' (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
    Assembly.Standing S → ∀ m : M, iVF m → RootHullEmbedding (M := M) (N := N) S f m) :
    M4Cases.Cases (M := M) (N := N) :=
  cases_of_rootHullEmbedding h

/-! ## 5b. The paper's Lemma 3.5 hypothesis is a *new-`rv`* configuration

`Case35.not_rootStepHyp_of_notSeparated` shows the paper's `lift:divisible:hull` hypothesis
(`m^n = a ∈ VF(Ŝ)`, `vv(m^i) ∉ Γ(Ŝ)` for `0 < i < n`, `n ≥ 2`) is inconsistent with the
not-separated slot.  The theorem below is the sharp form of that: the paper's hypothesis *itself*
forces `rv(m) ∉ S`, i.e. it is a `M4Cases.CaseNewRV` configuration.  So the exponent-one form
`Case35.RVOldClass` really is the whole of the not-separated branch, and the paper's Lemma 3.5
belongs to the other slot. -/

/-- **`iRv m ∈ S` kills the paper's separation hypothesis** at `n ≥ 2`, provided `S` is
VF-generated.  (VF-generation is essential: `M5L.Separated` quantifies over `VF`-elements of `S`,
and `iRv m ∈ S` alone gives only an `RV`-element, not a `VF`-one.) -/
theorem not_mem_rv_of_separatedBelow {S : LRV.Substructure M} (hgen : Assembly.IsVFGen S)
    {m : M} (hmVF : iVF m) (hm0 : m ≠ iVFZero) {n : ℕ} (hn : 2 ≤ n)
    (hbelow : Case35.SeparatedBelow S m n) : iRv m ∉ S := by
  intro hmrv
  have hmrv0 : iRv m ≠ iRVZero := Case35.rv_mem_ne hmVF hm0
  have hrvRV : iRV (iRv m) := rv_mem hM hmVF
  rcases hgen (iRv m) hmrv hrvRV with ⟨y, hyS, hyVF, hyr⟩ | hz
  · have hy0 : y ≠ iVFZero := fun h => hmrv0 (by rw [← hyr, h, rv_zero_eq hM])
    have hcls : Transc.Cls (iRVMul (Transc.rvpow (iRv m) 1) (iRv (iVFOne : M))) (iRv y) := by
      rw [Case35.transc_rvpow_one hrvRV, rv_one hM,
        MulNormalForm.rv_mul_one_right hM hrvRV, ← hyr]
      exact Transc.cls_refl hM (rv_mem hM hyVF)
    exact hbelow 1 (by norm_num) (by omega) iVFOne y (Transfer.vf_one_mem (M := M) hM) hyVF
      (Case35.vfOne_mem_sub S) hyS (fun h => RVCalc.vf_zero_ne_one hM h.symm) hy0 hcls
  · exact hmrv0 hz

/-- **The paper's Lemma-3.5 configuration is a `CaseNewRV` point.**  Combined with
`Case35.not_rootStepHyp_of_standing` (the `m^n = a` shape is impossible at `Standing S` when
`iRv m ∈ S`), this says: at a VF-generated standing `S`, the paper's `lift:divisible:hull`
hypothesis is exactly the `rv m ∉ S` regime, i.e. the new-`rv` slot. -/
theorem lemma35_hyp_is_newRV {S : LRV.Substructure M} (hgen : Assembly.IsVFGen S) {m : M}
    (hmVF : iVF m) (hm0 : m ≠ iVFZero) {n : ℕ} (hn : 2 ≤ n)
    (hbelow : Case35.SeparatedBelow S m n) : iRv m ∉ S :=
  not_mem_rv_of_separatedBelow hgen hmVF hm0 hn hbelow

/-- **The perturbation obstruction bites at genuine `CaseNotSeparated` points.**  If `m = y + ε` with
`y ∈ S ∩ VF` strictly dominating `ε ∈ VF`, and `rv ε` is not an old class, then *all* the slot's
hypotheses hold (`Standing S` gives `KEqTop S`; `perturbation_rv_mem` gives `iRv m ∈ S`;
`notSeparated_of_RVOldClass` gives `¬ Separated S m` because `iRv m ∈ S` and `S` is VF-generated)
and yet `M5L.ResidualClasses S T` fails for **every** `T ⊇ S` containing `m`.  So
`Case35.NotSeparatedBranch`'s conclusion is not available at admissible points: the branch has to
conclude the embedding, not the class control. -/
theorem perturbation_notSeparated_without_classControl {S : LRV.Substructure M}
    (hK : Assembly.KEqTop S) (hgen : Assembly.IsVFGen S) {y ε : M} (hyS : y ∈ S) (hyVF : iVF y)
    (heVF : iVF ε) (hle : Transc.VLe y ε) (hnle : ¬ Transc.VLe ε y)
    (hm0 : iVFAdd y ε ≠ iVFZero)
    (hnew : ∀ s : M, s ∈ S → iRV s →
      ¬ Transc.Cls (iRv (iVFAdd (iVFAdd y ε) (iVFNeg y))) s) :
    iVF (iVFAdd y ε) ∧ iRv (iVFAdd y ε) ∈ S ∧ ¬ M5L.Separated S (iVFAdd y ε) ∧
      ∀ T : LRV.Substructure M, S ≤ T → iVFAdd y ε ∈ T → ¬ M5L.ResidualClasses S T := by
  have hmVF : iVF (iVFAdd y ε) := Transfer.vf_add_mem hM hyVF heVF
  have hmrv : iRv (iVFAdd y ε) ∈ S := Case35.perturbation_rv_mem hK hyS hyVF heVF hle hnle
  have hnot : ¬ M5L.Separated S (iVFAdd y ε) :=
    Case35.notSeparated_of_RVOldClass hgen hmVF (rvOldClass_of_rv_mem hmVF hm0 hmrv)
  refine ⟨hmVF, hmrv, hnot, fun T hST hmT => ?_⟩
  have heps0 : iVFAdd (iVFAdd y ε) (iVFNeg y) ≠ iVFZero := by
    intro h0
    have hcls : Transc.Cls (iRv (iVFAdd (iVFAdd y ε) (iVFNeg y))) iRVZero := by
      rw [h0, rv_zero_eq hM]
      exact Transc.cls_refl hM (rv_zero_mem hM)
    exact hnew iRVZero (M5L.rvZero_mem_sub S) (rv_zero_mem hM) hcls
  exact Case35.not_residualClasses_of_perturbation hST hmT hyS hmVF hyVF heps0 hnew

/-! ## 5c. The exponent-one branch in the tree's inverse-free *ratio* form

The merged `QE/OldRVClaim.lean` (`M5LOldRV`) replaces `M5L.ResidualClasses` by
`M5LOldRV.RatioInS S y` (`y · rv s ~ rv t` with `s, t ∈ S ∩ VF` nonzero), which needs no inverse in
`S`.  The theorem below shows that `Case35.monomial_class_control` — the exponent-one branch's
`Γ`-fragment — produces exactly that form, for every monomial.

What it does **not** produce is the *sum* step: `RatioInS` is not closed under sums (the class of
`p + q` is not a function of the classes of `p` and `q` when the two classes agree), and the
separated slot's escape (`M5L.separated_dis` giving `hdis`, then `M5L.cls_vsum_monomial`) is
unavailable at `CaseNotSeparated`.  That is the precise place where the branch's Claim (⋆) fails
(`perturbation_notSeparated_without_classControl`), and why §3–§4 route the slot through the root
hull instead. -/

/-- **The monomial fragment of the exponent-one branch, in the inverse-free ratio form.** -/
theorem monomial_ratio {S : LRV.Substructure M} (hgen : Assembly.IsVFGen S) {m u u' : M}
    (hmVF : iVF m) (huS : u ∈ S) (hu'S : u' ∈ S) (hu : iRV u) (hu' : iRV u')
    (hu0 : u ≠ iRVZero) (hu'0 : u' ≠ iRVZero)
    (hcls : Transc.Cls (iRVMul (iRv m) u) u') {b : M} (hbVF : iVF b) (hbS : b ∈ S)
    (hb0 : b ≠ iVFZero) (j : ℕ) :
    M5LOldRV.RatioInS S (iRv (iVFMul b (Transc.vpow m j))) := by
  obtain ⟨s, hsS, hsRV, hs0, hcls'⟩ :=
    Case35.monomial_class_control hmVF huS hu'S hu hu' hu0 hu'0 hcls hbVF hbS hb0 j
  have hpowS : Transc.rvpow u j ∈ S := Case35.rvpow_mem_sub_of_mem S huS j
  have hpowRV : iRV (Transc.rvpow u j) := Transc.iRV_rvpow hM hu j
  have hpowNZ : Transc.rvpow u j ≠ iRVZero := Transc.rvpow_ne_zero hM hu hu0 j
  rcases hgen s hsS hsRV with ⟨t, htS, htVF, htr⟩ | hz
  swap
  · rw [hz] at hs0
    exact absurd rfl hs0
  rcases hgen (Transc.rvpow u j) hpowS hpowRV with ⟨w, hwS, hwVF, hwr⟩ | hz'
  swap
  · rw [hz'] at hpowNZ
    exact absurd rfl hpowNZ
  refine ⟨w, t, hwVF, htVF, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hwr]; exact hpowS
  · rw [htr]; exact hsS
  · intro h0
    exact hpowNZ (by rw [← hwr, h0, rv_zero_eq hM])
  · intro h0
    exact hs0 (by rw [← htr, h0, rv_zero_eq hM])
  · rw [hwr, htr]
    exact hcls'

/-! ## 6. Stress tests -/

/-- **The tree's class-control route implies the new invariant** — so `RootClosedOn` is not a
strengthening of what the merged `Γ`-machinery already establishes, only a weaker packaging of it. -/
theorem standing_of_residualClasses' {S T : LRV.Substructure M} (hST : S ≤ T)
    (hS : Assembly.Standing S) (hres : M5L.ResidualClasses S T) : Assembly.Standing T :=
  M5L.standing_of_ClassControl hST hS hres

/-- **The base of the hull is `closure (S ∪ {m})`**: the hull is the paper's `⟨Ŝ,e⟩` plus its
divisible hull, not an unrelated object. -/
theorem stage_zero_eq (S : LRV.Substructure M) (m : M) :
    stage S m 0 = Substructure.closure LRV ((S : Set M) ∪ {m}) := rfl

/-- **`rootHull ⊤ m = ⊤`**: on the whole model the hull is the model. -/
theorem rootHull_top (m : M) : rootHull (⊤ : LRV.Substructure M) m = ⊤ :=
  le_antisymm le_top (le_rootHull ⊤ m)

/-- **The residual is satisfiable at `S = ⊤`**: at the top slot, `f` itself is the required
embedding.  So `NotSeparatedBranchRealise`'s conclusion is not contradictory at the slot which is
always available, and `rootHull` does not add anything there. -/
theorem rootHullEmbedding_top {N : Type} [LRV.Structure N]
    (f : (⊤ : LRV.Substructure M) ↪[LRV] N) (m : M) :
    RootHullEmbedding (M := M) (N := N) (⊤ : LRV.Substructure M) f m := by
  refine ⟨f.comp (Substructure.inclusion (rootHull_top (M := M) m).le), fun x => ?_⟩
  exact congrArg f (Subtype.ext rfl)

/-- **The residual is satisfiable outright at `N = M`**: with `M` as the target and `f` the
inclusion, the identity is the required embedding.  So the residual is not a contradiction in
general — it fails at most for the saturation content of the pair `(M, N)`. -/
theorem rootHullEmbedding_self (S : LRV.Substructure M) (m : M) :
    RootHullEmbedding (M := M) (N := M) S (Substructure.subtype S) m :=
  ⟨Substructure.subtype (rootHull S m), fun _ => rfl⟩

/-- **The residual is implied by Proposition 3.9 at the pair** — a global extension restricts to the
root hull, so the new branch is *below* the paper's conclusion and not an unrelated assertion. -/
theorem rootHullEmbedding_of_global
    (hglob : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ∃ g : M ↪[LRV] N,
      ∀ x : S, g (x : M) = f x)
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M) :
    RootHullEmbedding (M := M) (N := N) S f m := by
  obtain ⟨g, hg⟩ := hglob S f
  exact ⟨g.domRestrict (rootHull S m), fun x => hg x⟩

/-- **Cardinality is unchanged.**  `Standing S` already forces `#Kˣ(M) ≤ #N` through any embedding
of `S`; passing to the root hull does not weaken that, because `S ≤ rootHull S m` gives an
embedding of `S` from any embedding of the hull. -/
theorem rootHullEmbedding_units_size {S : LRV.Substructure M} {f : S ↪[LRV] N} {m : M}
    (hS : Assembly.Standing S) (h : RootHullEmbedding (M := M) (N := N) S f m) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N :=
  M4Cases.standing_forces_units_size S f hS

/-- **`Standing ⊤` recovered through §1** — the invariant agrees with the tree's at `⊤`. -/
theorem standing_top_via_rootClosed : Assembly.Standing (⊤ : LRV.Substructure M) :=
  (standing_iff_rootClosedOn _).mpr
    ⟨fun _ _ => trivial, rootClosedOn_top⟩

end Branch

/-! ## 7. The gated route: `M4Cases.OneStepPaper` from the embedding obligation -/

/-- **The frozen one-step at the paper's pairs, from the root-hull embedding obligation.**  Since
`oneStepVFP_of_rootHullEmbedding` needs no gate of its own, the paper's `PaperHyp` is never used. -/
theorem oneStepPaper_of_rootHullEmbedding
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
        RootHullEmbedding (M := M) (N := N) S f m) :
    M4Cases.OneStepPaper :=
  fun M N _ _ _ _ _ => oneStepVFP_of_rootHullEmbedding (h M N)

/-- **The frozen target from the five ledger inputs and the root-hull embedding obligation.**
`M4Cases.paper_theorem_2_3_sat_of_cases` with its case ledger supplied by §4; the paper's
`PaperHyp` gate is never touched. -/
theorem paper_theorem_2_3_sat_of_rootHullEmbedding
    (hShoen : M7Paper.ShoenfieldTestSat)
    (h1 : M5Ledger.LedgerInput1P) (h2 : M5Ledger.LedgerInput2)
    (h3 : M5Ledger.LedgerInput3P) (h4 : M5Ledger.LedgerInput4P) (h5 : M5Ledger.LedgerInput5P)
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
        RootHullEmbedding (M := M) (N := N) S f m) :
    HasQE Axioms.ACVF :=
  M4Cases.paper_theorem_2_3_sat_of_cases hShoen h1 h2 h3 h4 h5
    (fun M N _ _ _ _ _ => cases_of_rootHullEmbedding (h M N))

/-! ## 8. The residual, named, with its status -/

/-- **THE RESIDUAL of Lemma 3.5's surviving branch (and, by §4, of the whole one-step).**

For every pair of models, every standing `S`, every `L_RV`-monomorphism `f : S ↪[LRV] N` and every
`m ∈ VF(M)`: `f` extends to the root hull of `S` at `m`.

Status (machine-checked in this file):
* it is **sufficient** for the frozen `Assembly.OneStepVFP` (`oneStepVFP_of_rootHullEmbedding`), for
  `M4Cases.OneStepPaper` (`oneStepPaper_of_rootHullEmbedding`), and for the frozen target given the
  five ledger inputs (`paper_theorem_2_3_sat_of_rootHullEmbedding`);
* it is **consistent**: implied by Proposition 3.9 at the pair (`rootHullEmbedding_of_global`), and
  satisfied outright for `N = M` (`rootHullEmbedding_self`) and at `S = ⊤`
  (`rootHullEmbedding_top`);
* it contains **no `Γ`-content**: no `ResidualClasses`, no `M5L.Separated`, no `RVOldClass`, no
  `M5L.VFInvClosedOn`, no `IsVFGen`, no `QuotExpansions`; `Standing (rootHull S m)` is a theorem
  (`standing_rootHull`) and `rootHull S m ∋ m` is a theorem (`mem_rootHull_self`).

So what is open is *exactly* the saturation / atomic-realisation half of Lemmas 3.4–3.8. -/
def RootHullRealisation : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      RootHullEmbedding (M := M) (N := N) S f m

/-- The named residual is exactly the hypothesis of `oneStepPaper_of_rootHullEmbedding`. -/
theorem oneStepPaper_of_rootHullRealisation (h : RootHullRealisation) : M4Cases.OneStepPaper :=
  oneStepPaper_of_rootHullEmbedding h

/-- The named residual also gives the frozen target, given the five ledger inputs. -/
theorem paper_theorem_2_3_of_rootHullRealisation (h : RootHullRealisation)
    (hShoen : M7Paper.ShoenfieldTestSat)
    (h1 : M5Ledger.LedgerInput1P) (h2 : M5Ledger.LedgerInput2)
    (h3 : M5Ledger.LedgerInput3P) (h4 : M5Ledger.LedgerInput4P) (h5 : M5Ledger.LedgerInput5P) :
    HasQE Axioms.ACVF :=
  paper_theorem_2_3_sat_of_rootHullEmbedding hShoen h1 h2 h3 h4 h5 h

end SpecialTransformations.Milestone0.Case35Hull

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.Case35Hull.cls_mul_unit_right
#print axioms SpecialTransformations.Milestone0.Case35Hull.gammaDivisible_of_rootClosedOn
#print axioms SpecialTransformations.Milestone0.Case35Hull.rootClosedOn_of_gammaDivisible
#print axioms SpecialTransformations.Milestone0.Case35Hull.standing_iff_rootClosedOn
#print axioms SpecialTransformations.Milestone0.Case35Hull.exists_cls_root
#print axioms SpecialTransformations.Milestone0.Case35Hull.rootClosedOn_top
#print axioms SpecialTransformations.Milestone0.Case35Hull.stage_le_succ
#print axioms SpecialTransformations.Milestone0.Case35Hull.stage_mono
#print axioms SpecialTransformations.Milestone0.Case35Hull.le_rootHull
#print axioms SpecialTransformations.Milestone0.Case35Hull.mem_rootHull_self
#print axioms SpecialTransformations.Milestone0.Case35Hull.mem_rootHull
#print axioms SpecialTransformations.Milestone0.Case35Hull.rootClosedOn_rootHull
#print axioms SpecialTransformations.Milestone0.Case35Hull.standing_rootHull
#print axioms SpecialTransformations.Milestone0.Case35Hull.caseNotSeparated_of_rootHullEmbedding
#print axioms SpecialTransformations.Milestone0.Case35Hull.caseSeparated_of_rootHullEmbedding
#print axioms SpecialTransformations.Milestone0.Case35Hull.caseNewRV_of_rootHullEmbedding
#print axioms SpecialTransformations.Milestone0.Case35Hull.cases_of_rootHullEmbedding
#print axioms SpecialTransformations.Milestone0.Case35Hull.oneStepVFP_of_rootHullEmbedding
#print axioms SpecialTransformations.Milestone0.Case35Hull.rvOldClass_of_rv_mem
#print axioms SpecialTransformations.Milestone0.Case35Hull.rvOldClass_iff_notSeparated
#print axioms SpecialTransformations.Milestone0.Case35Hull.caseNotSeparated_of_branchRealise
#print axioms SpecialTransformations.Milestone0.Case35Hull.rootHull_top
#print axioms SpecialTransformations.Milestone0.Case35Hull.rootHullEmbedding_top
#print axioms SpecialTransformations.Milestone0.Case35Hull.rootHullEmbedding_self
#print axioms SpecialTransformations.Milestone0.Case35Hull.rootHullEmbedding_of_global
#print axioms SpecialTransformations.Milestone0.Case35Hull.rootHullEmbedding_units_size
#print axioms SpecialTransformations.Milestone0.Case35Hull.standing_top_via_rootClosed
#print axioms SpecialTransformations.Milestone0.Case35Hull.oneStepPaper_of_rootHullEmbedding
#print axioms SpecialTransformations.Milestone0.Case35Hull.not_mem_rv_of_separatedBelow
#print axioms SpecialTransformations.Milestone0.Case35Hull.lemma35_hyp_is_newRV
#print axioms SpecialTransformations.Milestone0.Case35Hull.perturbation_notSeparated_without_classControl
#print axioms SpecialTransformations.Milestone0.Case35Hull.rootClosedOn_of_close
#print axioms SpecialTransformations.Milestone0.Case35Hull.standing_of_residualClasses'
#print axioms SpecialTransformations.Milestone0.Case35Hull.oneStepVFP_iff_rootClosed
#print axioms SpecialTransformations.Milestone0.Case35Hull.oneStepRootClosed_of_rootHullEmbedding
#print axioms SpecialTransformations.Milestone0.Case35Hull.monomial_ratio
#print axioms SpecialTransformations.Milestone0.Case35Hull.paper_theorem_2_3_sat_of_rootHullEmbedding
#print axioms SpecialTransformations.Milestone0.Case35Hull.oneStepPaper_of_rootHullRealisation
#print axioms SpecialTransformations.Milestone0.Case35Hull.paper_theorem_2_3_of_rootHullRealisation
