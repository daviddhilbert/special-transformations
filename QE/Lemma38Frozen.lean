/-
# Lemma 3.8 (`lift:value:full`) at the frozen level: which slot is it, and what is left

Member `m6`, swarm `smw2ox51x`, direction r6.

## What this file settles (machine-checked)

The frozen ledger `M4Cases.Cases` has three slots.  The paper's Lemma 3.8 is *not* the new-`rv` slot
(`M4Cases.CaseNewRV = M5.OneStepRVNew`), whose very hypothesis is `iRv m ∉ S`: Lemma 3.8's standing
hypothesis is `rv(e) ∈ RV(S) ∖ RV(Ŝ)` (`qe.tex`, the `sta` block before `lift:all:root`), i.e.
`iRv m ∈ S` in the frozen encoding.  This file proves the precise correspondence:

* `Hyp S m` — Lemma 3.8's case hypotheses at the frozen level: `m ∈ VF(M)`, `iRv m ∈ S`,
  the separation condition `M5L.Separated S m` (`vv(m^k) ∉ Γ(Ŝ)` for `k > 0`), `m ≠ 0` (the paper's
  `rv(e) ≠ 0`), and `¬ iUnits (iRv m)` (3.8's `vv(e) ∉ Γ(Ŝ)`, so `e` is not a unit).
* `Slot` — the frozen statement of Lemma 3.8: from `Hyp S m` and `Standing S`, produce
  `T ⊇ S ∋ m` with an embedding `g : T ↪[LRV] N` extending `f` and `Standing T`.
* **`slot_iff_caseSeparated`** — `Slot ↔ M4Cases.CaseSeparated`.  So Lemma 3.8's frozen home is
  exactly the `separated` slot of `M4Cases.Cases` (which `QE/Case34Slot.lean` showed cannot be the
  home of Lemmas 3.4/3.6, whose units are never separated).  Two of the five conjuncts of `Hyp` are
  thereby *derived*, not extra assumptions: `not_unit_derived` (from `not_separated_of_units`) and
  `ne_zero` (the `m = 0` case is discharged directly in `caseSeparated_of_slot`).
* **`slot_of_control`** — the slot follows from Claim (⋆) in `Γ`-class form
  (`M5L.ResidualClasses S T`), through the tree's `M5L.standing_of_ClassControl`.
* **`slot_of_struct`** — the same, with `ResidualClasses` *discharged* by the merged algebraic
  fragment `M5L.standing_of_paper_hypotheses` (whose `RV` content is
  `M5L.ResidualClasses_of_VFGen = Claim (⋆)`): given the extension `T` with `Assembly.IsVFGen T` and
  `M5L.QuotExpansions S T m`, plus `M5L.VFInvClosedOn S`, the slot holds.
* **`StructResidual`** — the named residual: the extension carrying the two field-theoretic facts of
  `⟨Ŝ, m⟩`.  `slot_of_struct` says this plus `VFInvClosedOn` is *all* that is missing.
* **`slot_at_relGate`** — at the honest gate (`M5Shoenfield.Input5R` at `relGate`), the slot is
  *supplied*, not assumed (`QE/NewRVGlue.lean`'s total-extension route).  So the final theorem never
  needs `Slot` as an extra hypothesis.

## What this file does not do (the isolated residuals)

1. `M5L.VFInvClosedOn S` is *not* a consequence of `Standing S` (the frozen language `L_RV` has no
   inverse on the `VF` sort; `QE/OneStepCases.lean` §2).  It is owed by 3.4/3.5/3.6 as well, so it is
   a standing gap of the whole `rv`-old side, not a specific debt of 3.8.
2. `StructResidual`: `T` must contain the closure of `S ∪ {m}` (so `IsVFGen T` is the paper's
   Remark 3.1 and `QuotExpansions` is `qe.tex:645` — both about the *closed* substructure, provable
   in principle from the structure of `L_RV`-terms) *and* the embedding `g : T ↪[LRV] N` extending
   `f`.  The embedding half is realisation, not algebra: at an Archimedean target carrying the
   infinitesimal configuration, `M5.OneStepRVNew` — hence every slot of `Cases`
   (`QE/NewRVGlue.lean`'s `not_cases_of_infinitesimal`) — fails.
3. **No Engler–Prestel inequality occurs in any statement of this file.**  `Hyp`, `Slot`,
   `StructResidual` are built from `iVF`, `iRv`, `M5L.Separated`, `Assembly.Standing`,
   `Assembly.IsVFGen`, `M5L.QuotExpansions`, `M5L.VFInvClosedOn` only.  The *algebraic* content of 3.8 (`Claim (⋆)`'s two halves)
   is `QE/Lemma38RV.lean` + `QE/Case38Value.lean`, and `.ultramath/smw2ox51x/m6/Lemma38EP.lean`
   proves their hypothesis list EP-free (deriving Lemma 3.8's "and hence `e` is transcendental" from
   `Γ(Ŝ)` divisible by the minimal-polynomial argument, not from the dimension inequality).  So the
   answer to the flagged `MILESTONES.md` question is: m1 is right, Lemma 3.8 consumes no EP
   3.3.4/3.4.3; the comment at `QE/Lemma38RV.lean:71`'s "fundamental inequality" refers to a
   *derivation Yin does not make at 3.8* (his 3.8 text cites only Lemma 3.7), and the tree had
   recorded that derivation as unformalized rather than using it as a hypothesis.

No `sorry`, no `axiom`, no `native_decide`; axiom audit at the end.
-/
import NewRVGlue
import NewRVClaim
import Case34Slot
import InterfaceClosure
import Bookkeeping

set_option autoImplicit false
set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Milestone0.M6Lemma38

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-! ## 1. Lemma 3.8's case hypotheses at the frozen level -/

/-- **Lemma 3.8's hypotheses**, frozen: `m` is a new `VF`-element whose `rv`-class is already in `S`
(the paper's `rv(e) ∈ RV(S) ∖ RV(Ŝ)`), the separation condition `vv(m^k) ∉ Γ(Ŝ)` for `k > 0`
(`M5L.Separated`), `m ≠ 0` and `m` not a unit (`vv(e) ∉ Γ(Ŝ)`). -/
structure Hyp (S : LRV.Substructure M) (m : M) : Prop where
  /-- `m` is a `VF`-sort element. -/
  vf : iVF m
  /-- the paper's `rv(e) ∈ RV(S)`: the `rv`-class is old. -/
  rvmem : iRv m ∈ S
  /-- the paper's separation hypothesis `vv(m^k) ∉ Γ(Ŝ)` for `0 < k`. -/
  sep : M5L.Separated S m
  /-- the paper's `rv(e) ≠ 0`. -/
  ne_zero : m ≠ iVFZero
  /-- the paper's `vv(e) ∉ Γ(Ŝ)`: a unit's class *is* in `Γ(Ŝ)`, so `e` is not a unit. -/
  not_unit : ¬ iUnits (iRv m)

/-- **Lemma 3.8 (`lift:value:full`)) at the frozen level**: Claim (⋆) — the extension `f*` and
`Standing T`.  This is the paper's Claim (⋆) for 3.8's case `rv(e) ∈ RV(S) ∖ RV(Ŝ)`. -/
def Slot : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, Hyp S m →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T

/-! ## 2. The slot is exactly the frozen `separated` slot -/

/-- Any `Hyp`-configuration is a `M4Cases.CaseSeparated` configuration (drop hypotheses). -/
theorem slot_of_caseSeparated (h : M4Cases.CaseSeparated (M := M) (N := N)) :
    Slot (M := M) (N := N) :=
  fun S f hS m hm => h S f hS m hm.vf hm.rvmem hm.sep

/-- Conversely every `CaseSeparated` configuration is (up to the trivial `m = 0` case) a `Hyp`
configuration: `¬ iUnits (iRv m)` is *derived* from separation by `not_separated_of_units`, and
`m ≠ 0` is the case `m = 0`, where `T = S` and `g = f` work. -/
theorem caseSeparated_of_slot (h : Slot (M := M) (N := N)) :
    M4Cases.CaseSeparated (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hsep
  by_cases hm0 : m = iVFZero
  · subst hm0
    exact ⟨S, f, le_rfl, fun _ => rfl, M3Slot.vfZero_mem_sub S, hS⟩
  · exact h S f hS m
      ⟨hmVF, hmrv, hsep, hm0, fun hu => M5P1.not_separated_of_units hmVF hu hsep⟩

/-- **Lemma 3.8's frozen home is the `separated` slot of `M4Cases.Cases`.** -/
theorem slot_iff_caseSeparated :
    Slot (M := M) (N := N) ↔ M4Cases.CaseSeparated (M := M) (N := N) :=
  ⟨caseSeparated_of_slot, slot_of_caseSeparated⟩

/-- The `¬ iUnits (iRv m)` conjunct of `Hyp` is *derived*, not an extra assumption: a unit is never
separated (`QE/Case34Slot.lean`).  Recorded so that `Hyp` is visibly the paper's hypothesis list and
nothing more. -/
theorem not_unit_derived {S : LRV.Substructure M} {m : M} (hmVF : iVF m)
    (hsep : M5L.Separated S m) : ¬ iUnits (iRv m) :=
  fun hu => M5P1.not_separated_of_units hmVF hu hsep

/-! ## 3. The slot from Claim (⋆) in `Γ`-class form -/

/-- **The frozen statement of Lemma 3.8 from Claim (⋆)**: it suffices to produce the extension with
the class computation `M5L.ResidualClasses S T` (every `RV`-element of `T` is class-equal to an
element of `S`, i.e. `RV(⟨Ŝ,m⟩) = ⟨RV(Ŝ), rv m⟩ ⊆ RV(S)` in the frozen vocabulary).  `Standing T`
then follows from the tree's `M5L.standing_of_ClassControl`. -/
theorem slot_of_control
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, Hyp S m →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ M5L.ResidualClasses S T) :
    Slot (M := M) (N := N) := by
  intro S f hS m hm
  obtain ⟨T, g, hST, hagree, hmT, hcc⟩ := h S f hS m hm
  exact ⟨T, g, hST, hagree, hmT, M5L.standing_of_ClassControl hST hS hcc⟩

/-- **The frozen ledger with 3.8's own hypotheses in the `separated` slot.** -/
theorem cases_of_slot (h : Slot (M := M) (N := N))
    (hnotsep : M4Cases.CaseNotSeparated (M := M) (N := N))
    (hnew : M4Cases.CaseNewRV (M := M) (N := N)) : M4Cases.Cases (M := M) (N := N) where
  separated := slot_iff_caseSeparated.mp h
  notSeparated := hnotsep
  newRV := hnew

/-! ## 4. The named residual, and the slot from the merged algebraic fragment -/

/-- **The residual of Lemma 3.8 at the frozen level**: a `T ⊇ S` containing `m`, with an embedding
`g : T ↪[LRV] N` extending `f`, and the two field-theoretic facts the paper's `⟨Ŝ, m⟩` has —
`Assembly.IsVFGen T` (Remark 3.1: `L_v` and `L_RV` are interdefinable, so `⟨Ŝ,m⟩` is `VF`-generated)
and `M5L.QuotExpansions S T m` (`qe.tex:645`: every nonzero `VF`-element of `⟨Ŝ,m⟩` is a quotient of
expansions `Σ bᵢ mⁱ` with `bᵢ ∈ S`).

The embedding half is *realisation* in `N` (saturation), not value theory: `QE/NewRVGlue.lean`'s
`not_oneStepRVNew_of_infinitesimal` and `not_cases_of_infinitesimal` show that at an Archimedean
target carrying the infinitesimal configuration no slot of `Cases` can be produced. -/
def StructResidual : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, Hyp S m →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧
        Assembly.IsVFGen T ∧ M5L.QuotExpansions S T m

/-- **Lemma 3.8 from the residual plus `VFInvClosedOn`.**  Given the extension with the two
field-theoretic facts, the merged fragment `M5L.standing_of_paper_hypotheses` (whose `RV` content is
`M5L.ResidualClasses_of_VFGen`, i.e. Claim (⋆)) supplies `Standing T`.  So the *entire* algebraic
content of 3.8 is already merged; what `StructResidual` adds is the extension and the structural
description of the closed substructure. -/
theorem slot_of_struct
    (hfinv : ∀ S : LRV.Substructure M, Assembly.Standing S → M5L.VFInvClosedOn S)
    (h : StructResidual (M := M) (N := N)) : Slot (M := M) (N := N) := by
  intro S f hS m hm
  obtain ⟨T, g, hST, hagree, hmT, hvfgen, hquot⟩ := h S f hS m hm
  exact ⟨T, g, hST, hagree, hmT,
    M5L.standing_of_paper_hypotheses hM hST hS (hfinv S hS) hm.vf hm.ne_zero hm.rvmem hm.sep
      hvfgen hquot⟩

/-- The `RF`-content of `StructResidual`'s field-theoretic facts, in the form in which the merged
fragment consumes them: at a `Standing S` the two facts give the class computation
`ResidualClasses S T` outright.  (Wiring of `M5L.ResidualClasses_of_VFGen`; included so that the
"which merged fragment does 3.8 consume" question has a machine-checked answer.) -/
theorem residualClasses_of_struct {S T : LRV.Substructure M} {m : M}
    (hS : Assembly.Standing S) (hfinv : M5L.VFInvClosedOn S) (hm : Hyp S m)
    (hvfgen : Assembly.IsVFGen T) (hquot : M5L.QuotExpansions S T m) :
    M5L.ResidualClasses S T :=
  M5L.ResidualClasses_of_VFGen hM hS.1 hfinv hm.vf hm.ne_zero hm.rvmem hm.sep hvfgen hquot

/-! ## 5. The slot is supplied at the honest gate

`cases_of_slot` records that `M4Cases.Cases` can be stated with `Slot` (Lemma 3.8's hypotheses) in
place of `M4Cases.CaseSeparated` — the two are equivalent by `slot_iff_caseSeparated`, so no slot of
the ledger needs re-stating; what 3.8 contributes to the ledger is the `separated` slot verbatim. -/

/-- **At the honest gate the slot is supplied, not assumed**: `M5Shoenfield.Input5R` (Marker's
saturated realisation at `relGate`) gives the extension at every `relGate` pair, hence every slot of
`M4Cases.Cases`, hence `Slot` by `slot_iff_caseSeparated`.  So a complete proof of `HasQE` never
needs Lemma 3.8's slot as an extra hypothesis. -/
theorem slot_at_relGate (h5 : M5Shoenfield.Input5R) (hR : M5Shoenfield.relGate M N) :
    Slot (M := M) (N := N) :=
  slot_of_caseSeparated (NewRVGlue.cases_at_relGate_of_input5R h5 hR).separated

/-- **3.8's slot plus the `¬ Separated` slot give the `rv`-old half of the frozen one-step.**  So the
ledger's `rv`-old side is `Slot` (= 3.8) together with `M4Cases.CaseNotSeparated` (= 3.4/3.5/3.6). -/
theorem oneStepRVOld_of_slot (h : Slot (M := M) (N := N))
    (hnotsep : M4Cases.CaseNotSeparated (M := M) (N := N)) :
    M5.OneStepRVOld (M := M) (N := N) :=
  M4Cases.oneStepRVOld_of_cases (slot_iff_caseSeparated.mp h) hnotsep

/-! ## 6. Stress tests -/

/-- **The frozen new-`rv` branch is not Lemma 3.8.**  `M5.OneStepRVNew`'s hypothesis is
`iRv m ∉ S`; `Hyp` contains `iRv m ∈ S`.  So no configuration is in both, and `CaseNewRV` cannot be
"3.8's slot": the paper's Claim (⋆) is `rv`-old control (`RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv(e)⟩ ⊆ RV(S)`), while
`CaseNewRV` asks for the phase transition (the divisible hull of `Γ(S) + ℤ·vv(m)` inside `T`,
`QE/NewRVGlue.lean`'s `oneStepRVNew_iff_gammaDivisible`). -/
theorem hyp_and_newRV_incompatible {S : LRV.Substructure M} {m : M} (hm : Hyp S m)
    (hnew : iRv m ∉ S) : False :=
  hnew hm.rvmem

/-- **`Hyp` is not satisfiable at `S = ⊤`**: a `VF`-element of `⊤` is never separated
(`QE/NewRVClaim.lean`'s `not_separated_top`, via `rv`-surjectivity).  So the slot is not the
conclusion at the trivial substructure — the case analysis is needed at genuinely new elements. -/
theorem not_hyp_top {m : M} (hmVF : iVF m) (hm0 : m ≠ iVFZero) :
    ¬ Hyp (⊤ : LRV.Substructure M) m :=
  fun hm => M5LNewRV.not_separated_top hmVF hm0 hm.sep

/-- **3.8's slot is empty over a `VF`-generated base** — in particular over the paper's own base
`Ŝ = ⟨VF(S)⟩` (`qe.tex`'s standing assumption).  `QE/Bookkeeping.lean`'s `not_separated_of_isVFGen`
refutes separation at `k = 1` as soon as `Assembly.IsVFGen S` and `iRv m ∈ S`: the `RV`-preimage
`x ∈ S ∩ VF` of `rv(m)` is the witness.  So, like `M4Cases.CaseSeparated` itself
(`QE/Lemma36Audit.lean`'s `caseSeparated_empty_of_vfgen`), Lemma 3.8's frozen hypotheses cannot hold
at a `VF`-generated substructure: the paper's 3.8 contributes to the frozen obligation only at
non-`VF`-generated junctions, and no proof of it — EP-free or not — can fire where the paper uses it.
This is the sharp negative answer to "finish Lemma 3.8 at `CaseNewRV`'s hypotheses": the frozen
obligation cannot consume 3.8 at its own hypotheses as soon as the base is the paper's `Ŝ`. -/
theorem hyp_false_of_isVFGen {S : LRV.Substructure M} {m : M} (hgen : Assembly.IsVFGen S)
    (hm : Hyp S m) : False :=
  Bookkeeping.not_separated_of_isVFGen hm.sep hgen hm.vf hm.ne_zero hm.rvmem

/-- The same at the level of the frozen slot: `Slot`'s hypothesis set is empty at every
`VF`-generated base, so `Slot` is discharged vacuously there. -/
theorem separated_hyp_false_of_isVFGen {S : LRV.Substructure M} {m : M}
    (hgen : Assembly.IsVFGen S) (hmVF : iVF m) (hmrv : iRv m ∈ S) (hm0 : m ≠ iVFZero)
    (hsep : M5L.Separated S m) : False :=
  Bookkeeping.not_separated_of_isVFGen hsep hgen hmVF hm0 hmrv

/-- **The `m = 0` case of `Hyp` is excluded but harmless**: at `m = 0` the slot's conclusion holds
trivially with `T = S`, `g = f` (`caseSeparated_of_slot`'s first branch) — which is why
`Hyp`'s `ne_zero` loses nothing and why the equivalence with `CaseSeparated` still holds. -/
theorem zero_case_trivial (S : LRV.Substructure M) (f : S ↪[LRV] N) (hS : Assembly.Standing S) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ iVFZero ∈ T ∧ Assembly.Standing T :=
  ⟨S, f, le_rfl, fun _ => rfl, M3Slot.vfZero_mem_sub S, hS⟩

end SpecialTransformations.Milestone0.M6Lemma38

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.M6Lemma38.slot_of_caseSeparated
#print axioms SpecialTransformations.Milestone0.M6Lemma38.caseSeparated_of_slot
#print axioms SpecialTransformations.Milestone0.M6Lemma38.slot_iff_caseSeparated
#print axioms SpecialTransformations.Milestone0.M6Lemma38.not_unit_derived
#print axioms SpecialTransformations.Milestone0.M6Lemma38.slot_of_control
#print axioms SpecialTransformations.Milestone0.M6Lemma38.cases_of_slot
#print axioms SpecialTransformations.Milestone0.M6Lemma38.slot_of_struct
#print axioms SpecialTransformations.Milestone0.M6Lemma38.residualClasses_of_struct
#print axioms SpecialTransformations.Milestone0.M6Lemma38.slot_at_relGate
#print axioms SpecialTransformations.Milestone0.M6Lemma38.oneStepRVOld_of_slot
#print axioms SpecialTransformations.Milestone0.M6Lemma38.hyp_and_newRV_incompatible
#print axioms SpecialTransformations.Milestone0.M6Lemma38.not_hyp_top
#print axioms SpecialTransformations.Milestone0.M6Lemma38.hyp_false_of_isVFGen
#print axioms SpecialTransformations.Milestone0.M6Lemma38.separated_hyp_false_of_isVFGen
#print axioms SpecialTransformations.Milestone0.M6Lemma38.zero_case_trivial
