/-
# M5: what the one-step `OneStepVFP` can and cannot be

`QE/Assembly_frozen.lean` freezes the paper's Section 3 reduction to

    PrepStepP    -- Lemma 3.3 + henselization   (K(S) = K(M), Γ(S) divisible)
    OneStepVFP   -- Lemmas 3.4-3.8              (add one `VF` element, keep `Standing`)
    Prop39FS     -- Proposition 3.9 at `SaturatedFS`

and `M7_vfgen.lean` removed the third ingredient (`VFGenCaseP`), leaving the route

    ShoenfieldTestFS → (∀ M N, PrepStepP) → (∀ M N, OneStepVFP) → HasQE Axioms.ACVF.

This file does three things to that route.

## 1. The `∀ M N` form of `PrepStepP` carries a cardinality obligation (`units_le_of_prepStepP`)

`Assembly.Standing S` has `KEqTop S = ∀ x, iUnits x → x ∈ S`: *every* unit of `M` lies in `S`.
`PrepStepP` produces `T ⊇ S` with `Standing T` and an embedding `g : T ↪[LRV] N`.  Hence *every*
unit of `M` is injected into `N`, i.e.

    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N.

So `PrepStepP (M := M) (N := N)` is not a statement that can hold for all pairs of models of
`ACVF`: its `S`-independence means the bound has nothing to do with `S`, and it is refuted as soon
as one has two models whose residue fields have different cardinalities (e.g. the repository's
`C v` models of `Milestone0/accepted/ACVF_general_model.lean` at `K = ℂ` and `K = ℚ̄`).  The
hypothesis set of `theorem_2_3_of_two` is therefore *too strong*: `PrepStepP` must be demanded only
at pairs `(M, N)` for which `N` is at least as large as the residue field of `M` — which is exactly
what the paper's `‖M‖⁺`-saturation of `N` gives.  Dropping saturation from the ingredients, as
`Prop39FS_of_two` does, drops precisely the hypothesis that makes them true.

`M7_vfgen.lean` records the same defect for the deleted `VFGenCaseP`; the point here is that it
applies to `PrepStepP` itself, which `Prop39FS_of_two` keeps.

## 2. The repaired route (`Prop39FS_of_two_FS`, `Prop39FS_of_two_sz`)

The derivation `Assembly.exists_vf_allP` → `Assembly.prop39P_noVFGen` never uses the saturation
hypothesis of the ingredient, so the ingredients can be demanded *at* `SaturatedFS`:

    Prop39FS_of_two_FS : (∀ M N, SaturatedFS N → PrepStepP) →
                         (∀ M N, SaturatedFS N → OneStepVFP) → Prop39FS

which is the minimal repair that keeps the frozen `Prop39FS`/`ShoenfieldTestFS`/`theorem_2_3_of_fs`
chain intact.  The stronger, cardinality-safe form is `Prop39FSsz_of_two_sz`, for a `Prop39FS`
whose saturation hypothesis is a genuine `‖M‖⁺`-saturation, i.e. one that also carries
`Cardinal.mk M ≤ Cardinal.mk N`.

## 3. `Standing` is preserved by `RV`-control (`standing_of_RV_le`, `oneStepVFP_of_RVstep`)

This is the shared skeleton of the paper's Lemmas 3.4-3.8, and the reason the paper's Claim (⋆) is
stated as `RV(⟨Ŝ, e⟩) = ⟨RV(Ŝ), rv(e)⟩ ⊆ RV(S)`: if every `RV`-element of `T` already lies in `S`,
then

* `KEqTop T` follows from `KEqTop S` (units are in `S ⊆ T`), and
* `GammaDivisible T` follows from `GammaDivisible S` *verbatim* (the witnesses are in `S ⊆ T`).

So `Standing` needs no new mathematics in the case lemmas — it is a corollary of the `RV`-control
that the case lemmas must establish anyway.  `oneStepVFP_of_RVstep` makes that precise: a one-step
of Claim-(⋆) shape for elements whose `rv` is *already* in `S` yields the one-step with `Standing T`.

Note that this restriction is not an artefact: `GammaDivisible T` for `T ⊇ S` with `Γ(S)` divisible
*forces* `Γ(T)` to be divisible, so if `m` has `rv(m) ∉ RV(S)` then `T` must contain not only `m`
but witnesses `u_n` with `u_n^n = rv(m)·c_n` for every `n ≥ 1`, i.e. the whole divisible hull of
`Γ(S) + ℤ·v(m)` inside `T`, all at once.  A one-element step that adds only `m` therefore cannot
close; and when `Γ(N)` has no room for that hull there is no `T` at all (see `AUDIT.md` §2).  That
is the precise sense in which the frozen `OneStepVFP` is stronger than the paper's per-element
Claim (⋆), which only ever adds `e` with `rv(e) ∈ RV(S)` and re-hulls between phases.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Enc
import Prop39Two
import Standing

namespace SpecialTransformations.Milestone0
namespace M5

open Axioms FirstOrder FirstOrder.Language

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]

/-! ### 1. The cardinality obligation hidden in `PrepStepP`

`Standing T` contains `KEqTop T`, and `KEqTop T` says that every unit of `M` is an element of `T`.
Since `PrepStepP` also gives an injection `T ↪ N`, the units of `M` inject into `N`. -/

/-- **`PrepStepP` forces the units of `M` to inject into `N`.**  This is independent of the
substructure `S` at which the lemma is applied and of the map `f`: `KEqTop` forgets both. -/
theorem units_le_of_prepStepP (h : Assembly.PrepStepP (M := M) (N := N))
    (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N := by
  obtain ⟨T, g, _hST, _hagree, hK, _hDiv⟩ := h S f
  refine Cardinal.mk_le_of_injective
    (f := fun x : {x : M // iUnits x} => (g ⟨x.1, hK x.1 x.2⟩ : N)) ?_
  intro a b hab
  have h1 : (⟨a.1, hK a.1 a.2⟩ : T) = ⟨b.1, hK b.1 b.2⟩ := g.injective hab
  exact Subtype.ext (congrArg (fun z : T => (z : M)) h1)

/-- **The refutation form.**  If the units of `M` do not inject into `N`, then `PrepStepP` fails at
that pair of models, which is what makes the `∀ M N` quantification of `Prop39FS_of_two` too
strong.  (The `S`, `f` argument is needed because `PrepStepP` only asserts something once a
monomorphism out of a substructure is given.) -/
theorem not_prepStepP_of_not_units_le
    (hcard : ¬ Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N)
    (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    ¬ Assembly.PrepStepP (M := M) (N := N) :=
  fun h => hcard (units_le_of_prepStepP h S f)

/-- **The whole two-hypothesis pair is refuted by the same bound**: `Prop39FS_of_two`/`M7.theorem_2_3_of_two`
use `PrepStepP` and `OneStepVFP` at the same pair, and `PrepStepP` alone already forces the units of
`M` into `N`. -/
theorem not_both_of_not_units_le
    (hcard : ¬ Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N)
    (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    ¬ (Assembly.PrepStepP (M := M) (N := N) ∧ Assembly.OneStepVFP (M := M) (N := N)) :=
  fun h => hcard (units_le_of_prepStepP h.1 S f)

/-- **The conclusion of `PrepStepP` at `S = ⊤`**, where it holds outright: `T = ⊤`, `g = f`, and
`Standing ⊤` is `StandingTree.standing_top`.  So `units_le_of_prepStepP` restricts `PrepStepP` to
pairs with room, it does not make the conclusion unreachable. -/
theorem prepStepP_at_top (f : (⊤ : LRV.Substructure M) ↪[LRV] N) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : (⊤ : LRV.Substructure M) ≤ T),
      (∀ x : (⊤ : LRV.Substructure M), g ⟨(x : M), hST x.2⟩ = f x) ∧ Assembly.Standing T :=
  ⟨⊤, f, le_rfl, fun _ => rfl, StandingTree.standing_top⟩

/-! ### 2. `Standing` is preserved by `RV`-control -/

/-- `KEqTop` is monotone: a bigger substructure still contains every unit. -/
theorem KEqTop_mono {S T : LRV.Substructure M} (hST : S ≤ T) (hS : Assembly.KEqTop S) :
    Assembly.KEqTop T :=
  fun x hx => hST (hS x hx)

/-- **`RV`-control preserves `Standing`.**  If every `RV`-element of `T` already lies in `S`, then
`Standing S` gives `Standing T`: the units are in `S ⊆ T` (`KEqTop_mono`), and the divisibility
witnesses for an `RV`-element `t ∈ T` may be taken in `S`, because `t` itself is in `S`. -/
theorem standing_of_RV_le {S T : LRV.Substructure M} (hST : S ≤ T) (hS : Assembly.Standing S)
    (hRV : ∀ y : M, y ∈ T → iRV y → y ∈ S) : Assembly.Standing T := by
  obtain ⟨hK, hDiv⟩ := hS
  refine ⟨KEqTop_mono hST hK, ?_⟩
  intro t htT hRVt ht0 n hn
  obtain ⟨u, c, huS, huRV, hu0, hcS, hcU, hpow⟩ := hDiv t (hRV t htT hRVt) hRVt ht0 n hn
  exact ⟨u, c, hST huS, huRV, hu0, hST hcS, hcU, hpow⟩

/-- **Claim (⋆) in the frozen encoding**: one step that adds a `VF`-element whose `rv` is already in
`S`, keeps `RV` inside `S`, and extends the monomorphism.  This is the shape in which the paper's
Lemmas 3.4-3.8 are stated (there `RV(⟨Ŝ, e⟩) = ⟨RV(Ŝ), rv(e)⟩ ⊆ RV(S)`), restricted to the
elements whose value is available. -/
def RVStepP {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
    {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF] : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧
        (∀ y : M, y ∈ T → iRV y → y ∈ S)

/-- **The one-step with `Standing` preserved, from Claim (⋆).**  The only thing to prove is
`Standing T`, and that is `standing_of_RV_le`. -/
theorem oneStepVFP_restricted_of_RVstep (h : RVStepP (M := M) (N := N)) :
    ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S →
      ∀ m : M, iVF m → iRv m ∈ S →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T := by
  intro S f hS m hmVF hmrv
  obtain ⟨T, g, hST, hagree, hmT, hRV⟩ := h S f hS m hmVF hmrv
  exact ⟨T, g, hST, hagree, hmT, standing_of_RV_le hST hS hRV⟩

/-- **The trivial instance of the one-step**: an element already in `S` needs no work.  This is the
base case of every exhaustion, and it shows that `RVStepP` is not a restatement of its own
conclusion. -/
theorem RVStepP_trivial_of_mem (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    ∀ m : M, iVF m → m ∈ S → iRv m ∈ S →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧
          (∀ y : M, y ∈ T → iRV y → y ∈ S) := by
  intro m _ hmS _
  exact ⟨S, f, le_rfl, fun _ => rfl, hmS, fun _ hy _ => hy⟩

/-- **The one-step that adds an element whose `rv` is already present** (the paper's Lemmas 3.4,
3.6, 3.8: nothing new happens in `RV`). -/
def OneStepRVOld {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
    {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF] : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T

/-- **The one-step that adds an element with a new `rv`** (the paper's Lemmas 3.5 and 3.7: `Γ` grows,
and `Standing T` can only be reached by adding the divisible hull at the same time). -/
def OneStepRVNew {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
    {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF] : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∉ S →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T

/-- **`OneStepVFP` is exactly these two.**  The case split is on whether the new element's `rv` is
already in `S`; the two halves are the paper's two kinds of step, and `RVStepP` supplies the first
half (`oneStepVFP_restricted_of_RVstep`). -/
theorem oneStepVFP_of_two_steps (hOld : OneStepRVOld (M := M) (N := N))
    (hNew : OneStepRVNew (M := M) (N := N)) : Assembly.OneStepVFP (M := M) (N := N) := by
  intro S f hS m hmVF
  by_cases h : iRv m ∈ S
  · exact hOld S f hS m hmVF h
  · exact hNew S f hS m hmVF h

/-- **`OneStepVFP` holds at `S = ⊤`**, where the conclusion is the hypothesis: the exhaustion's last
step, and the check that `OneStepVFP`'s conclusion is consistent with `Standing`. -/
theorem oneStepVFP_top (m : M) (f : (⊤ : LRV.Substructure M) ↪[LRV] N) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : (⊤ : LRV.Substructure M) ≤ T),
      (∀ x : (⊤ : LRV.Substructure M), g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧
        Assembly.Standing T :=
  ⟨⊤, f, le_rfl, fun _ => rfl, trivial, StandingTree.standing_top⟩

/-! ### 3. The repaired route: the ingredients at `SaturatedFS`, and with the size condition

`Assembly.exists_vf_allP` and `Assembly.prop39P_noVFGen` never touch a saturation hypothesis, so the
ingredients can be demanded only at `SaturatedFS N` — the pairs at which `Prop39FS` uses them. -/

/-- **`Prop39FS` from the two ingredients demanded at `SaturatedFS`.**  This is `M7.Prop39FS_of_two`
with the hypothesis weakened, so it no longer asserts `PrepStepP`/`OneStepVFP` at pairs of models
where `units_le_of_prepStepP` makes it impossible. -/
theorem Prop39FS_of_two_FS
    (hPrep : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], Assembly.SaturatedFS N → Assembly.PrepStepP (M := M) (N := N))
    (hOne : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], Assembly.SaturatedFS N → Assembly.OneStepVFP (M := M) (N := N)) :
    Assembly.Prop39FS := by
  intro M N _ _ hM hN hSat S f
  exact Assembly.prop39P_noVFGen (hPrep M N hSat) (hOne M N hSat) S f

/-- `Prop39FS` with the size condition of a genuine `‖M‖⁺`-saturation made explicit.  This is the
statement the paper proves: `N` realises the finitely satisfiable pushed types *and* is at least as
large as `M`, which is what defeats `units_le_of_prepStepP`. -/
def Prop39FSsz : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
    (_hSat : Assembly.SaturatedFS N) (_hcard : Cardinal.mk M ≤ Cardinal.mk N)
    (S : LRV.Substructure M) (f : S ↪[LRV] N),
    ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x

/-- `Prop39FS` implies the size-conditioned form (the size condition is extra hypothesis). -/
theorem Prop39FSsz_of_Prop39FS (h : Assembly.Prop39FS) : Prop39FSsz :=
  fun M N _ _ _ _ hSat _ S f => h M N hSat S f

/-- **The size-conditioned route**: `Prop39FSsz` from the two ingredients demanded at pairs
`(M, N)` with `SaturatedFS N` and `Cardinal.mk M ≤ Cardinal.mk N`.  These are the pairs on which
`PrepStepP` is not excluded by the cardinality obligation. -/
theorem Prop39FSsz_of_two_sz
    (hPrep : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], Assembly.SaturatedFS N → Cardinal.mk M ≤ Cardinal.mk N →
        Assembly.PrepStepP (M := M) (N := N))
    (hOne : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], Assembly.SaturatedFS N → Cardinal.mk M ≤ Cardinal.mk N →
        Assembly.OneStepVFP (M := M) (N := N)) :
    Prop39FSsz := by
  intro M N _ _ hM hN hSat hcard S f
  exact Assembly.prop39P_noVFGen (hPrep M N hSat hcard) (hOne M N hSat hcard) S f

/-- **The frozen Theorem 2.3 modulo the two ingredients, at `SaturatedFS`** — the same conclusion
as `M7.theorem_2_3_of_two`, with the hypotheses weakened to the pairs the derivation uses. -/
theorem theorem_2_3_of_two_FS (hShoen : Assembly.ShoenfieldTestFS)
    (hPrep : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], Assembly.SaturatedFS N → Assembly.PrepStepP (M := M) (N := N))
    (hOne : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], Assembly.SaturatedFS N → Assembly.OneStepVFP (M := M) (N := N)) :
    HasQE Axioms.ACVF :=
  Assembly.theorem_2_3_of_fs hShoen (Prop39FS_of_two_FS hPrep hOne)

end M5
end SpecialTransformations.Milestone0

#print axioms SpecialTransformations.Milestone0.M5.units_le_of_prepStepP
#print axioms SpecialTransformations.Milestone0.M5.not_prepStepP_of_not_units_le
#print axioms SpecialTransformations.Milestone0.M5.KEqTop_mono
#print axioms SpecialTransformations.Milestone0.M5.standing_of_RV_le
#print axioms SpecialTransformations.Milestone0.M5.oneStepVFP_restricted_of_RVstep
#print axioms SpecialTransformations.Milestone0.M5.RVStepP_trivial_of_mem
#print axioms SpecialTransformations.Milestone0.M5.Prop39FS_of_two_FS
#print axioms SpecialTransformations.Milestone0.M5.Prop39FSsz_of_Prop39FS
#print axioms SpecialTransformations.Milestone0.M5.Prop39FSsz_of_two_sz
#print axioms SpecialTransformations.Milestone0.M5.theorem_2_3_of_two_FS
#print axioms SpecialTransformations.Milestone0.M5.not_both_of_not_units_le
#print axioms SpecialTransformations.Milestone0.M5.oneStepVFP_of_two_steps
#print axioms SpecialTransformations.Milestone0.M5.oneStepVFP_top
#print axioms SpecialTransformations.Milestone0.M5.prepStepP_at_top
