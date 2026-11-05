/-
# The §3.1 frontier at the paper's own hypothesis: Lemma 3.3 + henselization ⟹ Theorem 2.3

`M7Paper.PrepStepSize` (`QE/PaperRoute.lean`) is Lemma 3.3 demanded at every pair of models with
`SizeHyp M N : #M ≤ #N`.  That statement is **not** what the paper proves, and the difference is
machine-checked, not a matter of taste:

* `M7Paper.prepStepSize_forces_unitsN_size` (base `M6L33`, from
  `M7Paper.prepStepP_forces_units_size` and `M5.units_le_of_prepStepP`) —
  `PrepStepSize` at a size-bounded pair *forces* `#Kˣ(M) ≤ #Kˣ(N)`, i.e. the residue field of `M`
  must inject into the residue field of `N`;
* `SizeHyp` says nothing about residue fields (`M7Paper.paperHyp_supplies_units_size` shows the
  paper's hypothesis does, through `#M ≤ #N`).

The paper proves Lemma 3.3 at the pairs where `N` is `‖M‖⁺`-saturated (`qe.tex`:578), and the tree's
`Assembly.SaturatedFS` is exactly the formula-level saturation notion of those pairs.  So the honest
frontier of the route is

    ShoenfieldTestFS  (Marker, quoted by the author ruling)
    PaperLemma33 at SaturatedFS pairs  (Lemma 3.3 verbatim, `M6L33.PaperLemma33`)
    OneStepVFP at SaturatedFS pairs    (Lemmas 3.4-3.8)

and this file proves that this frontier yields `HasQE Axioms.ACVF`, with the one-step supplied by
the henselization inputs of `M7Hensel.lean` (`HenselizationExists`, `ImmediateLift`) plus the case
lemmas at henselian domains.  The assembly is `M5.theorem_2_3_of_two_FS`, which is the paper's own
quantifier shape; nothing new is assumed here.

## What is proved

* `paper_theorem_2_3_sat_of_paperLemma33_hens` — Theorem 2.3 from Shoenfield's test, Lemma 3.3 at
  `SaturatedFS`, and Lemmas 3.4-3.8 at henselian domains (with the two henselization inputs);
* `paper_theorem_2_3_sat_of_steps` — the same with the base's `UnitsStep` (the paper's step (i),
  the field homomorphism `K(M) → K(N)`) and `MDivStep` (the divisible hull of `Γ(S)`) in place of
  Lemma 3.3 as a whole;
* `PrepStepFS` / `OneStepFS` — the two ingredients named at `SaturatedFS`, so that the frontier can
  be quoted without the refutable `SizeHyp` version;
* `prepStepSize_of_prepStepFS` — the inclusion that *does* hold: the `SaturatedFS` version plus a
  size bound at every pair would give `PrepStepSize` (which is why `PrepStepSize` is stronger than
  the paper, not weaker).

No `sorry`, no `axiom`, no `native_decide`.
-/
import M7Hensel
import M5OneStep

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace SpecialTransformations
namespace Milestone0
namespace M7PaperHyp

/-! ### The two ingredients at the paper's hypothesis -/

/-- Lemma 3.3 at the paper's pairs: every monomorphism out of a substructure of `M` extends to one
whose domain is `Standing` (`K = K(M)`, `Γ` divisible), for `N` `SaturatedFS`. -/
def PrepStepFS : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    Assembly.SaturatedFS N → Assembly.PrepStepP (M := M) (N := N)

/-- Lemmas 3.4-3.8 at the paper's pairs. -/
def OneStepFS : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    Assembly.SaturatedFS N → Assembly.OneStepVFP (M := M) (N := N)

/-- **The paper's Lemma 3.3 discharges `PrepStepFS`.**  (`M6L33.PaperLemma33` carries the three
clauses of `qe.tex`:580, so this is the paper's own statement, not a weakening.) -/
theorem prepStepFS_of_paperLemma33
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      Assembly.SaturatedFS N → M6L33.PaperLemma33 (M := M) (N := N)) :
    PrepStepFS :=
  fun M N _ _ _ _ hSat => M6L33.prepStepP_of_paperLemma33 (h M N hSat)

/-- **The paper's steps (i) and the divisible hull discharge `PrepStepFS`.**  `UnitsStep` is step
(i) (`g : K(M) → K(N)`, one residue unit at a time), `MDivStep` is the iteration producing the
divisible hull of `Γ(S)`. -/
theorem prepStepFS_of_steps
    (hU : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], M6L33.UnitsStep (M := M) (N := N))
    (hD : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], M6L33.MDivStep (M := M) (N := N)) :
    PrepStepFS :=
  fun M N _ _ _ _ _ => M6L33.prepStepP_of_unitsStep_divStep (hU M N) (hD M N)

/-- **Lemmas 3.4-3.8 discharge `OneStepFS`** once the henselization inputs and the case lemmas at
henselian domains are available (`M7Hens.oneStepVFP_of_hens` is size-free, so it applies here). -/
theorem oneStepFS_of_hens
    (hE : ∀ (P : Type) [LRV.Structure P] [P ⊨ Axioms.ACVF], M7Hens.HenselizationExists P)
    (hL : M7Hens.ImmediateLift)
    (hOne : ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF] [Q ⊨ Axioms.ACVF]
      (S : LRV.Substructure P) (f : S ↪[LRV] Q), Assembly.Standing S → M7Hens.IsHenselianVF S →
      ∀ m : P, iVF m →
        ∃ (T : LRV.Substructure P) (g : T ↪[LRV] Q) (hST : S ≤ T),
          (∀ x : S, g ⟨(x : P), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T) :
    OneStepFS :=
  fun M N _ _ _ _ _ => M7Hens.oneStepVFP_of_hens hE hL hOne M N

/-! ### Theorem 2.3 at the paper's hypothesis -/

/-- **Theorem 2.3 (`qe:acvf`) at the paper's hypothesis**: Shoenfield's test (`Marker` content,
quoted per the author ruling) together with Lemmas 3.3-3.8 at `SaturatedFS` pairs.  The assembly is
`M5.Prop39FS_of_two_FS` / `M5.theorem_2_3_of_two_FS`, which is the paper's quantifier shape. -/
theorem paper_theorem_2_3_FS (hShoen : Assembly.ShoenfieldTestFS)
    (hPrep : PrepStepFS) (hOne : OneStepFS) : HasQE Axioms.ACVF :=
  M5.theorem_2_3_of_two_FS hShoen
    (fun M N _ _ _ _ hSat => hPrep M N hSat)
    (fun M N _ _ _ _ hSat => hOne M N hSat)

/-- **Theorem 2.3 with the paper's Lemma 3.3 and the henselization inputs**: the frontier is
Lemma 3.3 (`PaperLemma33`, the three clauses of `qe.tex`:580), the henselization inputs of
`M7Hensel.lean`, and Lemmas 3.4-3.8 at henselian domains.  `M7Paper.PrepStepSize` is *not* on this
route: its `SizeHyp` is strictly weaker than the paper's saturation hypothesis (see the module
docstring). -/
theorem paper_theorem_2_3_sat_of_paperLemma33_hens (hShoen : Assembly.ShoenfieldTestFS)
    (h33 : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], Assembly.SaturatedFS N → M6L33.PaperLemma33 (M := M) (N := N))
    (hE : ∀ (P : Type) [LRV.Structure P] [P ⊨ Axioms.ACVF], M7Hens.HenselizationExists P)
    (hL : M7Hens.ImmediateLift)
    (hOne : ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF] [Q ⊨ Axioms.ACVF]
      (S : LRV.Substructure P) (f : S ↪[LRV] Q), Assembly.Standing S → M7Hens.IsHenselianVF S →
      ∀ m : P, iVF m →
        ∃ (T : LRV.Substructure P) (g : T ↪[LRV] Q) (hST : S ≤ T),
          (∀ x : S, g ⟨(x : P), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T) :
    HasQE Axioms.ACVF :=
  paper_theorem_2_3_FS hShoen (prepStepFS_of_paperLemma33 h33) (oneStepFS_of_hens hE hL hOne)

/-- **Theorem 2.3 from the paper's steps (i) and the divisible hull, plus the henselization
inputs**: the same frontier with `UnitsStep`/`MDivStep` (the base's machine-checked decomposition of
Lemma 3.3) in place of the lemma as a whole. -/
theorem paper_theorem_2_3_sat_of_steps_hens (hShoen : Assembly.ShoenfieldTestFS)
    (hU : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], M6L33.UnitsStep (M := M) (N := N))
    (hD : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], M6L33.MDivStep (M := M) (N := N))
    (hE : ∀ (P : Type) [LRV.Structure P] [P ⊨ Axioms.ACVF], M7Hens.HenselizationExists P)
    (hL : M7Hens.ImmediateLift)
    (hOne : ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF] [Q ⊨ Axioms.ACVF]
      (S : LRV.Substructure P) (f : S ↪[LRV] Q), Assembly.Standing S → M7Hens.IsHenselianVF S →
      ∀ m : P, iVF m →
        ∃ (T : LRV.Substructure P) (g : T ↪[LRV] Q) (hST : S ≤ T),
          (∀ x : S, g ⟨(x : P), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T) :
    HasQE Axioms.ACVF :=
  paper_theorem_2_3_FS hShoen (prepStepFS_of_steps hU hD) (oneStepFS_of_hens hE hL hOne)

/-! ### How the two frontiers compare -/

/-- The inclusion that does hold: the `SaturatedFS` ingredient plus the size bound **at every pair**
gives the frozen `M7Paper.PrepStepSize`.  So `PrepStepSize` asks for strictly more than the paper's
Lemma 3.3 — it asks for the paper's lemma at pairs where the residue field of `M` need not have room
in `N` (`M7Paper.prepStepSize_forces_unitsN_size`). -/
theorem prepStepSize_of_prepStepFS_and_size
    (hPrep : PrepStepFS)
    (hSize : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], M7Paper.SizeHyp M N → Assembly.SaturatedFS N) :
    M7Paper.PrepStepSize :=
  fun M N _ _ _ _ hSz => hPrep M N (hSize M N hSz)

/-- Conversely, the frozen `PrepStepSize` gives `PrepStepFS` as soon as every `SaturatedFS` pair
carries the size bound — i.e. as soon as the tree's `SaturatedFS` really is `‖M‖⁺`-saturation.  The
two statements are then the same lemma, and the paper's is the one at the pairs the paper fixes. -/
theorem prepStepFS_of_prepStepSize
    (hSize : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], Assembly.SaturatedFS N → M7Paper.SizeHyp M N)
    (h : M7Paper.PrepStepSize) : PrepStepFS :=
  fun M N _ _ _ _ hSat => h M N (hSize M N hSat)

/-! ### The audit: each frozen ingredient is, given the other, the target

`M6L33.prepStepP_iff_total_extension` shows `PrepStepP ↔` (Proposition 3.9's conclusion) given
`OneStepVFP`.  The symmetric direction is below: given `PrepStepP`, the frozen one-step
`OneStepVFP` is *also* equivalent to Proposition 3.9's conclusion.  So the frozen decomposition
`PrepStepP + OneStepVFP` is not a decomposition of the paper's argument: each ingredient already
implies the target (given the other), which is why the paper states them at the pair where `N` is
`‖M‖⁺`-saturated and not at arbitrary pairs.  Recorded, not assumed. -/

section Audit

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- The total-extension property gives the frozen one-step (`T = ⊤`, `Standing ⊤`). -/
theorem oneStepVFP_of_total_extension
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ∃ g : M ↪[LRV] N,
      ∀ x : S, g (x : M) = f x) :
    Assembly.OneStepVFP (M := M) (N := N) := by
  intro S f _hStand m _hm
  obtain ⟨g, hg⟩ := h S f
  refine ⟨⊤, g.comp (Substructure.topEquiv (L := LRV) (M := M)).toEmbedding, fun _ => by simp,
    ?_, trivial, StandingTree.standing_top⟩
  intro x
  show g ((Substructure.topEquiv (L := LRV) (M := M)).toEmbedding ⟨(x : M), trivial⟩) = f x
  exact hg x

/-- **Given `PrepStepP`, the frozen one-step is equivalent to Proposition 3.9's conclusion.** -/
theorem oneStepVFP_iff_total_extension
    (hPrep : Assembly.PrepStepP (M := M) (N := N)) :
    Assembly.OneStepVFP (M := M) (N := N) ↔
      ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ∃ g : M ↪[LRV] N,
        ∀ x : S, g (x : M) = f x :=
  ⟨fun hOne S f => Assembly.prop39P_noVFGen hPrep hOne S f, oneStepVFP_of_total_extension⟩

end Audit

end M7PaperHyp
end Milestone0
end SpecialTransformations

#print axioms SpecialTransformations.Milestone0.M7PaperHyp.prepStepFS_of_paperLemma33
#print axioms SpecialTransformations.Milestone0.M7PaperHyp.prepStepFS_of_steps
#print axioms SpecialTransformations.Milestone0.M7PaperHyp.oneStepFS_of_hens
#print axioms SpecialTransformations.Milestone0.M7PaperHyp.paper_theorem_2_3_FS
#print axioms SpecialTransformations.Milestone0.M7PaperHyp.paper_theorem_2_3_sat_of_paperLemma33_hens
#print axioms SpecialTransformations.Milestone0.M7PaperHyp.paper_theorem_2_3_sat_of_steps_hens
#print axioms SpecialTransformations.Milestone0.M7PaperHyp.prepStepSize_of_prepStepFS_and_size
#print axioms SpecialTransformations.Milestone0.M7PaperHyp.prepStepFS_of_prepStepSize
#print axioms SpecialTransformations.Milestone0.M7PaperHyp.oneStepVFP_of_total_extension
#print axioms SpecialTransformations.Milestone0.M7PaperHyp.oneStepVFP_iff_total_extension
