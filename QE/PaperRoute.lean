/-
# Fidelity repair of the frozen Section 3 route against Yin's paper

`QE/Assembly_frozen.lean` reduces Theorem 2.3 to two Section 3 obligations plus Shoenfield's test
(`Assembly.theorem_2_3_of_two`, `.ultramath/smw1rx5g2/m7/M7_vfgen.lean`):

    ShoenfieldTestFS → (∀ M N, PrepStepP) → (∀ M N, OneStepVFP) → HasQE Axioms.ACVF

and records as a *feature* that "the three ingredients are saturation-free, so Proposition 3.9 is
too".  **The paper does the opposite.**  Yin, *Special transformations in algebraically closed
valued fields*, §3.1 (`refs/qe.tex`, l. 578) fixes the data of the whole section as

> Now we fix two models `M`, `N ⊨ ACVF` such that `N` is `‖M‖⁺`-saturated.  We shall work with a
> fixed substructure `S ⊆ M` and a fixed monomorphism `f : S → N`.

Every statement from Lemma 3.3 to Proposition 3.9 (`lrv:mono:lift`) is proved at that fixed pair,
with the saturation hypothesis available, and `qe:acvf` is then one line: "This proposition and
Shoenfield's test immediately yield: the theory ACVF admits quantifier elimination".

## The defect, and why it cannot be ignored

The frozen `Assembly.PrepStepP (M := M) (N := N)` says: for **every** substructure `S ⊆ M` and
**every** `f : S ↪[LRV] N` there is `T ⊇ S` with `Assembly.Standing T` and an embedding `T ↪[LRV] N`.
`Assembly.Standing` contains `Assembly.KEqTop`, i.e. *every unit of the residue field of `M` lies in
`T`*.  Composing, the units of `M` inject into `N`:

    prepStepP_forces_units_size : PrepStepP (M := M) (N := N) →  #Kˣ(M) ≤ #N

So the unconditional `∀ M N, PrepStepP` is strictly stronger than the paper's Lemma 3.3: it asks for
`#Kˣ(M) ≤ #N` at *every* pair of models of `ACVF`, which fails as soon as two models have residue
fields of different cardinality (the classical input — upward Löwenheim–Skolem for `Axioms.ACVF`,
i.e. models in every infinite cardinal — is direction d6's; it is not machine-checked in this
repository yet, so what is machine-checked here is the *forcing*, `prepStepP_forces_units_size` and
its contrapositive `not_prepStepP_of_units_large`).  The paper's `‖M‖⁺`-saturation is exactly what
supplies `#M ≤ #N`, hence `#Kˣ(M) ≤ #N`: `paperHyp_supplies_units_size` below.

Any proof of the frozen `∀ M N, PrepStepP` must therefore also prove a global inequality between the
residue fields of arbitrary model pairs; the route that consumes it is not a reduction of the
paper's Theorem 2.3.  This file states the repaired obligation and machine-checks that the repaired
route still yields it.

## The repair is minimal: only Lemma 3.3 needs it

`Assembly.OneStepVFP` (Lemmas 3.4–3.8) takes `Standing S` as a *hypothesis*, and that hypothesis
already contains the size content (`KEqTop S`).  Its conclusion adds one element to `S` and stays
inside `N`, so nothing in it is size-broken: the one-step obligation is left exactly as frozen (as
`OneStepSizeFree`).  Only Lemma 3.3 — whose first step is "there is a field homomorphism
`g : K(M) → K(N)` extending `f ↾ K(S)`" and whose conclusion (2) is `K(S*) = K(M)`, i.e. the frozen
`Assembly.KEqTop` over the *whole* residue field of `M` — needs the size hypothesis:

    PrepStepSize := ∀ (S) (f), SizeHyp M N → ∃ T ⊇ S, ∃ g : T ↪[LRV] N, (agrees) ∧ Standing T

with `SizeHyp M N := Cardinal.mk M ≤ Cardinal.mk N`.  `SizeHyp` is *necessary*
(`prepStepP_forces_units_size`, `not_prepStepP_of_units_large`) and, in the paper, supplied by the
saturation hypothesis.

## What is proved here

    prop39Size_of_two      PrepStepSize + frozen OneStepVFP ⟹ Proposition 3.9 at the size-bounded pair
    paper_theorem_2_3      + the criterion (Shoenfield's test at such pairs) ⟹ HasQE Axioms.ACVF
    paper_theorem_2_3_sat  same, with the paper's literal `SaturatedFS ∧ size` hypothesis
    prop39Sat_of_size      `Prop39Size → Prop39Sat`
    shoenfieldTestFS_of_sat  the repaired criterion discharges the frozen `Assembly.ShoenfieldTestFS`
    prepStepP_forces_units_size, prop39FS_forces_size, vfGenCaseP_forces_size,
    not_prepStepP_of_units_large, standing_forces_units_size                the defect and its scope
    paperHyp_supplies_units_size                                      the repair is not refutable

Verification (from the repository root):

    cp .ultramath/smw1rx5g2/m7/M7_vfgen.lean .scratch2/sec3/M7VF.lean
    cd .scratch2/sec3 && LEAN_PATH=$PWD:$LEAN_PATH lean -o M7VF.olean M7VF.lean
    cp ../../.ultramath/smw1tqlqv/m7/PaperRoute.lean M7Paper.lean
    LEAN_PATH=$PWD:$LEAN_PATH lean -o M7Paper.olean M7Paper.lean     # exit 0, no errors, no sorry
-/
import Enc
import Prop39Two

namespace SpecialTransformations
namespace Milestone0
namespace M7Paper

open FirstOrder FirstOrder.Language

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-! ### The two hypotheses

`SizeHyp` is the part of the paper's `‖M‖⁺`-saturation that the Section 3 conclusions need;
`PaperHyp` adds the saturation property itself, which only the criterion (Shoenfield's test) uses. -/

/-- `#M ≤ #N` — the size consequence of "`N` is `‖M‖⁺`-saturated". -/
def SizeHyp (M N : Type) : Prop := Cardinal.mk M ≤ Cardinal.mk N

/-- The paper's §3.1 hypothesis at the frozen interface. -/
def PaperHyp (M N : Type) [LRV.Structure M] [LRV.Structure N] : Prop :=
  Assembly.SaturatedFS N ∧ SizeHyp M N

theorem sizeHyp_of_paperHyp (h : PaperHyp M N) : SizeHyp M N := h.2

/-! ### The repaired Section 3 obligations -/

/-- **Lemma 3.3 + henselization**, repaired: the paper proves it at a pair with `#M ≤ #N`. -/
def PrepStepSize : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    SizeHyp M N → Assembly.PrepStepP (M := M) (N := N)

/-- **Lemmas 3.4–3.8**, exactly as frozen: no repair needed (see the module docstring). -/
def OneStepSizeFree : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    Assembly.OneStepVFP (M := M) (N := N)

/-- **Proposition 3.9 (`lrv:mono:lift`)** at a size-bounded pair. -/
def Prop39Size : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    SizeHyp M N → ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
      ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x

/-- **Proposition 3.9** at the paper's literal hypothesis. -/
def Prop39Sat : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    PaperHyp M N → ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
      ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x

/-- Shoenfield's test at the paper's pairs: Proposition 3.9 (with its saturation hypothesis) gives
quantifier elimination.  This is the step the paper takes in one sentence after `lrv:mono:lift`. -/
def ShoenfieldTestSat : Prop := Prop39Sat → HasQE Axioms.ACVF

/-- The same criterion with the size hypothesis only (no saturation). -/
def ShoenfieldTestSize : Prop := Prop39Size → HasQE Axioms.ACVF

/-! ### Proposition 3.9 at a size-bounded pair -/

/-- **Proposition 3.9**, from the repaired Lemma 3.3 and the frozen Lemmas 3.4–3.8.  The assembly is
`Assembly.exists_vf_allP` followed by `Assembly.eq_top_of_vf_all`; all of it is stated at a fixed pair of
models, so carrying `SizeHyp` costs nothing. -/
theorem prop39Size_of_two (hPrep : PrepStepSize) (hOne : OneStepSizeFree) : Prop39Size := by
  intro M N _ _ _hM _hN hSize S f
  exact Assembly.prop39P_noVFGen (hPrep M N hSize) (hOne M N) S f

/-- The paper's literal hypothesis version of Proposition 3.9. -/
theorem prop39Sat_of_size (h : Prop39Size) : Prop39Sat :=
  fun M N _ _ _hM _hN hP S f => h M N hP.2 S f

/-- **Theorem 2.3** (`qe:acvf`) at the repaired hypotheses. -/
theorem paper_theorem_2_3 (hShoen : ShoenfieldTestSize) (hPrep : PrepStepSize)
    (hOne : OneStepSizeFree) : HasQE Axioms.ACVF :=
  hShoen (prop39Size_of_two hPrep hOne)

/-- Theorem 2.3 with the paper's literal saturation hypothesis in the criterion. -/
theorem paper_theorem_2_3_sat (hShoen : ShoenfieldTestSat) (hPrep : PrepStepSize)
    (hOne : OneStepSizeFree) : HasQE Axioms.ACVF :=
  hShoen (prop39Sat_of_size (prop39Size_of_two hPrep hOne))

/-! ### The repaired criterion discharges the frozen one -/

/-- The frozen `Prop39FS` is Proposition 3.9 with the saturation hypothesis deleted, so it implies
the paper's version. -/
theorem prop39Sat_of_prop39FS (h : Assembly.Prop39FS) : Prop39Sat :=
  fun M N _ _ _hM _hN hP S f => h M N hP.1 S f

/-- A proof of the paper's criterion discharges the frozen hypothesis of the route.  (The converse
is not available: `Prop39Sat` gives no extension at a pair whose size is unbounded, which is exactly
the defect repaired above.) -/
theorem shoenfieldTestFS_of_sat (h : ShoenfieldTestSat) : Assembly.ShoenfieldTestFS :=
  fun h39 => h (prop39Sat_of_prop39FS h39)

/-! ### The defect, machine-checked -/

/-- `PrepStepP` forces a size inequality: `KEqTop T` puts every unit of the residue field of `M` into
`T`, and `T` embeds into `N`. -/
theorem prepStepP_forces_units_size [_hM : M ⊨ Axioms.ACVF] [_hN : N ⊨ Axioms.ACVF]
    (h : Assembly.PrepStepP (M := M) (N := N)) (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N := by
  obtain ⟨T, g, _hST, _hagree, hStand⟩ := h S f
  refine Cardinal.mk_le_of_injective (f := fun x : {x : M // iUnits x} =>
    g ⟨x.1, hStand.1 x.1 x.2⟩) ?_
  intro a b hab
  have h2 : (⟨a.1, hStand.1 a.1 a.2⟩ : T) = ⟨b.1, hStand.1 b.1 b.2⟩ :=
    Embedding.injective g hab
  exact Subtype.ext (congrArg (fun y : T => (y : M)) h2)

/-- Why the one-step needs no repair: `Standing S` **already** contains the size content, because
`KEqTop S` puts every unit of `M` inside `S`.  So `Assembly.OneStepVFP` cannot be size-broken beyond
its own hypothesis — it is `PrepStepP`, which must *produce* a `Standing` substructure out of an
arbitrary one, that needs the size hypothesis. -/
theorem standing_forces_units_size (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (hStand : Assembly.Standing S) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N := by
  refine Cardinal.mk_le_of_injective (f := fun x : {x : M // iUnits x} =>
    f ⟨x.1, hStand.1 x.1 x.2⟩) ?_
  intro a b hab
  have h2 : (⟨a.1, hStand.1 a.1 a.2⟩ : S) = ⟨b.1, hStand.1 b.1 b.2⟩ :=
    Embedding.injective f hab
  exact Subtype.ext (congrArg (fun y : S => (y : M)) h2)

/-- The contrapositive, in the form that refutes the frozen obligation at a pair: if the residue
field of `M` is larger than `N`, `PrepStepP` fails there. -/
theorem not_prepStepP_of_units_large [_hM : M ⊨ Axioms.ACVF] [_hN : N ⊨ Axioms.ACVF]
    (hbig : Cardinal.mk N < Cardinal.mk {x : M // iUnits x}) (S : LRV.Substructure M)
    (f : S ↪[LRV] N) : ¬ Assembly.PrepStepP (M := M) (N := N) :=
  fun h => absurd (prepStepP_forces_units_size h S f) (not_le.mpr hbig)

/-- The same for the whole model: the frozen `Prop39FS` asserts an embedding `M ↪[LRV] N` at every
pair, hence `#M ≤ #N` at every pair. -/
theorem prop39FS_forces_size (h : Assembly.Prop39FS) [_hM : M ⊨ Axioms.ACVF]
    [_hN : N ⊨ Axioms.ACVF] (hSat : Assembly.SaturatedFS N) (S : LRV.Substructure M)
    (f : S ↪[LRV] N) : Cardinal.mk M ≤ Cardinal.mk N :=
  Cardinal.mk_le_of_injective (Embedding.injective (h M N hSat S f).choose)

/-- The third frozen ingredient, `Assembly.VFGenCaseP` (Remark 3.1 + Weispfenning), has the same
shape of defect: its conclusion is a total embedding `M ↪[LRV] N`, hence `#M ≤ #N` at every pair of
models admitting a monomorphism out of a `VF`-generated substructure.  (It is also redundant on the
route: `Assembly.theorem_2_3_of_two` does not consume it.) -/
theorem vfGenCaseP_forces_size [_hM : M ⊨ Axioms.ACVF] [_hN : N ⊨ Axioms.ACVF]
    (h : Assembly.VFGenCaseP (M := M) (N := N)) (S : LRV.Substructure M)
    (f : S ↪[LRV] N) (hS : Assembly.IsVFGen S) : Cardinal.mk M ≤ Cardinal.mk N :=
  Cardinal.mk_le_of_injective (Embedding.injective (h S f hS).choose)

/-- The paper's hypothesis supplies exactly the bound that Lemma 3.3 needs, so the repaired
obligation is not refuted by the argument above. -/
theorem paperHyp_supplies_units_size (h : PaperHyp M N) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N :=
  le_trans (Cardinal.mk_subtype_le (fun x : M => iUnits x)) h.2

end M7Paper

end Milestone0
end SpecialTransformations

#print axioms SpecialTransformations.Milestone0.M7Paper.prop39Size_of_two
#print axioms SpecialTransformations.Milestone0.M7Paper.prop39Sat_of_size
#print axioms SpecialTransformations.Milestone0.M7Paper.paper_theorem_2_3
#print axioms SpecialTransformations.Milestone0.M7Paper.paper_theorem_2_3_sat
#print axioms SpecialTransformations.Milestone0.M7Paper.shoenfieldTestFS_of_sat
#print axioms SpecialTransformations.Milestone0.M7Paper.prepStepP_forces_units_size
#print axioms SpecialTransformations.Milestone0.M7Paper.not_prepStepP_of_units_large
#print axioms SpecialTransformations.Milestone0.M7Paper.standing_forces_units_size
#print axioms SpecialTransformations.Milestone0.M7Paper.prop39FS_forces_size
#print axioms SpecialTransformations.Milestone0.M7Paper.vfGenCaseP_forces_size
#print axioms SpecialTransformations.Milestone0.M7Paper.paperHyp_supplies_units_size
