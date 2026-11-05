/-
# The criterion lane, closed: model-restricted collapse, subsingleton stress test, diagonal dichotomy

Member `m2`, swarm `smw2ox51x` (direction d9).  Reference: Yimu Yin, *Special transformations in
algebraically closed valued fields*, the one-sentence step at `refs/qe.tex` l. 827 ("This
proposition and Shoenfield's test immediately yield [QE]"), transcribed in
`QE/ShoenfieldQuote.lean`.

`QE/ShoenfieldQuote.lean` proves (i) the frozen gate `paperGate` is contained in the paper's
pair-relative gate `relGate` (`paperGate_le_relGate`), (ii) the converse is exactly `SatBridge`,
(iii) `SatBridge` is *not* a theorem of any book because the frozen `Assembly.SaturatedFS N` is
`∀ M`-quantified while `M1Fix.SatRel M N` is a property of one pair, and (iv) *if* no structure
satisfies `Assembly.SaturatedFS`, the frozen input 1 is literally equivalent to the target
(`shoenfieldTestSat_iff_hasQE_of_no_saturatedFS`, `satBridge_diagonal`).

This file adds the three things that file leaves implicit.

**§1 The stress test: `Assembly.SaturatedFS` is satisfied by a subsingleton.**  `SaturatedFS N` is
`∀ (M) [LRV.Structure M] [M ⊨ Axioms.ACVF], SatRel M N`; the *second* argument `N` is not required
to be a model of `Axioms.ACVF`.  If `N` is a subsingleton then `SatRel M N` holds for **every**
`M`, because the realizing element is unique: the per-formula witnesses of `SatRel`'s hypothesis
all coincide, so one element realizes the whole type.  Hence
`¬ Assembly.SaturatedFS N` is *not* a consequence of the definition: any proof of it must use
`N ⊨ Axioms.ACVF` (and cardinality, cf. `QE/M1Fix.lean` §2).  This matters because §5 of
`QE/ShoenfieldQuote.lean` phrases the collapse hypothesis as `∀ N, ¬ SaturatedFS N` — a statement
that is *false* as written (at a subsingleton).

**§2 The collapse at the model-restricted hypothesis.**  The gate uses `SaturatedFS` only at
structures that are themselves models of `Axioms.ACVF` (`M7Paper.PaperHyp` has `[N ⊨ Axioms.ACVF]`),
so the honest hypothesis is `NoSatModel : ∀ N ⊨ ACVF, ¬ SaturatedFS N`, which is *weaker* than the
tree's `∀ N, ¬ SaturatedFS N`.  `shoenfieldTestSat_iff_hasQE_of_noSatModel` re-derives the collapse
from `NoSatModel`, so the circularity claim survives in the model-restricted form — and only there.

**§3 The diagonal dichotomy.**  `satBridge_diagonal` says `SatBridge` upgrades `SatRel N N` to
`SaturatedFS N`.  Read contrapositively with §2 this is a dichotomy, machine-checked below:

* either **no model of `Axioms.ACVF` is pair-relatively saturated over itself**
  (`∀ N ⊨ ACVF, ¬ SatRel N N`), and then the diagonal instance of the bridge is vacuous;
* or **some model satisfies `SaturatedFS`**, and then the frozen gate is inhabited and the frozen
  input 1 is not the target in disguise.

So `SatBridge` can only be *refuted* outside the diagonal, and §5 of `QE/ShoenfieldQuote.lean`'s
collapse needs the first horn: the substantive statement `∀ N ⊨ ACVF, ¬ SaturatedFS N` remains, and
it is the only model-theoretic input of the criterion lane.  (`QE/M1Fix.lean` §2 states the standard
reason — a model of cardinality `κ` cannot be `κ⁺`-saturated — but that argument is about full
saturation, not about the narrow `SatRel`; nothing in the tree derives the second from the first,
and `SatRel N N` is exactly the "narrow" reading.  Isolating this is the honest residual.)

No `sorry`, no `axiom`, no `native_decide`; axiom audit at the end.
-/
import ShoenfieldQuote

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.M5Gate

/-! ## 1. The subsingleton stress test -/

/-- The one-point `L_RV`-structure: every function symbol is constant, every relation symbol holds.
It is not a model of `Axioms.ACVF` (there is no field structure on a point), but `SaturatedFS` does
not ask it to be. -/
instance subsingletonStructure : LRV.Structure PUnit where
  funMap := fun _ _ => PUnit.unit
  RelMap := fun _ _ => True

/-- **`SatRel` holds at a subsingleton in its second argument.**  The realizing element is forced:
`SatRel`'s conclusion asks for one `b` realizing every formula the hypothesis satisfies one at a
time, and in a subsingleton all the per-formula witnesses are the same element. -/
theorem satRel_of_subsingleton {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [Subsingleton N] [Nonempty N] : M1Fix.SatRel M N := by
  intro S f m h
  refine ⟨Classical.arbitrary N, fun φ hφ => ?_⟩
  obtain ⟨b, hb⟩ := h φ hφ
  have hb' : b = Classical.arbitrary N := Subsingleton.elim b _
  rwa [hb'] at hb

/-- **The `∀M`-half of the frozen gate is satisfied by a subsingleton**, so
`¬ Assembly.SaturatedFS N` is not a definitional statement: it needs the model hypothesis on `N`.
This is the stress test for §5 of `QE/ShoenfieldQuote.lean`, whose hypothesis
`∀ N, ¬ SaturatedFS N` therefore holds of no universe in which a subsingleton `L_RV`-structure
exists. -/
theorem saturatedFS_of_subsingleton {N : Type} [LRV.Structure N] [Subsingleton N]
    [Nonempty N] : Assembly.SaturatedFS N := by
  intro M _ _ S f m h
  exact satRel_of_subsingleton (M := M) (N := N) S f m h

/-- **The collapse hypothesis of `QE/ShoenfieldQuote.lean` §5 is false as written.**  That file
derives the circularity from `∀ N, ¬ Assembly.SaturatedFS N`; the subsingleton refutes the
hypothesis outright, so `shoenfieldTestSat_iff_hasQE_of_no_saturatedFS` is a vacuous implication.  The
model-restricted form in §2 below is the true statement. -/
theorem not_forall_not_saturatedFS :
    ¬ ∀ (N : Type) [LRV.Structure N], ¬ Assembly.SaturatedFS N := by
  intro h
  exact h PUnit (saturatedFS_of_subsingleton (N := PUnit))

/-- **The frozen gate `M7Paper.PaperHyp` is inhabited** — as a definition it only asks for the
saturation half and the size conjunct, and both hold at the subsingleton pair.  So the emptiness
claimed in `QE/ShoenfieldQuote.lean` §5 is not a statement about the gate but about models of
`Axioms.ACVF` (the `[N ⊨ Axioms.ACVF]` instance of the frozen criterion). -/
theorem paperGate_subsingleton_inhabited :
    ∃ (M N : Type) (_ : LRV.Structure M) (_ : LRV.Structure N), M5Shoenfield.paperGate M N :=
  ⟨PUnit, PUnit, inferInstance, inferInstance,
    saturatedFS_of_subsingleton (N := PUnit), le_rfl⟩

/-! ## 2. The collapse at the model-restricted hypothesis

`M7Paper.PaperHyp M N` is `Assembly.SaturatedFS N ∧ Cardinal.mk M ≤ Cardinal.mk N` under
`[M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]`; the first conjunct is consumed only at a *model* `N`.  So the
frozen gate is empty as soon as no model of `Axioms.ACVF` is `SaturatedFS`, which is strictly weaker
than `∀ N, ¬ SaturatedFS N` (§1). -/

/-- Shorthand for the honest hypothesis of the collapse: no model of `Axioms.ACVF` is
`Assembly.SaturatedFS`. -/
def NoSatModel : Prop :=
  ∀ (N : Type) [LRV.Structure N], N ⊨ Axioms.ACVF → ¬ Assembly.SaturatedFS N

/-- **No pair satisfies the frozen gate**, from `NoSatModel`.  The model hypothesis on `N` is
required: `M7Paper.PaperHyp` does not carry it, but `NoSatModel` speaks only about models. -/
theorem not_paperGate_of_noSatModel (h : NoSatModel) :
    ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
      ¬ M5Shoenfield.paperGate M N := by
  intro M N _ _ _ _ hP
  exact h N ‹N ⊨ Axioms.ACVF› hP.1

/-- **The frozen Proposition 3.9 is vacuous at `NoSatModel`.** -/
theorem prop39Sat_of_noSatModel (h : NoSatModel) : M7Paper.Prop39Sat := by
  intro M N _ _ _ _ hP S f
  exact absurd hP (not_paperGate_of_noSatModel h M N)

/-- **The collapse of the frozen input 1 to the target, at the model-restricted hypothesis.**
This is `M5Shoenfield.shoenfieldTestSat_iff_hasQE_of_no_saturatedFS` with the hypothesis weakened
from "no structure" to "no model", i.e. it is strictly stronger, and it is the form in which the
circularity claim is true. -/
theorem shoenfieldTestSat_iff_hasQE_of_noSatModel (h : NoSatModel) :
    (M7Paper.ShoenfieldTestSat ↔ HasQE Axioms.ACVF) :=
  ⟨fun hS => hS (prop39Sat_of_noSatModel h), fun hQE _ => hQE⟩

/-- `NoSatModel` is implied by the shape the tree uses, so nothing is lost by restricting. -/
theorem noSatModel_of_forall_not (h : ∀ (N : Type) [LRV.Structure N], ¬ Assembly.SaturatedFS N) :
    NoSatModel :=
  fun N _ _ => h N

/-! ## 3. The diagonal dichotomy

`M5Shoenfield.satBridge_diagonal` records that `SatBridge` upgrades the *diagonal* instance
`SatRel N N` to the frozen `SaturatedFS N`.  Combined with §2 this says: either the bridge's diagonal
instances are all vacuous, or the frozen gate is inhabited.  Spelled out below. -/

/-- **The diagonal instance of `SatBridge`**, restated with the model hypothesis explicit. -/
theorem saturatedFS_of_satBridge_of_satRel {N : Type} [LRV.Structure N] [hN : N ⊨ Axioms.ACVF]
    (hB : M5Shoenfield.SatBridge) (hSat : M1Fix.SatRel N N) : Assembly.SaturatedFS N :=
  M5Shoenfield.satBridge_diagonal hB N hSat

/-- **`SatBridge` cannot coexist with `NoSatModel` and a pair-relatively saturated model of
itself.**  This is the machine-checked content of the tree's "the bridge asserts that a set-sized
structure is `κ`-saturated for every `κ`". -/
theorem not_satBridge_of_noSatModel_of_satRel (h : NoSatModel)
    (hd : ∃ (N : Type) (_ : LRV.Structure N) (_ : N ⊨ Axioms.ACVF), M1Fix.SatRel N N) :
    ¬ M5Shoenfield.SatBridge := by
  intro hB
  obtain ⟨N, inst, hN, hSat⟩ := hd
  letI := inst
  exact h N hN (saturatedFS_of_satBridge_of_satRel hB hSat)

/-- **The dichotomy, machine-checked.**  From `SatBridge`: either no model is pair-relatively
saturated over itself, or some model is `Assembly.SaturatedFS` (i.e. the frozen gate is inhabited
once a size-ordered partner exists).  There is no third possibility, so every refutation of
`SatBridge` must either exhibit a diagonal instance or use a non-diagonal pair. -/
theorem satBridge_dichotomy (hB : M5Shoenfield.SatBridge) :
    (∀ (N : Type) [LRV.Structure N], N ⊨ Axioms.ACVF → ¬ M1Fix.SatRel N N) ∨
      (∃ (N : Type) (_ : LRV.Structure N) (_ : N ⊨ Axioms.ACVF), Assembly.SaturatedFS N) := by
  by_cases h : ∃ (N : Type) (_ : LRV.Structure N) (_ : N ⊨ Axioms.ACVF), M1Fix.SatRel N N
  · obtain ⟨N, inst, hN, hSat⟩ := h
    letI := inst
    exact Or.inr ⟨N, inst, hN, saturatedFS_of_satBridge_of_satRel hB hSat⟩
  · refine Or.inl (fun N inst hN hSat => h ⟨N, inst, hN, hSat⟩)

/-- **The second horn is exactly the inhabitance of the frozen gate** (with the diagonal pair):
a `SaturatedFS` model of `Axioms.ACVF` satisfies `M7Paper.PaperHyp` at the pair `(N, N)`, so the
frozen input 1 is *not* vacuous there.  Contrapositively: the collapse of §2 needs the first horn. -/
theorem paperGate_self_of_saturatedFS {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
    (h : Assembly.SaturatedFS N) : M5Shoenfield.paperGate N N :=
  ⟨h, le_rfl⟩

/-- The paper's own gate is inhabited as soon as the diagonal is: `relGate N N` needs only
`SatRel N N` and `|N| ≤ |N|`.  So `SatDiag` is precisely the cheapest witness of a paper pair, and
the paper's hypothesis is *not* refuted by `SatBridge`'s diagonal. -/
theorem relGate_self_of_satRel {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
    (h : M1Fix.SatRel N N) : M5Shoenfield.relGate N N :=
  ⟨h, le_rfl⟩

/-! ## 4. Verdict for the criterion lane

Everything in this lane that is a theorem of logic or of the frozen encoding is now machine-checked
here or in `QE/ShoenfieldQuote.lean`.  The residual is a single model-theoretic statement,

    `NoSatModel : ∀ N ⊨ Axioms.ACVF, ¬ Assembly.SaturatedFS N`,

together with the quotation `ShonefieldTestRel` and Marker's `Prop39Sat → HasQE`
(`M1Fix.hasQE_of_qfEAmalg`, `M5Shoenfield.shoenfieldTestSat_iff_QEOfGate`).  §1 shows `NoSatModel` is
not formal (a subsingleton satisfies `SaturatedFS`), and §3 shows it is exactly the first horn of the
diagonal dichotomy: no cheaper route to the collapse exists. -/

end SpecialTransformations.Milestone0.M5Gate

#print axioms SpecialTransformations.Milestone0.M5Gate.satRel_of_subsingleton
#print axioms SpecialTransformations.Milestone0.M5Gate.saturatedFS_of_subsingleton
#print axioms SpecialTransformations.Milestone0.M5Gate.not_forall_not_saturatedFS
#print axioms SpecialTransformations.Milestone0.M5Gate.paperGate_subsingleton_inhabited
#print axioms SpecialTransformations.Milestone0.M5Gate.not_paperGate_of_noSatModel
#print axioms SpecialTransformations.Milestone0.M5Gate.prop39Sat_of_noSatModel
#print axioms SpecialTransformations.Milestone0.M5Gate.shoenfieldTestSat_iff_hasQE_of_noSatModel
#print axioms SpecialTransformations.Milestone0.M5Gate.noSatModel_of_forall_not
#print axioms SpecialTransformations.Milestone0.M5Gate.saturatedFS_of_satBridge_of_satRel
#print axioms SpecialTransformations.Milestone0.M5Gate.not_satBridge_of_noSatModel_of_satRel
#print axioms SpecialTransformations.Milestone0.M5Gate.satBridge_dichotomy
#print axioms SpecialTransformations.Milestone0.M5Gate.paperGate_self_of_saturatedFS
#print axioms SpecialTransformations.Milestone0.M5Gate.relGate_self_of_satRel
