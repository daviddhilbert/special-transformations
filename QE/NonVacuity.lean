/-
# m7 / p7 (direction d4) — Non-vacuity at `relGate`, and the Archimedean-config interaction

Swarm `smw2mluv7`, member m7.  The frozen route (`QE/Prop39Decomp.lean`)

    G3.paper_theorem_rel_two : ShoenfieldTestRel → Input5R → HasQE Axioms.ACVF

spends two quotations at the honest gate `relGate M N = M1Fix.SatRel M N ∧ #M ≤ #N`.
This file settles what makes that route non-vacuous and isolates the exact obligation behind
`QE/Prop39Decomp.lean`'s Archimedean-config refutations.  It proves nothing about `ACVF` itself.

## §1  The gate: conditional inhabitants, and the two degenerate readings

* `relGate_of_saturatedFS`, `relGate_diag_of_saturatedFS` — a `SaturatedFS` target gives a gate
  pair; the diagonal gate is `relGate N N`.
* `saturatedFS_of_relGate_diag` — with the tree's `SatBridge` gap, a diagonal gate pair *is* full
  saturation: the diagonal instance of the gate is saturation-hard.
* `qeOfGate_iff_hasQE_of_empty`, `shoenfieldTestRel_iff_hasQE_of_no_relGate` — **degenerate
  reading 1**: at an empty gate the quotation is *equivalent to the target*; the route is then
  circular (its first hypothesis is its conclusion).
* `shoenfieldTestRel_of_not_extendsAt` — **degenerate reading 2**: if the extension property
  fails, the quotation is trivially true.
* `input5R_of_no_relGate`, `extendsAt_relGate_of_no_relGate` — both hypotheses of the route are
  vacuous at an empty gate, so inhabitedness of the gate is load-bearing.
* `hasQE_iff_qfTypeDetWS` — `HasQE ACVF` is *equivalent* to well-sorted qf-type determination, so
  the conclusion is not strengthened by the criterion.
* `input5R_implies_prop39Sat` — `Input5R` implies the frozen Proposition 3.9.

## §2  The Archimedean configuration: the exact obligation

`G3.not_extendsAt_rel_of_archimedean_config` refutes the extension property *globally* from one
pair which is a `relGate` pair, has an `ArchimedeanRV` target, and carries the infinitesimal
configuration (`Hahn.not_embAt_of_infinitesimal`).  Machine-checked here:

* `not_finsat_of_configHuge` — at such a pair the pushed type of the configuration's element is
  **not finitely satisfiable** (tree: `G3.not_finSat_of_satRel_of_archimedean`).  Saturation
  realises finitely satisfiable types only, so the refutation is consistent only in the reading
  in which the configuration's type fails finite satisfiability.
* `not_finSatAt_iff` — **the exact obligation**: failure of finite satisfiability at a triple is
  *one formula* of the pushed type with no realisation in the target.
* `configHuge_ordinal_core_finsat`, `configTiny_ordinal_core_finsat` — but every finite piece of
  the configuration's **ordinal core** is realised in **every** model of `ACVF`, in particular at
  the Archimedean target: for the huge configuration by the single element `c^{N₀+1}`, for the
  tiny configuration by an `(N₀+1)`-st root of the target point (which exists because `Γ` is
  divisible, `StandingTree.gammaDivisible_top`).  Hence the failing formula asserted by the tree
  cannot be one of the configuration's own ordinal formulas: it must come from the
  residue-field/quantifier part of the pushed type.

## §3  The verdict (documented; the machine-checked content is §1–§2)

The configuration itself is not an obstruction to the *statement*: a source model with the
configuration and an Archimedean target exist in ordinary mathematics.  What must be decided is
whether such a pair can be a **gate** pair, and the tree's own theorem reduces that question
exactly to finite satisfiability of the configuration's pushed type.  If that type is finitely
satisfiable — the expected answer: by quantifier elimination for `ACVF` the type of the
configuration's element is determined by its quantifier-free (value/residue) type, and every
finite piece of that is realised in an Archimedean target by §2 plus residue-field freedom — then
`SatRel` realises it, contradicting `ArchimedeanRV N`, so no gate pair carries the configuration:
`not_extendsAt_rel_of_archimedean_config` and `not_prop39Sat_of_archimedean_config` are then
vacuous and `Input5R` is not refuted.  The tree proves only the consistency direction of the
other reading; the missing input for the first is precisely the non-ordinal part of the
configuration's finite satisfiability.

This §3 argument uses quantifier elimination for `ACVF`, i.e. the theorem the project is proving;
it is an argument *about the statement*, not a step in its proof.
-/
import Prop39Decomp
import M1Fix
import ShoenfieldQuote
import GammaGroup
import GammaDiv
import Jm2T1
import Standing

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.M7NonVac

/-! ## §1. The gate: conditional inhabitants and the degenerate readings -/

/-- `relGate` unfolded: definitional. -/
theorem relGate_iff (M N : Type) [LRV.Structure M] [LRV.Structure N] :
    M5Shoenfield.relGate M N ↔ M1Fix.SatRel M N ∧ M7Paper.SizeHyp M N :=
  Iff.rfl

/-- **The gate is inhabited at every pair whose target is `SaturatedFS`** and no smaller than the
source (`SaturatedFS N` is `∀ M, SatRel M N`). -/
theorem relGate_of_saturatedFS {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hSat : Assembly.SaturatedFS N) (hsize : M7Paper.SizeHyp M N) :
    M5Shoenfield.relGate M N :=
  ⟨(M1Fix.saturatedFS_iff.mp hSat) M, hsize⟩

/-- The diagonal instance: a `SaturatedFS` model inhabits the gate at `M = N`. -/
theorem relGate_diag_of_saturatedFS {N : Type} [LRV.Structure N] [hN : N ⊨ Axioms.ACVF]
    (hSat : Assembly.SaturatedFS N) : M5Shoenfield.relGate N N :=
  relGate_of_saturatedFS hSat (le_refl _)

/-- **The diagonal gate is saturation-hard**: given the tree's `SatBridge` gap, a diagonal gate
pair is exactly full saturation (`M5Shoenfield.satBridge_diagonal`). -/
theorem saturatedFS_of_relGate_diag (hB : M5Shoenfield.SatBridge) {N : Type} [LRV.Structure N]
    [hN : N ⊨ Axioms.ACVF] (h : M5Shoenfield.relGate N N) : Assembly.SaturatedFS N :=
  M5Shoenfield.satBridge_diagonal hB N h.1

/-- **Degenerate reading 1, abstract form.**  At an empty gate the criterion
`ExtendsAt G → HasQE` collapses to `HasQE`: the criterion then *is* the target. -/
theorem qeOfGate_iff_hasQE_of_empty (G : M5Shoenfield.Gate)
    (hG : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N], ¬ G M N) :
    (M5Shoenfield.QEOfGate G ↔ HasQE Axioms.ACVF) := by
  constructor
  · intro hQ
    refine hQ ?_
    intro M N _ _ _ _ hg _ _
    exact absurd hg (hG M N)
  · intro hQE _
    exact hQE

/-- **Degenerate reading 1 for the quotation**: at an empty `relGate` the quotation is equivalent
to the target, so the two-hypothesis route is circular unless the gate is inhabited. -/
theorem shoenfieldTestRel_iff_hasQE_of_no_relGate
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N], ¬ M5Shoenfield.relGate M N) :
    (M5Shoenfield.ShoenfieldTestRel ↔ HasQE Axioms.ACVF) :=
  qeOfGate_iff_hasQE_of_empty M5Shoenfield.relGate h

/-- **Degenerate reading 2**: if the extension property fails, the criterion is trivially true.
So `ShoenfieldTestRel` has content only where the extension property *holds*. -/
theorem shoenfieldTestRel_of_not_extendsAt (h : ¬ M5Shoenfield.ExtendsAt M5Shoenfield.relGate) :
    M5Shoenfield.ShoenfieldTestRel :=
  fun hExt => absurd hExt h

/-- At an empty gate the extension property is vacuous. -/
theorem extendsAt_relGate_of_no_relGate
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N], ¬ M5Shoenfield.relGate M N) :
    M5Shoenfield.ExtendsAt M5Shoenfield.relGate :=
  fun M N _ _ _ _ hR => absurd hR (h M N)

/-- At an empty gate the second hypothesis `Input5R` is vacuous too. -/
theorem input5R_of_no_relGate
    (h : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N], ¬ M5Shoenfield.relGate M N) :
    M5Shoenfield.Input5R :=
  fun M N _ _ _ _ hR => absurd hR (h M N)

/-- **The conclusion is not strengthened by the criterion**: `HasQE ACVF` is *equivalent* to the
well-sorted qf-type determination property that the Shoenfield criterion produces. -/
theorem hasQE_iff_qfTypeDetWS :
    HasQE Axioms.ACVF ↔ M1Shoenfield.QFTypeDetWS Axioms.ACVF :=
  ⟨M1Shoenfield.qfTypeDetWS_of_hasQE, M1Shoenfield.hasQE_ACVF_of_qfTypeDet⟩

/-- `Input5R` implies the frozen Proposition 3.9, so it is not a weakening of the paper's
statement (tree: `G3.prop39Sat_of_input5R`). -/
theorem input5R_implies_prop39Sat (h5 : M5Shoenfield.Input5R) : M7Paper.Prop39Sat :=
  G3.prop39Sat_of_input5R h5

/-! ## §2. The Archimedean configuration: the exact obligation -/

section Config

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-- The **huge** configuration: an `RV`-element `m` strictly above `1` and above every power of a
parameter `s ∈ S` of positive value (configuration of `G3.not_finSat_of_satRel_of_archimedean`). -/
def ConfigHuge (S : LRV.Substructure M) (s m : M) : Prop :=
  s ∈ S ∧ iRV s ∧ s ≠ iRVZero ∧ ¬ iLe s iRVOne ∧
    iRV m ∧ m ≠ iRVZero ∧ ¬ iLe m iRVOne ∧ ∀ n : ℕ, iLe (Assembly.rvPow s n) m

/-- The **tiny** configuration: a `VF`-element `m ∉ S` whose `rv` is strictly above `1` and below
every power of a parameter `s ∈ S` of positive value (configuration of
`Hahn.not_embAt_of_infinitesimal`, used by `G3.not_extendsAt_rel_of_archimedean_config`). -/
def ConfigTiny (S : LRV.Substructure M) (s m : M) : Prop :=
  s ∈ S ∧ iRV s ∧ s ≠ iRVZero ∧ ¬ iLe s iRVOne ∧
    iVF m ∧ m ∉ S ∧ ¬ iLe (iRv m) iRVOne ∧ ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s

/-- Finite satisfiability of the pushed type at one triple `(S, f, m)` — the antecedent of
`M1Fix.SatRel`. -/
def FinSatAt (S : LRV.Substructure M) (f : ↥S ↪[LRV] N) (m : M) : Prop :=
  ∀ φ : LRV.Formula (S ⊕ Unit), φ.Realize (Realize.mv S m) → ∃ b : N, φ.Realize (Realize.wv f b)

/-- `QFFinSat` is finite satisfiability at every triple. -/
theorem qffinsat_iff_finSatAt :
    M2Saturation.QFFinSat M N ↔ ∀ (S : LRV.Substructure M) (f : ↥S ↪[LRV] N) (m : M),
      FinSatAt S f m :=
  Iff.rfl

/-- **THE EXACT OBLIGATION.**  Failure of finite satisfiability at a triple is *one formula* of the
pushed type with no realisation in the target.  So "does the Archimedean-config refutation bite?"
is exactly: *is there such a formula, and which one?* -/
theorem not_finSatAt_iff (S : LRV.Substructure M) (f : ↥S ↪[LRV] N) (m : M) :
    ¬ FinSatAt S f m ↔
      ∃ φ : LRV.Formula (S ⊕ Unit),
        φ.Realize (Realize.mv S m) ∧ ∀ b : N, ¬ φ.Realize (Realize.wv f b) := by
  constructor
  · intro h
    simp only [FinSatAt] at h
    push_neg at h
    exact h
  · rintro ⟨φ, hφ, hno⟩ hfs
    obtain ⟨b, hb⟩ := hfs φ hφ
    exact hno b hb

variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **The tree's theorem in configuration form**: at a gate pair with an Archimedean target
carrying the huge configuration, the pushed type fails finite satisfiability.  (`f` is not part of
the configuration; it is the arbitrary embedding at which the finite satisfiability is evaluated,
so it is quantified here as an argument.) -/
theorem not_finsat_of_configHuge (hSat : M1Fix.SatRel M N) (hArch : Hahn.ArchimedeanRV N)
    {S : LRV.Substructure M} {f : ↥S ↪[LRV] N} {s m : M} (h : ConfigHuge (M := M) S s m) :
    ¬ M2Saturation.QFFinSat M N :=
  G3.not_finSat_of_satRel_of_archimedean (f := f) hSat hArch h.1 h.2.1 h.2.2.1 h.2.2.2.1
    h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2

/-- **The tree's refutation in configuration form**: one gate pair with an Archimedean target
carrying the tiny configuration refutes the extension property at the gate (hence `Input5R`,
hence `Prop39Sat`). -/
theorem not_extendsAt_of_configTiny (hSat : M1Fix.SatRel M N) (hsize : M7Paper.SizeHyp M N)
    (hArch : Hahn.ArchimedeanRV N) {S : LRV.Substructure M} {f : ↥S ↪[LRV] N} {s m : M}
    (h : ConfigTiny (M := M) S s m) :
    ¬ M5Shoenfield.ExtendsAt M5Shoenfield.relGate :=
  G3.not_extendsAt_rel_of_archimedean_config (f := f) hSat hsize hArch h.1 h.2.1 h.2.2.1 h.2.2.2.1
    h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2

/-- The tiny configuration refutes the extension property **at the pair** (`ExtendsHere`), with no
saturation and no gate hypothesis (`G3.not_extendsHere_of_archimedean`). -/
theorem not_extendsHere_of_configTiny (hArch : Hahn.ArchimedeanRV N) {S : LRV.Substructure M}
    {f : ↥S ↪[LRV] N} {s m : M} (h : ConfigTiny (M := M) S s m) :
    ¬ G3.ExtendsHere M N :=
  G3.not_extendsHere_of_archimedean (f := f) hArch h.1 h.2.1 h.2.2.1 h.2.2.2.1
    h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2

/-- **The configuration refutes the route's *second hypothesis*, not merely the extension
property.**  A single gate pair with an Archimedean target carrying the tiny configuration makes
`Input5R` false, so the two-hypothesis final statement is vacuous at that pair. -/
theorem not_input5R_of_config_gate_pair
    (hSat : M1Fix.SatRel M N) (hsize : M7Paper.SizeHyp M N) (hArch : Hahn.ArchimedeanRV N)
    {S : LRV.Substructure M} {f : ↥S ↪[LRV] N} {s m : M} (h : ConfigTiny (M := M) S s m) :
    ¬ M5Shoenfield.Input5R := fun h5 =>
  not_extendsHere_of_configTiny (f := f) hArch h
    (G3.extendsAt_rel_of_input5R h5 M N ⟨hSat, hsize⟩)

/-- **If the huge configuration's pushed type were finitely satisfiable at the triple, then the
triple could not be a `SatRel` pair over an Archimedean target.**  So the refutations bite exactly
at the pairs where the type fails finite satisfiability. -/
theorem not_satRel_of_configHuge_of_finsat
    {S : LRV.Substructure M} {f : ↥S ↪[LRV] N} {s m : M} (h : ConfigHuge (M := M) S s m)
    (hfin : FinSatAt S f m) (hArch : Hahn.ArchimedeanRV N) :
    ¬ M1Fix.SatRel M N := by
  intro hSat
  obtain ⟨b, hb⟩ := hSat S f m hfin
  -- `b` realises the whole pushed type, in particular `m`'s ordinal core, contradicting
  -- the Archimedean property; this is `Hahn.not_archimedeanRV_of_infinitesimalRoom`.
  have hbRV : iRV b := by
    have hφ : (Hahn.fRV (Hahn.varX S)).Realize (Realize.mv S m) := by
      simp [h.2.2.2.2.1]
    simpa using hb (Hahn.fRV (Hahn.varX S)) hφ
  have hbne : b ≠ iRVZero := by
    have hφ : (Hahn.fNe (Hahn.varX S) Hahn.rvZeroTm).Realize (Realize.mv S m) := by
      simp [h.2.2.2.2.2.1]
    simpa using hb (Hahn.fNe (Hahn.varX S) Hahn.rvZeroTm) hφ
  have hbgt : ¬ iLe b iRVOne := by
    have hφ : (Hahn.fNotLe (Hahn.varX S) Hahn.rvOneTm).Realize (Realize.mv S m) := by
      simp [h.2.2.2.2.2.2.1]
    simpa using hb (Hahn.fNotLe (Hahn.varX S) Hahn.rvOneTm) hφ
  have hfsRV : iRV (f ⟨s, h.1⟩) := by
    have hφ : (Hahn.fRV (Hahn.varP ⟨s, h.1⟩)).Realize (Realize.mv S m) := by
      simp [h.2.1]
    simpa using hb (Hahn.fRV (Hahn.varP ⟨s, h.1⟩)) hφ
  have hfsne : f ⟨s, h.1⟩ ≠ iRVZero := by
    have hφ : (Hahn.fNe (Hahn.varP ⟨s, h.1⟩) Hahn.rvZeroTm).Realize (Realize.mv S m) := by
      simp [h.2.2.1]
    simpa using hb (Hahn.fNe (Hahn.varP ⟨s, h.1⟩) Hahn.rvZeroTm) hφ
  have hfsgt : ¬ iLe (f ⟨s, h.1⟩) iRVOne := by
    have hφ : (Hahn.fNotLe (Hahn.varP ⟨s, h.1⟩) Hahn.rvOneTm).Realize (Realize.mv S m) := by
      simp [h.2.2.2.1]
    simpa using hb (Hahn.fNotLe (Hahn.varP ⟨s, h.1⟩) Hahn.rvOneTm) hφ
  have hbinf : ∀ n : ℕ, iLe (Assembly.rvPow (f ⟨s, h.1⟩) n) b := by
    intro n
    have hφ : (Hahn.fLe (Hahn.powTm (Hahn.varP ⟨s, h.1⟩) n) (Hahn.varX S)).Realize
        (Realize.mv S m) := by
      simp [Hahn.powTm_realize, h.2.2.2.2.2.2.2 n]
    have hle := hb (Hahn.fLe (Hahn.powTm (Hahn.varP ⟨s, h.1⟩) n) (Hahn.varX S)) hφ
    simpa [Hahn.powTm_realize] using hle
  exact Hahn.not_archimedeanRV_of_infinitesimalRoom hN hfsRV hbRV hbne hfsne hfsgt hbinf hArch

/-- The same configuration already refutes the one-step **at the pair**, with no saturation and no
`Standing` hypothesis (`Hahn.not_oneStepAt_of_infinitesimal_sharp`): the failure of the extension
is a fact about the value groups; only its *application to the gate* needs `SatRel`. -/
theorem not_oneStepAt_of_configTiny (hArch : Hahn.ArchimedeanRV N) {S : LRV.Substructure M}
    {f : ↥S ↪[LRV] N} {s m : M} (h : ConfigTiny (M := M) S s m) :
    ¬ Hahn.OneStepAt S f m :=
  Hahn.not_oneStepAt_of_infinitesimal_sharp hArch h.1 h.2.1 h.2.2.1 h.2.2.2.1
    h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2

/-! ### §2.1 Powers in the `RV` sort -/

variable {c : M}

/-- `rvPow` stays in the `RV` sort. -/
theorem rvPow_iRV (hc : iRV c) (n : ℕ) : iRV (Assembly.rvPow c n) :=
  Hahn.rvPow_mem hM hc n

/-- `rvPow` of a nonzero element stays nonzero. -/
theorem rvPow_ne (hc : iRV c) (hc0 : c ≠ iRVZero) (n : ℕ) :
    Assembly.rvPow c n ≠ iRVZero :=
  Hahn.rvPow_ne_zero hM hc hc0 n

/-- Product monotonicity in the `RV` preorder (`leMulCompatFull` twice). -/
theorem mul_le_mul_rv {a a' b b' : M} (ha : iRV a) (ha' : iRV a') (hb : iRV b) (hb' : iRV b')
    (ha'0 : a' ≠ iRVZero) (hb0 : b ≠ iRVZero) (h1 : iLe a a') (h2 : iLe b b') :
    iLe (iRVMul a b) (iRVMul a' b') := by
  have h1' : iLe (iRVMul a b) (iRVMul a' b) := GammaGroup.le_mul_right_rv ha ha' hb hb0 h1
  have h2' : iLe (iRVMul a' b) (iRVMul a' b') := by
    rw [Transfer.rv_mul_comm_of_model hM ha' hb, Transfer.rv_mul_comm_of_model hM ha' hb']
    exact GammaGroup.le_mul_right_rv hb hb' ha' ha'0 h2
  exact RVCalc.le_trans_rv hM (Transfer.rv_mul_mem hM ha hb) (Transfer.rv_mul_mem hM ha' hb)
    (Transfer.rv_mul_mem hM ha' hb') h1' h2'

/-- **`1 ≤ rvPow c n` whenever `1 ≤ c`.** -/
theorem one_le_rvPow (hc : iRV c) (hc0 : c ≠ iRVZero) (hc1 : iLe iRVOne c) :
    ∀ n : ℕ, iLe iRVOne (Assembly.rvPow c n)
  | 0 => by
    rw [Assembly.rvPow.eq_1]
    exact RVCalc.le_refl_rv hM (Transfer.rv_one_mem hM)
  | (n + 1) => by
    rw [Assembly.rvPow.eq_2]
    have hn : iRV (Assembly.rvPow c n) := rvPow_iRV hc n
    have h := mul_le_mul_rv (a := iRVOne) (a' := Assembly.rvPow c n) (b := iRVOne) (b' := c)
      (Transfer.rv_one_mem hM) hn (Transfer.rv_one_mem hM) hc
      (rvPow_ne hc hc0 n) (RVCalc.rv_one_ne_zero hM)
      (one_le_rvPow hc hc0 hc1 n) hc1
    rwa [Transfer.rv_mul_one_any_right hM (Transfer.rv_one_mem hM)] at h

/-- Splitting powers: `c^{n+k} = c^n · c^k`. -/
theorem rvPow_mul_add (hc : iRV c) (n k : ℕ) :
    Assembly.rvPow c (n + k) = iRVMul (Assembly.rvPow c n) (Assembly.rvPow c k) := by
  induction k with
  | zero =>
    rw [Nat.add_zero, Assembly.rvPow.eq_1,
      Transfer.rv_mul_one_any_right hM (rvPow_iRV hc n)]
  | succ k ih =>
    rw [Nat.add_succ, Assembly.rvPow.eq_2, ih, Assembly.rvPow.eq_2,
      Transfer.rv_mul_assoc_of_model hM (rvPow_iRV hc n) (rvPow_iRV hc k) hc]

/-- **Powers increase** when `1 ≤ c`. -/
theorem rvPow_mono (hc : iRV c) (hc0 : c ≠ iRVZero) (hc1 : iLe iRVOne c) {n m : ℕ}
    (hnm : n ≤ m) : iLe (Assembly.rvPow c n) (Assembly.rvPow c m) := by
  induction m, hnm using Nat.le_induction with
  | base => exact RVCalc.le_refl_rv hM (rvPow_iRV hc n)
  | succ m hnm ih =>
    refine RVCalc.le_trans_rv hM (rvPow_iRV hc n) (rvPow_iRV hc m)
      (rvPow_iRV hc (m + 1)) ih ?_
    rw [Assembly.rvPow.eq_2]
    have hone : iRV (iRVOne (M := M)) := Transfer.rv_one_mem hM
    have hm : iRV (Assembly.rvPow c m) := rvPow_iRV hc m
    have h := GammaGroup.le_mul_right_rv hone hc hm (rvPow_ne hc hc0 m) hc1
    rwa [Transfer.rv_mul_one_any hM hm, Transfer.rv_mul_comm_of_model hM hc hm] at h

/-- **The ordinal core of the huge configuration is finitely satisfiable in every model.**  For
every finite set of exponents there is one `RV`-element above `1` and above all the corresponding
powers of `c` (namely `c^{N₀+1}`). -/
theorem configHuge_ordinal_core_finsat (hc : iRV c) (hc0 : c ≠ iRVZero)
    (hcgt : ¬ iLe c iRVOne) (N₀ : ℕ) :
    ∃ b : M, iRV b ∧ b ≠ iRVZero ∧ ¬ iLe b iRVOne ∧
      ∀ n : ℕ, n ≤ N₀ → iLe (Assembly.rvPow c n) b := by
  have hc1 : iLe iRVOne c :=
    (RVCalc.le_total_rv hM hc (Transfer.rv_one_mem hM)).resolve_left hcgt
  refine ⟨Assembly.rvPow c (N₀ + 1), rvPow_iRV hc (N₀ + 1), rvPow_ne hc hc0 (N₀ + 1), ?_, ?_⟩
  · intro hle
    have h1 : iLe c (Assembly.rvPow c (N₀ + 1)) := by
      have h := rvPow_mono hc hc0 hc1 (n := 1) (m := N₀ + 1) (by omega)
      rwa [Assembly.rvPow.eq_2, Assembly.rvPow.eq_1, Transfer.rv_mul_one_any hM hc] at h
    exact hcgt (RVCalc.le_trans_rv hM hc (rvPow_iRV hc (N₀ + 1)) (Transfer.rv_one_mem hM) h1 hle)
  · intro n hn
    exact rvPow_mono hc hc0 hc1 (by omega)

/-- **Powers of an element below `1` stay below `1`.** -/
theorem rvPow_le_one (hu : iRV c) (hu0 : c ≠ iRVZero) (hu1 : iLe c iRVOne) :
    ∀ k : ℕ, iLe (Assembly.rvPow c k) iRVOne
  | 0 => by
    rw [Assembly.rvPow.eq_1]
    exact RVCalc.le_refl_rv hM (Transfer.rv_one_mem hM)
  | (k + 1) => by
    rw [Assembly.rvPow.eq_2]
    have hk : iRV (Assembly.rvPow c k) := rvPow_iRV hu k
    have h := mul_le_mul_rv (a := Assembly.rvPow c k) (a' := iRVOne) (b := c) (b' := iRVOne)
      hk (Transfer.rv_one_mem hM) hu (Transfer.rv_one_mem hM)
      (RVCalc.rv_one_ne_zero hM) hu0 (rvPow_le_one hu hu0 hu1 k) hu1
    rwa [Transfer.rv_mul_one_any hM (Transfer.rv_one_mem hM)] at h

/-- **The ordinal core of the tiny configuration is finitely satisfiable in every model.**  For
every finite set of exponents there is an `RV`-element above `1` whose corresponding powers are
all below `c`: the `(N₀+1)`-st root of `c`, which exists because `Γ = RV/Kˣ` is divisible
(`StandingTree.gammaDivisible_top`).  The `Kˣ`-ambiguity allowed by `GammaDivisible` is absorbed by
the unit factor `c'`, which is `≤ 1`. -/
theorem configTiny_ordinal_core_finsat (hc : iRV c) (hc0 : c ≠ iRVZero)
    (hcgt : ¬ iLe c iRVOne) (N₀ : ℕ) :
    ∃ b : M, iRV b ∧ b ≠ iRVZero ∧ ¬ iLe b iRVOne ∧
      ∀ n : ℕ, n ≤ N₀ → iLe (Assembly.rvPow b n) c := by
  have hc1 : iLe iRVOne c :=
    (RVCalc.le_total_rv hM hc (Transfer.rv_one_mem hM)).resolve_left hcgt
  obtain ⟨u, c', -, hu, hu0, -, hc'unit, hpow⟩ :=
    (StandingTree.gammaDivisible_top (M := M)) c (Substructure.mem_top c) hc hc0 (N₀ + 1)
      (by omega)
  have hc'rv : iRV c' := Jm2.iRV_of_units (M := M) hc'unit
  have hc'0 : c' ≠ iRVZero := GammaGroup.units_ne_zero (M := M) hc'unit
  have hc'le1 : iLe c' iRVOne := ((RVCalc.units_iff_le_one hM hc'rv hc'0).mp hc'unit).2
  have hc'ge1 : iLe iRVOne c' := ((RVCalc.units_iff_le_one hM hc'rv hc'0).mp hc'unit).1
  have hc_le : iLe c (iRVMul c c') := by
    have h := (RVCalc.le_mul_iff hM (Transfer.rv_one_mem hM) hc'rv hc hc0).mp hc'ge1
    rwa [Transfer.rv_mul_one_any hM hc, Transfer.rv_mul_comm_of_model hM hc'rv hc] at h
  have hune : ¬ iLe u iRVOne := by
    intro hule
    have hle1 : iLe (Assembly.rvPow u (N₀ + 1)) iRVOne := rvPow_le_one hu hu0 hule (N₀ + 1)
    rw [hpow] at hle1
    exact hcgt (RVCalc.le_trans_rv hM hc (Transfer.rv_mul_mem hM hc hc'rv)
      (Transfer.rv_one_mem hM) hc_le hle1)
  have hu1 : iLe iRVOne u := (RVCalc.le_total_rv hM hu (Transfer.rv_one_mem hM)).resolve_left hune
  refine ⟨u, hu, hu0, hune, ?_⟩
  intro n hn
  have hj : n + (N₀ + 1 - n) = N₀ + 1 := Nat.add_sub_cancel' (by omega)
  have hsplit : Assembly.rvPow u (N₀ + 1) =
      iRVMul (Assembly.rvPow u n) (Assembly.rvPow u (N₀ + 1 - n)) := by
    have h := rvPow_mul_add hu n (N₀ + 1 - n)
    rwa [hj] at h
  have hc'le : iLe c' (Assembly.rvPow u (N₀ + 1 - n)) :=
    RVCalc.le_trans_rv hM hc'rv (Transfer.rv_one_mem hM) (rvPow_iRV hu (N₀ + 1 - n))
      hc'le1 (one_le_rvPow hu hu0 hu1 (N₀ + 1 - n))
  have h1 : iLe (iRVMul (Assembly.rvPow u n) (Assembly.rvPow u (N₀ + 1 - n)))
      (iRVMul c c') := by
    rw [← hsplit, hpow]
    exact RVCalc.le_refl_rv hM (Transfer.rv_mul_mem hM hc hc'rv)
  have h2 : iLe (iRVMul c c') (iRVMul c (Assembly.rvPow u (N₀ + 1 - n))) := by
    rw [Transfer.rv_mul_comm_of_model hM hc hc'rv,
      Transfer.rv_mul_comm_of_model hM hc (rvPow_iRV hu (N₀ + 1 - n))]
    exact GammaGroup.le_mul_right_rv hc'rv (rvPow_iRV hu (N₀ + 1 - n)) hc hc0 hc'le
  have h3 : iLe (iRVMul (Assembly.rvPow u n) (Assembly.rvPow u (N₀ + 1 - n)))
      (iRVMul c (Assembly.rvPow u (N₀ + 1 - n))) :=
    RVCalc.le_trans_rv hM (Transfer.rv_mul_mem hM (rvPow_iRV hu n) (rvPow_iRV hu (N₀ + 1 - n)))
      (Transfer.rv_mul_mem hM hc hc'rv) (Transfer.rv_mul_mem hM hc (rvPow_iRV hu (N₀ + 1 - n)))
      h1 h2
  exact (RVCalc.le_mul_iff hM (rvPow_iRV hu n) hc (rvPow_iRV hu (N₀ + 1 - n))
    (rvPow_ne hu hu0 (N₀ + 1 - n))).mpr h3

end Config

/-! ## §2.2 The frozen theory is strictly stronger than the pre-repair theory: `axNontrivialRV` -/

/-- `axNontrivialRV` (the nontriviality of the valuation) is part of the frozen `Axioms.ACVF`;
it is *not* part of the pre-repair `ACVFpaper` of `Milestone0/accepted/ACVFModel.lean`, which is
why that file's `exists_model_ACVF` does not establish consistency of the frozen theory. -/
theorem axNontrivialRV_mem : Axioms.axNontrivialRV ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Axioms.repairRV, Axioms.ofList, Set.mem_union,
    Set.mem_ofPred_eq, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, true_or,
    or_true]

/-! ## §3. Axiom audit -/

#print axioms SpecialTransformations.Milestone0.M7NonVac.relGate_of_saturatedFS
#print axioms SpecialTransformations.Milestone0.M7NonVac.saturatedFS_of_relGate_diag
#print axioms SpecialTransformations.Milestone0.M7NonVac.shoenfieldTestRel_iff_hasQE_of_no_relGate
#print axioms SpecialTransformations.Milestone0.M7NonVac.shoenfieldTestRel_of_not_extendsAt
#print axioms SpecialTransformations.Milestone0.M7NonVac.input5R_of_no_relGate
#print axioms SpecialTransformations.Milestone0.M7NonVac.hasQE_iff_qfTypeDetWS
#print axioms SpecialTransformations.Milestone0.M7NonVac.input5R_implies_prop39Sat
#print axioms SpecialTransformations.Milestone0.M7NonVac.not_finSatAt_iff
#print axioms SpecialTransformations.Milestone0.M7NonVac.not_finsat_of_configHuge
#print axioms SpecialTransformations.Milestone0.M7NonVac.not_extendsAt_of_configTiny
#print axioms SpecialTransformations.Milestone0.M7NonVac.not_oneStepAt_of_configTiny
#print axioms SpecialTransformations.Milestone0.M7NonVac.configHuge_ordinal_core_finsat
#print axioms SpecialTransformations.Milestone0.M7NonVac.configTiny_ordinal_core_finsat
#print axioms SpecialTransformations.Milestone0.M7NonVac.not_extendsHere_of_configTiny
#print axioms SpecialTransformations.Milestone0.M7NonVac.not_input5R_of_config_gate_pair
#print axioms SpecialTransformations.Milestone0.M7NonVac.not_satRel_of_configHuge_of_finsat
#print axioms SpecialTransformations.Milestone0.M7NonVac.axNontrivialRV_mem

end SpecialTransformations.Milestone0.M7NonVac
