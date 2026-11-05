/-
# m8 / p8: the henselianity demand table

For each of Yin's case lemmas 3.4–3.8 (`refs/qe.tex` l. 613–815), where is
`M7Hens.IsHenselianVF` *consumed*, and does the case slot's conclusion need it?

This file machine-checks the two halves of the answer that the merged tree allows:

* **§2 (the honest predicate is inhabited).**  `IsHenselianVF S` holds of every substructure whose
  `VF`-part is the whole model — in particular of `⊤`.  This is the stress test the erratum of
  2026-11-04 (`¬ iLe (rv (a 0)) (rv 1)`) demands: the honest predicate must not be vacuous, or
  `M7Hens.HenselizationExists` would be a false quotation and the whole `M7Hens` route vacuous.
  The proof also records which *clauses* of `IsHenselianVF` are actually load-bearing: over a model
  only `Monic`-ness (degree + leading coefficient) and the constant-term clause are used; the
  coefficient-in-`O` clause and the `iUnits (rv (a 1))` clause are redundant (they matter over a
  henselian *local ring* `O(Ŝ)`, not over the field of a model).

* **§3 (henselianity is eliminable at the one-step).**  `OneStepAtHens` is the paper's per-element
  step with the henselianity hypothesis attached (the `hOne` of `M7Hens.oneStepVFP_of_hens`).
  Machine-checked: `OneStepAtHens ↔ OneStepSizeFree` given `HenselizationExists` and `ImmediateLift`.
  So henselianity buys exactly the *henselization step* (an immediate extension of `S` that is
  henselian, plus the lift of the monomorphism along it) — and nothing at the level of the frozen
  obligation.

* **§4 (the table rows).**  Each row is the tree's fragment for that case lemma, restated with an
  *added* `IsHenselianVF` hypothesis and proved by discarding it.  Read as: the fragment's
  conclusion does not consume henselianity; the place the paper uses it is the *embedding half*
  (Lemma 3.4's "irreducible + henselian ⟹ valued-field embedding of `⟨Ŝ,e⟩`"), which in the frozen
  encoding is the separate `M1QF.Frozen.StepObligation`/saturation input.

No `sorry`, no `axiom`, no `native_decide`; axiom audit at the end.
-/
import M7Hensel
import Standing
import VFValued
import VFAlgClosed
import RVDict
import M5L34_36
import HullAudit
import OneStepCases
import RV_henselian

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.HensDemand

/-! ## §1 The polynomial bridge `vfEval ↔ Polynomial.eval`

`M7Hens.vfEval` is the encoding's evaluation of `Σ_{i ≤ n} aᵢ xⁱ` in the `VF` sort.  To use
Mathlib's valuation theory (§2) we need it as `Polynomial.eval` of an honest polynomial over
`Transfer.VFType M`.  The encoding's `iVFAdd`/`iVFMul` **are** the field operations of `VFType`
definitionally, so the bridge is bookkeeping. -/

section PolyBridge

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The polynomial `Σ_{i ≤ n} Aᵢ Xⁱ` over the `VF` sort. -/
noncomputable def polyOf (A : ℕ → Transfer.VFType (M := M)) (n : ℕ) :
    Polynomial (Transfer.VFType (M := M)) :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (A i) * Polynomial.X ^ i

/-- The Horner-free evaluation fold, matching `M7Hens.vfSum` index by index. -/
noncomputable def evalFold (A : ℕ → Transfer.VFType (M := M)) (x : Transfer.VFType (M := M)) :
    ℕ → Transfer.VFType (M := M)
  | 0 => A 0
  | (k + 1) => evalFold A x k + A (k + 1) * x ^ (k + 1)

/-- The successor step of `polyOf`, matching `evalFold`'s recursion. -/
theorem polyOf_succ (A : ℕ → Transfer.VFType (M := M)) (k : ℕ) :
    polyOf A (k + 1) = polyOf A k + Polynomial.C (A (k + 1)) * Polynomial.X ^ (k + 1) := by
  simp only [polyOf, Finset.sum_range_succ]

theorem evalFold_val (A : ℕ → Transfer.VFType (M := M)) (x : Transfer.VFType (M := M)) :
    ∀ n, (evalFold A x n).1
      = M7Hens.vfEval (M := M) (fun i => (A i).1) n x.1
  | 0 => (RVCalc.vf_mul_one hM (A 0).2).symm
  | (k + 1) => by
    have h1 : (evalFold A x (k + 1)).1
        = iVFAdd (evalFold A x k).1 (iVFMul (A (k + 1)).1 ((x ^ (k + 1) : Transfer.VFType (M := M))).1) :=
      rfl
    rw [h1, evalFold_val A x k, StandingTree.vfTypePow_val]
    rfl

theorem evalFold_zero (A : ℕ → Transfer.VFType (M := M)) (n : ℕ) :
    evalFold A 0 n = A 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show evalFold A 0 k + A (k + 1) * (0 : Transfer.VFType (M := M)) ^ (k + 1) = A 0
    rw [ih]
    have hz : A (k + 1) * (0 : Transfer.VFType (M := M)) ^ (k + 1) = 0 := by
      rw [show (0 : Transfer.VFType (M := M)) ^ (k + 1) = 0 from zero_pow (Nat.succ_ne_zero k)]
      exact mul_zero _
    rw [hz]
    exact add_zero _

theorem eval_polyOf (A : ℕ → Transfer.VFType (M := M)) (x : Transfer.VFType (M := M))
    (n : ℕ) : (polyOf A n).eval x = evalFold A x n := by
  induction n with
  | zero =>
    have h : polyOf A 0 = Polynomial.C (A 0) := by
      rw [polyOf, show (0 : ℕ) + 1 = 1 from rfl, Finset.range_one, Finset.sum_singleton,
        pow_zero, mul_one]
    rw [h]
    show Polynomial.eval x (Polynomial.C (A 0)) = A 0
    rw [Polynomial.eval_C]
  | succ k ih =>
    rw [polyOf_succ, Polynomial.eval_add, ih]
    show evalFold A x k + Polynomial.eval x (Polynomial.C (A (k + 1)) * Polynomial.X ^ (k + 1))
      = evalFold A x k + A (k + 1) * x ^ (k + 1)
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rfl

theorem coeff_polyOf_self (A : ℕ → Transfer.VFType (M := M)) (n : ℕ) :
    (polyOf A n).coeff n = A n := by
  rw [polyOf, Polynomial.finsetSum_coeff]
  have h : ∀ i ∈ Finset.range (n + 1),
      (Polynomial.C (A i) * Polynomial.X ^ i).coeff n = if n = i then A i else 0 := by
    intro i _
    exact Polynomial.coeff_C_mul_X_pow (A i) i n
  rw [Finset.sum_congr rfl h, Finset.sum_eq_single n]
  · rw [if_pos rfl]
  · intro i _ hi
    exact if_neg (Ne.symm hi)
  · intro hn
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) hn

theorem coeff_polyOf_of_lt (A : ℕ → Transfer.VFType (M := M)) {n m : ℕ} (hm : n < m) :
    (polyOf A n).coeff m = 0 := by
  rw [polyOf, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [Polynomial.coeff_C_mul_X_pow]
  exact if_neg (by have := Finset.mem_range.mp hi; omega)

/-- `polyOf A n` is monic as soon as its top coefficient is `1`.  (The degree clause
`∀ i, n < i → A i = 0` of `IsHenselianVF` is *not* needed: `polyOf` already stops at `n`.) -/
theorem monic_polyOf (A : ℕ → Transfer.VFType (M := M)) {n : ℕ} (hn : A n = 1) :
    (polyOf A n).Monic := by
  have hdeg : (polyOf A n).natDegree = n := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      exact coeff_polyOf_of_lt A hm
    · intro h
      have h2 := congrArg Subtype.val h
      rw [coeff_polyOf_self, hn] at h2
      exact Transfer.vf_zero_ne_one hM h2.symm
  have hlead : (polyOf A n).leadingCoeff = 1 := by
    rw [Polynomial.leadingCoeff, hdeg, coeff_polyOf_self]
    exact hn
  exact hlead

end PolyBridge

/-! ## §2 The honest `IsHenselianVF` is inhabited: `VF`-full substructures are henselian

`IsHenselianVF S` is a statement about the valued field `(VF(S), O(S))`.  Over a model of `ACVF`
the `VF` sort is algebraically closed (`VFAlgClosed.isAlgClosed_vfType`), and an algebraically
closed valued field is henselian: `RVCalc.exists_root_of_eval_lt_one` (the Hensel lifting proved in
`QE/RV_henselian.lean`) produces, for a monic `F` with `F(0) ∈ m`, a root in `m`.  Transporting
along `VFValued.exists_valuation_predV` (a genuine Mathlib valuation whose order relation is the
encoding's `iLe ∘ rv`) gives the predicate.

Note which hypotheses of `IsHenselianVF` are *not* used: the coefficient-in-`O` clause and the
`iUnits (rv (a 1))` clause.  Over the field of a model the constant-term clause `a₀ ∈ m` alone
forces a root in `m` (the roots of a monic polynomial satisfy `Σ v(rᵢ) = v(a₀) > 0`, so one of them
has positive value).  Those two clauses are what a genuine `HenselianLocalRing` argument needs
(`O(Ŝ)` is only a *ring*), so this is a property of the model case, not a defect. -/

section Top

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- **Every `VF`-full substructure is henselian.**  `S` contains every `VF`-element of the model, so
the root produced in the model lies in `S`. -/
theorem isHenselianVF_of_vf_full (S : LRV.Substructure M) (hfull : ∀ x : M, iVF x → x ∈ S) :
    M7Hens.IsHenselianVF S := by
  classical
  intro n a _hn _hmem hVF hdeg hmon _hle h0 _h1
  obtain ⟨Γ, hΓ, w, hw⟩ := VFValued.exists_valuation_predV (M := M) (hM := hM)
  letI := hΓ
  haveI : IsAlgClosed (Transfer.VFType (M := M)) :=
    VFAlgClosed.isAlgClosed_vfType (M := M) (hM := hM)
  let A : ℕ → Transfer.VFType (M := M) := fun i => ⟨a i, hVF i⟩
  -- the constant term has negative value
  have hA0 : w (A 0) < 1 := by
    have h1 : ¬ (w (1 : Transfer.VFType (M := M)) ≤ w (A 0)) := fun hle =>
      h0 ((hw (1 : Transfer.VFType (M := M)) (A 0)).mpr hle)
    have h2 : w (A 0) < w (1 : Transfer.VFType (M := M)) := not_le.mp h1
    have h3 : w (1 : Transfer.VFType (M := M)) = 1 := Valuation.map_one w
    rw [h3] at h2
    exact h2
  -- the polynomial is monic and its value at `0` is the constant term
  have hAn : A n = (1 : Transfer.VFType (M := M)) := Subtype.ext hmon
  have hmonic : (polyOf A n).Monic := monic_polyOf A hAn
  have heval0 : (polyOf A n).eval 0 = A 0 := by
    rw [eval_polyOf, evalFold_zero]
  have hlt : w ((polyOf A n).eval 0) < 1 := by rw [heval0]; exact hA0
  -- Hensel lifting over an algebraically closed valued field
  obtain ⟨b, hbroot, hbm⟩ := RVCalc.exists_root_of_eval_lt_one (v := w) hmonic hlt
  refine ⟨b.1, hfull b.1 b.2, b.2, ?_, ?_⟩
  · have h1 : ((polyOf A n).eval b).1
        = M7Hens.vfEval (M := M) (fun i => (A i).1) n b.1 := by
      rw [eval_polyOf]
      exact evalFold_val A b n
    rw [Polynomial.IsRoot.def] at hbroot
    rw [← h1, hbroot]
    rfl
  · have hbw : w b < 1 := by
      have h := hbm
      have h1 : (0 : Transfer.VFType (M := M)) - b = -b := zero_sub b
      rw [h1] at h
      have h2 : w (-b) = w b := Valuation.map_neg w b
      rw [h2] at h
      exact h
    have hnot : ¬ (w (1 : Transfer.VFType (M := M)) ≤ w b) := by
      have h3 : w (1 : Transfer.VFType (M := M)) = 1 := Valuation.map_one w
      rw [h3]
      exact not_le.mpr hbw
    exact fun hle => hnot ((hw (1 : Transfer.VFType (M := M)) b).mp hle)

/-- **The honest `IsHenselianVF` is inhabited at `⊤`**: every model of `ACVF` is henselian in the
encoding's sense.  This is the ⊤-witness the erratum needs — without it `HenselizationExists` would
be a quotation with a false target, and `M7Hens.oneStepVFP_of_hens` vacuous. -/
theorem isHenselianVF_top : M7Hens.IsHenselianVF (⊤ : LRV.Substructure M) :=
  isHenselianVF_of_vf_full ⊤ (fun _ _ => trivial)

/-- The erratum's stress test, positive side, in the shape `HenselizationExists` consumes: the
conclusion of `HenselizationExists` is *inhabited at `⊤`*.  (`Immediate ⊤ ⊤` is reflexive, so the
henselian witness is `⊤` itself; what is not available in the tree is the witness at a *proper*
`S`, which is the honest henselization theorem.) -/
theorem exists_immediate_henselian_of_top :
    ∃ T : LRV.Substructure M, M6L33.Immediate (⊤ : LRV.Substructure M) T ∧
      M7Hens.IsHenselianVF T :=
  M7Hens.henselian_self_immediate isHenselianVF_top

end Top

/-! ## §3 Henselianity is eliminable at the one-step

The paper states Lemmas 3.4–3.6 at henselian `(VF(Ŝ), O(Ŝ))`.  The frozen obligation
`Assembly.OneStepVFP` carries no henselianity.  `OneStepAtHens` below is the paper's step with the
henselianity hypothesis attached; the two directions show it is exactly equivalent to the frozen
obligation *given* the henselization quotes.  So the demand the paper's hypothesis stands for is the
`HenselizationStep`: an immediate (hence `Standing`-preserving, `RV`-invisible) extension that gains
henselianity, together with the lift of the monomorphism along it. -/

section Step

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **The paper's per-element step at henselian domains** — `hOne` of
`M7Hens.paper_theorem_2_3_sat_of_hens`, i.e. Lemmas 3.4–3.8 with the henselian hypothesis of
3.4/3.5 kept. -/
def OneStepAtHens : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → M7Hens.IsHenselianVF S →
    ∀ m : M, iVF m →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T

/-- Henselianity is not needed when the step is available at every domain: the frozen
henselianity-free one-step implies the paper's henselian-domains one. -/
theorem oneStepAtHens_of_oneStepVFP (h : Assembly.OneStepVFP (M := M) (N := N)) :
    OneStepAtHens (M := M) (N := N) :=
  fun S f hS _hhen m hm => h S f hS m hm

end Step

/-- The global (all pairs) form of `OneStepAtHens`, the shape in which
`M7Hens.oneStepVFP_of_hens` consumes its `hOne`. -/
def OneStepAtHensAll : Prop :=
  ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF] [Q ⊨ Axioms.ACVF],
    OneStepAtHens (M := P) (N := Q)

/-- **Elimination, direction 1**: the henselianity-free frozen obligation gives the paper's step. -/
theorem oneStepAtHensAll_of_oneStepSizeFree (h : M7Paper.OneStepSizeFree) : OneStepAtHensAll :=
  fun P Q _ _ _ _ => oneStepAtHens_of_oneStepVFP (M := P) (N := Q) (h P Q)

/-- **Elimination, direction 2**: the paper's step at henselian domains gives the frozen obligation,
using the two henselization quotes.  This is `M7Hens.oneStepVFP_of_hens` read through the table. -/
theorem oneStepSizeFree_of_oneStepAtHensAll
    (hE : ∀ (P : Type) [LRV.Structure P] [P ⊨ Axioms.ACVF], M7Hens.HenselizationExists P)
    (hL : M7Hens.ImmediateLift) (h : OneStepAtHensAll) : M7Paper.OneStepSizeFree :=
  M7Hens.oneStepVFP_of_hens hE hL (fun P Q _ _ _ _ => h P Q)

/-- **The demand table's headline: `IsHenselianVF` is eliminable at the one-step.**  Given the
henselization quotes, the paper's henselian-domains version of Lemmas 3.4–3.8 and the frozen
henselianity-free `OneStepVFP` are the *same obligation*.  Henselianity therefore buys exactly
`HenselizationStep` (existence of the immediate henselian extension + the lift of the
monomorphism), not any part of the case analysis' arithmetic. -/
theorem oneStepAtHensAll_iff_oneStepSizeFree
    (hE : ∀ (P : Type) [LRV.Structure P] [P ⊨ Axioms.ACVF], M7Hens.HenselizationExists P)
    (hL : M7Hens.ImmediateLift) :
    OneStepAtHensAll ↔ M7Paper.OneStepSizeFree :=
  ⟨oneStepSizeFree_of_oneStepAtHensAll hE hL, oneStepAtHensAll_of_oneStepSizeFree⟩

/-! ## §4 The table rows: the tree's fragments do not consume henselianity

Each theorem below is the tree's own fragment for the case lemma named in its title, *with an
`IsHenselianVF` hypothesis added* and the proof discarding it.  What this machine-checks is exactly
the negative half of the demand table: adding henselianity to that fragment changes nothing, so the
fragment's conclusion is not derived from it.  (The positive half — that the paper *does* use
henselianity, for the embedding half of 3.4/3.5 — is prose: it is the sentence "irreducible over
`VF(Ŝ)` and `(VF(Ŝ), O(Ŝ))` henselian ⟹ a valued-field embedding `⟨Ŝ,e⟩ → N`", which in the frozen
encoding is the separate `M1QF.Frozen.StepObligation` / `M5Ledger.SaturationRealization` input.) -/

section Rows

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **Row 3.4 / 3.6 (separated branch): the `RV`/`Γ` half.**  `M5L`'s fragment produces
`Standing T` from `Standing S`, `VFInvClosedOn S`, the separation hypothesis, `rv e ∈ S` and the two
field-theoretic facts about `T` — and the added `IsHenselianVF S` is not used. -/
theorem row_separated_rv_half {S T : LRV.Substructure M} (hST : S ≤ T)
    (_hhen : M7Hens.IsHenselianVF S) (hS : Assembly.Standing S)
    (hfinv : M5L.VFInvClosedOn S) {e : M} (he : iVF e) (he0 : e ≠ Transfer.iVFZero (M := M))
    (heS : iRv e ∈ S) (hsep : M5L.Separated S e) (hgen : Assembly.IsVFGen T)
    (hquot : M5L.QuotExpansions S T e) : Assembly.Standing T :=
  M5L.standing_of_paper_hypotheses hM hST hS hfinv he he0 heS hsep hgen hquot

/-- **Row 3.6's `Γ`-half (the hull conclusion).**  `HullAudit`'s pinning theorem: the two
`DivisibilityStep` `Γ`-conjuncts pin `Γ(T)` to the divisible hull of `Γ(S)`.  The paper's Lemma 3.6
ends with exactly this (`RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv e⟩`); the added henselianity is not used — as
`HullAudit`'s verdict 4 says, the hull statement is group-theoretic. -/
theorem row_hull_gamma_half {S T : LRV.Substructure M} (hST : S ≤ T)
    (_hhen : M7Hens.IsHenselianVF S) (hdivT : Assembly.GammaDivisible (M := M) T)
    (hhull : M5Ledger.GammaHullInitial S T) :
    HullAudit.gammaSub (M := M) T =
      Ultramath.M2.divHull (HullAudit.gammaSub (M := M) S) :=
  HullAudit.divisibilityStep_pins_hull' hST hdivT hhull

/-- **Row 3.7 / 3.8 (value-new): the slot.**  `M5.OneStepRVNew` is the frozen form of Lemmas
3.7/3.8; it carries no henselianity.  The added hypothesis is discarded. -/
theorem row_newRV_slot (hnew : M5.OneStepRVNew (M := M) (N := N))
    (_hhen : M7Hens.IsHenselianVF (⊤ : LRV.Substructure M)) : M5.OneStepRVNew (M := M) (N := N) :=
  hnew

/-- **The embedding half alone discharges every slot.**  `M1QF.Frozen.StepObligation` is an atomic
match for the new element plus `RV`-control of the closure — the frozen encoding's form of "the
monomorphism extends to `⟨S, m⟩`".  A proof of it at every `(S, f, m)` gives all three slots of
`M4Cases.Cases` with no henselianity hypothesis anywhere.  This is the machine-checked form of the
table's positive statement: what henselianity is *for* in Lemma 3.4/3.5 is the embedding, and the
frozen encoding keeps the embedding as an independent input. -/
theorem row_embedding_half_discharges_all
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      M1QF.Frozen.StepObligation S f m) : M4Cases.Cases (M := M) (N := N) :=
  M4Cases.cases_of_stepObligation h

/-- **`isHenselianVF_top` unblocks Lemma 3.3's input 4 at `S = ⊤`.**  `QE/FinalRoute.lean`'s audit
of `DivisibilityStep` records that no cardinality content can be extracted from input 4 because the
only `S` that would force `#M ≤ #N` is `⊤`, "for which the tree does not derive `IsHenselianVF ⊤`".
That is exactly what §2 supplies: input 4 is now *applicable* at `S = ⊤` in every model. -/
theorem divisibilityStep_at_top (h : M5Ledger.DivisibilityStep (M := M) (N := N))
    (f : (⊤ : LRV.Substructure M) ↪[LRV] N) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : (⊤ : LRV.Substructure M) ≤ T),
      M5Ledger.Extends hST g f ∧ Assembly.GammaDivisible (M := M) T ∧
        M5Ledger.GammaHullInitial (⊤ : LRV.Substructure M) T :=
  h ⊤ f (fun _ _ => trivial) isHenselianVF_top

/-- Consequently input 4 is *not applicable* at a pair with `#N < #M`: its hypothesis at `S = ⊤`
already needs an embedding `M ↪ N`.  (This is the cardinality audit `FinalRoute`'s docstring
declares unavailable; it comes from the hypothesis `f`, not from input 4's conclusion.) -/
theorem input4_at_top_forces_size (f : (⊤ : LRV.Substructure M) ↪[LRV] N) :
    Cardinal.mk M ≤ Cardinal.mk N :=
  Cardinal.mk_le_of_injective (f := fun x : M => f ⟨x, trivial⟩)
    (fun a b hab => Subtype.ext_iff.mp (Embedding.injective f hab))

/-- **The table's punchline.**  The frozen target follows from the henselianity-free case ledger
`M4Cases.Cases` (plus the five Lemma-3.3 inputs).  The only occurrence of henselianity anywhere in
this route is `M5Ledger.LedgerInput2` — the henselization *existence* quotation, which Lemma 3.3
uses for its residue-representative step, not for the case lemmas. -/
theorem theorem_2_3_of_cases_no_henselianity
    (hShoen : M7Paper.ShoenfieldTestSat)
    (h1 : M5Ledger.LedgerInput1P) (h2 : M5Ledger.LedgerInput2)
    (h3 : M5Ledger.LedgerInput3P) (h4 : M5Ledger.LedgerInput4P) (h5 : M5Ledger.LedgerInput5P)
    (hcases : ∀ (M' N' : Type) [LRV.Structure M'] [LRV.Structure N'] [M' ⊨ Axioms.ACVF]
      [N' ⊨ Axioms.ACVF], M7Paper.PaperHyp M' N' → M4Cases.Cases (M := M') (N := N')) :
    HasQE Axioms.ACVF :=
  M4Cases.paper_theorem_2_3_sat_of_cases hShoen h1 h2 h3 h4 h5 hcases

end Rows

/-! ## §5 Non-vacuity of the separated slot's structural hypotheses

The tree replaces the paper's "`VF(Ŝ)` is a field" by `M5L.VFInvClosedOn S`, and the paper's
`⟨Ŝ,e⟩` by `IsVFGen` + `QuotExpansions`.  None of those is provable from `Standing` alone, so each
is a genuine hypothesis of the separated slot; the two lemmas below check that neither is *vacuous*
(it holds at `⊤` in every model).  Together with `isHenselianVF_top` this says the separated slot's
hypothesis package is jointly satisfiable at `S = ⊤`. -/

section NonVacuous

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `VFInvClosedOn ⊤`: the whole `VF` sort of a model is closed under inverses. -/
theorem vfInvClosedOn_top : M5L.VFInvClosedOn (⊤ : LRV.Substructure M) := by
  intro x hx _ hx0
  let X : Transfer.VFType (M := M) := ⟨x, hx⟩
  have hx' : X ≠ (0 : Transfer.VFType (M := M)) := fun h => hx0 (congrArg Subtype.val h)
  refine ⟨(X⁻¹).1, (X⁻¹).2, trivial, ?_⟩
  exact Transfer.vfInv_val (x := X) hx'

/-- `Assembly.IsVFGen ⊤`: every `RV`-element of a model is `rv` of a `VF`-element, up to `0`
(the encoding's `rvSurj` axiom). -/
theorem isVFGen_top : Assembly.IsVFGen (⊤ : LRV.Substructure M) := by
  intro x _ hxRV
  rcases Assembly.RVeqRvVF_of_model (M := M) x hxRV with ⟨y, hy, hyr⟩ | hz
  · exact Or.inl ⟨y, trivial, hy, hyr⟩
  · exact Or.inr hz

end NonVacuous

/-! ## §6 Axiom audit -/

#print axioms SpecialTransformations.Milestone0.HensDemand.polyOf_succ
#print axioms SpecialTransformations.Milestone0.HensDemand.evalFold_val
#print axioms SpecialTransformations.Milestone0.HensDemand.evalFold_zero
#print axioms SpecialTransformations.Milestone0.HensDemand.eval_polyOf
#print axioms SpecialTransformations.Milestone0.HensDemand.coeff_polyOf_self
#print axioms SpecialTransformations.Milestone0.HensDemand.coeff_polyOf_of_lt
#print axioms SpecialTransformations.Milestone0.HensDemand.monic_polyOf
#print axioms SpecialTransformations.Milestone0.HensDemand.isHenselianVF_of_vf_full
#print axioms SpecialTransformations.Milestone0.HensDemand.isHenselianVF_top
#print axioms SpecialTransformations.Milestone0.HensDemand.exists_immediate_henselian_of_top
#print axioms SpecialTransformations.Milestone0.HensDemand.oneStepAtHens_of_oneStepVFP
#print axioms SpecialTransformations.Milestone0.HensDemand.oneStepAtHensAll_of_oneStepSizeFree
#print axioms SpecialTransformations.Milestone0.HensDemand.oneStepSizeFree_of_oneStepAtHensAll
#print axioms SpecialTransformations.Milestone0.HensDemand.oneStepAtHensAll_iff_oneStepSizeFree
#print axioms SpecialTransformations.Milestone0.HensDemand.row_separated_rv_half
#print axioms SpecialTransformations.Milestone0.HensDemand.row_hull_gamma_half
#print axioms SpecialTransformations.Milestone0.HensDemand.row_newRV_slot
#print axioms SpecialTransformations.Milestone0.HensDemand.row_embedding_half_discharges_all
#print axioms SpecialTransformations.Milestone0.HensDemand.divisibilityStep_at_top
#print axioms SpecialTransformations.Milestone0.HensDemand.input4_at_top_forces_size
#print axioms SpecialTransformations.Milestone0.HensDemand.theorem_2_3_of_cases_no_henselianity
#print axioms SpecialTransformations.Milestone0.HensDemand.vfInvClosedOn_top
#print axioms SpecialTransformations.Milestone0.HensDemand.isVFGen_top

end SpecialTransformations.Milestone0.HensDemand
