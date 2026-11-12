module

/-
**The `mul`-cancellation normal form off `Kˣ`** — from swarm `smw1bwjo2` m3, verified here
(compiled, 0 errors, no `sorry`; `#print axioms` on `rv_mul_eq_mul_iff`, `rv_mul_solution_unique`,
`mkMul_perm`, `rv_mul_inv`, `pEq_tRVMul_iff`: all within {propext, Classical.choice, Quot.sound}).

This is the third of the three blockers the handoff named.  The mixed-context elimination needs to
cancel a common `rvMul` factor at elements *outside* `Kˣ`, and the frozen axioms guard the unit laws
by `Kˣ` (`rvMulOne`, `rvMulInv` say nothing off the units).  What makes it work is the *repaired*
pair `rvMulOneRV`/`rvMulInvRV`, which are unguarded, so cancellation is available on all of `RV^×`:

* `rv_mul_eq_mul_iff : a ≠ 0 → (a * b = a * c ↔ b = c)`, and the left/right forms;
* `rv_mul_solution_unique : a ≠ 0 → ∃! x, iRV x ∧ x * a = b`;
* the word layer `mkMul` (a fold of `tRVMul` over a list) with `realize_mkMul`, `mkMul_ne_zero`,
  `mkMul_units` (a word of units is the residue-field factor), `mkMul_append`, `rvPow`,
  `mkMul_pow_times_factor` (`tⁿ · rest`), `mkMul_perm` (the value depends only on the multiset),
  `mkMul_cons_eq_iff`;
* the formula layer for the QF cover: `pEq_tRVMul_iff`, `pEq_tRVMul_right_iff`,
  `pEq_mkMul_cons_iff`.

So the QF cover at a mixed context can now put an arbitrary `RV`-monomial into the normal form
`tⁿ · (residue factor)`, which is exactly what `qfq_cover` (`smw19wtoj` m3's named gap) was missing.
Not attempted here, and still open: `qfq_cover` itself.
-/
/-
The `mul` normal form on `RV`, off `Kˣ`.

The mixed-context quantifier elimination (the `qfq_cover` piece of the `L_RV` QE induction) has to
compare two *group words* in the multiplicative group `RV^×`: nested `rvMul`-combinations of `RV`-terms.
The residue-field operations `kAdd`, `kNeg` are junk at elements off `K = Kˣ ∪ {0}` (`kJunkZero`,
`kNegJunkZero`), so on the off-`K` part of `RV` the *only* structure available is the multiplication —
and there the elimination needs two things:

* **cancellation**: `a · b = a · c ↔ b = c` for `a ≠ 0`, so that a common factor of two words can be
  divided out and a word equation reduced to a shorter one; and
* **the normal form**: a word whose factors are all in `Kˣ` is a single "residue-field factor", so
  `x · c₁ · ⋯ · cₖ = t` reads `x · c = t` with `c ∈ Kˣ` — one term times a residue-field factor,
  and by cancellation `x` is then *uniquely determined* by `t` and the `cᵢ`.

Both facts are consequences of the two *repair* axioms `Axioms.rvMulOneRV` (`1 · x = x` for every
`x ≠ 0`, not merely for `x ∈ Kˣ`) and `Axioms.rvMulInvRV` (every `x ≠ 0` is invertible), together
with the group axioms `rvMulAssoc`/`rvMulComm`/`rvMulInfty`.  This is exactly why the repair was
needed: `Axioms.rvMulOne`/`rvMulInv` are guarded by `pUnits`, hence give a group structure only on
`Kˣ` and no cancellation at off-`K` elements.

Main results (namespace `SpecialTransformations.Milestone0.MulNormalForm`, all under
`hM : M ⊨ Axioms.ACVF`):

* `rv_mul_ne_zero`, `rv_mul_eq_zero` — `RV^×` is closed under `×` and `0` is absorbing;
* `rv_mul_left_cancel`, `rv_mul_right_cancel`, `rv_mul_eq_mul_iff` — cancellation at any `a ≠ 0`,
  with no `iUnits` hypothesis;
* `rv_mul_solution_unique` — `x · a = b` has exactly one solution in `RV`;
* `rv_mul_eq_iff_inv_mul` — that solution is `a⁻¹ · b`;
* `mkMul`, `realize_mkMul`, `iRV_realize_mkMul`, `mkMul_ne_zero`, `mkMul_units` — the term-level
  word and the `Kˣ`-factor normal form; `mkMul_single_times_factor` — one term times a
  residue-field factor;
* `mkMul_cons_eq_iff` — cancellation of a leading factor of two words; `rv_mul_swap`,
  `mkMul_perm` — a word's value depends only on the *multiset* of its factors;
* `mkMul_append`, `rvPow`, `realize_tRVPow`, `mkMul_replicate`, `mkMul_pow_times_factor` — the
  `∏ t_j^{a_j}` form, i.e. `t ^ n` times the remaining factors;
* `pEq_tRVMul_iff`, `pEq_tRVMul_right_iff`, `pEq_mkMul_cons_iff` — the same at the level of
  *formulas*: a common `rvMul` factor can be cancelled inside a quantifier-free atom, which is the
  form the QF-cover argument consumes.
-/
public import Enc

@[expose] public section

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace SpecialTransformations
namespace Milestone0
namespace MulNormalForm

open LRV Axioms

variable {M : Type} [LRV.Structure M]

/-! ## 0. Realisation lemmas for the symbols of `L_RV`

These are copied from `QE/Assembly_val.lean` (where they are proved against the same encoding);
they are not in `Milestone0/Encoding.lean` itself. -/

theorem realize_tv {k : ℕ} (i : Fin k) (v : Empty → M) (x : Fin k → M) :
    (tv i.1 i.2).realize (Sum.elim v x) = x i := rfl

theorem realize_tRVZero {k : ℕ} (v : Empty ⊕ Fin k → M) :
    (tRVZero (n := k)).realize v = (iRVZero : M) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvZero
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iRVZero
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem realize_tRVOne {k : ℕ} (v : Empty ⊕ Fin k → M) :
    (tRVOne (n := k)).realize v = (iRVOne : M) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvOne
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iRVOne
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem realize_tRVMul {k : ℕ} (v : Empty ⊕ Fin k → M) (a b : Tm k) :
    (tRVMul a b).realize v = iRVMul (a.realize v) (b.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvMul
      (fun i => Term.realize (L := LRV) v (![a, b] i)) = iRVMul (a.realize v) (b.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a, b] i))
      = ![a.realize v, b.realize v] from by
    funext i
    fin_cases i <;> simp]
  rfl

theorem pVF_realize {k : ℕ} (t : Tm k) (v : Empty → M) (x : Fin k → M) :
    (pVF t).Realize v x ↔ iVF (t.realize (Sum.elim v x)) := by
  show FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memVF
      (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      ↔ iVF (t.realize (Sum.elim v x))
  rw [show (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      = ![t.realize (Sum.elim v x)] from by
    funext i
    fin_cases i
    simp]
  rfl

theorem pRVsort_realize {k : ℕ} (t : Tm k) (v : Empty → M) (x : Fin k → M) :
    (pRVsort t).Realize v x ↔ iRV (t.realize (Sum.elim v x)) := by
  show FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memRV
      (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      ↔ iRV (t.realize (Sum.elim v x))
  rw [show (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      = ![t.realize (Sum.elim v x)] from by
    funext i
    fin_cases i
    simp]
  rfl

theorem sortPred_realize {k : ℕ} (s : SortTag) (t : Tm k) (v : Empty → M) (x : Fin k → M) :
    (sortPred s t).Realize v x ↔
      (match s with
        | .vf => iVF (t.realize (Sum.elim v x))
        | .rv => iRV (t.realize (Sum.elim v x))) := by
  cases s with
  | vf => exact pVF_realize t v x
  | rv => exact pRVsort_realize t v x

theorem pUnits_realize {k : ℕ} (t : Tm k) (v : Empty → M) (x : Fin k → M) :
    (pUnits t).Realize v x ↔ iUnits (t.realize (Sum.elim v x)) := by
  show FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memUnits
      (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      ↔ iUnits (t.realize (Sum.elim v x))
  rw [show (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      = ![t.realize (Sum.elim v x)] from by
    funext i
    fin_cases i
    simp]
  rfl

theorem pRV_realize {k : ℕ} (t : Tm k) (v : Empty → M) (x : Fin k → M) :
    (pRV t).Realize v x ↔ t.realize (Sum.elim v x) ≠ iRVZero := by
  simp only [pRV, pEq, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    realize_tRVZero]

theorem sortedHyps_foldr_realize {k : ℕ} (ss : Fin k → SortTag)
    (l : List (Fin k)) (v : Empty → M) (x : Fin k → M) :
    (l.foldr (fun i acc => sortPred (ss i) (tv i.1 i.2) ⊓ acc) ⊤).Realize v x
      ↔ ∀ i ∈ l, (match ss i with
          | .vf => iVF (x i)
          | .rv => iRV (x i)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, BoundedFormula.realize_inf, ih]
    have hhead : (sortPred (ss a) (tv a.1 a.2)).Realize v x
        ↔ (match ss a with | .vf => iVF (x a) | .rv => iRV (x a)) := by
      rw [sortPred_realize, realize_tv]
    rw [hhead]
    constructor
    · rintro ⟨ha, hall⟩ i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact ha
      · exact hall i hi
    · intro h
      exact ⟨h a List.mem_cons_self, fun i hi => h i (List.mem_cons_of_mem a hi)⟩

theorem sortedHyps_realize {k : ℕ} (ss : Fin k → SortTag)
    (v : Empty → M) (x : Fin k → M) :
    (sortedHyps ss).Realize v x ↔ ∀ i, (match ss i with
        | .vf => iVF (x i)
        | .rv => iRV (x i)) := by
  rw [sortedHyps, sortedHyps_foldr_realize]
  constructor
  · intro h i
    exact h i (List.mem_finRange i)
  · intro h i _
    exact h i

theorem allSorted_realize {T : LRV.Theory} (hM : M ⊨ T)
    {k : ℕ} {ss : Fin k → SortTag} {φ : Bf k} (hmem : allSorted ss φ ∈ T) :
    ∀ x : Fin k → M, (∀ i, (match ss i with
        | .vf => iVF (x i)
        | .rv => iRV (x i)))
      → @BoundedFormula.Realize LRV M _ Empty k φ (default : Empty → M) x := by
  intro x hx
  have h := hM.realize_of_mem (allSorted ss φ) hmem
  simp only [allSorted, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_imp] at h
  exact h x ((sortedHyps_realize ss (default : Empty → M) x).mpr hx)

theorem allOne_realize {T : LRV.Theory} (hM : M ⊨ T)
    {φ : Bf 1} (hmem : allOne φ ∈ T) :
    ∀ x : Fin 1 → M,
      @BoundedFormula.Realize LRV M _ Empty 1 φ (default : Empty → M) x := by
  intro x
  have h := hM.realize_of_mem (allOne φ) hmem
  simp only [allOne, Sentence.Realize, BoundedFormula.realize_alls] at h
  exact h x

/-- The value of the variable that `Fin.snoc` appends. -/
theorem realize_tv_last_apply {k : ℕ} (v : Empty → M) (x : Fin k → M) (a : M) :
    (tv k (Nat.lt_succ_self k)).realize (Sum.elim v (Fin.snoc x a)) = a := by
  rw [show tv k (Nat.lt_succ_self k) = tv (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)).1
      (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)).2 from rfl, realize_tv]
  simp [Fin.snoc]

/-- **The guarded existential**, semantically: `∃ x ∈ s, φ`. -/
theorem exSorted_realize {k : ℕ} (s : SortTag) (φ : Bf (k + 1)) (v : Empty → M)
    (x : Fin k → M) :
    (exSorted s φ).Realize v x ↔
      ∃ a : M, (match s with | .vf => iVF a | .rv => iRV a) ∧ φ.Realize v (Fin.snoc x a) := by
  have key : ∀ a : M, (sortPred s (tv k (Nat.lt_succ_self k))).Realize v (Fin.snoc x a)
      ↔ (match s with | .vf => iVF a | .rv => iRV a) := by
    intro a
    rw [sortPred_realize, realize_tv_last_apply]
  simp only [exSorted, BoundedFormula.realize_ex, BoundedFormula.realize_inf, key]

/-! ## 1. Membership of the axioms of `ACVF` -/

theorem mem_ACVF_sortClosure {s : LRV.Sentence} (h : s ∈ Axioms.sortClosure) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.sortAxioms, Set.mem_union]
  tauto

theorem mem_ACVF_rvGroup {s : LRV.Sentence} (h : s ∈ Axioms.rvGroup) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

theorem mem_ACVF_repairRV {s : LRV.Sentence} (h : s ∈ Axioms.repairRV) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

theorem mem_ACVF_kField {s : LRV.Sentence} (h : s ∈ Axioms.kField) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

theorem mem_ACVF_sdRVMul : Axioms.sdRVMul ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_rvZeroNeOne : (∼(pEq tRVZero tRVOne) : LRV.Sentence) ∈ Axioms.ACVF :=
  mem_ACVF_kField (by simp [Axioms.kField, Axioms.ofList])

/-- `1 ≠ 0` in `RV` (`Axioms.kField`'s `0 ≠ 1`). -/
theorem rv_one_ne_zero (hM : M ⊨ Axioms.ACVF) : (iRVOne : M) ≠ iRVZero := by
  have h := hM.realize_of_mem (φ := ∼(pEq tRVZero tRVOne)) mem_ACVF_rvZeroNeOne
  rw [Sentence.Realize] at h
  simp only [Formula.Realize, BoundedFormula.realize_not, pEq,
    BoundedFormula.realize_bdEqual, realize_tRVZero, realize_tRVOne] at h
  exact fun hc => h hc.symm

theorem mem_ACVF_sdRVZero : Axioms.sdRVZero ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdRVOne : Axioms.sdRVOne ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdUnits : Axioms.sdUnits ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_rvMulAssoc : Axioms.rvMulAssoc ∈ Axioms.ACVF :=
  mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvMulComm : Axioms.rvMulComm ∈ Axioms.ACVF :=
  mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvMulMem : Axioms.rvMulMem ∈ Axioms.ACVF :=
  mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvMulInfty : Axioms.rvMulInfty ∈ Axioms.ACVF :=
  mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvOneMem : Axioms.rvOneMem ∈ Axioms.ACVF :=
  mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvMulOneRV : Axioms.rvMulOneRV ∈ Axioms.ACVF :=
  mem_ACVF_repairRV (by simp [Axioms.repairRV, Axioms.ofList])

theorem mem_ACVF_rvMulInvRV : Axioms.rvMulInvRV ∈ Axioms.ACVF :=
  mem_ACVF_repairRV (by simp [Axioms.repairRV, Axioms.ofList])

/-! ## 2. The sort discipline on `RV` -/

/-- `RV` is closed under `×` (`Axioms.sdRVMul`). -/
theorem rv_mul_mem (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iRV x) (hy : iRV y) :
    iRV (iRVMul x y) := by
  have h := allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv])
    (φ := pRVsort (tRVMul &0 &1)) mem_ACVF_sdRVMul ![x, y]
    (by intro i; fin_cases i <;> simp [hx, hy])
  rw [pRVsort_realize] at h
  simpa [realize_tRVMul] using h

/-- `0` of `RV` lies in `RV`. -/
theorem rv_zero_mem (hM : M ⊨ Axioms.ACVF) : iRV (iRVZero : M) := by
  have h := hM.realize_of_mem Axioms.sdRVZero mem_ACVF_sdRVZero
  rw [Axioms.sdRVZero, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pRVsort_realize, realize_tRVZero] at h
  exact h

/-- `1` of `RV` lies in `RV`. -/
theorem rv_one_mem (hM : M ⊨ Axioms.ACVF) : iRV (iRVOne : M) := by
  have h := hM.realize_of_mem Axioms.sdRVOne mem_ACVF_sdRVOne
  rw [Axioms.sdRVOne, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pRVsort_realize, realize_tRVOne] at h
  exact h

/-- Every element of `Kˣ` is an `RV`-element (`Axioms.sdUnits`). -/
theorem units_mem_rv (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iUnits a) : iRV a := by
  have h := allOne_realize hM (φ := (pUnits &0 ⟹ pRVsort &0)) mem_ACVF_sdUnits ![a]
  have h' : iUnits a → iRV a := by simpa [pUnits_realize, pRVsort_realize] using h
  exact h' ha

/-- `1 ∈ Kˣ` (`Axioms.rvOneMem`). -/
theorem units_one (hM : M ⊨ Axioms.ACVF) : iUnits (iRVOne : M) := by
  have h := hM.realize_of_mem Axioms.rvOneMem mem_ACVF_rvOneMem
  rw [Axioms.rvOneMem, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pUnits_realize, realize_tRVOne] at h
  exact h

/-- `Kˣ` is closed under `×` (`Axioms.rvMulMem`). -/
theorem units_mul (hM : M ⊨ Axioms.ACVF) {a b : M} (ha : iUnits a) (hb : iUnits b)
    (harv : iRV a) (hbrv : iRV b) : iUnits (iRVMul a b) := by
  have h := allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv])
    (φ := (pUnits &0 ⟹ (pUnits &1 ⟹ pUnits (tRVMul &0 &1)))) mem_ACVF_rvMulMem ![a, b]
    (by intro i; fin_cases i <;> simp [harv, hbrv])
  have h' : iUnits a → iUnits b → iUnits (iRVMul a b) := by
    simpa [pUnits_realize, realize_tRVMul] using h
  exact h' ha hb

/-! ## 3. The multiplicative group structure of `RV` -/

/-- `×` on the `RV` sort is commutative (`Axioms.rvMulComm`). -/
theorem rv_mul_comm (hM : M ⊨ Axioms.ACVF) {a b : M} (ha : iRV a) (hb : iRV b) :
    iRVMul a b = iRVMul b a := by
  have h := allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv])
    (φ := pEq (tRVMul &0 &1) (tRVMul &1 &0)) mem_ACVF_rvMulComm ![a, b]
    (by intro i; fin_cases i <;> simp [ha, hb])
  rw [pEq, BoundedFormula.realize_bdEqual] at h
  simpa [realize_tRVMul] using h

/-- `×` on the `RV` sort is associative (`Axioms.rvMulAssoc`). -/
theorem rv_mul_assoc (hM : M ⊨ Axioms.ACVF) {x y z : M} (hx : iRV x) (hy : iRV y) (hz : iRV z) :
    iRVMul (iRVMul x y) z = iRVMul x (iRVMul y z) := by
  have h := allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv, SortTag.rv])
    (φ := pEq (tRVMul (tRVMul &0 &1) &2) (tRVMul &0 (tRVMul &1 &2))) mem_ACVF_rvMulAssoc
    ![x, y, z] (by intro i; fin_cases i <;> simp [hx, hy, hz])
  rw [pEq, BoundedFormula.realize_bdEqual] at h
  simpa [realize_tRVMul] using h

/-- `1` is neutral for `×` at every *nonzero* `RV`-element (`Axioms.rvMulOneRV`, a repair axiom).
This is the axiom that makes cancellation work off `Kˣ`. -/
theorem rv_mul_one_of_ne_zero (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) (ha0 : a ≠ iRVZero) :
    iRVMul iRVOne a = a := by
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pRV &0 ⟹ pEq (tRVMul tRVOne &0) &0)) mem_ACVF_rvMulOneRV ![a]
    (by intro i; fin_cases i; simpa using ha)
  have h' : a ≠ iRVZero → iRVMul (iRVOne : M) a = a := by
    simpa [pRV, pEq, realize_tRVMul, realize_tRVOne, realize_tRVZero] using h
  exact h' ha0

/-- Every nonzero `RV`-element is invertible (`Axioms.rvMulInvRV`, a repair axiom). -/
theorem rv_mul_inv (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) (ha0 : a ≠ iRVZero) :
    ∃ b : M, iRV b ∧ b ≠ iRVZero ∧ iRVMul b a = iRVOne := by
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pRV &0 ⟹ exSorted .rv (pRV &1 ⊓ pEq (tRVMul &1 &0) tRVOne))) mem_ACVF_rvMulInvRV
    ![a] (by intro i; fin_cases i; simpa using ha)
  rw [BoundedFormula.realize_imp, pRV_realize, exSorted_realize] at h
  obtain ⟨b, hb, hbody⟩ := h ha0
  have hsplit : b ≠ iRVZero ∧ iRVMul b a = iRVOne := by
    simpa [pRV, pEq, realize_tRVMul, realize_tRVZero, realize_tRVOne] using hbody
  exact ⟨b, hb, hsplit.1, hsplit.2⟩

/-- `a · 0 = 0` on the `RV` sort (`Axioms.rvMulInfty`); `0 = ∞` absorbs. -/
theorem rv_mul_infty (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) :
    iRVMul a iRVZero = iRVZero := by
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := pEq (tRVMul &0 tRVInfty) tRVInfty) mem_ACVF_rvMulInfty ![a]
    (by intro i; fin_cases i; simpa using ha)
  rw [pEq, BoundedFormula.realize_bdEqual] at h
  simpa [realize_tRVMul, realize_tRVZero, tRVInfty] using h

/-- `0 · b = 0` on the `RV` sort. -/
theorem rv_zero_mul (hM : M ⊨ Axioms.ACVF) {b : M} (hb : iRV b) :
    iRVMul iRVZero b = iRVZero := by
  rw [rv_mul_comm hM (rv_zero_mem hM) hb]
  exact rv_mul_infty hM hb

/-- `1` is neutral for `×` at *every* `RV`-element (the `0` case is absorption). -/
theorem rv_mul_one_all (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) :
    iRVMul iRVOne a = a := by
  by_cases ha0 : a = iRVZero
  · rw [ha0, rv_mul_infty hM (rv_one_mem hM)]
  · exact rv_mul_one_of_ne_zero hM ha ha0

/-- `a · 1 = a` on `RV`. -/
theorem rv_mul_one_right (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) :
    iRVMul a iRVOne = a := by
  rw [rv_mul_comm hM ha (rv_one_mem hM)]
  exact rv_mul_one_all hM ha

/-- **`RV^×` is closed under `×`**: a product of two nonzero `RV`-elements is nonzero.

This uses only the repair axioms: if `a · b = 0` with `b ≠ 0` and `c · b = 1`, then
`a = 1 · a = (c · b) · a = c · (a · b) = c · 0 = 0`. -/
theorem rv_mul_ne_zero (hM : M ⊨ Axioms.ACVF) {a b : M} (ha : iRV a) (hb : iRV b)
    (ha0 : a ≠ iRVZero) (hb0 : b ≠ iRVZero) : iRVMul a b ≠ iRVZero := by
  intro hab
  obtain ⟨c, hc, -, hcb⟩ := rv_mul_inv hM hb hb0
  have key : a = iRVZero := by
    calc a = iRVMul iRVOne a := (rv_mul_one_of_ne_zero hM ha ha0).symm
      _ = iRVMul (iRVMul c b) a := by rw [hcb]
      _ = iRVMul c (iRVMul b a) := rv_mul_assoc hM hc hb ha
      _ = iRVMul c (iRVMul a b) := by rw [rv_mul_comm hM hb ha]
      _ = iRVMul c iRVZero := by rw [hab]
      _ = iRVZero := rv_mul_infty hM hc
  exact ha0 key

/-- `a · b = 0 ↔ a = 0 ∨ b = 0` on `RV`. -/
theorem rv_mul_eq_zero_iff (hM : M ⊨ Axioms.ACVF) {a b : M} (ha : iRV a) (hb : iRV b) :
    iRVMul a b = iRVZero ↔ a = iRVZero ∨ b = iRVZero := by
  constructor
  · intro h
    by_cases ha0 : a = iRVZero
    · exact Or.inl ha0
    · exact Or.inr (by
        by_contra hb0
        exact rv_mul_ne_zero hM ha hb ha0 hb0 h)
  · rintro (rfl | rfl)
    · exact rv_zero_mul hM hb
    · exact rv_mul_infty hM ha

/-- **Cancellation on `RV`** by a nonzero left factor.  No `iUnits` hypothesis: the factor may be
any `RV`-element off `K = Kˣ ∪ {0}`, which is the point of the repair axioms. -/
theorem rv_mul_left_cancel (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c)
    (ha0 : a ≠ iRVZero) (h : iRVMul a b = iRVMul a c) : b = c := by
  by_cases hb0 : b = iRVZero
  · have hc0 : c = iRVZero := by
      have hz : iRVMul a c = iRVZero := by
        rw [← h, hb0, rv_mul_infty hM ha]
      rcases (rv_mul_eq_zero_iff hM ha hc).mp hz with h' | h'
      · exact absurd h' ha0
      · exact h'
    rw [hb0, hc0]
  · by_cases hc0 : c = iRVZero
    · have hb' : b = iRVZero := by
        have hz : iRVMul a b = iRVZero := by
          rw [h, hc0, rv_mul_infty hM ha]
        rcases (rv_mul_eq_zero_iff hM ha hb).mp hz with h' | h'
        · exact absurd h' ha0
        · exact h'
      exact absurd hb' hb0
    · obtain ⟨d, hd, -, hda⟩ := rv_mul_inv hM ha ha0
      have h1 : iRVMul (iRVMul d a) b = iRVMul (iRVMul d a) c := by
        rw [rv_mul_assoc hM hd ha hb, rv_mul_assoc hM hd ha hc, h]
      rw [hda, rv_mul_one_of_ne_zero hM hb hb0,
        rv_mul_one_of_ne_zero hM hc hc0] at h1
      exact h1

/-- **Cancellation on `RV`** by a nonzero right factor. -/
theorem rv_mul_right_cancel (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c)
    (ha0 : a ≠ iRVZero) (h : iRVMul b a = iRVMul c a) : b = c := by
  apply rv_mul_left_cancel hM ha hb hc ha0
  rw [rv_mul_comm hM ha hb, rv_mul_comm hM ha hc]
  exact h

/-- **The `mul`-cancellation dictionary**: at a nonzero left factor, `×` is left-cancellative. -/
theorem rv_mul_eq_mul_iff (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c)
    (ha0 : a ≠ iRVZero) : iRVMul a b = iRVMul a c ↔ b = c :=
  ⟨fun h => rv_mul_left_cancel hM ha hb hc ha0 h, fun h => by rw [h]⟩

/-! ### 4. Solving `x · a = b`

Eliminating an `RV`-variable from a multiplicative atom is the *unique-solution* statement below:
`x · a = b` has at most one solution in `RV` as soon as `a ≠ 0`, and it has one as soon as
`a ≠ 0` and `b ∈ RV`.  So an atom `x · a = b` pins `x` given one solution, and two such atoms are
compared by cancelling `x`. -/

/-- **The solution formula for `x · a = b`**: for any inverse `d` of `a`, the equation is equivalent
to `x = d · b`.  (With `a ∈ Kˣ`, `d` and `d · b` are computed inside `K`.) -/
theorem rv_mul_eq_iff_inv_mul (hM : M ⊨ Axioms.ACVF) {a b x d : M} (ha : iRV a) (hb : iRV b)
    (hx : iRV x) (hd : iRV d) (hda : iRVMul d a = iRVOne) :
    iRVMul x a = b ↔ x = iRVMul d b := by
  constructor
  · intro h
    calc x = iRVMul iRVOne x := (rv_mul_one_all hM hx).symm
      _ = iRVMul (iRVMul d a) x := by rw [hda]
      _ = iRVMul d (iRVMul a x) := rv_mul_assoc hM hd ha hx
      _ = iRVMul d (iRVMul x a) := by rw [rv_mul_comm hM ha hx]
      _ = iRVMul d b := by rw [h]
  · intro h
    rw [h]
    calc iRVMul (iRVMul d b) a = iRVMul d (iRVMul b a) := rv_mul_assoc hM hd hb ha
      _ = iRVMul d (iRVMul a b) := by rw [rv_mul_comm hM hb ha]
      _ = iRVMul (iRVMul d a) b := (rv_mul_assoc hM hd ha hb).symm
      _ = iRVMul iRVOne b := by rw [hda]
      _ = b := rv_mul_one_all hM hb

/-- **`x · a = b` has at most one solution in `RV`** for `a ≠ 0`, and it has one when `b ∈ RV`. -/
theorem rv_mul_solution_unique (hM : M ⊨ Axioms.ACVF) {a b : M} (ha : iRV a) (hb : iRV b)
    (ha0 : a ≠ iRVZero) : ∃! x : M, iRV x ∧ iRVMul x a = b := by
  obtain ⟨d, hd, -, hda⟩ := rv_mul_inv hM ha ha0
  have hx : iRV (iRVMul d b) := rv_mul_mem hM hd hb
  refine ⟨iRVMul d b, ⟨hx, (rv_mul_eq_iff_inv_mul hM ha hb hx hd hda).mpr rfl⟩, ?_⟩
  rintro x ⟨hx', hxeq⟩
  exact (rv_mul_eq_iff_inv_mul hM ha hb hx' hd hda).mp hxeq

/-! ## 5. Group words: the term-level normal form

A *group word* is a term in the multiplicative language of `RV`.  `mkMul l` is the word with factor
list `l`; `mkMul_units` says that a word all of whose factors lie in `Kˣ` is a single element of
`Kˣ` — the "residue-field factor" of a word — and `mkMul_cons_eq_iff` cancels a common leading
factor of two words. -/

/-- The product of a list of terms, read in the multiplicative language of `RV`. -/
def mkMul {k : ℕ} (l : List (Tm k)) : Tm k := l.foldr tRVMul tRVOne

theorem mkMul_nil {k : ℕ} : (mkMul ([] : List (Tm k))) = tRVOne := rfl

theorem mkMul_cons {k : ℕ} (t : Tm k) (l : List (Tm k)) :
    mkMul (t :: l) = tRVMul t (mkMul l) := rfl

/-- A word with a head factor: its value is the head times the value of the tail. -/
theorem mkMul_realize_cons {k : ℕ} (V : Empty ⊕ Fin k → M) (t : Tm k) (l : List (Tm k)) :
    (mkMul (t :: l)).realize V = iRVMul (t.realize V) ((mkMul l).realize V) := by
  show (tRVMul t (mkMul l)).realize V = _
  rw [realize_tRVMul]

/-- A word realises as the product of its factors. -/
theorem realize_mkMul {k : ℕ} (V : Empty ⊕ Fin k → M) (l : List (Tm k)) :
    (mkMul l).realize V = l.foldr (fun t acc => iRVMul (t.realize V) acc) (iRVOne : M) := by
  induction l with
  | nil => exact realize_tRVOne V
  | cons t l ih =>
    show (tRVMul t (mkMul l)).realize V
      = iRVMul (t.realize V) (l.foldr (fun t acc => iRVMul (t.realize V) acc) iRVOne)
    rw [realize_tRVMul, ih]

/-- A word whose factors are all in `RV` is in `RV`. -/
theorem iRV_realize_mkMul (hM : M ⊨ Axioms.ACVF) {k : ℕ} (V : Empty ⊕ Fin k → M) (l : List (Tm k))
    (h : ∀ t ∈ l, iRV (t.realize V)) : iRV ((mkMul l).realize V) := by
  induction l with
  | nil => simpa [mkMul, realize_tRVOne] using rv_one_mem hM
  | cons t l ih =>
    have ht : iRV (t.realize V) := h t List.mem_cons_self
    have hl : ∀ u ∈ l, iRV (u.realize V) := fun u hu => h u (List.mem_cons_of_mem t hu)
    have hgoal : (mkMul (t :: l)).realize V
        = iRVMul (t.realize V) ((mkMul l).realize V) := by
      show (tRVMul t (mkMul l)).realize V = _
      rw [realize_tRVMul]
    rw [hgoal]
    exact rv_mul_mem hM ht (ih hl)

/-- A word none of whose factors is `0` is nonzero. -/
theorem mkMul_ne_zero (hM : M ⊨ Axioms.ACVF) {k : ℕ} (V : Empty ⊕ Fin k → M) (l : List (Tm k))
    (h : ∀ t ∈ l, iRV (t.realize V) ∧ t.realize V ≠ iRVZero) :
    (mkMul l).realize V ≠ iRVZero := by
  induction l with
  | nil =>
    show (tRVOne : Tm k).realize V ≠ iRVZero
    rw [realize_tRVOne]
    exact rv_one_ne_zero hM
  | cons t l ih =>
    have ht : iRV (t.realize V) ∧ t.realize V ≠ iRVZero := h t List.mem_cons_self
    have hl : ∀ u ∈ l, iRV (u.realize V) ∧ u.realize V ≠ iRVZero :=
      fun u hu => h u (List.mem_cons_of_mem t hu)
    have hgoal : (mkMul (t :: l)).realize V
        = iRVMul (t.realize V) ((mkMul l).realize V) := by
      show (tRVMul t (mkMul l)).realize V = _
      rw [realize_tRVMul]
    rw [hgoal]
    exact rv_mul_ne_zero hM ht.1 (iRV_realize_mkMul hM V l (fun u hu => (hl u hu).1))
      ht.2 (ih hl)

/-- A word whose factors all lie in `Kˣ` lies in `Kˣ`: this is the **residue-field factor** of the
normal form. -/
theorem mkMul_units (hM : M ⊨ Axioms.ACVF) {k : ℕ} (V : Empty ⊕ Fin k → M) (l : List (Tm k))
    (h : ∀ t ∈ l, iUnits (t.realize V)) : iUnits ((mkMul l).realize V) := by
  induction l with
  | nil =>
    show iUnits (((tRVOne : Tm k)).realize V)
    rw [realize_tRVOne]
    exact units_one hM
  | cons t l ih =>
    have ht : iUnits (t.realize V) := h t List.mem_cons_self
    have hl : ∀ u ∈ l, iUnits (u.realize V) := fun u hu => h u (List.mem_cons_of_mem t hu)
    have hgoal : (mkMul (t :: l)).realize V
        = iRVMul (t.realize V) ((mkMul l).realize V) := by
      show (tRVMul t (mkMul l)).realize V = _
      rw [realize_tRVMul]
    rw [hgoal]
    exact units_mul hM ht (ih hl) (units_mem_rv hM ht) (units_mem_rv hM (ih hl))

/-- **The normal form, term level**: a word `t · c₁ · ⋯ · cₖ` in which every `cᵢ` lies in `Kˣ` is a
single term `t` times a residue-field factor `c₁ ⋯ cₖ`, and that factor is itself in `Kˣ`. -/
theorem mkMul_single_times_factor (hM : M ⊨ Axioms.ACVF) {k : ℕ} (V : Empty ⊕ Fin k → M)
    (t : Tm k) (l : List (Tm k)) (h : ∀ u ∈ l, iUnits (u.realize V)) :
    (mkMul (t :: l)).realize V = iRVMul (t.realize V) ((mkMul l).realize V) ∧
      iUnits ((mkMul l).realize V) := by
  refine ⟨?_, mkMul_units hM V l h⟩
  show (tRVMul t (mkMul l)).realize V = _
  rw [realize_tRVMul]

/-- **Cancelling a common leading factor of two words.**  This is the group-word comparison the
mixed-context elimination needs: a shared factor at the head of both words can be divided out, at
any nonzero `RV`-element (in particular at elements off `Kˣ`). -/
theorem mkMul_cons_eq_iff (hM : M ⊨ Axioms.ACVF) {k : ℕ} (V : Empty ⊕ Fin k → M)
    (t : Tm k) (l₁ l₂ : List (Tm k))
    (ht : iRV (t.realize V)) (ht0 : t.realize V ≠ iRVZero)
    (h₁ : ∀ u ∈ l₁, iRV (u.realize V)) (h₂ : ∀ u ∈ l₂, iRV (u.realize V)) :
    (mkMul (t :: l₁)).realize V = (mkMul (t :: l₂)).realize V
      ↔ (mkMul l₁).realize V = (mkMul l₂).realize V := by
  have e₁ : (mkMul (t :: l₁)).realize V
      = iRVMul (t.realize V) ((mkMul l₁).realize V) := by
    show (tRVMul t (mkMul l₁)).realize V = _
    rw [realize_tRVMul]
  have e₂ : (mkMul (t :: l₂)).realize V
      = iRVMul (t.realize V) (((mkMul l₂)).realize V) := by
    show (tRVMul t (mkMul l₂)).realize V = _
    rw [realize_tRVMul]
  rw [e₁, e₂,
    rv_mul_eq_mul_iff hM ht (iRV_realize_mkMul hM V l₁ h₁) (iRV_realize_mkMul hM V l₂ h₂) ht0]

/-! ## 6. The dictionary at the level of formulas

The QF-cover argument reads a quantifier-free atom off a tuple; the two lemmas below say that a
common `rvMul` factor can be cancelled *inside* the atom, so a word equation reduces to a shorter
word equation without changing the truth set. -/

/-- **Cancelling a common left `rvMul` factor inside an equality atom.** -/
theorem pEq_tRVMul_iff (hM : M ⊨ Axioms.ACVF) {k : ℕ} (a b c : Tm k) (v : Empty → M)
    (x : Fin k → M)
    (ha : iRV (a.realize (Sum.elim v x))) (ha0 : a.realize (Sum.elim v x) ≠ iRVZero)
    (hb : iRV (b.realize (Sum.elim v x))) (hc : iRV (c.realize (Sum.elim v x))) :
    (pEq (tRVMul a b) (tRVMul a c)).Realize v x ↔ (pEq b c).Realize v x := by
  simp only [pEq, BoundedFormula.realize_bdEqual, realize_tRVMul]
  exact rv_mul_eq_mul_iff hM ha hb hc ha0

/-- **Cancelling a common right `rvMul` factor inside an equality atom.** -/
theorem pEq_tRVMul_right_iff (hM : M ⊨ Axioms.ACVF) {k : ℕ} (a b c : Tm k) (v : Empty → M)
    (x : Fin k → M)
    (ha : iRV (a.realize (Sum.elim v x))) (ha0 : a.realize (Sum.elim v x) ≠ iRVZero)
    (hb : iRV (b.realize (Sum.elim v x))) (hc : iRV (c.realize (Sum.elim v x))) :
    (pEq (tRVMul b a) (tRVMul c a)).Realize v x ↔ (pEq b c).Realize v x := by
  simp only [pEq, BoundedFormula.realize_bdEqual, realize_tRVMul]
  exact ⟨fun h => rv_mul_right_cancel hM ha hb hc ha0 h, fun h => by rw [h]⟩

/-- **Cancelling a common leading factor of two group words, as formulas.** -/
theorem pEq_mkMul_cons_iff (hM : M ⊨ Axioms.ACVF) {k : ℕ} (v : Empty → M) (x : Fin k → M)
    (t : Tm k) (l₁ l₂ : List (Tm k))
    (ht : iRV (t.realize (Sum.elim v x))) (ht0 : t.realize (Sum.elim v x) ≠ iRVZero)
    (h₁ : ∀ u ∈ l₁, iRV (u.realize (Sum.elim v x)))
    (h₂ : ∀ u ∈ l₂, iRV (u.realize (Sum.elim v x))) :
    (pEq (mkMul (t :: l₁)) (mkMul (t :: l₂))).Realize v x
      ↔ (pEq (mkMul l₁) (mkMul l₂)).Realize v x := by
  simp only [pEq, BoundedFormula.realize_bdEqual]
  exact mkMul_cons_eq_iff hM (Sum.elim v x) t l₁ l₂ ht ht0 h₁ h₂

/-! ## 6. Normal form up to permutation of the factors

A group word is a *multiset* of factors read in some order: `mkMul_perm` below says the value does
not depend on the order, and `rv_mul_swap` is the exchange step.  Together with
`mkMul_cons_eq_iff` this is what lets the elimination rearrange a word, cancel a common factor, and
compare the remainder. -/

/-- The exchange step: `a · (b · r) = b · (a · r)` on `RV`. -/
theorem rv_mul_swap (hM : M ⊨ Axioms.ACVF) {a b r : M} (ha : iRV a) (hb : iRV b) (hr : iRV r) :
    iRVMul a (iRVMul b r) = iRVMul b (iRVMul a r) := by
  rw [← rv_mul_assoc hM ha hb hr, ← rv_mul_assoc hM hb ha hr, rv_mul_comm hM ha hb]

/-- **The value of a word depends only on the multiset of its factors.** -/
theorem mkMul_perm (hM : M ⊨ Axioms.ACVF) {k : ℕ} (V : Empty ⊕ Fin k → M) {l₁ l₂ : List (Tm k)}
    (hp : List.Perm l₁ l₂) :
    ∀ _h : ∀ t ∈ l₁, iRV (t.realize V),
      (mkMul l₁).realize V = (mkMul l₂).realize V := by
  induction hp with
  | nil => intro _; rfl
  | cons t hp ih =>
    intro h
    rw [mkMul_realize_cons, mkMul_realize_cons,
      ih (fun u hu => h u (List.mem_cons_of_mem t hu))]
  | swap t₁ t₂ l =>
    intro h
    have h₁ : iRV (t₁.realize V) := h t₁ (List.mem_cons_of_mem t₂ List.mem_cons_self)
    have h₂ : iRV (t₂.realize V) := h t₂ List.mem_cons_self
    have hr : iRV ((mkMul l).realize V) :=
      iRV_realize_mkMul hM V l (fun u hu =>
        h u (List.mem_cons_of_mem t₂ (List.mem_cons_of_mem t₁ hu)))
    rw [mkMul_realize_cons, mkMul_realize_cons, mkMul_realize_cons, mkMul_realize_cons,
      rv_mul_swap hM h₁ h₂ hr]
  | trans hp1 hp2 ih1 ih2 =>
    intro h
    exact (ih1 h).trans (ih2 (fun u hu => h u (hp1.symm.subset hu)))

/-! ## 7. Splitting a word: `∏ t_j ^ a_j`

The form the elimination actually manipulates is a word written as a *power of one atom times the
rest*; `mkMul_append` is the split, `mkMul_replicate` reads `List.replicate` as a power, and
`mkMul_pow_times_factor` is the combined statement.  With `mkMul_units` this is
`t ^ n · (residue-field factor)`. -/

/-- Powers in the multiplicative monoid of `RV`. -/
def rvPow (a : M) : ℕ → M
  | 0 => iRVOne
  | n + 1 => iRVMul (rvPow a n) a

theorem rvPow_zero (a : M) : rvPow a 0 = (iRVOne : M) := rfl

theorem rvPow_succ (a : M) (n : ℕ) : rvPow a (n + 1) = iRVMul (rvPow a n) a := rfl

theorem rvPow_mem (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) : ∀ n : ℕ, iRV (rvPow a n)
  | 0 => rv_one_mem hM
  | n + 1 => rv_mul_mem hM (rvPow_mem hM ha n) ha

/-- The language's `tRVPow` realises as the model's power. -/
theorem realize_tRVPow {k : ℕ} (V : Empty ⊕ Fin k → M) (t : Tm k) :
    ∀ n : ℕ, (tRVPow t n).realize V = rvPow (t.realize V) n
  | 0 => realize_tRVOne V
  | n + 1 => by
      show (tRVMul (tRVPow t n) t).realize V = _
      rw [realize_tRVMul, realize_tRVPow V t n, rvPow_succ]

/-- A word with `n` copies of the same factor is the `n`-th power. -/
theorem mkMul_replicate (hM : M ⊨ Axioms.ACVF) {k : ℕ} (V : Empty ⊕ Fin k → M) (t : Tm k)
    (ht : iRV (t.realize V)) :
    ∀ n : ℕ, (mkMul (List.replicate n t)).realize V = rvPow (t.realize V) n
  | 0 => realize_tRVOne V
  | n + 1 => by
      rw [List.replicate_succ, mkMul_realize_cons, mkMul_replicate hM V t ht n, rvPow_succ]
      exact rv_mul_comm hM ht (rvPow_mem hM ht n)

/-- **Products split**: the product of a concatenation is the product of the products. -/
theorem mkMul_append (hM : M ⊨ Axioms.ACVF) {k : ℕ} (V : Empty ⊕ Fin k → M)
    (l₂ : List (Tm k)) (h₂ : ∀ t ∈ l₂, iRV (t.realize V)) :
    ∀ l₁ : List (Tm k), (∀ t ∈ l₁, iRV (t.realize V)) →
      (mkMul (l₁ ++ l₂)).realize V
        = iRVMul ((mkMul l₁).realize V) ((mkMul l₂).realize V)
  | [], _ => by
      rw [List.nil_append,
        show (mkMul ([] : List (Tm k))).realize V = iRVOne from realize_tRVOne V,
        rv_mul_one_all hM (iRV_realize_mkMul hM V l₂ h₂)]
  | t :: l₁, h₁ => by
      have ht : iRV (t.realize V) := h₁ t List.mem_cons_self
      have h₁' : ∀ u ∈ l₁, iRV (u.realize V) := fun u hu => h₁ u (List.mem_cons_of_mem t hu)
      rw [List.cons_append, mkMul_realize_cons, mkMul_append hM V l₂ h₂ l₁ h₁',
        mkMul_realize_cons]
      exact (rv_mul_assoc hM ht (iRV_realize_mkMul hM V l₁ h₁')
        (iRV_realize_mkMul hM V l₂ h₂)).symm

/-- **The normal form of a word of powers**: `t ^ n` followed by the remaining factors. -/
theorem mkMul_pow_times_factor (hM : M ⊨ Axioms.ACVF) {k : ℕ} (V : Empty ⊕ Fin k → M)
    (t : Tm k) (n : ℕ) (l : List (Tm k))
    (ht : iRV (t.realize V)) (hl : ∀ u ∈ l, iRV (u.realize V)) :
    (mkMul (List.replicate n t ++ l)).realize V
      = iRVMul (rvPow (t.realize V) n) ((mkMul l).realize V) := by
  rw [mkMul_append hM V l hl (List.replicate n t)
      (fun u hu => by rw [List.eq_of_mem_replicate hu]; exact ht),
    mkMul_replicate hM V t ht n]

end MulNormalForm
end Milestone0
end SpecialTransformations
