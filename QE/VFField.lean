/-
**The `VF` field laws and the `Field` instance on `VFType`, from the frozen axioms.**

`Milestone0/Encoding.lean` states `Axioms.vfField` as a list of `allSorted`-guarded sentences and
contains no realization lemmas for them, so until now nothing in a file importing `Enc` could treat
`VF` as a field.  This file ports the layer from `QE/Assembly_val.lean` (where it is proved against
that file's own copy of the encoding) to the frozen encoding, so that

* `QF/ValBridge`-style arguments can put a Mathlib `Valuation` on `VFType M`, and
* the paper's valuation-theoretic lemmas (`rv:root:lift:vf`, `lift:divisible:hull`,
  `e:transc`) can be instantiated at a model of the frozen `ACVF` instead of re-proved.

Nothing here is new mathematics: it is the axiom extraction, term realization and field laws that
`Assembly_val` already had, re-pointed at `Enc`.
-/
import Enc

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0

namespace Transfer

/-! The two missing constants: `Milestone0/Encoding.lean` defines `iVFAdd`, `iVFMul`, `iVFNeg` but
not the `VF`-sorted `0` and `1` as elements of the carrier. -/

/-- `0` of the `VF` sort. -/
def iVFZero {M : Type} [LRV.Structure M] : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfZero fun i => i.elim0

/-- `1` of the `VF` sort. -/
def iVFOne {M : Type} [LRV.Structure M] : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfOne fun i => i.elim0

theorem realize_tVFZero {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M) :
    (tVFZero (n := n)).realize v = iVFZero := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfZero
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iVFZero
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem realize_tVFOne {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M) :
    (tVFOne (n := n)).realize v = iVFOne := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfOne
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iVFOne
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem realize_tVFAdd {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M)
    (a b : Tm n) : (tVFAdd a b).realize v = iVFAdd (a.realize v) (b.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfAdd
      (fun i => Term.realize (L := LRV) v (![a, b] i)) = iVFAdd (a.realize v) (b.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a, b] i)) = ![a.realize v, b.realize v] from by
    funext i
    fin_cases i <;> simp]
  rfl

theorem realize_tVFMul {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M)
    (a b : Tm n) : (tVFMul a b).realize v = iVFMul (a.realize v) (b.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfMul
      (fun i => Term.realize (L := LRV) v (![a, b] i)) = iVFMul (a.realize v) (b.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a, b] i)) = ![a.realize v, b.realize v] from by
    funext i
    fin_cases i <;> simp]
  rfl

theorem realize_tVFNeg {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M)
    (a : Tm n) : (tVFNeg a).realize v = iVFNeg (a.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfNeg
      (fun i => Term.realize (L := LRV) v (![a] i)) = iVFNeg (a.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a] i)) = ![a.realize v] from by
    funext i
    fin_cases i
    simp]
  rfl


/-! ### The sort discipline, semantically -/

theorem realize_tv {M : Type} [LRV.Structure M] {k : ℕ} (i : Fin k) (v : Empty → M)
    (x : Fin k → M) : (tv i.1 i.2).realize (Sum.elim v x) = x i := rfl

theorem pVF_realize {M : Type} [LRV.Structure M] {k : ℕ} (t : Tm k) (v : Empty → M)
    (x : Fin k → M) : (pVF t).Realize v x ↔ iVF (t.realize (Sum.elim v x)) := by
  show FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memVF
      (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      ↔ iVF (t.realize (Sum.elim v x))
  rw [show (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      = ![t.realize (Sum.elim v x)] from by
    funext i
    fin_cases i
    simp]
  rfl

theorem pRVsort_realize {M : Type} [LRV.Structure M] {k : ℕ} (t : Tm k) (v : Empty → M)
    (x : Fin k → M) : (pRVsort t).Realize v x ↔ iRV (t.realize (Sum.elim v x)) := by
  show FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memRV
      (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      ↔ iRV (t.realize (Sum.elim v x))
  rw [show (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      = ![t.realize (Sum.elim v x)] from by
    funext i
    fin_cases i
    simp]
  rfl

theorem sortPred_realize {M : Type} [LRV.Structure M] {k : ℕ} (s : SortTag) (t : Tm k)
    (v : Empty → M) (x : Fin k → M) :
    (sortPred s t).Realize v x ↔
      (match s with
        | .vf => iVF (t.realize (Sum.elim v x))
        | .rv => iRV (t.realize (Sum.elim v x))) := by
  cases s with
  | vf => exact pVF_realize t v x
  | rv => exact pRVsort_realize t v x

/-- **The conjunction of sort hypotheses realises as the pointwise sort conditions.** -/
theorem sortedHyps_foldr_realize {M : Type} [LRV.Structure M] {k : ℕ} (ss : Fin k → SortTag)
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

/-- **The gateway lemma**: `sortedHyps ss` realises as the pointwise sort conditions. -/
theorem sortedHyps_realize {M : Type} [LRV.Structure M] {k : ℕ} (ss : Fin k → SortTag)
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

/-- **Uniform extraction from an `allSorted`-guarded sentence.**  If `∀ x̄ ∈ s̄, φ` is in a theory
`T` and `M ⊨ T`, then `φ` holds at every tuple of the prescribed sorts.  Every axiom of `ACVF`
that constrains the `VF` order or the `RV` order has this shape. -/
theorem allSorted_realize {M : Type} [LRV.Structure M] {T : LRV.Theory} (hM : M ⊨ T)
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

/-- Extraction from a sentence closed by a single universal quantifier. -/
theorem allOne_realize {M : Type} [LRV.Structure M] {T : LRV.Theory} (hM : M ⊨ T)
    {φ : Bf 1} (hmem : allOne φ ∈ T) :
    ∀ x : Fin 1 → M,
      @BoundedFormula.Realize LRV M _ Empty 1 φ (default : Empty → M) x := by
  intro x
  have h := hM.realize_of_mem (allOne φ) hmem
  simp only [allOne, Sentence.Realize, BoundedFormula.realize_alls] at h
  exact h x

/-- Extraction from a sentence with no quantifiers. -/
theorem sentence_realize {M : Type} [LRV.Structure M] {T : LRV.Theory} (hM : M ⊨ T)
    {φ : LRV.Sentence} (hmem : φ ∈ T) : M ⊨ φ :=
  hM.realize_of_mem φ hmem
/-! ### Membership of the axioms, and closure of the `VF` sort -/

/-- A member of the sort closure is an axiom of `ACVF`. -/
theorem mem_ACVF_sortClosure {s : LRV.Sentence} (h : s ∈ Axioms.sortClosure) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.sortAxioms, Set.mem_union]
  tauto

/-- A member of `vfField` is an axiom of `ACVF`. -/
theorem mem_ACVF_vfField {s : LRV.Sentence} (h : s ∈ Axioms.vfField) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

/-- A member of `vfAlgClosed` is an axiom of `ACVF`. -/
theorem mem_ACVF_vfAlgClosed {s : LRV.Sentence} (h : s ∈ Axioms.vfAlgClosed) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

/-- A member of `preorderRV` is an axiom of `ACVF`. -/
theorem mem_ACVF_preorderRV {s : LRV.Sentence} (h : s ∈ Axioms.preorderRV) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

/-- A member of `rvAxioms` is an axiom of `ACVF`. -/
theorem mem_ACVF_rvAxioms {s : LRV.Sentence} (h : s ∈ Axioms.rvAxioms) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

theorem mem_ACVF_sdVFZero : Axioms.sdVFZero ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdVFOne : Axioms.sdVFOne ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdVFAdd : Axioms.sdVFAdd ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdVFNeg : Axioms.sdVFNeg ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdVFMul : Axioms.sdVFMul ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

/-- `0` of the ring language lies in the `VF` sort. -/
theorem vf_zero_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iVF (iVFZero (M := M)) := by
  have h := sentence_realize hM (φ := Axioms.sdVFZero) mem_ACVF_sdVFZero
  rw [Axioms.sdVFZero, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pVF_realize, realize_tVFZero] at h
  exact h

/-- `1` of the ring language lies in the `VF` sort. -/
theorem vf_one_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iVF (iVFOne (M := M)) := by
  have h := sentence_realize hM (φ := Axioms.sdVFOne) mem_ACVF_sdVFOne
  rw [Axioms.sdVFOne, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pVF_realize, realize_tVFOne] at h
  exact h

/-- The `VF` sort is closed under `+`. -/
theorem vf_add_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVF (iVFAdd x y) := by
  have h := allSorted_realize hM (T := Axioms.ACVF) mem_ACVF_sdVFAdd ![x, y] (by
    intro i
    fin_cases i <;> simp [hx, hy])
  rw [pVF_realize, realize_tVFAdd] at h
  simpa using h

/-- The `VF` sort is closed under `-`. -/
theorem vf_neg_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVF (iVFNeg x) := by
  have h := allSorted_realize hM (T := Axioms.ACVF) mem_ACVF_sdVFNeg ![x] (by
    intro i
    fin_cases i
    simpa using hx)
  rw [pVF_realize, realize_tVFNeg] at h
  simpa using h

/-- The `VF` sort is closed under `×`. -/
theorem vf_mul_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVF (iVFMul x y) := by
  have h := allSorted_realize hM (T := Axioms.ACVF) mem_ACVF_sdVFMul ![x, y] (by
    intro i
    fin_cases i <;> simp [hx, hy])
  rw [pVF_realize, realize_tVFMul] at h
  simpa using h

/-! ### The field laws on the `VF` sort -/

/-- Extract an equation from an `allSorted`-guarded `pEq` sentence. -/
theorem eq_of_allSorted {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {k : ℕ}
    {ss : Fin k → SortTag} {a b : Tm k} (hmem : allSorted ss (pEq a b) ∈ Axioms.ACVF)
    (x : Fin k → M) (hx : ∀ i, (match ss i with
      | .vf => iVF (x i)
      | .rv => iRV (x i))) :
    a.realize (Sum.elim (default : Empty → M) x)
      = b.realize (Sum.elim (default : Empty → M) x) := by
  have h := allSorted_realize hM hmem x hx
  simpa only [pEq, BoundedFormula.realize_bdEqual] using h

/-- The reduction of the `VF` field axioms to a list membership in `vfField`. -/
theorem mem_vfField {s : LRV.Sentence} (h : s ∈ Axioms.vfField) : s ∈ Axioms.ACVF :=
  mem_ACVF_vfField h

theorem vf_add_assoc {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFAdd (iVFAdd x y) z = iVFAdd x (iVFAdd y z) := by
  have hmem : allSorted ![.vf, .vf, .vf]
      (pEq (tVFAdd (tVFAdd &0 &1) &2) (tVFAdd &0 (tVFAdd &1 &2))) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y, z] (by intro i; fin_cases i <;> simp [hx, hy, hz])
  simpa [realize_tVFAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    using h

theorem vf_add_comm {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVFAdd x y = iVFAdd y x := by
  have hmem : allSorted ![.vf, .vf] (pEq (tVFAdd &0 &1) (tVFAdd &1 &0)) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y] (by intro i; fin_cases i <;> simp [hx, hy])
  simpa [realize_tVFAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

theorem vf_add_zero {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVFAdd x iVFZero = x := by
  have hmem : allSorted ![.vf] (pEq (tVFAdd &0 tVFZero) &0) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simpa [realize_tVFAdd, realize_tVFZero, Matrix.cons_val_zero] using h

theorem vf_add_neg {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVFAdd x (iVFNeg x) = iVFZero := by
  have hmem : allSorted ![.vf] (pEq (tVFAdd &0 (tVFNeg &0)) tVFZero) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simpa [realize_tVFAdd, realize_tVFNeg, realize_tVFZero, Matrix.cons_val_zero] using h

theorem vf_mul_assoc {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFMul (iVFMul x y) z = iVFMul x (iVFMul y z) := by
  have hmem : allSorted ![.vf, .vf, .vf]
      (pEq (tVFMul (tVFMul &0 &1) &2) (tVFMul &0 (tVFMul &1 &2))) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y, z] (by intro i; fin_cases i <;> simp [hx, hy, hz])
  simpa [realize_tVFMul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    using h

theorem vf_mul_comm {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVFMul x y = iVFMul y x := by
  have hmem : allSorted ![.vf, .vf] (pEq (tVFMul &0 &1) (tVFMul &1 &0)) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y] (by intro i; fin_cases i <;> simp [hx, hy])
  simpa [realize_tVFMul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

theorem vf_mul_one {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVFMul x iVFOne = x := by
  have hmem : allSorted ![.vf] (pEq (tVFMul &0 tVFOne) &0) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simpa [realize_tVFMul, realize_tVFOne, Matrix.cons_val_zero] using h

theorem vf_left_distrib {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFMul x (iVFAdd y z) = iVFAdd (iVFMul x y) (iVFMul x z) := by
  have hmem : allSorted ![.vf, .vf, .vf]
      (pEq (tVFMul &0 (tVFAdd &1 &2)) (tVFAdd (tVFMul &0 &1) (tVFMul &0 &2)))
      ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y, z] (by intro i; fin_cases i <;> simp [hx, hy, hz])
  simpa [realize_tVFAdd, realize_tVFMul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using h

/-- `0 ≠ 1` on the `VF` sort. -/
theorem vf_zero_ne_one {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iVFZero (M := M) ≠ iVFOne := by
  have hmem : (∼(pEq tVFZero tVFOne)) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := sentence_realize hM hmem
  rw [Sentence.Realize] at h
  simp only [Formula.Realize, BoundedFormula.realize_not, pEq, BoundedFormula.realize_bdEqual,
    realize_tVFZero, realize_tVFOne] at h
  exact h

/-- **The invertibility law**: a `VF`-element is `0` or has a multiplicative inverse.  The
encoding states it this way because the language has no inverse symbol. -/
theorem vf_mul_inv_or_zero {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : x = iVFZero ∨ ∃ y : M, iVF y ∧ iVFMul x y = iVFOne := by
  have hmem : allSorted ![.vf]
      (pEq &0 tVFZero ⊔ exSorted .vf (pEq (tVFMul &0 &1) tVFOne)) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := allSorted_realize hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simp only [BoundedFormula.realize_sup, exSorted, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, sortPred, pEq, BoundedFormula.realize_bdEqual, realize_tVFZero,
    realize_tVFMul, realize_tVFOne, realize_tv, Term.realize_var, Sum.elim_inr, Function.comp_apply, pVF_realize, Term.realize_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
  exact h
/-! ### The `VF` sort as a field -/

section VFField

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The `VF` sort of an `ACVF`-model, as a type. -/
def VFType : Type := {x : M // iVF x}

instance vfInstZero : Zero (VFType (M := M)) := ⟨⟨iVFZero, vf_zero_mem hM⟩⟩

instance vfInstOne : One (VFType (M := M)) := ⟨⟨iVFOne, vf_one_mem hM⟩⟩

instance vfInstAdd : Add (VFType (M := M)) :=
  ⟨fun x y => ⟨iVFAdd x.1 y.1, vf_add_mem hM x.2 y.2⟩⟩

instance vfInstNeg : Neg (VFType (M := M)) :=
  ⟨fun x => ⟨iVFNeg x.1, vf_neg_mem hM x.2⟩⟩

instance vfInstMul : Mul (VFType (M := M)) :=
  ⟨fun x y => ⟨iVFMul x.1 y.1, vf_mul_mem hM x.2 y.2⟩⟩

/-- The inverse on the `VF` sort: `0⁻¹ = 0`, and a nonzero element inverts by the
invertibility law. -/
noncomputable def vfInvFun (x : VFType (M := M)) : VFType (M := M) := by
  classical
  exact if h : x.1 = iVFZero then 0
    else
      let w := (vf_mul_inv_or_zero hM x.2).resolve_left h
      ⟨Classical.choose w, (Classical.choose_spec w).1⟩

noncomputable instance vfInstInv : Inv (VFType (M := M)) := ⟨vfInvFun⟩

theorem vfInv_zero : (0 : VFType (M := M))⁻¹ = 0 := dif_pos rfl

theorem vfInv_val {x : VFType (M := M)} (hx : x ≠ 0) :
    iVFMul x.1 ((x⁻¹ : VFType (M := M))).1 = iVFOne := by
  have hx' : x.1 ≠ iVFZero := fun h => hx (Subtype.ext h)
  have hval : ((x⁻¹ : VFType (M := M))).1
      = Classical.choose ((vf_mul_inv_or_zero hM x.2).resolve_left hx') := by
    show (vfInvFun x).1 = _
    unfold vfInvFun
    exact congrArg Subtype.val (dif_neg hx')
  rw [hval]
  exact (Classical.choose_spec ((vf_mul_inv_or_zero hM x.2).resolve_left hx')).2

/-- **The `VF` sort is a field.** -/
noncomputable def vfFieldOfModel : Field (VFType (M := M)) :=
  Field.ofMinimalAxioms (VFType (M := M))
    (fun a b c => Subtype.ext (vf_add_assoc hM a.2 b.2 c.2))
    (fun a => Subtype.ext (by
      show iVFAdd iVFZero a.1 = a.1
      rw [vf_add_comm hM (vf_zero_mem hM) a.2]
      exact vf_add_zero hM a.2))
    (fun a => Subtype.ext (by
      show iVFAdd (iVFNeg a.1) a.1 = iVFZero
      rw [vf_add_comm hM (vf_neg_mem hM a.2) a.2]
      exact vf_add_neg hM a.2))
    (fun a b c => Subtype.ext (vf_mul_assoc hM a.2 b.2 c.2))
    (fun a b => Subtype.ext (vf_mul_comm hM a.2 b.2))
    (fun a => Subtype.ext (by
      show iVFMul iVFOne a.1 = a.1
      rw [vf_mul_comm hM (vf_one_mem hM) a.2]
      exact vf_mul_one hM a.2))
    (fun a ha => Subtype.ext (vfInv_val ha))
    vfInv_zero
    (fun a b c => Subtype.ext (vf_left_distrib hM a.2 b.2 c.2))
    ⟨0, 1, fun h => vf_zero_ne_one hM (congrArg Subtype.val h)⟩

end VFField

end Transfer

end SpecialTransformations.Milestone0
