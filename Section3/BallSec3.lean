module

/-
# Ball structure in the frozen `L_RV`, and the exact content of "has centers"

Works in the frozen encoding (`import Enc`, i.e. `Milestone0/Encoding.lean`), reusing the
realisation toolkit of `QE/MulNormalForm.lean`, and proves:

* the `VF`-sorted term realisation lemmas and the `VF` field laws, extracted from `Axioms.vfField`
  (copied from `QE/Assembly_val.lean`, which carries the same copy of the encoding);
* `rv_neg_equiv` : `rv (-z)` and `rv z` are `≤`-equivalent — the fact every ball argument in this
  encoding needs, because `IsClosedBall` writes its membership as `rv (x + -a)`, so comparing two
  balls with different centres forces it;
* the ball lemmas: every closed ball contains its centre, hence is nonempty; a closed ball is
  monotone in its radius; two closed balls whose centre distance is strictly below the radius are
  disjoint;
* **the refutation**: in every model of `Axioms.ACVF` there are three closed balls `b1, b2 ⊆ b3`
  with `b1 ∩ b2 = ∅` and both nonempty, so no `C` is a "set of centers" in the frozen sense
  (`∃! c, c ∈ C ∧ c ∈ b` for every `b`), i.e. `Sec3.HasCenters` is FALSE for an algebraic set of
  closed balls.  The paper's Definition 4.14 asks instead for a *function* `f` with `f b ∈ b`;
  the frozen `IsSetOfCenters` strengthens that to "exactly one point of `C` lies in each ball",
  and the strengthening is refuted here from the axioms alone (no model construction).
-/
public import Enc
public import MulNormalForm

@[expose] public section

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace SpecialTransformations
namespace Milestone0
namespace BallSec3

open LRV Axioms
open SpecialTransformations.Milestone0.MulNormalForm

set_option autoImplicit false

variable {M : Type} [LRV.Structure M]

/-! ## 0. The interpretation of the `VF` constants

`Milestone0/Encoding.lean` names the two `RV` constants (`iRVZero`, `iRVOne`) but not the two of
the `VF` sort; these are the definitions `QE/Assembly_val.lean` uses. -/

/-- the interpretation of `0` of the `VF` sort -/
def iVFZero : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfZero fun i => i.elim0

/-- the interpretation of `1` of the `VF` sort -/
def iVFOne : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfOne fun i => i.elim0

/-! ## 1. Realisation of the `VF`-sorted terms -/

theorem realize_tVFZero {n : ℕ} (v : Empty ⊕ Fin n → M) :
    (tVFZero (n := n)).realize v = (iVFZero : M) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfZero
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iVFZero
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem realize_tVFOne {n : ℕ} (v : Empty ⊕ Fin n → M) :
    (tVFOne (n := n)).realize v = (iVFOne : M) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfOne
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iVFOne
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem realize_tVFAdd {n : ℕ} (v : Empty ⊕ Fin n → M) (a b : Tm n) :
    (tVFAdd a b).realize v = iVFAdd (a.realize v) (b.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfAdd
      (fun i => Term.realize (L := LRV) v (![a, b] i)) = iVFAdd (a.realize v) (b.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a, b] i)) = ![a.realize v, b.realize v] from by
    funext i
    fin_cases i <;> simp]
  rfl

theorem realize_tVFMul {n : ℕ} (v : Empty ⊕ Fin n → M) (a b : Tm n) :
    (tVFMul a b).realize v = iVFMul (a.realize v) (b.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfMul
      (fun i => Term.realize (L := LRV) v (![a, b] i)) = iVFMul (a.realize v) (b.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a, b] i)) = ![a.realize v, b.realize v] from by
    funext i
    fin_cases i <;> simp]
  rfl

theorem realize_tVFNeg {n : ℕ} (v : Empty ⊕ Fin n → M) (a : Tm n) :
    (tVFNeg a).realize v = iVFNeg (a.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfNeg
      (fun i => Term.realize (L := LRV) v (![a] i)) = iVFNeg (a.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a] i)) = ![a.realize v] from by
    funext i
    fin_cases i
    simp]
  rfl

theorem realize_tRv' {n : ℕ} (v : Empty ⊕ Fin n → M) (a : Tm n) :
    (tRv a).realize v = iRv (a.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvMap
      (fun i => Term.realize (L := LRV) v (![a] i)) = iRv (a.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a] i)) = ![a.realize v] from by
    funext i
    fin_cases i
    simp]
  rfl

theorem pLe_realize' {n : ℕ} (a b : Tm n) (v : Empty → M) (x : Fin n → M) :
    (pLe a b).Realize v x ↔ iLe (a.realize (Sum.elim v x)) (b.realize (Sum.elim v x)) := by
  have h : (fun i => Term.realize (L := LRV) (Sum.elim v x) (![a, b] i))
      = ![a.realize (Sum.elim v x), b.realize (Sum.elim v x)] := by
    funext i
    fin_cases i <;> simp
  show FirstOrder.Language.Structure.RelMap (L := LRV) Rel.rvLe
      (fun i => Term.realize (L := LRV) (Sum.elim v x) (![a, b] i)) ↔ iLe
        (a.realize (Sum.elim v x)) (b.realize (Sum.elim v x))
  rw [h]
  rfl

/-! ## 2. Reading the axioms off a model -/

theorem sentence_realize' {T : LRV.Theory} (hM : M ⊨ T) {φ : LRV.Sentence} (hmem : φ ∈ T) :
    M ⊨ φ := hM.realize_of_mem φ hmem

theorem mem_ACVF_vfField {s : LRV.Sentence} (h : s ∈ Axioms.vfField) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

theorem mem_ACVF_preorderRV {s : LRV.Sentence} (h : s ∈ Axioms.preorderRV) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

theorem mem_ACVF_rvAxioms {s : LRV.Sentence} (h : s ∈ Axioms.rvAxioms) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

theorem mem_ACVF_axNontrivialRV : Axioms.axNontrivialRV ∈ Axioms.ACVF :=
  mem_ACVF_repairRV (by simp [Axioms.repairRV, Axioms.ofList])

theorem mem_ACVF_leMulCompatFull : Axioms.leMulCompatFull ∈ Axioms.ACVF :=
  mem_ACVF_repairRV (by simp [Axioms.repairRV, Axioms.ofList])

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

theorem mem_ACVF_sdRv : Axioms.sdRv ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

/-! ### Closure of the `VF` sort, and `rv` of a `VF`-element -/

theorem vf_add_mem (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y) :
    iVF (iVFAdd x y) := by
  have h := allSorted_realize hM (T := Axioms.ACVF) mem_ACVF_sdVFAdd ![x, y] (by
    intro i
    fin_cases i <;> simp [hx, hy])
  rw [pVF_realize, realize_tVFAdd] at h
  simpa using h

theorem vf_neg_mem (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) : iVF (iVFNeg x) := by
  have h := allSorted_realize hM (T := Axioms.ACVF) mem_ACVF_sdVFNeg ![x] (by
    intro i
    fin_cases i
    simpa using hx)
  rw [pVF_realize, realize_tVFNeg] at h
  simpa using h

theorem vf_mul_mem (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y) :
    iVF (iVFMul x y) := by
  have h := allSorted_realize hM (T := Axioms.ACVF) mem_ACVF_sdVFMul ![x, y] (by
    intro i
    fin_cases i <;> simp [hx, hy])
  rw [pVF_realize, realize_tVFMul] at h
  simpa using h

theorem vf_zero_mem (hM : M ⊨ Axioms.ACVF) : iVF (iVFZero : M) := by
  have h := sentence_realize' hM mem_ACVF_sdVFZero
  have h2 : iVF (Term.realize (Sum.elim (default : Empty → M) (default : Fin 0 → M))
      (tVFZero (n := 0))) := by
    simpa [Axioms.sdVFZero, Sentence.Realize, Formula.Realize, pVF_realize] using h
  simpa [realize_tVFZero] using h2

theorem vf_one_mem (hM : M ⊨ Axioms.ACVF) : iVF (iVFOne : M) := by
  have h := sentence_realize' hM mem_ACVF_sdVFOne
  have h2 : iVF (Term.realize (Sum.elim (default : Empty → M) (default : Fin 0 → M))
      (tVFOne (n := 0))) := by
    simpa [Axioms.sdVFOne, Sentence.Realize, Formula.Realize, pVF_realize] using h
  simpa [realize_tVFOne] using h2

/-- `rv` of a `VF`-element is an `RV`-element. -/
theorem rv_mem_ax (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) : iRV (iRv x) := by
  have h := allSorted_realize hM (T := Axioms.ACVF) mem_ACVF_sdRv ![x] (by
    intro i
    fin_cases i
    simpa using hx)
  rw [pRVsort_realize, realize_tRv'] at h
  simpa using h

/-! ### The field laws on the `VF` sort -/

theorem eq_of_allSorted (hM : M ⊨ Axioms.ACVF) {k : ℕ}
    {ss : Fin k → SortTag} {a b : Tm k} (hmem : allSorted ss (pEq a b) ∈ Axioms.ACVF)
    (x : Fin k → M) (hx : ∀ i, (match ss i with
      | .vf => iVF (x i)
      | .rv => iRV (x i))) :
    a.realize (Sum.elim (default : Empty → M) x)
      = b.realize (Sum.elim (default : Empty → M) x) := by
  have h := allSorted_realize hM hmem x hx
  simpa only [pEq, BoundedFormula.realize_bdEqual] using h

theorem mem_vfField {s : LRV.Sentence} (h : s ∈ Axioms.vfField) : s ∈ Axioms.ACVF :=
  mem_ACVF_vfField h

theorem vf_add_assoc (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFAdd (iVFAdd x y) z = iVFAdd x (iVFAdd y z) := by
  have hmem : allSorted ![.vf, .vf, .vf]
      (pEq (tVFAdd (tVFAdd &0 &1) &2) (tVFAdd &0 (tVFAdd &1 &2))) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y, z] (by intro i; fin_cases i <;> simp [hx, hy, hz])
  simpa [realize_tVFAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    using h

theorem vf_add_comm (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y) :
    iVFAdd x y = iVFAdd y x := by
  have hmem : allSorted ![.vf, .vf] (pEq (tVFAdd &0 &1) (tVFAdd &1 &0)) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y] (by intro i; fin_cases i <;> simp [hx, hy])
  simpa [realize_tVFAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

theorem vf_add_zero (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iVFAdd x iVFZero = x := by
  have hmem : allSorted ![.vf] (pEq (tVFAdd &0 tVFZero) &0) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simpa [realize_tVFAdd, realize_tVFZero, Matrix.cons_val_zero] using h

theorem vf_add_neg (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iVFAdd x (iVFNeg x) = iVFZero := by
  have hmem : allSorted ![.vf] (pEq (tVFAdd &0 (tVFNeg &0)) tVFZero) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simpa [realize_tVFAdd, realize_tVFNeg, realize_tVFZero, Matrix.cons_val_zero] using h

theorem vf_mul_assoc (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFMul (iVFMul x y) z = iVFMul x (iVFMul y z) := by
  have hmem : allSorted ![.vf, .vf, .vf]
      (pEq (tVFMul (tVFMul &0 &1) &2) (tVFMul &0 (tVFMul &1 &2))) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y, z] (by intro i; fin_cases i <;> simp [hx, hy, hz])
  simpa [realize_tVFMul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    using h

theorem vf_mul_comm (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y) :
    iVFMul x y = iVFMul y x := by
  have hmem : allSorted ![.vf, .vf] (pEq (tVFMul &0 &1) (tVFMul &1 &0)) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y] (by intro i; fin_cases i <;> simp [hx, hy])
  simpa [realize_tVFMul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

theorem vf_mul_one (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iVFMul x iVFOne = x := by
  have hmem : allSorted ![.vf] (pEq (tVFMul &0 tVFOne) &0) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simpa [realize_tVFMul, realize_tVFOne, Matrix.cons_val_zero] using h

theorem vf_left_distrib (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFMul x (iVFAdd y z) = iVFAdd (iVFMul x y) (iVFMul x z) := by
  have hmem : allSorted ![.vf, .vf, .vf]
      (pEq (tVFMul &0 (tVFAdd &1 &2)) (tVFAdd (tVFMul &0 &1) (tVFMul &0 &2)))
      ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y, z] (by intro i; fin_cases i <;> simp [hx, hy, hz])
  simpa [realize_tVFAdd, realize_tVFMul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using h

theorem vf_zero_ne_one (hM : M ⊨ Axioms.ACVF) : (iVFZero : M) ≠ iVFOne := by
  have hmem : (∼(pEq tVFZero tVFOne)) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := sentence_realize' hM hmem
  rw [Sentence.Realize] at h
  simp only [Formula.Realize, BoundedFormula.realize_not, pEq, BoundedFormula.realize_bdEqual,
    realize_tVFZero, realize_tVFOne] at h
  exact h

theorem vf_mul_inv_or_zero (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    x = iVFZero ∨ ∃ y : M, iVF y ∧ iVFMul x y = iVFOne := by
  have hmem : allSorted ![.vf]
      (pEq &0 tVFZero ⊔ exSorted .vf (pEq (tVFMul &0 &1) tVFOne)) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := allSorted_realize hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  rw [BoundedFormula.realize_sup, pEq, BoundedFormula.realize_bdEqual, realize_tVFZero,
    exSorted_realize] at h
  rcases h with h | ⟨y, hy, hy2⟩
  · exact Or.inl h
  · refine Or.inr ⟨y, hy, ?_⟩
    simpa [pEq, realize_tVFMul, realize_tVFOne] using hy2

/-! ## 3. The `RV` preorder, the projection `rv`, and the two repair axioms -/

theorem mem_ACVF_leRefl : Axioms.leRefl ∈ Axioms.ACVF :=
  mem_ACVF_preorderRV (by simp [Axioms.preorderRV, Axioms.ofList])

theorem mem_ACVF_leTrans : Axioms.leTrans ∈ Axioms.ACVF :=
  mem_ACVF_preorderRV (by simp [Axioms.preorderRV, Axioms.ofList])

theorem mem_ACVF_leTotal : Axioms.leTotal ∈ Axioms.ACVF :=
  mem_ACVF_preorderRV (by simp [Axioms.preorderRV, Axioms.ofList])

theorem mem_ACVF_leTop : Axioms.leTop ∈ Axioms.ACVF :=
  mem_ACVF_preorderRV (by simp [Axioms.preorderRV, Axioms.ofList])

theorem mem_ACVF_leInftyEq : Axioms.leInftyEq ∈ Axioms.ACVF :=
  mem_ACVF_preorderRV (by simp [Axioms.preorderRV, Axioms.ofList])

theorem mem_ACVF_rvZeroEq : Axioms.rvZeroEq ∈ Axioms.ACVF :=
  mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])

theorem mem_ACVF_rvEqInfty : Axioms.rvEqInfty ∈ Axioms.ACVF :=
  mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])

theorem mem_ACVF_rvMulHom : Axioms.rvMulHom ∈ Axioms.ACVF :=
  mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])

theorem mem_ACVF_rvUltrametric : Axioms.rvUltrametric ∈ Axioms.ACVF :=
  mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])

/-- `rv 0 = ∞ = 0`. -/
theorem rv_zero_eq (hM : M ⊨ Axioms.ACVF) : iRv (iVFZero : M) = iRVZero := by
  have h := sentence_realize' hM mem_ACVF_rvZeroEq
  simpa [Axioms.rvZeroEq, Sentence.Realize, Formula.Realize, pEq, realize_tRv',
    realize_tVFZero, realize_tRVZero, tRVInfty] using h

/-- `rv x = ∞` forces `x = 0`. -/
theorem rv_eq_infty (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) (h : iRv x = iRVZero) :
    x = iVFZero := by
  have key : (iRv x = iRVZero) → (x = iVFZero) := by
    have h' := allSorted_realize hM mem_ACVF_rvEqInfty (x := ![x]) (by
      intro i; fin_cases i; simpa using hx)
    simpa [pEq, realize_tRv', realize_tRVZero, realize_tVFZero, tRVInfty] using h'
  exact key h

/-- `≤` is reflexive at every nonzero `RV`-element. -/
theorem le_refl_ax (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) (ha0 : a ≠ iRVZero) :
    iLe a a := by
  have h := allSorted_realize hM mem_ACVF_leRefl (x := ![a]) (by
    intro i; fin_cases i; simpa using ha)
  rw [BoundedFormula.realize_imp, pLe_realize'] at h
  exact h (by simpa [pRV, pEq, realize_tRVZero] using ha0)

/-- `≤` is transitive at nonzero `RV`-elements. -/
theorem le_trans_ax (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c)
    (ha0 : a ≠ iRVZero) (hb0 : b ≠ iRVZero) (hc0 : c ≠ iRVZero) (h1 : iLe a b) (h2 : iLe b c) :
    iLe a c := by
  have h := allSorted_realize hM mem_ACVF_leTrans (x := ![a, b, c]) (by
    intro i; fin_cases i <;> simp [ha, hb, hc])
  simp only [BoundedFormula.realize_imp, pLe_realize'] at h
  exact h (by simpa [pRV, pEq, realize_tRVZero] using ha0)
    (by simpa [pRV, pEq, realize_tRVZero] using hb0)
    (by simpa [pRV, pEq, realize_tRVZero] using hc0) h1 h2

/-- `≤` is total at nonzero `RV`-elements. -/
theorem le_total_ax (hM : M ⊨ Axioms.ACVF) {a b : M} (ha : iRV a) (hb : iRV b)
    (ha0 : a ≠ iRVZero) (hb0 : b ≠ iRVZero) : iLe a b ∨ iLe b a := by
  have h := allSorted_realize hM mem_ACVF_leTotal (x := ![a, b]) (by
    intro i; fin_cases i <;> simp [ha, hb])
  simp only [BoundedFormula.realize_imp, pLe_realize', BoundedFormula.realize_sup] at h
  exact h (by simpa [pRV, pEq, realize_tRVZero] using ha0)
    (by simpa [pRV, pEq, realize_tRVZero] using hb0)

/-- `∞` is the top of the `RV` preorder. -/
theorem le_top_ax (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) (ha0 : a ≠ iRVZero) :
    iLe a iRVZero := by
  have h := allSorted_realize hM mem_ACVF_leTop (x := ![a]) (by
    intro i; fin_cases i; simpa using ha)
  rw [BoundedFormula.realize_imp] at h
  have h2 := h (by simpa [pRV, pEq, realize_tRVZero] using ha0)
  simpa [pLe_realize', tRVInfty, realize_tRVZero] using h2

/-- `∞` is alone in its class. -/
theorem le_infty_eq_ax (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) (ha0 : a ≠ iRVZero)
    (h : iLe iRVZero a) : a = iRVZero := by
  have h' := allSorted_realize hM mem_ACVF_leInftyEq (x := ![a]) (by
    intro i; fin_cases i; simpa using ha)
  simp only [BoundedFormula.realize_imp, pLe_realize', pEq, BoundedFormula.realize_bdEqual,
    realize_tRVZero, tRVInfty] at h'
  exact h' (by simpa [pRV, pEq, realize_tRVZero] using ha0) h

/-- `rv` is multiplicative on the `VF` sort. -/
theorem rv_mul_hom_ax (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y) :
    iRv (iVFMul x y) = iRVMul (iRv x) (iRv y) := by
  have h := allSorted_realize hM mem_ACVF_rvMulHom (x := ![x, y]) (by
    intro i; fin_cases i <;> simp [hx, hy])
  simpa [pEq, realize_tRv', realize_tVFMul, realize_tRVMul] using h

/-- the ultrametric inequality `vv (x+y) ≥ min (vv x) (vv y)`, in the encoding's disjunctive form. -/
theorem rv_ultrametric_ax (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y) :
    iLe (iRv x) (iRv (iVFAdd x y)) ∨ iLe (iRv y) (iRv (iVFAdd x y)) := by
  have h := allSorted_realize hM mem_ACVF_rvUltrametric (x := ![x, y]) (by
    intro i; fin_cases i <;> simp [hx, hy])
  simpa [pLe_realize', realize_tRv', realize_tVFAdd, BoundedFormula.realize_sup] using h

/-- the order on `RV` is invariant under scaling by any `c ≠ 0`. -/
theorem le_mul_compat_full_ax (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b)
    (hc : iRV c) (hc0 : c ≠ iRVZero) :
    (iLe a b ↔ iLe (iRVMul a c) (iRVMul b c)) := by
  have h := allSorted_realize hM mem_ACVF_leMulCompatFull (x := ![a, b, c]) (by
    intro i; fin_cases i <;> simp [ha, hb, hc])
  rw [BoundedFormula.realize_imp] at h
  have h2 := h (by simpa [pRV, pEq, realize_tRVZero] using hc0)
  simpa [pLe_realize', realize_tRVMul, BoundedFormula.realize_iff] using h2

/-- **Nontriviality**: there is a nonzero `VF`-element whose value is strictly below the value of
`1`. -/
theorem nontrivial_ax (hM : M ⊨ Axioms.ACVF) :
    ∃ x : M, iVF x ∧ x ≠ iVFZero ∧ ¬ iLe (iRv x) (iRv iVFOne) := by
  have h := sentence_realize' hM mem_ACVF_axNontrivialRV
  rw [Sentence.Realize] at h
  simp only [Axioms.axNontrivialRV, Formula.Realize] at h
  rw [exSorted_realize (s := SortTag.vf) (v := (default : Empty → M))
    (x := (default : Fin 0 → M))] at h
  simp only [BoundedFormula.realize_inf, BoundedFormula.realize_not, pEq,
    BoundedFormula.realize_bdEqual, realize_tVFZero, realize_tRv', pLe_realize',
    realize_tVFOne] at h
  exact h


/-! ## 4. Consequences of the field laws -/

theorem vf_zero_add (hM : M ⊨ Axioms.ACVF) {y : M} (hy : iVF y) : iVFAdd iVFZero y = y := by
  rw [vf_add_comm hM (vf_zero_mem hM) hy, vf_add_zero hM hy]

theorem vf_add_left_cancel (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) (h : iVFAdd x y = iVFAdd x z) : y = z := by
  have hx' : iVF (iVFNeg x) := vf_neg_mem hM hx
  have h1 : iVFAdd (iVFNeg x) (iVFAdd x y) = iVFAdd (iVFNeg x) (iVFAdd x z) := by rw [h]
  rw [← vf_add_assoc hM hx' hx hy, ← vf_add_assoc hM hx' hx hz,
    vf_add_comm hM hx' hx, vf_add_neg hM hx,
    vf_zero_add hM hy, vf_zero_add hM hz] at h1
  exact h1

theorem vf_neg_zero (hM : M ⊨ Axioms.ACVF) : iVFNeg (iVFZero : M) = iVFZero := by
  have h0 : iVF (iVFZero : M) := vf_zero_mem hM
  have h0' : iVF (iVFNeg (iVFZero : M)) := vf_neg_mem hM h0
  have h1 : iVFAdd (iVFZero : M) (iVFNeg (iVFZero : M))
      = iVFAdd (iVFZero : M) (iVFZero : M) := by
    rw [vf_add_neg hM h0, vf_add_zero hM h0]
  exact vf_add_left_cancel (x := (iVFZero : M)) (y := iVFNeg (iVFZero : M))
    (z := (iVFZero : M)) hM h0 h0' h0 h1

theorem vf_add_neg_zero (hM : M ⊨ Axioms.ACVF) {y : M} (hy : iVF y) :
    iVFAdd y (iVFNeg iVFZero) = y := by
  rw [vf_neg_zero hM, vf_add_zero hM hy]

theorem vf_mul_zero (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iVFMul x iVFZero = iVFZero := by
  have h0 : iVF (iVFZero : M) := vf_zero_mem hM
  have hx0 : iVF (iVFMul x iVFZero) := vf_mul_mem hM hx h0
  have h1 : iVFAdd (iVFMul x iVFZero) (iVFMul x iVFZero)
      = iVFAdd (iVFMul x iVFZero) iVFZero := by
    rw [← vf_left_distrib hM hx h0 h0, vf_add_zero hM h0, vf_add_zero hM hx0]
  exact vf_add_left_cancel hM hx0 hx0 h0 h1

theorem vf_mul_neg (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y) :
    iVFMul x (iVFNeg y) = iVFNeg (iVFMul x y) := by
  have h0 : iVF (iVFZero : M) := vf_zero_mem hM
  have hy' : iVF (iVFNeg y) := vf_neg_mem hM hy
  have hxy : iVF (iVFMul x y) := vf_mul_mem hM hx hy
  have hxy' : iVF (iVFMul x (iVFNeg y)) := vf_mul_mem hM hx hy'
  have h1 : iVFAdd (iVFMul x y) (iVFMul x (iVFNeg y)) = iVFZero := by
    rw [← vf_left_distrib hM hx hy hy', vf_add_neg hM hy, vf_mul_zero hM hx]
  have h2 : iVFAdd (iVFMul x y) (iVFNeg (iVFMul x y)) = iVFZero := vf_add_neg hM hxy
  have h3 : iVFAdd (iVFMul x y) (iVFMul x (iVFNeg y))
      = iVFAdd (iVFMul x y) (iVFNeg (iVFMul x y)) := by rw [h1, h2]
  exact vf_add_left_cancel hM hxy hxy' (vf_neg_mem hM hxy) h3

theorem vf_neg_neg (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iVFNeg (iVFNeg x) = x := by
  have hx' : iVF (iVFNeg x) := vf_neg_mem hM hx
  have h1 : iVFAdd (iVFNeg x) (iVFNeg (iVFNeg x)) = iVFAdd (iVFNeg x) x := by
    rw [vf_add_neg hM hx', vf_add_comm hM hx' hx, vf_add_neg hM hx]
  exact vf_add_left_cancel hM hx' (vf_neg_mem hM hx') hx h1

theorem vf_neg_add (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y) :
    iVFNeg (iVFAdd x y) = iVFAdd (iVFNeg x) (iVFNeg y) := by
  have hx' : iVF (iVFNeg x) := vf_neg_mem hM hx
  have hy' : iVF (iVFNeg y) := vf_neg_mem hM hy
  have hxy : iVF (iVFAdd x y) := vf_add_mem hM hx hy
  have hs : iVF (iVFAdd (iVFNeg x) (iVFNeg y)) := vf_add_mem hM hx' hy'
  have h1 : iVFAdd (iVFAdd x y) (iVFAdd (iVFNeg x) (iVFNeg y)) = iVFZero := by
    rw [vf_add_assoc hM hx hy hs, ← vf_add_assoc hM hy hx' hy', vf_add_comm hM hy hx',
      vf_add_assoc hM hx' hy hy', vf_add_neg hM hy, vf_add_zero hM hx', vf_add_neg hM hx]
  have h2 : iVFAdd (iVFAdd x y) (iVFNeg (iVFAdd x y)) = iVFZero := vf_add_neg hM hxy
  have h3 : iVFAdd (iVFAdd x y) (iVFAdd (iVFNeg x) (iVFNeg y))
      = iVFAdd (iVFAdd x y) (iVFNeg (iVFAdd x y)) := by rw [h1, h2]
  exact (vf_add_left_cancel hM hxy hs (vf_neg_mem hM hxy) h3).symm

theorem vf_neg_mul_neg (hM : M ⊨ Axioms.ACVF) {z : M} (hz : iVF z) :
    iVFMul (iVFNeg z) (iVFNeg z) = iVFMul z z := by
  have hz' : iVF (iVFNeg z) := vf_neg_mem hM hz
  have h1 : iVFMul (iVFNeg z) (iVFNeg z) = iVFNeg (iVFMul (iVFNeg z) z) :=
    vf_mul_neg hM hz' hz
  have h2 : iVFMul (iVFNeg z) z = iVFNeg (iVFMul z z) := by
    rw [vf_mul_comm hM hz' hz, vf_mul_neg hM hz hz]
  rw [h1, h2, vf_neg_neg hM (vf_mul_mem hM hz hz)]

/-! ## 5. `rv (-z)` and `rv z` are `≤`-equivalent

This is the lemma every ball argument in this encoding needs: `IsClosedBall` writes its membership
as `rv (x + -a)`, so any comparison of two balls with *different* centres has to move a negation
through `rv`.  Nothing in the encoding does that directly, so it is derived here from the two
consequences `(-z)·(-z) = z·z` and the group structure of `RV^×` (repair axioms). -/

/-- `rv (-z) = 0` forces `rv z = 0`, and `z = 0`. -/
theorem neg_eq_zero_of_neg_eq_zero (hM : M ⊨ Axioms.ACVF) {z : M} (hz : iVF z)
    (h : iRv (iVFNeg z) = iRVZero) : z = iVFZero := by
  have h1 : iVFNeg z = iVFZero := rv_eq_infty (x := iVFNeg z) hM (vf_neg_mem hM hz) h
  have h2 : iVFNeg (iVFNeg z) = iVFNeg iVFZero := by rw [h1]
  rw [vf_neg_neg hM hz, vf_neg_zero hM] at h2
  exact h2

/-- a four-factor rearrangement in the abelian group `RV^×`, used for `q * q = 1`. -/
theorem rv_mul4 (hM : M ⊨ Axioms.ACVF) {a b c d : M} (ha : iRV a) (hb : iRV b)
    (hc : iRV c) (hd : iRV d) :
    iRVMul (iRVMul a b) (iRVMul c d) = iRVMul (iRVMul a c) (iRVMul b d) := by
  have hcd : iRV (iRVMul c d) := rv_mul_mem hM hc hd
  have hbd : iRV (iRVMul b d) := rv_mul_mem hM hb hd
  have hbc : iRV (iRVMul b c) := rv_mul_mem hM hb hc
  rw [rv_mul_assoc hM ha hb hcd]
  rw [← rv_mul_assoc hM hb hc hd, rv_mul_comm hM hb hc, rv_mul_assoc hM hc hb hd]
  rw [← rv_mul_assoc hM ha hc hbd]

theorem rv_neg_equiv_of_ne (hM : M ⊨ Axioms.ACVF) {z : M} (hz : iVF z) (hz0 : z ≠ iVFZero) :
    iLe (iRv (iVFNeg z)) (iRv z) ∧ iLe (iRv z) (iRv (iVFNeg z)) := by
  have hz' : iVF (iVFNeg z) := vf_neg_mem hM hz
  have hw : iRV (iRv (iVFNeg z)) := rv_mem_ax hM hz'
  have hu : iRV (iRv z) := rv_mem_ax hM hz
  have hw0 : iRv (iVFNeg z) ≠ iRVZero := by
    intro h; exact hz0 (neg_eq_zero_of_neg_eq_zero hM hz h)
  have hu0 : iRv z ≠ iRVZero := by
    intro h; exact hz0 (rv_eq_infty (x := z) hM hz h)
  -- the two squares agree
  have hsq : iRVMul (iRv (iVFNeg z)) (iRv (iVFNeg z)) = iRVMul (iRv z) (iRv z) := by
    have e1 : iRVMul (iRv (iVFNeg z)) (iRv (iVFNeg z)) = iRv (iVFMul (iVFNeg z) (iVFNeg z)) :=
      (rv_mul_hom_ax hM hz' hz').symm
    have e2 : iRv (iVFMul (iVFNeg z) (iVFNeg z)) = iRv (iVFMul z z) := by
      rw [vf_neg_mul_neg hM hz]
    have e3 : iRv (iVFMul z z) = iRVMul (iRv z) (iRv z) := rv_mul_hom_ax hM hz hz
    rw [e1, e2, e3]
  -- an inverse of `rv z`
  obtain ⟨ui, hui, hui0, hmul⟩ := rv_mul_inv hM hu hu0
  have hmul' : iRVMul (iRv z) ui = iRVOne := by
    rw [rv_mul_comm hM hu hui]; exact hmul
  set q := iRVMul (iRv (iVFNeg z)) ui with hqdef
  have hq : iRV q := rv_mul_mem hM hw hui
  have hq0 : q ≠ iRVZero := rv_mul_ne_zero hM hw hui hw0 hui0
  have hqq : iRVMul q q = iRVMul (iRVMul (iRv (iVFNeg z)) (iRv (iVFNeg z))) (iRVMul ui ui) := by
    rw [hqdef]
    exact rv_mul4 hM hw hui hw hui
  have huiui : iRV (iRVMul ui ui) := rv_mul_mem hM hui hui
  have hqsq : iRVMul q q = iRVOne := by
    rw [hqq, hsq]
    rw [← rv_mul4 hM hu hui hu hui, hmul']
    exact rv_mul_one_of_ne_zero hM (rv_one_mem hM) (rv_one_ne_zero hM)
  -- `q` is `≤`-equivalent to `1`
  have hq_le : iLe q iRVOne := by
    rcases le_total_ax (a := q) (b := iRVOne) hM hq (rv_one_mem hM) hq0
      (rv_one_ne_zero hM) with h | h
    · exact h
    · have hs := (le_mul_compat_full_ax (a := iRVOne) (b := q) (c := q) hM (rv_one_mem hM) hq
        hq hq0).1 h
      rwa [rv_mul_one_of_ne_zero hM hq hq0, hqsq] at hs
  have hone_le_q : iLe iRVOne q := by
    rcases le_total_ax (a := q) (b := iRVOne) hM hq (rv_one_mem hM) hq0
      (rv_one_ne_zero hM) with h | h
    · have hs := (le_mul_compat_full_ax (a := q) (b := iRVOne) (c := q) hM hq (rv_one_mem hM)
        hq hq0).1 h
      rwa [hqsq, rv_mul_one_of_ne_zero hM hq hq0] at hs
    · exact h
  have hqU : iRVMul q (iRv z) = iRv (iVFNeg z) := by
    rw [hqdef, rv_mul_assoc hM hw hui hu, rv_mul_comm hM hui hu, hmul',
      rv_mul_comm hM hw (rv_one_mem hM), rv_mul_one_of_ne_zero hM hw hw0]
  constructor
  · have hs := (le_mul_compat_full_ax (a := q) (b := iRVOne) (c := iRv z) hM hq
      (rv_one_mem hM) hu hu0).1 hq_le
    rwa [hqU, rv_mul_one_of_ne_zero hM hu hu0] at hs
  · have hs := (le_mul_compat_full_ax (a := iRVOne) (b := q) (c := iRv z) hM (rv_one_mem hM)
      hq hu hu0).1 hone_le_q
    rwa [hqU, rv_mul_one_of_ne_zero hM hu hu0] at hs

/-- `rv z ≤ rv (-z)`: the direction needed to move a negation out of a ball membership. -/
theorem le_rv_neg_of_le (hM : M ⊨ Axioms.ACVF) {z a : M} (hz : iVF z) (ha : iRV a)
    (ha0 : a ≠ iRVZero) (h : iLe a (iRv z)) : iLe a (iRv (iVFNeg z)) := by
  by_cases hz0 : z = iVFZero
  · simpa [hz0, vf_neg_zero hM] using h
  · exact le_trans_ax (b := iRv z) hM ha (rv_mem_ax hM hz) (rv_mem_ax hM (vf_neg_mem hM hz)) ha0
      (by intro hc; exact hz0 (rv_eq_infty (x := z) hM hz hc))
      (by intro hc; exact hz0 (neg_eq_zero_of_neg_eq_zero hM hz hc))
      h (rv_neg_equiv_of_ne hM hz hz0).2

/-- `rv (-z) ≤ rv z`: the other direction. -/
theorem le_of_le_rv_neg (hM : M ⊨ Axioms.ACVF) {z a : M} (hz : iVF z) (ha : iRV a)
    (ha0 : a ≠ iRVZero) (h : iLe a (iRv (iVFNeg z))) : iLe a (iRv z) := by
  by_cases hz0 : z = iVFZero
  · simpa [hz0, vf_neg_zero hM] using h
  · exact le_trans_ax (b := iRv (iVFNeg z)) hM ha (rv_mem_ax hM (vf_neg_mem hM hz))
      (rv_mem_ax hM hz) ha0
      (by intro hc; exact hz0 (neg_eq_zero_of_neg_eq_zero hM hz hc))
      (by intro hc; exact hz0 (rv_eq_infty (x := z) hM hz hc))
      h (rv_neg_equiv_of_ne hM hz hz0).1



/-- `1 · t = t` for `t` a value of a `VF`-element. -/
theorem rv_mul_one_left (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iRVMul (iRv (iVFOne : M)) (iRv x) = iRv x := by
  rw [← rv_mul_hom_ax hM (vf_one_mem hM) hx]
  have e : iVFMul (iVFOne : M) x = x := by
    rw [vf_mul_comm hM (vf_one_mem hM) hx, vf_mul_one hM hx]
  rw [e]

/-! ## 6. Closed balls -/

/-- The closed ball `C (a, r)` of radius `r` around `a`. -/
def Ball (a r : M) : Set M := {x | iVF x ∧ iLe r (iRv (iVFAdd x (iVFNeg a)))}

theorem ball_isClosedBall (_hM : M ⊨ Axioms.ACVF) {a r : M} (ha : iVF a) (hr : iRV r)
    (hr0 : r ≠ iRVZero) : IsClosedBall (Ball (M := M) a r) := ⟨a, r, ha, hr, hr0, rfl⟩

/-- **Every closed ball is nonempty**: it contains its centre. -/
theorem centre_mem (hM : M ⊨ Axioms.ACVF) {a r : M} (ha : iVF a) (hr : iRV r)
    (hr0 : r ≠ iRVZero) : a ∈ Ball a r := by
  have hsum : iVFAdd a (iVFNeg a) = (iVFZero : M) := vf_add_neg hM ha
  refine ⟨ha, ?_⟩
  rw [hsum, rv_zero_eq hM]
  exact le_top_ax hM hr hr0

/-- transitivity of `≤` at nonzero `RV`-elements, needing only the *middle* term to be nonzero. -/
theorem le_trans' (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c)
    (hb0 : b ≠ iRVZero) (h1 : iLe a b) (h2 : iLe b c) : iLe a c := by
  by_cases ha0 : a = iRVZero
  · exfalso
    rw [ha0] at h1
    exact hb0 (le_infty_eq_ax hM hb hb0 h1)
  · by_cases hc0 : c = iRVZero
    · rw [hc0]; exact le_top_ax hM ha ha0
    · exact le_trans_ax hM ha hb hc ha0 hb0 hc0 h1 h2

/-- A closed ball is monotone in its radius. -/
theorem ball_mono (hM : M ⊨ Axioms.ACVF) {a r s : M} (ha : iVF a) (hr : iRV r) (hs : iRV s)
    (hr0 : r ≠ iRVZero) (h : iLe r s) : Ball a s ⊆ Ball a r := by
  rintro x ⟨hx, hxs⟩
  refine ⟨hx, ?_⟩
  have hx' : iVF (iVFAdd x (iVFNeg a)) := vf_add_mem hM hx (vf_neg_mem hM ha)
  by_cases hs0 : s = iRVZero
  · have hz : iRv (iVFAdd x (iVFNeg a)) = iRVZero := by
      by_contra hc
      exact hc (le_infty_eq_ax hM (rv_mem_ax hM hx') hc (by rw [hs0] at hxs; exact hxs))
    rw [hz]; exact le_top_ax hM hr hr0
  · exact le_trans' hM hr hs (rv_mem_ax hM hx') hs0 h hxs

/-- `a + -y` and `y + -x + x = y`: the two term identities the ball arguments use. -/
theorem add_neg_cancel_left (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y) :
    iVFAdd (iVFAdd y (iVFNeg x)) x = y := by
  have hx' : iVF (iVFNeg x) := vf_neg_mem hM hx
  rw [vf_add_assoc hM hy hx' hx, vf_add_comm hM hx' hx, vf_add_neg hM hx,
    vf_add_zero hM hy]

theorem add_neg_cancel_right (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y) :
    iVFAdd x (iVFAdd (iVFNeg x) y) = y := by
  have hx' : iVF (iVFNeg x) := vf_neg_mem hM hx
  rw [← vf_add_assoc hM hx hx' hy, vf_add_neg hM hx, vf_zero_add hM hy]

/-- `a + (-y) + (y + (-b)) = a + (-b)`: the ultrametric applied to this pair produces the
centre distance of the two balls. -/
theorem sum_add_neg (hM : M ⊨ Axioms.ACVF) {a b y : M} (ha : iVF a) (hb : iVF b) (hy : iVF y) :
    iVFAdd (iVFAdd a (iVFNeg y)) (iVFAdd y (iVFNeg b)) = iVFAdd a (iVFNeg b) := by
  have h1 : iVF (iVFNeg y) := vf_neg_mem hM hy
  have h2 : iVF (iVFAdd y (iVFNeg b)) := vf_add_mem hM hy (vf_neg_mem hM hb)
  rw [vf_add_assoc hM ha h1 h2, ← vf_add_assoc hM h1 hy (vf_neg_mem hM hb),
    vf_add_comm hM h1 hy, vf_add_neg hM hy, vf_zero_add hM (vf_neg_mem hM hb)]

/-- `-(y + -a) = a + -y`: the term identity behind the negation-swap in the ball membership. -/
theorem neg_add_neg (hM : M ⊨ Axioms.ACVF) {a y : M} (ha : iVF a) (hy : iVF y) :
    iVFNeg (iVFAdd y (iVFNeg a)) = iVFAdd a (iVFNeg y) := by
  rw [vf_neg_add hM hy (vf_neg_mem hM ha), vf_neg_neg hM ha, vf_add_comm hM (vf_neg_mem hM hy) ha]

/-- `a + -y = 0` forces `a = y`. -/
theorem eq_of_add_neg_eq_zero (hM : M ⊨ Axioms.ACVF) {a y : M} (ha : iVF a) (hy : iVF y)
    (h : iVFAdd a (iVFNeg y) = iVFZero) : a = y := by
  have hy' : iVF (iVFNeg y) := vf_neg_mem hM hy
  have h1 : iVFAdd (iVFAdd a (iVFNeg y)) y = iVFAdd (iVFZero : M) y := by rw [h]
  rw [add_neg_cancel_left hM hy ha, vf_zero_add hM hy] at h1
  exact h1

/-- **Two closed balls with the same radius and centre distance strictly below the radius are
disjoint.**  This is the ball lemma `IsClosedBall (rvFibre t)` would need, and it is exactly where
the negation-invariance `rv_neg_equiv_of_ne` is used. -/
theorem ball_disjoint (hM : M ⊨ Axioms.ACVF) {a b r : M} (ha : iVF a) (hb : iVF b) (hr : iRV r)
    (hr0 : r ≠ iRVZero) (hdisj : ¬ iLe r (iRv (iVFAdd a (iVFNeg b)))) :
    Ball a r ∩ Ball b r = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨⟨hy, h1⟩, -, h2⟩
  have hyneg : iVF (iVFNeg y) := vf_neg_mem hM hy
  have h1' : iVF (iVFAdd y (iVFNeg a)) := vf_add_mem hM hy (vf_neg_mem hM ha)
  have h2' : iVF (iVFAdd y (iVFNeg b)) := vf_add_mem hM hy (vf_neg_mem hM hb)
  -- move the negation out of the first membership
  have h3 : iLe r (iRv (iVFAdd a (iVFNeg y))) := by
    have hs := le_rv_neg_of_le (hM := hM) (z := iVFAdd y (iVFNeg a)) (a := r) h1' hr hr0 h1
    rwa [neg_add_neg hM ha hy] at hs
  -- the ultrametric inequality for the pair `(a + -y, y + -b)`, whose sum is `a + -b`
  have hultra := rv_ultrametric_ax (hM := hM) (x := iVFAdd a (iVFNeg y))
    (y := iVFAdd y (iVFNeg b)) (vf_add_mem hM ha hyneg) h2'
  rw [sum_add_neg hM ha hb hy] at hultra
  have hs1 : iRV (iRv (iVFAdd a (iVFNeg y))) := rv_mem_ax hM (vf_add_mem hM ha hyneg)
  have hs2 : iRV (iRv (iVFAdd y (iVFNeg b))) := rv_mem_ax hM h2'
  have hs3 : iRV (iRv (iVFAdd a (iVFNeg b))) := rv_mem_ax hM (vf_add_mem hM ha (vf_neg_mem hM hb))
  rcases hultra with hu | hu
  · by_cases hz : iRv (iVFAdd a (iVFNeg y)) = iRVZero
    · have hz' : iVFAdd a (iVFNeg y) = iVFZero :=
        rv_eq_infty (x := iVFAdd a (iVFNeg y)) hM (vf_add_mem hM ha hyneg) hz
      have hay : a = y := eq_of_add_neg_eq_zero hM ha hy hz'
      rw [← hay] at h2
      exact hdisj h2
    · exact hdisj (le_trans' hM hr hs1 hs3 hz h3 hu)
  · by_cases hz : iRv (iVFAdd y (iVFNeg b)) = iRVZero
    · have hz' : iVFAdd y (iVFNeg b) = iVFZero :=
        rv_eq_infty (x := iVFAdd y (iVFNeg b)) hM h2' hz
      have hyb : y = b := eq_of_add_neg_eq_zero hM hy hb hz'
      rw [hyb] at h3
      exact hdisj h3
    · exact hdisj (le_trans' hM hr hs2 hs3 hz h2 hu)

/-! ## 7. The three-ball configuration exists in every model of `ACVF` -/

/-- **The counterexample configuration.**  In every model of `Axioms.ACVF` there are three closed
balls `b1, b2 ⊆ b3` with `b1 ∩ b2 = ∅` and both nonempty: take `x` with `v x` strictly above the
value of `1` (nontriviality), `γ = v (x·x)`, `b3 = C (0, v 1)`, `b1 = C (0, γ)`,
`b2 = C (x, γ)`.  The three balls are distinct as required: `x ∈ b3` and `x ∉ b1`, because
`γ > v x`. -/
theorem three_balls (hM : M ⊨ Axioms.ACVF) :
    ∃ b1 b2 b3 : Set M, IsClosedBall b1 ∧ IsClosedBall b2 ∧ IsClosedBall b3 ∧
      b1.Nonempty ∧ b2.Nonempty ∧ b1 ⊆ b3 ∧ b2 ⊆ b3 ∧ b1 ∩ b2 = ∅ := by
  obtain ⟨x, hx, hx0, hlt⟩ := nontrivial_ax hM
  have hx2 : iVF (iVFMul x x) := vf_mul_mem hM hx hx
  have h1mem : iVF (iVFOne : M) := vf_one_mem hM
  have hrv1 : iRV (iRv (iVFOne : M)) := rv_mem_ax hM h1mem
  have hrvx : iRV (iRv x) := rv_mem_ax hM hx
  have hrvx2 : iRV (iRv (iVFMul x x)) := rv_mem_ax hM hx2
  have hxne : iRv x ≠ iRVZero := by
    intro h; exact hx0 (rv_eq_infty (x := x) hM hx h)
  have hx2ne : iRv (iVFMul x x) ≠ iRVZero := by
    have h := rv_mul_ne_zero hM hrvx hrvx hxne hxne
    rwa [← rv_mul_hom_ax hM hx hx] at h
  have h1ne : iRv (iVFOne : M) ≠ iRVZero := by
    intro h; exact vf_zero_ne_one hM ((rv_eq_infty (x := iVFOne) hM h1mem h).symm)
  -- `v 1 ≤ v x ≤ v (x·x)`
  have h1x : iLe (iRv (iVFOne : M)) (iRv x) := by
    rcases le_total_ax (a := iRv (iVFOne : M)) (b := iRv x) hM hrv1 hrvx h1ne hxne with h | h
    · exact h
    · exact absurd h hlt
  have hx2' : iLe (iRv x) (iRv (iVFMul x x)) := by
    have hs := (le_mul_compat_full_ax (a := iRv (iVFOne : M)) (b := iRv x) (c := iRv x) hM
      hrv1 hrvx hrvx hxne).1 h1x
    have e1 : iRVMul (iRv (iVFOne : M)) (iRv x) = iRv x := rv_mul_one_left hM hx
    have e2 : iRVMul (iRv x) (iRv x) = iRv (iVFMul x x) := (rv_mul_hom_ax hM hx hx).symm
    rwa [e1, e2] at hs
  have hnot : ¬ iLe (iRv (iVFMul x x)) (iRv x) := by
    intro hs
    have e1 : iRVMul (iRv x) (iRv x) = iRv (iVFMul x x) := (rv_mul_hom_ax hM hx hx).symm
    have e2 : iRVMul (iRv (iVFOne : M)) (iRv x) = iRv x := rv_mul_one_left hM hx
    have hs' : iLe (iRVMul (iRv x) (iRv x)) (iRVMul (iRv (iVFOne : M)) (iRv x)) := by
      rw [e1, e2]; exact hs
    exact hlt ((le_mul_compat_full_ax (a := iRv x) (b := iRv (iVFOne : M)) (c := iRv x) hM
      hrvx hrv1 hrvx hxne).2 hs')
  refine ⟨Ball (iVFZero : M) (iRv (iVFMul x x)), Ball x (iRv (iVFMul x x)),
    Ball (iVFZero : M) (iRv (iVFOne : M)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ball_isClosedBall hM (vf_zero_mem hM) hrvx2 hx2ne
  · exact ball_isClosedBall hM hx hrvx2 hx2ne
  · exact ball_isClosedBall hM (vf_zero_mem hM) hrv1 h1ne
  · exact ⟨iVFZero, centre_mem hM (vf_zero_mem hM) hrvx2 hx2ne⟩
  · exact ⟨x, centre_mem hM hx hrvx2 hx2ne⟩
  · -- `Ball 0 γ ⊆ Ball 0 (v 1)`
    exact ball_mono hM (vf_zero_mem hM) hrv1 hrvx2 h1ne (le_trans' hM hrv1 hrvx hrvx2 hxne h1x hx2')
  · -- `Ball x γ ⊆ Ball 0 (v 1)`
    intro y hy
    obtain ⟨hyv, hyb⟩ := hy
    have hyneg : iVF (iVFNeg x) := vf_neg_mem hM hx
    have hmem : iVF (iVFAdd y (iVFNeg x)) := vf_add_mem hM hyv hyneg
    have hultra := rv_ultrametric_ax (hM := hM) (x := iVFAdd y (iVFNeg x)) (y := x) hmem hx
    rw [add_neg_cancel_left hM hx hyv] at hultra
    have hrmem : iRV (iRv (iVFAdd y (iVFNeg x))) := rv_mem_ax hM hmem
    have hle1 : iLe (iRv (iVFOne : M)) (iRv y) := by
      rcases hultra with hu | hu
      · by_cases hz : iRv (iVFAdd y (iVFNeg x)) = iRVZero
        · have hz' : iVFAdd y (iVFNeg x) = iVFZero :=
            rv_eq_infty (x := iVFAdd y (iVFNeg x)) hM hmem hz
          have hyx : y = x := eq_of_add_neg_eq_zero hM hyv hx hz'
          rw [hyx]; exact h1x
        · have hmid : iLe (iRv (iVFOne : M)) (iRv (iVFAdd y (iVFNeg x))) :=
            le_trans' (a := iRv (iVFOne : M)) (b := iRv (iVFMul x x))
              (c := iRv (iVFAdd y (iVFNeg x))) hM hrv1 hrvx2 hrmem hx2ne
              (le_trans' (a := iRv (iVFOne : M)) (b := iRv x) (c := iRv (iVFMul x x))
                hM hrv1 hrvx hrvx2 hxne h1x hx2') hyb
          exact le_trans' (a := iRv (iVFOne : M)) (b := iRv (iVFAdd y (iVFNeg x)))
            (c := iRv y) hM hrv1 hrmem (rv_mem_ax hM hyv) hz hmid hu
      · exact le_trans' hM hrv1 hrvx (rv_mem_ax hM hyv) hxne h1x hu
    have hy0 : iVFAdd y (iVFNeg iVFZero) = y := vf_add_neg_zero hM hyv
    refine ⟨hyv, ?_⟩
    rw [hy0]
    exact hle1
  · refine ball_disjoint hM (vf_zero_mem hM) hx hrvx2 hx2ne ?_
    intro h
    rw [vf_zero_add hM (vf_neg_mem hM hx)] at h
    exact hnot (le_of_le_rv_neg (hM := hM) (z := x) (a := iRv (iVFMul x x)) hx hrvx2 hx2ne h)

/-! ## 8. The frozen `HasCenters` is refuted

`QE/Sec3_sat.lean` states `Sec3.IsSetOfCenters` and `Sec3.HasCenters` as the transcription of
Definition 4.14 of arXiv:1006.1393 ("`𝓑` has centers [if] there is a definable function
`f : 𝓑 → VF` such that `f(𝔟ᵢ) ∈ 𝔟ᵢ`").  The transcription reads the *set* `f(𝓑) = C` and requires
**exactly one** point of `C` in each ball — a strengthening: for a nested pair `b1 ⊆ b3` the paper's
definition allows `f b3 = f b1 ∈ b1`, while `∃! c, c ∈ C ∧ c ∈ b` forbids it unless no other member
of `C` lies in `b3`.  Three balls already defeat it. -/

namespace Sec3Copy

/-- `QE/Sec3_sat.lean`'s `Sec3.IsAlgebraicSetOfBalls`, verbatim. -/
def IsAlgebraicSetOfBalls (𝓑 : Set (Set M)) : Prop := 𝓑.Finite ∧ ∀ b ∈ 𝓑, IsBall b

/-- `QE/Sec3_sat.lean`'s `Sec3.IsSetOfCenters`, verbatim. -/
def IsSetOfCenters (𝓑 : Set (Set M)) (C : Set M) : Prop := ∀ b ∈ 𝓑, ∃! c : M, c ∈ C ∧ c ∈ b

/-- `QE/Sec3_sat.lean`'s `Sec3.HasCenters`, verbatim. -/
def HasCenters (𝓑 : Set (Set M)) : Prop := ∃ C : Set M, IsSetOfCenters 𝓑 C

end Sec3Copy

/-- **Two disjoint nonempty sets inside a third have no "set of centers"**: the unique point of `C`
in the third must be the point of the first and of the second. -/
theorem not_isSetOfCenters_three {b1 b2 b3 C : Set M} (_hne1 : b1.Nonempty)
    (_hne2 : b2.Nonempty)
    (hsub1 : b1 ⊆ b3) (hsub2 : b2 ⊆ b3) (hd : b1 ∩ b2 = ∅) :
    ¬ Sec3Copy.IsSetOfCenters {b | b = b1 ∨ b = b2 ∨ b = b3} C := by
  intro hC
  obtain ⟨c1, ⟨hc1C, hc1b1⟩, -⟩ := hC b1 (Or.inl rfl)
  obtain ⟨c2, ⟨hc2C, hc2b2⟩, -⟩ := hC b2 (Or.inr (Or.inl rfl))
  obtain ⟨c3, ⟨-, hc3b3⟩, hu3⟩ := hC b3 (Or.inr (Or.inr rfl))
  have e1 : c1 = c3 := hu3 c1 ⟨hc1C, hsub1 hc1b1⟩
  have e2 : c2 = c3 := hu3 c2 ⟨hc2C, hsub2 hc2b2⟩
  have hc12 : c1 = c2 := e1.trans e2.symm
  have hmem : c1 ∈ b1 ∩ b2 := ⟨hc1b1, by rw [hc12]; exact hc2b2⟩
  rw [hd] at hmem
  exact hmem

/-- **The frozen transcription of Definition 4.14 is false.**  In *every* model of `Axioms.ACVF`
there is an algebraic set of closed balls with no set of centers: the three balls
`C(0, v 1) ⊇ C(0, v(x·x))`, `C(x, v(x·x))` of `three_balls`, the last two disjoint and nonempty.

This is the shape of `Sec3.HasCenters`, so `swl_effectiveness` (`effectiveness`, Yin 4.15) and
`swl_algebraic_balls_definable_centers` (`algebraic:balls:definable:centers`, Yin 4.17) are false as
frozen in `QE/Sec3_sat.lean`: their hypotheses are met by this family in every model, and the
conclusion fails.  (The paper's own Definition 4.14 asks for a *function* `f` with `f b ∈ b`, which
is `hasCenters_fun` below and is unconditional.) -/
theorem hasCenters_false (hM : M ⊨ Axioms.ACVF) :
    ∃ 𝓑 : Set (Set M), Sec3Copy.IsAlgebraicSetOfBalls 𝓑 ∧
      (∀ b ∈ 𝓑, IsClosedBall b) ∧ ¬ Sec3Copy.HasCenters 𝓑 := by
  obtain ⟨b1, b2, b3, hc1, hc2, hc3, hne1, hne2, hs1, hs2, hd⟩ := three_balls hM
  refine ⟨{b | b = b1 ∨ b = b2 ∨ b = b3}, ⟨?_, ?_⟩, ?_, ?_⟩
  · have hset : ({b | b = b1 ∨ b = b2 ∨ b = b3} : Set (Set M)) = {b1, b2, b3} := by
      ext b
      simp [Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hset]; exact Set.toFinite _
  · rintro b (rfl | rfl | rfl)
    · exact Or.inr (Or.inl hc1)
    · exact Or.inr (Or.inl hc2)
    · exact Or.inr (Or.inl hc3)
  · rintro b (rfl | rfl | rfl)
    · exact hc1
    · exact hc2
    · exact hc3
  · rintro ⟨C, hC⟩
    exact not_isSetOfCenters_three hne1 hne2 hs1 hs2 hd hC

/-- **The paper's Definition 4.14, correctly transcribed**: "there is a function `f : 𝓑 → VF` such
that `f(𝔟ᵢ) ∈ 𝔟ᵢ`".  Unlike `Sec3Copy.HasCenters` this is *unconditionally* true for any family of
nonempty sets — no mathematics, only choice — which is why the frozen `∃!`-form carries a
strengthening of the definition rather than its content. -/
theorem hasCenters_fun (𝓑 : Set (Set M)) (hne : ∀ b ∈ 𝓑, b.Nonempty) :
    ∃ f : (b : Set M) → b ∈ 𝓑 → M, ∀ (b : Set M) (hb : b ∈ 𝓑), f b hb ∈ b :=
  ⟨fun b hb => Classical.choose (hne b hb), fun b hb => Classical.choose_spec (hne b hb)⟩

/-- Every closed ball is nonempty, so the paper's form of "has centers" holds for any family of
closed balls — in particular for every algebraic set of closed balls. -/
theorem hasCenters_fun_of_closed (hM : M ⊨ Axioms.ACVF) (𝓑 : Set (Set M))
    (hc : ∀ b ∈ 𝓑, IsClosedBall b) :
    ∃ f : (b : Set M) → b ∈ 𝓑 → M, ∀ (b : Set M) (hb : b ∈ 𝓑), f b hb ∈ b := by
  refine hasCenters_fun 𝓑 ?_
  intro b hb
  obtain ⟨a, r, ha, hr, hr0, rfl⟩ := hc b hb
  exact ⟨a, centre_mem hM ha hr hr0⟩

#print axioms hasCenters_false
#print axioms three_balls
#print axioms rv_neg_equiv_of_ne
#print axioms ball_disjoint
#print axioms hasCenters_fun_of_closed

end BallSec3
end Milestone0
end SpecialTransformations
