/-
**Route (T1) of the QE plan: the syntactic translation `L_val → L_RV` over the frozen `Enc`,
and the reduction of the frozen `HasQE` at the all-`VF` context to `L_val` quantifier
elimination plus one exactly stated residual.**

`QE-PLAN.md` §"(T1) Syntactic translation" proposes to get the frozen `HasQE Axioms.ACVF` from
`hasQE_ACVF_val` (the `L_val` quantifier elimination of `QE/Assembly_val.lean`) by a composition:

  1. a syntactic translation `L_val → L_RV` (every `L_val` formula becomes an `L_RV` formula
     whose context is all-`VF`), plus
  2. an elimination of the `RV` quantifier, `∃ y (RV), ψ ↦ ∃ x (VF), ψ[rv x / y]`, plus
  3. an atom layer: a quantifier-free `L_RV` formula whose context is all-`VF` is still built
     from `rvMul`/`kAdd`/`kNeg`, and those composite `RV`-terms have to be eliminated formula by
     formula, because they have no `L_val` image term by term.

This file builds and verifies (1) and (2) and reduces the target to (3) exactly.

**What is proved here (no `sorry`, no `axiom`, no `native_decide`).**

* §1–§4 `LV`, `valStruct`, `tTm`, `tBf`: the language `L_val` (a copy of `Assembly_val`'s
  `Language.val`: rings plus `v x ≤ v y`) and the translation.  `v s ≤ v t` goes to `rv t ≤ rv s`
  because `L_val`'s predicate is the *absolute-value* order (`v (x+y) ≤ max`, `v 0` minimal —
  `Assembly_val`'s `axUltra`, `axZeroLe`) and the encoding's `pLe` is the *paper's* value-group
  order; the two are reverse to each other, which is the same dictionary as `VFValued.predV`.
* §5 `realize_tTm`, `realize_tBf`: the translation is semantically correct, in **every**
  `L_RV`-structure, with no model hypothesis — `valStruct`'s junk values off the `VF` sort are
  never reached, because the same assignment is used on both sides.
* §6 `tmSort_tTm` (every `L_val`-term translates to a `VF`-sorted `L_RV` term), `isQF_tBf`,
  `wellSorted_tBf` (the translation of a quantifier-free `L_val` formula is a well-sorted formula
  of the frozen fragment at the all-`VF` context — the `all` case is excluded by `IsQF`, which is
  why only quantifier-free `L_val` output can be translated: `WellSorted.all` demands a guard the
  translation does not have).
* §8 `iRv_zero` (`rv 0 = 0 = ∞`), `rv_surj_vf` (**`rv` is onto the whole `RV` sort, with no
  exception**), `real_exSorted_rv` and **`exSorted_rv_iff_vf`**: the `RV` quantifier is exactly a
  `VF` quantifier over `rv`, `∃ y ∈ RV, ψ ↔ ∃ x ∈ VF, ψ[rv x / y]`.  This is the quantifier case
  of (T1), and it is unconditional: `Axioms.rvSurj` gives `RV ∖ {rv 0} ⊆ rv(VF)` and
  `Axioms.rvZeroEq` identifies `rv 0` with `0 = ∞`, so the paper's exceptional value disappears.
  **The "twelfth encoding defect" does not block (T1).**
* §9–§10 the two named inputs and the composition: **`hasQE_vf_of_valQE : LvalQE → RVAtomElim →
  HasQEvf Axioms.ACVF`**, and `hasQEvf_of_hasQE` (the frozen `HasQE` implies `HasQEvf`).
* §11 the atom layer, split into what the tree already has (the `rv`-fragment dictionary:
  `RVCalc.units_iff_le_one`, `RVDict.rv_eq_iff_le`, `RVCalc.vf_eq_zero_of_rv_eq_zero`,
  `Transfer.rv_mul_hom_of_model`, `RVCalc.rv_one`) and what it does not (the recursion through
  `kAdd`/`kNeg`).
* §12 `kHyps_realize` and `allSortedK_realize` — the extraction lemma for `allSortedK`-guarded
  sentences (`Axioms.kField`, `Axioms.kAddLink`), ported from `QE/Assembly_val.lean:12812-12837`
  because that file cannot be imported; plus `iRV_of_inK` (`K ⊆ RV`), and the two `Axioms.kField`
  facts `iKAdd_zero` (`t + 0 = t` on `K`) and `iKAdd_comm` (`kAdd` is commutative on `K`) that the
  `kAdd` case analysis needs.  The case split itself is not carried out.

**What is NOT proved here, and why — `RVAtomElim`, stated exactly in §9.**

A well-sorted quantifier-free `L_RV` formula with an all-`VF` context may contain the composite
`RV`-terms `kAdd`, `kNeg` (`rvMul` is harmless: `rv` is multiplicative).  `kAdd`/`kNeg` are pinned
down completely by the frozen axioms — `kAddLink`/`kNegLink` on `K = Kˣ ∪ {0}`,
`kJunkZero`/`kNegJunkZero` off it — so the elimination is a finite case analysis on `pInK`
carried out on term structure; it is not carried out in this file.

**`LvalQE` is the second input, and it is the L_val QE itself.**  It is stated semantically
(quantifier elimination at `VF`-tuples in models of `ACVF`) rather than through
`QECriterion.HasQE (L := Language.val) ACVF_val`, because the two encoding snapshots cannot be
imported together (`QE/Assembly_val.lean` redefines the whole `Milestone0` namespace).  The
remaining bookkeeping on that side is the theory matching `valStruct M ⊨ ACVF_val`, which is
*false on the whole carrier* `M` — `M` carries junk outside `VF ∪ RV` and `Theory.field` is not
satisfied there — and true only for the structure on the subtype `VFType M` that
`QE/VFField.lean` and `QE/VFValued.lean` build.  That is why `LvalQE` is stated at `VF`-tuples of
`valStruct`: on those tuples the two structures agree definitionally and the junk never appears.

Written by swarm `smw1sd59b` member m2; direction (T1)'s syntactic-translation piece.
Build: `cd .scratch2/sec3 && cp ../../.ultramath/smw1sd59b/m2/Jm2T1.lean . &&
LEAN_PATH=$PWD:$LEAN_PATH lean Jm2T1.lean`.
-/
import Assembly_frozen
import RVDict

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace Jm2

/-! ## 1. The one-sorted language `L_val` of valued fields -/

inductive VFunc : ℕ → Type
  /-- `+` -/
  | add : VFunc 2
  /-- `×` -/
  | mul : VFunc 2
  /-- `-` -/
  | neg : VFunc 1
  /-- `0` -/
  | zero : VFunc 0
  /-- `1` -/
  | one : VFunc 0
  deriving DecidableEq

inductive VRel : ℕ → Type
  /-- `v x ≤ v y` -/
  | le : VRel 2
  deriving DecidableEq

/-- **Johnson's `L_val`**: the language of rings expanded by the predicate `v x ≤ v y`. -/
@[reducible] def LV : FirstOrder.Language := ⟨VFunc, VRel⟩

namespace LV

variable {α : Type}

/-- the term `0` of `L_val` -/
def tZero : LV.Term α := Term.func VFunc.zero fun i => i.elim0
/-- the term `1` of `L_val` -/
def tOne : LV.Term α := Term.func VFunc.one fun i => i.elim0
/-- the term `a + b` of `L_val` -/
def tAdd (a b : LV.Term α) : LV.Term α := Term.func VFunc.add ![a, b]
/-- the term `a × b` of `L_val` -/
def tMul (a b : LV.Term α) : LV.Term α := Term.func VFunc.mul ![a, b]
/-- the term `- a` of `L_val` -/
def tNeg (a : LV.Term α) : LV.Term α := Term.func VFunc.neg ![a]

/-- the atomic formula `v a ≤ v b` of `L_val` -/
def leF {n : ℕ} (a b : LV.Term (α ⊕ Fin n)) : LV.BoundedFormula α n :=
  Relations.boundedFormula₂ VRel.le a b

end LV

/-! ## 2. The `L_val`-structure attached to an `L_RV`-structure -/

/-- the `L_val`-structure read off an `L_RV`-structure.  `v x ≤ v y` is read as
`rv y ≤ rv x`: `L_val`'s predicate is the absolute-value order, the encoding's `pLe` is the
paper's value-group order, and the two are reverse to each other (`VFValued.predV`). -/
@[instance_reducible] def valStruct (M : Type) [LRV.Structure M] : LV.Structure M where
  funMap := fun {_} f x =>
    match f with
    | VFunc.add => iVFAdd (x 0) (x 1)
    | VFunc.mul => iVFMul (x 0) (x 1)
    | VFunc.neg => iVFNeg (x 0)
    | VFunc.zero => iVFZero
    | VFunc.one => iVFOne
  RelMap := fun {_} r x =>
    match r with
    | VRel.le => iLe (iRv (x 1)) (iRv (x 0))

instance instLVStructure (M : Type) [LRV.Structure M] : LV.Structure M := valStruct M

theorem funMap_zero {M : Type} [LRV.Structure M] :
    (Structure.funMap (L := LV) VFunc.zero (fun i : Fin 0 => i.elim0) : M) = iVFZero := rfl

theorem funMap_one {M : Type} [LRV.Structure M] :
    (Structure.funMap (L := LV) VFunc.one (fun i : Fin 0 => i.elim0) : M) = iVFOne := rfl

theorem funMap_add {M : Type} [LRV.Structure M] (a b : M) :
    Structure.funMap (L := LV) VFunc.add ![a, b] = iVFAdd a b := rfl

theorem funMap_mul {M : Type} [LRV.Structure M] (a b : M) :
    Structure.funMap (L := LV) VFunc.mul ![a, b] = iVFMul a b := rfl

theorem funMap_neg {M : Type} [LRV.Structure M] (a : M) :
    Structure.funMap (L := LV) VFunc.neg ![a] = iVFNeg a := rfl

theorem relMap_le {M : Type} [LRV.Structure M] (a b : M) :
    Structure.RelMap (L := LV) VRel.le ![a, b] = iLe (iRv b) (iRv a) := rfl

/-! ## 3. Wrappers for the `L_RV` term constructors at a general parameter type -/

/-- `rv` of an `L_RV`-term -/
def trv {α : Type} (t : LRV.Term α) : LRV.Term α := Term.func Fn.rvMap ![t]
/-- `+` of the `VF` sort -/
def vadd {α : Type} (a b : LRV.Term α) : LRV.Term α := Term.func Fn.vfAdd ![a, b]
/-- `×` of the `VF` sort -/
def vmul {α : Type} (a b : LRV.Term α) : LRV.Term α := Term.func Fn.vfMul ![a, b]
/-- `-` of the `VF` sort -/
def vneg {α : Type} (a : LRV.Term α) : LRV.Term α := Term.func Fn.vfNeg ![a]
/-- `0` of the `VF` sort -/
def vzero {α : Type} : LRV.Term α := Term.func Fn.vfZero fun i => i.elim0
/-- `1` of the `VF` sort -/
def vone {α : Type} : LRV.Term α := Term.func Fn.vfOne fun i => i.elim0

/-! ## 4. The translation `L_val → L_RV` -/

/-- **The term translation.** -/
def tTm {α : Type} : LV.Term α → LRV.Term α
  | Term.var a => Term.var a
  | Term.func f ts =>
    match f with
    | VFunc.add => vadd (tTm (ts 0)) (tTm (ts 1))
    | VFunc.mul => vmul (tTm (ts 0)) (tTm (ts 1))
    | VFunc.neg => vneg (tTm (ts 0))
    | VFunc.zero => vzero
    | VFunc.one => vone

/-- **The formula translation**: `t = u ↦ t = u`, `v s ≤ v t ↦ rv t ≤ rv s`, connectives
componentwise, the universal quantifier carried over. -/
def tBf {α : Type} : {n : ℕ} → LV.BoundedFormula α n → LRV.BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal a b => .equal (tTm a) (tTm b)
  | _, .rel VRel.le ts => .rel Rel.rvLe ![trv (tTm (ts 1)), trv (tTm (ts 0))]
  | _, .imp a b => .imp (tBf a) (tBf b)
  | _, .all θ => .all (tBf θ)

/-! ## 5. Realization lemmas at a general parameter type -/

section RealizeGen

variable {M : Type} [LRV.Structure M] {α : Type}

theorem realize_vadd (ρ : α → M) (a b : LRV.Term α) :
    Term.realize (L := LRV) ρ (vadd a b)
      = iVFAdd (Term.realize (L := LRV) ρ a) (Term.realize (L := LRV) ρ b) := by
  show Structure.funMap (L := LRV) Fn.vfAdd
      (fun i => Term.realize (L := LRV) ρ (![a, b] i)) = iVFAdd _ _
  rw [show (fun i : Fin 2 => Term.realize (L := LRV) ρ (![a, b] i))
      = ![Term.realize (L := LRV) ρ a, Term.realize (L := LRV) ρ b] from by
    funext i; fin_cases i <;> rfl]
  rfl

theorem realize_vmul (ρ : α → M) (a b : LRV.Term α) :
    Term.realize (L := LRV) ρ (vmul a b)
      = iVFMul (Term.realize (L := LRV) ρ a) (Term.realize (L := LRV) ρ b) := by
  show Structure.funMap (L := LRV) Fn.vfMul
      (fun i => Term.realize (L := LRV) ρ (![a, b] i)) = iVFMul _ _
  rw [show (fun i : Fin 2 => Term.realize (L := LRV) ρ (![a, b] i))
      = ![Term.realize (L := LRV) ρ a, Term.realize (L := LRV) ρ b] from by
    funext i; fin_cases i <;> rfl]
  rfl

theorem realize_vneg (ρ : α → M) (a : LRV.Term α) :
    Term.realize (L := LRV) ρ (vneg a) = iVFNeg (Term.realize (L := LRV) ρ a) := by
  show Structure.funMap (L := LRV) Fn.vfNeg
      (fun i => Term.realize (L := LRV) ρ (![a] i)) = iVFNeg _
  rw [show (fun i : Fin 1 => Term.realize (L := LRV) ρ (![a] i))
      = ![Term.realize (L := LRV) ρ a] from by funext i; fin_cases i; rfl]
  rfl

theorem realize_vzero (ρ : α → M) :
    Term.realize (L := LRV) ρ (vzero (α := α)) = iVFZero := by
  show Structure.funMap (L := LRV) Fn.vfZero
      (fun i : Fin 0 => Term.realize (L := LRV) ρ ((fun i : Fin 0 => i.elim0) i)) = iVFZero
  rw [show (fun i : Fin 0 => Term.realize (L := LRV) ρ ((fun i : Fin 0 => i.elim0) i))
      = (fun i : Fin 0 => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem realize_vone (ρ : α → M) :
    Term.realize (L := LRV) ρ (vone (α := α)) = iVFOne := by
  show Structure.funMap (L := LRV) Fn.vfOne
      (fun i : Fin 0 => Term.realize (L := LRV) ρ ((fun i : Fin 0 => i.elim0) i)) = iVFOne
  rw [show (fun i : Fin 0 => Term.realize (L := LRV) ρ ((fun i : Fin 0 => i.elim0) i))
      = (fun i : Fin 0 => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem realize_trv (ρ : α → M) (t : LRV.Term α) :
    Term.realize (L := LRV) ρ (trv t) = iRv (Term.realize (L := LRV) ρ t) := by
  show Structure.funMap (L := LRV) Fn.rvMap
      (fun i => Term.realize (L := LRV) ρ (![t] i)) = iRv _
  rw [show (fun i : Fin 1 => Term.realize (L := LRV) ρ (![t] i))
      = ![Term.realize (L := LRV) ρ t] from by funext i; fin_cases i; rfl]
  rfl

/-- value of the `L_val` term `a + b` -/
theorem val_realize_add (ρ : α → M) (ts : Fin 2 → LV.Term α) :
    Term.realize (L := LV) ρ (Term.func VFunc.add ts)
      = iVFAdd (Term.realize (L := LV) ρ (ts 0)) (Term.realize (L := LV) ρ (ts 1)) := by
  show Structure.funMap (L := LV) VFunc.add
      (fun i => Term.realize (L := LV) ρ (ts i)) = iVFAdd _ _
  rw [show (fun i : Fin 2 => Term.realize (L := LV) ρ (ts i))
      = ![Term.realize (L := LV) ρ (ts 0), Term.realize (L := LV) ρ (ts 1)] from by
    funext i; fin_cases i <;> rfl]
  exact funMap_add _ _

/-- value of the `L_val` term `a × b` -/
theorem val_realize_mul (ρ : α → M) (ts : Fin 2 → LV.Term α) :
    Term.realize (L := LV) ρ (Term.func VFunc.mul ts)
      = iVFMul (Term.realize (L := LV) ρ (ts 0)) (Term.realize (L := LV) ρ (ts 1)) := by
  show Structure.funMap (L := LV) VFunc.mul
      (fun i => Term.realize (L := LV) ρ (ts i)) = iVFMul _ _
  rw [show (fun i : Fin 2 => Term.realize (L := LV) ρ (ts i))
      = ![Term.realize (L := LV) ρ (ts 0), Term.realize (L := LV) ρ (ts 1)] from by
    funext i; fin_cases i <;> rfl]
  exact funMap_mul _ _

/-- value of the `L_val` term `- a` -/
theorem val_realize_neg (ρ : α → M) (ts : Fin 1 → LV.Term α) :
    Term.realize (L := LV) ρ (Term.func VFunc.neg ts)
      = iVFNeg (Term.realize (L := LV) ρ (ts 0)) := by
  show Structure.funMap (L := LV) VFunc.neg
      (fun i => Term.realize (L := LV) ρ (ts i)) = iVFNeg _
  rw [show (fun i : Fin 1 => Term.realize (L := LV) ρ (ts i))
      = ![Term.realize (L := LV) ρ (ts 0)] from by funext i; fin_cases i; rfl]
  exact funMap_neg _

/-- value of the `L_val` term `0` -/
theorem val_realize_zero (ρ : α → M) (ts : Fin 0 → LV.Term α) :
    Term.realize (L := LV) ρ (Term.func VFunc.zero ts) = iVFZero := by
  show Structure.funMap (L := LV) VFunc.zero
      (fun i : Fin 0 => Term.realize (L := LV) ρ (ts i)) = iVFZero
  rw [show (fun i : Fin 0 => Term.realize (L := LV) ρ (ts i)) = (fun i : Fin 0 => i.elim0) from by
    funext i; exact i.elim0]
  exact funMap_zero

/-- value of the `L_val` term `1` -/
theorem val_realize_one (ρ : α → M) (ts : Fin 0 → LV.Term α) :
    Term.realize (L := LV) ρ (Term.func VFunc.one ts) = iVFOne := by
  show Structure.funMap (L := LV) VFunc.one
      (fun i : Fin 0 => Term.realize (L := LV) ρ (ts i)) = iVFOne
  rw [show (fun i : Fin 0 => Term.realize (L := LV) ρ (ts i)) = (fun i : Fin 0 => i.elim0) from by
    funext i; exact i.elim0]
  exact funMap_one

/-- the `L_val` atom `v a ≤ v b`, realized -/
theorem realize_leF {n : ℕ} (ts : Fin 2 → LV.Term (α ⊕ Fin n)) (v : α → M) (x : Fin n → M) :
    (Relations.boundedFormula VRel.le ts).Realize v x ↔
      iLe (iRv (Term.realize (L := LV) (Sum.elim v x) (ts 1)))
        (iRv (Term.realize (L := LV) (Sum.elim v x) (ts 0))) := by
  show Structure.RelMap (L := LV) VRel.le
      (fun i => Term.realize (L := LV) (Sum.elim v x) (ts i)) ↔ _
  rw [show (fun i : Fin 2 => Term.realize (L := LV) (Sum.elim v x) (ts i))
      = ![Term.realize (L := LV) (Sum.elim v x) (ts 0),
          Term.realize (L := LV) (Sum.elim v x) (ts 1)] from by funext i; fin_cases i <;> rfl]
  exact Iff.of_eq (relMap_le _ _)

/-- its translated image `rv b ≤ rv a` -/
theorem realize_leR {n : ℕ} (ts : Fin 2 → LRV.Term (α ⊕ Fin n)) (v : α → M) (x : Fin n → M) :
    (Relations.boundedFormula Rel.rvLe ts).Realize v x ↔
      iLe (Term.realize (L := LRV) (Sum.elim v x) (ts 0))
        (Term.realize (L := LRV) (Sum.elim v x) (ts 1)) := by
  show Structure.RelMap (L := LRV) Rel.rvLe
      (fun i => Term.realize (L := LRV) (Sum.elim v x) (ts i)) ↔ _
  rw [show (fun i : Fin 2 => Term.realize (L := LRV) (Sum.elim v x) (ts i))
      = ![Term.realize (L := LRV) (Sum.elim v x) (ts 0),
          Term.realize (L := LRV) (Sum.elim v x) (ts 1)] from by funext i; fin_cases i <;> rfl]
  exact Iff.rfl

end RealizeGen

/-! ## 6. The translation lands in the paper's two-sorted fragment -/

/-- **Every `L_val`-term translates to a `VF`-sorted `L_RV`-term.** -/
theorem tmSort_tTm {α : Type} {n : ℕ} (t : LV.Term (α ⊕ Fin n)) :
    LRV.TmSort (fun _ : α => SortTag.vf) (fun _ : Fin n => SortTag.vf) (tTm t) = some .vf := by
  induction t with
  | var a =>
    rcases a with a | i
    · rfl
    · rfl
  | func f ts ih =>
    cases f
    · show LRV.TmSort (fun _ : α => SortTag.vf) (fun _ : Fin n => SortTag.vf)
        (Term.func Fn.vfAdd ![tTm (ts 0), tTm (ts 1)]) = some SortTag.vf
      exact (LRV.tmSort_vfAdd _ _).2 ⟨ih 0, ih 1⟩
    · show LRV.TmSort (fun _ : α => SortTag.vf) (fun _ : Fin n => SortTag.vf)
        (Term.func Fn.vfMul ![tTm (ts 0), tTm (ts 1)]) = some SortTag.vf
      exact (LRV.tmSort_vfMul _ _).2 ⟨ih 0, ih 1⟩
    · show LRV.TmSort (fun _ : α => SortTag.vf) (fun _ : Fin n => SortTag.vf)
        (Term.func Fn.vfNeg ![tTm (ts 0)]) = some SortTag.vf
      exact (LRV.tmSort_vfNeg _ _).2 (ih 0)
    · show LRV.TmSort (fun _ : α => SortTag.vf) (fun _ : Fin n => SortTag.vf)
        (Term.func Fn.vfZero fun i => i.elim0) = some SortTag.vf
      exact LRV.tmSort_vfZero _ _
    · show LRV.TmSort (fun _ : α => SortTag.vf) (fun _ : Fin n => SortTag.vf)
        (Term.func Fn.vfOne fun i => i.elim0) = some SortTag.vf
      exact LRV.tmSort_vfOne _ _

/-- `rv` of a `VF`-term is `RV`-sorted. -/
theorem tmSort_trv {α : Type} {n : ℕ} {t : LRV.Term (α ⊕ Fin n)}
    (h : LRV.TmSort (fun _ : α => SortTag.vf) (fun _ : Fin n => SortTag.vf) t = some .vf) :
    LRV.TmSort (fun _ : α => SortTag.vf) (fun _ : Fin n => SortTag.vf) (trv t) = some .rv := by
  show LRV.TmSort (fun _ : α => SortTag.vf) (fun _ : Fin n => SortTag.vf)
    (Term.func Fn.rvMap ![t]) = some SortTag.rv
  exact (LRV.tmSort_tRv _ _).2 h

/-- **The translation of a quantifier-free `L_val` formula is quantifier-free.** -/
theorem isQF_tBf {α : Type} {n : ℕ} {φ : LV.BoundedFormula α n} (h : φ.IsQF) :
    (tBf φ).IsQF := by
  induction h with
  | falsum => exact .falsum
  | of_isAtomic ha =>
    cases ha with
    | equal a b => exact .of_isAtomic (.equal (tTm a) (tTm b))
    | rel R ts =>
      cases R with
      | le => exact .of_isAtomic (BoundedFormula.IsAtomic.rel (L := LRV) Rel.rvLe _)
  | imp _ _ ih1 ih2 => exact .imp ih1 ih2

/-- **The translation of a quantifier-free `L_val` formula is well-sorted at the all-`VF`
context.** -/
theorem wellSorted_tBf {α : Type} {n : ℕ} {φ : LV.BoundedFormula α n} (h : φ.IsQF) :
    LRV.WellSorted (fun _ : α => SortTag.vf) (fun _ : Fin n => SortTag.vf) (tBf φ) := by
  induction h with
  | falsum => exact .falsum _
  | of_isAtomic ha =>
    cases ha with
    | equal a b => exact .equal _ (tmSort_tTm a) (tmSort_tTm b)
    | rel R ts =>
      cases R with
      | le => exact .rel _ Rel.rvLe _ (fun i => by
          fin_cases i
          · exact tmSort_trv (tmSort_tTm (ts 1))
          · exact tmSort_trv (tmSort_tTm (ts 0)))
  | imp _ _ ih1 ih2 => exact .imp _ ih1 ih2

/-! ## 7. The translation is semantically correct -/

/-- **Terms**: the value of the translation is the value of the `L_val`-term read through
`valStruct`. -/
theorem realize_tTm {M : Type} [LRV.Structure M] {α : Type} (ρ : α → M) (t : LV.Term α) :
    Term.realize (L := LV) ρ t = Term.realize (L := LRV) ρ (tTm t) := by
  induction t with
  | var a => rfl
  | func f ts ih =>
    cases f
    · show Term.realize (L := LV) ρ (Term.func VFunc.add ts)
          = Term.realize (L := LRV) ρ (vadd (tTm (ts 0)) (tTm (ts 1)))
      rw [val_realize_add, realize_vadd, ih 0, ih 1]
    · show Term.realize (L := LV) ρ (Term.func VFunc.mul ts)
          = Term.realize (L := LRV) ρ (vmul (tTm (ts 0)) (tTm (ts 1)))
      rw [val_realize_mul, realize_vmul, ih 0, ih 1]
    · show Term.realize (L := LV) ρ (Term.func VFunc.neg ts)
          = Term.realize (L := LRV) ρ (vneg (tTm (ts 0)))
      rw [val_realize_neg, realize_vneg, ih 0]
    · show Term.realize (L := LV) ρ (Term.func VFunc.zero ts)
          = Term.realize (L := LRV) ρ (vzero (α := α))
      rw [val_realize_zero, realize_vzero]
    · show Term.realize (L := LV) ρ (Term.func VFunc.one ts)
          = Term.realize (L := LRV) ρ (vone (α := α))
      rw [val_realize_one, realize_vone]

/-- **Formulas**: the translation preserves truth, in every `L_RV`-structure. -/
theorem realize_tBf {M : Type} [LRV.Structure M] {α : Type} :
    ∀ {n : ℕ} (φ : LV.BoundedFormula α n) (v : α → M) (x : Fin n → M),
      (tBf φ).Realize v x ↔ φ.Realize v x
  | _, .falsum, _, _ => Iff.rfl
  | _, .equal a b, v, x => by
    show ((tTm a) =' (tTm b)).Realize v x ↔ (a =' b).Realize v x
    rw [BoundedFormula.realize_bdEqual, BoundedFormula.realize_bdEqual,
      realize_tTm (Sum.elim v x) a, realize_tTm (Sum.elim v x) b]
  | _, .rel VRel.le ts, v, x => by
    show (Relations.boundedFormula Rel.rvLe ![trv (tTm (ts 1)), trv (tTm (ts 0))]).Realize v x
      ↔ (Relations.boundedFormula VRel.le ts).Realize v x
    rw [realize_leR, realize_leF]
    show iLe (Term.realize (L := LRV) (Sum.elim v x) (trv (tTm (ts 1))))
        (Term.realize (L := LRV) (Sum.elim v x) (trv (tTm (ts 0))))
      ↔ iLe (iRv (Term.realize (L := LV) (Sum.elim v x) (ts 1)))
        (iRv (Term.realize (L := LV) (Sum.elim v x) (ts 0)))
    rw [realize_trv, realize_trv, realize_tTm (Sum.elim v x) (ts 0),
      realize_tTm (Sum.elim v x) (ts 1)]
  | _, .imp a b, v, x => by
    show ((tBf a) ⟹ (tBf b)).Realize v x ↔ (a ⟹ b).Realize v x
    rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp, realize_tBf a, realize_tBf b]
  | _, .all θ, v, x => by
    show (∀' (tBf θ)).Realize v x ↔ (∀' θ).Realize v x
    rw [BoundedFormula.realize_all, BoundedFormula.realize_all]
    exact forall_congr' fun a => realize_tBf θ v (Fin.snoc x a)


/-! ## 8. `rv` is onto the `RV` sort, with `rv 0 = 0 = ∞`

The repaired `rvSurj` says `RV ∖ {rv 0} ⊆ rv(VF)`; `rvZeroEq` says `rv 0 = 0`, which is the
absorbing element `∞`.  Together: **every** `RV`-element is `rv` of a `VF`-element, with no
exception.  This is the lemma that removes the paper's exceptional value from the translation of an
`RV`-quantifier. -/

section Model

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `Axioms.rvZeroEq` read in a model: `rv 0 = 0 = ∞`. -/
theorem iRv_zero : iRv (iVFZero (M := M)) = iRVZero := by
  have hmem : Axioms.rvZeroEq ∈ Axioms.ACVF :=
    Transfer.mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])
  have h := Transfer.sentence_realize hM (φ := Axioms.rvZeroEq) hmem
  simp only [Axioms.rvZeroEq, LRV.pEq, LRV.tRVInfty, Sentence.Realize,
    Formula.Realize, BoundedFormula.realize_bdEqual, Transfer.realize_tRv,
    Transfer.realize_tVFZero, Transfer.realize_tRVZero] at h
  exact h

/-- **`rv` is onto the whole `RV` sort**: every `RV`-element is `rv` of a `VF`-element. -/
theorem rv_surj_vf {y : M} (hy : iRV y) : ∃ a : M, iVF a ∧ iRv a = y := by
  rcases Assembly.RVeqRvVF_of_model (M := M) y hy with ⟨a, haVF, ha⟩ | h0
  · exact ⟨a, haVF, ha⟩
  · exact ⟨Transfer.iVFZero, Transfer.vf_zero_mem hM, by rw [iRv_zero, h0]⟩

/-- **`∃ y ∈ RV, ψ` unfolded.** -/
theorem real_exSorted_rv {n : ℕ} (ψ : LRV.Bf (n + 1)) (x : Fin n → M) :
    (LRV.exSorted .rv ψ).Realize (default : Empty → M) x ↔
      ∃ y : M, iRV y ∧ ψ.Realize (default : Empty → M) (Fin.snoc x y) := by
  have h := BoundedFormula.realize_ex
    (θ := LRV.sortPred .rv (LRV.tv n (Nat.lt_succ_self n)) ⊓ ψ)
    (v := (default : Empty → M)) (xs := x)
  refine h.trans (exists_congr fun a => ?_)
  have h2 : (LRV.sortPred .rv (LRV.tv n (Nat.lt_succ_self n))).Realize
      (default : Empty → M) (Fin.snoc x a) ↔ iRV a := by
    rw [Assembly.real_sortPred_rv]
    have htv : Term.realize (Assembly.rho (Fin.snoc x a))
        (LRV.tv n (Nat.lt_succ_self n)) = a := by
      simp only [LRV.tv, Assembly.rho, Term.realize_var, Sum.elim_inr]
      exact Fin.snoc_last (α := fun _ => M) a x
    rw [htv]
  rw [BoundedFormula.realize_inf, h2]

/-- **The `RV` quantifier, eliminated**: `∃ y ∈ RV, ψ` is the same as `∃ x ∈ VF, ψ[rv x / y]`.
This is the "quantifier case" of route (T1); it uses `rv_surj_vf` and nothing else. -/
theorem exSorted_rv_iff_vf {n : ℕ} (ψ : LRV.Bf (n + 1)) (x : Fin n → M) :
    (LRV.exSorted .rv ψ).Realize (default : Empty → M) x ↔
      ∃ a : M, iVF a ∧ ψ.Realize (default : Empty → M) (Fin.snoc x (iRv a)) := by
  rw [real_exSorted_rv]
  constructor
  · rintro ⟨y, hy, hψ⟩
    obtain ⟨a, ha, rfl⟩ := rv_surj_vf hy
    exact ⟨a, ha, hψ⟩
  · rintro ⟨a, ha, hψ⟩
    exact ⟨iRv a, Transfer.rv_mem hM ha, hψ⟩

end Model

/-! ## 9. The two named inputs of route (T1), and the reduction

`LvalQE` is quantifier elimination for `L_val`, in the semantic form in which Johnson's criterion
at `L = Language.val` delivers it: `QE/Assembly_val.lean` proves
`QECriterion.HasQE (L := Language.val) ACVF_val`, and `VFValued`/`RVDict` identify the encoding's
`iLe ∘ iRv` with the valuation order of the `VF` sort, so an instantiation at `valStruct` (which is
`VFValued.predV` read as an `L_val`-structure) is exactly what the statement below asks for.
It is stated semantically rather than through `QECriterion.HasQE Σ` because the whole point of
route (T1) is that the two encodings cannot be imported together: what transfers is the *content*
of the `L_val` QE, not the `QECriterion` term that states it.

`RVAtomElim` is the atom layer, spelled out.  It is the exact piece of (T1) that is *not* a
syntactic translation: a well-sorted quantifier-free `L_RV` formula whose context is all-`VF` may
still contain the composite `RV`-terms `rvMul`, `kAdd`, `kNeg`, and those have no `L_val` image
term by term.  They do have one formula by formula, because the frozen `ACVF` pins all three down
completely — `kAddLink` and `kNegLink` on `K = Kˣ ∪ {0}`, `kJunkZero` and `kNegJunkZero` off it,
and `rvMulHom` on products of `rv`'s.  `RVAtomElim` is the resulting statement; the case analysis
that proves it is not carried out here (see the end of file). -/

/-- **Quantifier elimination in `L_val`**, semantically, at `VF`-tuples in models of `ACVF`.
The witness `ψ` is chosen before the model, which is what quantifier elimination delivers
(`QECriterion.HasQE Σ` gives `∃ ψ, ψ.IsQF ∧ Σ ⊨ᵇ (φ ⇔ ψ)`, so `ψ` depends on `φ` alone). -/
def LvalQE : Prop :=
  ∀ (m k : ℕ) (φ : LV.BoundedFormula (Fin m) k),
    ∃ ψ : LV.BoundedFormula (Fin m) k, ψ.IsQF ∧
      ∀ (M : Type) [LRV.Structure M], M ⊨ Axioms.ACVF →
        ∀ (v : Fin m → M) (x : Fin k → M), (∀ i, iVF (v i)) → (∀ i, iVF (x i)) →
          (φ.Realize v x ↔ ψ.Realize v x)

/-- **The atom layer of (T1).**  Every well-sorted quantifier-free-free-context `L_RV` formula with
an all-`VF` context is, at `VF`-tuples in models of `ACVF`, equivalent to the image of an
`L_val`-formula under the translation `tBf`. -/
def RVAtomElim : Prop :=
  ∀ (m k : ℕ) (φ : LRV.BoundedFormula (Fin m) k),
    LRV.WellSorted (fun _ : Fin m => SortTag.vf) (fun _ : Fin k => SortTag.vf) φ →
    ∃ ψ : LV.BoundedFormula (Fin m) k,
      ∀ (M : Type) [LRV.Structure M], M ⊨ Axioms.ACVF →
        ∀ (v : Fin m → M) (x : Fin k → M), (∀ i, iVF (v i)) → (∀ i, iVF (x i)) →
          (φ.Realize v x ↔ ψ.Realize v x)

/-- **The frozen `HasQE` at the all-`VF` context.**  This is `SpecialTransformations.Milestone0.HasQE`
instantiated at `α = Fin m`, `sα = const .vf`, `sn = const .vf` (see
`hasQEvf_of_hasQE`), i.e. exactly the case that `L_val` quantifier elimination can reach. -/
def HasQEvf (T : LRV.Theory) : Prop :=
  ∀ (m k : ℕ) (φ : LRV.BoundedFormula (Fin m) k),
    LRV.WellSorted (fun _ : Fin m => SortTag.vf) (fun _ : Fin k => SortTag.vf) φ →
    ∃ ψ : LRV.BoundedFormula (Fin m) k, ψ.IsQF ∧
      LRV.WellSorted (fun _ : Fin m => SortTag.vf) (fun _ : Fin k => SortTag.vf) ψ ∧
      ∀ (M : Type) [LRV.Structure M], M ⊨ T →
        ∀ (v : Fin m → M) (x : Fin k → M), (∀ i, iVF (v i)) → (∀ i, iVF (x i)) →
          (φ.Realize v x ↔ ψ.Realize v x)

/-- `sortEval .vf` **is** `iVF`. -/
theorem sortEval_vf {M : Type} [LRV.Structure M] {x : M} :
    sortEval SortTag.vf x = iVF x := rfl

/-- **The frozen `HasQE` implies its all-`VF` instance.** -/
theorem hasQEvf_of_hasQE {T : LRV.Theory} (h : HasQE T) : HasQEvf T := by
  intro m k φ hws
  obtain ⟨ψ, hqf, hws', he⟩ := h (Fin m) (fun _ => SortTag.vf) k (fun _ => SortTag.vf) φ hws
  exact ⟨ψ, hqf, hws', fun M _ hM v x hv hx => he M hM v x hv hx⟩

/-! ## 10. Route (T1), assembled -/

/-- **Route (T1), the composition.**  `L_val` quantifier elimination plus the atom layer gives
quantifier elimination for the frozen `L_RV` at every all-`VF` context. -/
theorem hasQEvf_of_valQE (hval : LvalQE) (hatom : RVAtomElim) : HasQEvf Axioms.ACVF := by
  intro m k φ hws
  obtain ⟨ψ₁, hψ₁⟩ := hatom m k φ hws
  obtain ⟨ψ₂, hqf₂, hψ₂⟩ := hval m k ψ₁
  refine ⟨tBf ψ₂, isQF_tBf hqf₂, wellSorted_tBf hqf₂, ?_⟩
  intro M inst hM v x hv hx
  exact (hψ₁ M hM v x hv hx).trans ((hψ₂ M hM v x hv hx).trans (realize_tBf ψ₂ v x).symm)

/-- **Route (T1) as a statement about the frozen target.**  `L_val` quantifier elimination plus the
atom layer gives `HasQE Axioms.ACVF` at every all-`VF` context of the frozen `HasQE`. -/
theorem hasQE_vf_of_valQE (hval : LvalQE) (hatom : RVAtomElim) :
    ∀ (m k : ℕ) (φ : LRV.BoundedFormula (Fin m) k),
      LRV.WellSorted (fun _ : Fin m => SortTag.vf) (fun _ : Fin k => SortTag.vf) φ →
      ∃ ψ : LRV.BoundedFormula (Fin m) k, ψ.IsQF ∧
        LRV.WellSorted (fun _ : Fin m => SortTag.vf) (fun _ : Fin k => SortTag.vf) ψ ∧
        ∀ (M : Type) [LRV.Structure M], M ⊨ Axioms.ACVF →
          ∀ (v : Fin m → M) (x : Fin k → M), (∀ i, iVF (v i)) → (∀ i, iVF (x i)) →
            (φ.Realize v x ↔ ψ.Realize v x) :=
  hasQEvf_of_valQE hval hatom

/-! ## 11. The atom layer: what is already in the tree, and what is not

`RVAtomElim` has two parts.

* **The atoms.**  Each atom of the `rv`-fragment is already a condition of `L_val` vocabulary,
  because `iLe ∘ iRv` *is* `L_val`'s predicate (`valStruct`), and the tree already contains the
  three dictionary lemmas:

  * `iRv a = iRv b` is `¬ v b ≤ v (a - b)` (`rvEqLink`, in `RVDict.rv_eq_iff_le`);
  * `iUnits (rv a)` is `v a ≤ v 1 ∧ v 1 ≤ v a` (`leClassOne`, in `RVCalc.units_iff_le_one`);
  * `rv a = 0` is `a = 0` (`rvEqInfty` + `rvZeroEq`, in `RVCalc.vf_eq_zero_of_rv_eq_zero`);
  * `rv (a b) = rv a · rv b` (`rvMulHom`, in `Transfer.rv_mul_hom_of_model`) and `rv 1 = 1`
    (`RVCalc.rv_one`), so a product of `rv`'s is again `rv` of a `VF`-term and `rvMul` is *not*
    part of the residual.

  These are restated in the `L_val`-free form below so that the statement of the residual is
  precise.
* **The terms.**  What is *not* in the tree, and what `RVAtomElim` still needs, is the recursion
  through `kAdd` and `kNeg`: `iKAdd (rv a) (rv b)` is `rv (a + b)` when `rv a`, `rv b` are units
  and `rv (a + b)` is one, is `0` when it is not, and is `0` as soon as either argument is in
  `RV ∖ K` (`kAddLink`, `kJunkZero`); `kNeg` likewise (`kNegLink`, `kNegJunkZero`).  That is a
  finite case analysis on `pInK`, carried out on term structure — it reproduces the elimination of
  the residue-field symbols rather than inventing anything. -/

section Atoms

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- **`rv a = 0` iff `a = 0`** (`rvEqInfty` plus `rvZeroEq`). -/
theorem iRv_zero_iff {a : M} (ha : iVF a) : iRv a = iRVZero ↔ a = iVFZero :=
  ⟨fun h => RVCalc.vf_eq_zero_of_rv_eq_zero hM ha h, fun h => by rw [h]; exact RVCalc.rv_zero_eq hM⟩

/-- **`Kˣ` at a `rv` is the class of `1`** (`leClassOne`); this is the `pUnits` atom. -/
theorem iUnits_iRv_iff {a : M} (ha : iVF a) (ha0 : a ≠ iVFZero) :
    iUnits (iRv a) ↔ iLe iRVOne (iRv a) ∧ iLe (iRv a) iRVOne :=
  RVCalc.units_iff_le_one hM (Transfer.rv_mem hM ha) (fun h => ha0 ((iRv_zero_iff ha).mp h))

/-- **`rv` is multiplicative** (`rvMulHom`): the `rvMul` symbol is not part of the residual. -/
theorem iRv_mul {a b : M} (ha : iVF a) (hb : iVF b) :
    iRVMul (iRv a) (iRv b) = iRv (iVFMul a b) :=
  (Transfer.rv_mul_hom_of_model hM ha hb).symm

/-- **`rv a = rv b` is `v b < v (a - b)`** (`rvEqLink`); this is the `pEq` atom. -/
theorem iRv_eq_iff {a b : M} (ha : iVF a) (hb : iVF b) (hb0 : b ≠ iVFZero) :
    (iRv a = iRv b ↔ ¬ iLe (iRv (iVFAdd a (iVFNeg b))) (iRv b)) :=
  RVDict.rv_eq_iff_le ha hb hb0

end Atoms

/-! ## 12. The `kAdd` extraction: the first half of the residual's hard case

`kAdd` is the only `RV`-symbol whose value is not pinned by an `allSorted`-guarded axiom but by
`allSortedK`-guarded ones (`Axioms.kField`, `Axioms.kAddLink`), i.e. its laws are stated only on
`K = Kˣ ∪ {0}`; off `K`, `Axioms.kJunkZero` makes it `0`.  So the case analysis that
`RVAtomElim` needs for `kAdd` runs on the predicate `pInK`.  This section ports the extraction
lemma for `allSortedK`-guarded sentences (`QE/Assembly_val.lean` has it at
`allSortedK_realize`, but that file cannot be imported here) and records the two `kField` facts
about `kAdd` that the case analysis uses.

Not proved here: the case split itself for `iKAdd (iRv a) (iRv b)`, and the same for `kNeg`. -/

section KAtoms

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- the fold inside `kHyps`, realized -/
theorem kHyps_foldr_realize {k : ℕ} (l : List (Fin k)) (v : Empty → M) (x : Fin k → M) :
    (l.foldr (fun i acc => LRV.pInK (LRV.tv i.val i.isLt) ⊓ acc) ⊤).Realize v x ↔
      ∀ i ∈ l, iUnits (x i) ∨ x i = iRVZero := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.foldr_cons, BoundedFormula.realize_inf, ih, TrivCase.pInK_realize]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases List.mem_cons.1 hi with rfl | hi'
      · simpa using h1
      · exact h2 i hi'
    · intro h
      exact ⟨by simpa using h a List.mem_cons_self,
        fun i hi => h i (List.mem_cons_of_mem a hi)⟩

/-- **`kHyps` realized**: the tuple lies in `K = Kˣ ∪ {0}`. -/
theorem kHyps_realize {k : ℕ} (v : Empty → M) (x : Fin k → M) :
    (LRV.kHyps (k := k)).Realize v x ↔ ∀ i, iUnits (x i) ∨ x i = iRVZero := by
  rw [LRV.kHyps, kHyps_foldr_realize]
  exact ⟨fun h i => h i (List.mem_finRange i), fun h i _ => h i⟩

/-- **Extraction from an `allSortedK`-guarded axiom** (the port of
`QE/Assembly_val.lean:12820`). -/
theorem allSortedK_realize {T : LRV.Theory} (hM : M ⊨ T) {k : ℕ} {ss : Fin k → SortTag}
    {φ : LRV.Bf k} (hmem : LRV.allSortedK ss φ ∈ T) (x : Fin k → M)
    (hx : ∀ i, match ss i with
      | SortTag.vf => iVF (x i)
      | SortTag.rv => iRV (x i))
    (hK : ∀ i, iUnits (x i) ∨ x i = iRVZero) :
    BoundedFormula.Realize φ (default : Empty → M) x := by
  have h := hM.realize_of_mem (LRV.allSortedK ss φ) hmem
  simp only [LRV.allSortedK, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_imp] at h
  refine h x ?_
  rw [BoundedFormula.realize_inf]
  exact ⟨(Transfer.sortedHyps_realize ss (default : Empty → M) x).mpr hx,
    (kHyps_realize (default : Empty → M) x).mpr hK⟩

theorem mem_ACVF_kField {s : LRV.Sentence} (h : s ∈ Axioms.kField) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union] at *
  tauto

/-- `Kˣ ⊆ RV` (`Axioms.sdUnits`). -/
theorem iRV_of_units {t : M} (h : iUnits t) : iRV t := by
  have hax := Transfer.allOne_realize hM (T := Axioms.ACVF) Transfer.mem_ACVF_sdUnits' ![t]
  simp only [BoundedFormula.realize_imp, Transfer.pUnits_realize,
    Transfer.pRVsort_realize] at hax
  exact hax h

/-- `K = Kˣ ∪ {0} ⊆ RV`. -/
theorem iRV_of_inK {t : M} (h : iUnits t ∨ t = iRVZero) : iRV t := by
  rcases h with h | h
  · exact iRV_of_units h
  · rw [h]; exact Transfer.rv_zero_mem hM

/-- **`t + 0 = t` for `t ∈ K`** (`Axioms.kField`). -/
theorem iKAdd_zero {t : M} (h : iUnits t ∨ t = iRVZero) : iKAdd t iRVZero = t := by
  have hmem : LRV.allSortedK ![SortTag.rv] (LRV.pEq (LRV.tKAdd (&0) LRV.tRVZero) (&0))
      ∈ Axioms.ACVF :=
    mem_ACVF_kField (by simp [Axioms.kField, Axioms.ofList])
  have hx : ∀ i : Fin 1, (match ![SortTag.rv] i with
      | SortTag.vf => iVF (![t] i)
      | SortTag.rv => iRV (![t] i)) := by
    intro i; fin_cases i; simpa using iRV_of_inK h
  have hK : ∀ i : Fin 1, iUnits (![t] i) ∨ ![t] i = iRVZero := by
    intro i; fin_cases i; simpa using h
  have hres := allSortedK_realize hM hmem ![t] hx hK
  simpa only [LRV.pEq, BoundedFormula.realize_bdEqual, TrivCase.realize_tKAdd,
    Transfer.realize_tRVZero, RVCalc.realize_var_inr, Matrix.cons_val_zero,
    Matrix.head_cons] using hres

/-- **`kAdd` is commutative on `K`** (`Axioms.kField`). -/
theorem iKAdd_comm {a b : M} (ha : iUnits a ∨ a = iRVZero) (hb : iUnits b ∨ b = iRVZero) :
    iKAdd a b = iKAdd b a := by
  have hmem : LRV.allSortedK ![SortTag.rv, SortTag.rv]
      (LRV.pEq (LRV.tKAdd (&0) (&1)) (LRV.tKAdd (&1) (&0))) ∈ Axioms.ACVF :=
    mem_ACVF_kField (by simp [Axioms.kField, Axioms.ofList])
  have hx : ∀ i : Fin 2, (match ![SortTag.rv, SortTag.rv] i with
      | SortTag.vf => iVF (![a, b] i)
      | SortTag.rv => iRV (![a, b] i)) := by
    intro i; fin_cases i
    · simpa using iRV_of_inK ha
    · simpa using iRV_of_inK hb
  have hK : ∀ i : Fin 2, iUnits (![a, b] i) ∨ ![a, b] i = iRVZero := by
    intro i; fin_cases i
    · simpa using ha
    · simpa using hb
  have hres := allSortedK_realize hM hmem ![a, b] hx hK
  simpa only [LRV.pEq, BoundedFormula.realize_bdEqual, TrivCase.realize_tKAdd,
    RVCalc.realize_var_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using hres

end KAtoms

end Jm2

/-! ## 13. Axiom audit -/

#print axioms Jm2.realize_tTm
#print axioms Jm2.realize_tBf
#print axioms Jm2.tmSort_tTm
#print axioms Jm2.isQF_tBf
#print axioms Jm2.wellSorted_tBf
#print axioms Jm2.iRv_zero
#print axioms Jm2.rv_surj_vf
#print axioms Jm2.exSorted_rv_iff_vf
#print axioms Jm2.hasQEvf_of_hasQE
#print axioms Jm2.hasQEvf_of_valQE
#print axioms Jm2.hasQE_vf_of_valQE
#print axioms Jm2.iRv_mul
#print axioms Jm2.iRv_zero_iff
#print axioms Jm2.iUnits_iRv_iff
#print axioms Jm2.iRv_eq_iff
#print axioms Jm2.kHyps_realize
#print axioms Jm2.allSortedK_realize
#print axioms Jm2.iKAdd_zero
#print axioms Jm2.iKAdd_comm
#print axioms Jm2.iRV_of_inK
