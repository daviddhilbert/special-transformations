/-
# A Hahn-series model of the frozen `ACVF` (consistency witness), part 1

**Merged judge-side from swarm `smw2ku6gn` m6** (expired without submitting).  Part 2 — the
per-axiom ledger for the algebraic groups (`rvMul` laws, `rvDivisible`, `kField`, `kAlgClosed`,
`preorderRV`, `rvAxioms`, `repairRV`) — was mid-edit at the cutoff; its original is at
`.ultramath/smw2ku6gn/m6/F2.lean` and a partially repaired copy at `.scratch2/repair/F2_wip.lean`
(4 known errors: three `pUnits`-unfolding sites and one `subst` shape).  Do not treat the sorted
axioms below as the whole consistency witness.

Direction **d3** of swarm `smw2ku6gn` (member m6): the orthogonal consistency witness.

The frozen theory `Axioms.ACVF` of `Milestone0/Encoding.lean` is
`sortAxioms ∪ vfField ∪ vfAlgClosed ∪ rvGroup ∪ kField ∪ kAlgClosed ∪ preorderRV ∪ rvAxioms
 ∪ repairRV ∪ repairRV`, and `repairRV` contains `axNontrivialRV`, so the trivial-valuation
model of `.ultramath/smw1tqlqv/m2/ACVFModel.lean` (pre-repair encoding) is **not** a model of
the frozen theory.  This file builds a model at a *nontrivial* valuation.

## The model

* `kf = ℂ` (the residue field), `VG = ℚ` (the value group), `VFT = kf⟦VG⟧` the Hahn-series
  field `ℂ((t^ℚ))` (Mathlib `RingTheory/HahnSeries/*`).
* the `RV` sort is `Option (kfˣ × VG)`: `none` is `0 = ∞ = rv 0`, and `some (a, γ)` is the
  `RV`-element with angular component `a` and value `γ`.  This is the split form
  `RV^× ≅ k^× × Γ` of the exact sequence `1 → k^× → RV^× → Γ → 1`, split by the
  angular-component map `x ↦ leadingCoeff x` of the Hahn field.
* the carrier is `VFT ⊕ RV`, with `memVF`/`memRV` the two injections.

`rv x = (leadingCoeff x, order x)` for `x ≠ 0`, `rv 0 = none`.

## The order on `RV`, pinned down

`pLe` is interpreted as **`val t ≤ val s`** where `val : RV → WithTop VG`, `val none = ⊤`
(the paper's `∞` on top, `vv(x+y) ≥ min (vv x) (vv y)`).  This is forced by the frozen
`rvUltrametric` together with `leTop`: the *other* reading (used by `Milestone0/RVModel.lean`,
where `t ≤ s ↔ vrv s ≤ vrv t` with `vrv : RV → WithZero Γ`), satisfies `leTop`/`leClassOne`
but **falsifies `rvUltrametric`** (take `x = 1 + t`, `y = -1` in `ℂ((t))`: both `rv x` and
`rv y` would have to be `≤ rv (x + y) = rv t`, i.e. `1 ≤ 0` in `WithZero ℚ`).  See
`rvUltrametric_fails_RVModel_order` below.

## Blocked group

`vfAlgClosed` (algebraic closedness of `ℂ((t^ℚ))`) is **not** available in Mathlib: there is
no Puiseux/Kaplansky theorem (`grep -rn "Puiseux" Mathlib/` is empty, and `IsAlgClosed` never
occurs in `Mathlib/RingTheory/HahnSeries/`).  It is kept as a hypothesis `[IsAlgClosed VFT]`,
which is exactly the classical quote "a Hahn field over an algebraically closed residue field
with divisible value group is algebraically closed".  Every *other* group of `ACVF` is proved
unconditionally.
-/
import Enc

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0

namespace SpecialTransformations
namespace Milestone0
namespace HahnModel

/- The frozen encoding declares `LRV : Language` with `def`, so `simp` and `rw` cannot unfold
`LRV.Relations`/`LRV.Functions` while matching (this is exactly why the pre-repair copy in
`.ultramath/smw1tqlqv/m2/ACVFModel.lean` had to change `LRV` to `abbrev`).  We do *not* touch
the frozen file: the constant is marked locally reducible here, which only affects the
elaborator's matching transparency, never the kernel. -/
set_option allowUnsafeReducibility true in
attribute [local reducible]
  LRV.tVFZero LRV.tVFOne LRV.tVFAdd LRV.tVFNeg LRV.tVFMul LRV.tRVOne LRV.tRVZero LRV.tRVInfty
  LRV.tRVMul LRV.tKAdd LRV.tKNeg LRV.tRv LRV.tv LRV.tVFNumeral LRV.tVFPow LRV.tRVPow
  LRV.pVF LRV.pRVsort LRV.pUnits LRV.pLe LRV.pEq LRV.pRV LRV.pK LRV.pRV0
  LRV.pGtOne LRV.pInK LRV.sortPred LRV.sortedHyps LRV.allSorted LRV.exSorted LRV.kHyps LRV.allSortedK
  LRV.exSortedK LRV.allOne LRV.TmSort LRV.pVFG LRV.pRVG LRV.pUnitsG LRV.pLeG LRV.pEqG
  LRV.sortPredG LRV.guardAtom LRV.Occurs LRV.GuardsLast LRV.exSortedG LRV.hornerPoly Axioms.ofList Axioms.sdCover
  Axioms.sdDisjoint Axioms.sdVFZero Axioms.sdVFOne Axioms.sdVFAdd Axioms.sdVFNeg Axioms.sdVFMul Axioms.sdRv Axioms.sdRVZero
  Axioms.sdRVInfty Axioms.sdRVOne Axioms.sdRVMul Axioms.sdUnits Axioms.sdKAdd Axioms.sdKNeg Axioms.sdKMul Axioms.sortClosure
  Axioms.sortAxioms Axioms.fieldAxioms Axioms.acfScheme Axioms.vfField Axioms.vfAlgClosed Axioms.kField Axioms.acfSchemeK Axioms.kAlgClosed
  Axioms.rvOneMem Axioms.rvMulMem Axioms.rvMulAssoc Axioms.rvMulComm Axioms.rvMulOne Axioms.rvMulInv Axioms.rvDivisible Axioms.rvMulZeroK
  Axioms.rvMulInfty Axioms.rvGroup Axioms.leRefl Axioms.leTrans Axioms.leTotal Axioms.leTop Axioms.leInftyEq Axioms.leClassOne
  Axioms.leMulCompat Axioms.preorderRV Axioms.rvZeroEq Axioms.rvEqInfty Axioms.rvMulHom Axioms.rvSurj Axioms.rvUltrametric Axioms.rvAxioms
  Axioms.rvMulOneRV Axioms.rvMulInvRV Axioms.leMulCompatFull Axioms.kAddLink Axioms.kNegLink Axioms.rvEqLink Axioms.kJunkZero Axioms.kNegJunkZero
  Axioms.axNontrivialRV Axioms.repairRV Axioms.ACVFpaper Axioms.ACVF Axioms.charZeroVF Axioms.residueCharZero Axioms.ACVF00paper Axioms.ACVF00

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Milestone0.LRV

noncomputable section

/-! ## 1. The carrier and its operations -/

/-- the residue field -/
abbrev kf : Type := ℂ
/-- the value group -/
abbrev VG : Type := ℚ
/-- the valued field `kf((t^VG))` -/
abbrev VFT : Type := HahnSeries VG kf

/-- the `RV` sort: `RV^× = k^× × Γ`, plus `0 = ∞ = rv 0` -/
abbrev RV : Type := Option (kfˣ × VG)

/-- the carrier of the model -/
abbrev Car : Type := VFT ⊕ RV

/-- an element of the `VF` sort -/
def mkVF (x : VFT) : Car := Sum.inl x
/-- an element of the `RV` sort -/
def mkRV (t : RV) : Car := Sum.inr t
/-- the paper's `0 = ∞ = rv 0`, one element -/
def cRVZero : Car := Sum.inr none
/-- the paper's `1` in the `RV` sort -/
def cRVOne : Car := Sum.inr (some ((1 : kfˣ), 0))
/-- an element of `K^×`: the class of `1`, i.e. the units of the residue field -/
def cUnitK (a : kfˣ) : Car := Sum.inr (some (a, 0))

/-- `K = K^× ∪ {0}` inside the `RV` sort -/
def inK (t : RV) : Prop := (∃ a : kfˣ, t = some (a, 0)) ∨ t = none
/-- `K^×` inside the `RV` sort -/
def isUnitRV (t : RV) : Prop := ∃ a : kfˣ, t = some (a, 0)
/-- `K = K^× ∪ {0}` on the carrier -/
def inKCar (z : Car) : Prop := (∃ a : kfˣ, z = cUnitK a) ∨ z = cRVZero
/-- `K^×` on the carrier -/
def isUnitCar (z : Car) : Prop := ∃ a : kfˣ, z = cUnitK a

/-- the valuation `vv : RV → Γ₀`, `∞ ↦ ⊤`; `vv (rv x) = order x` -/
def val : RV → WithTop VG
  | none => ⊤
  | some (_, γ) => γ

@[simp] theorem val_none : val (none : RV) = ⊤ := rfl
@[simp] theorem val_some (a : kfˣ) (γ : VG) : val (some (a, γ)) = (γ : WithTop VG) := rfl
theorem val_ne_top_iff {t : RV} : val t ≠ ⊤ ↔ ∃ a γ, t = some (a, γ) := by
  rcases t with _ | ⟨a, γ⟩
  · simp
  · exact ⟨fun _ => ⟨a, γ, rfl⟩, fun _ => by simp⟩

/-- the `RV`-multiplication: `(a,γ) * (b,δ) = (ab, γ+δ)`, `∞` absorbing -/
def rvMul : RV → RV → RV
  | some (a, γ), some (b, δ) => some (a * b, γ + δ)
  | _, _ => none

/-- read an `RV`-element as an element of the residue field `k = ℂ` (`∞` reads as `0`) -/
def toK : RV → kf
  | none => 0
  | some (a, _) => (a : kf)

/-- the residue field `k = ℂ` inside `RV`, with `0 ↦ ∞ = rv 0` -/
def fromK (x : kf) : RV := by
  classical
  exact if h : x = 0 then none else some (Units.mk0 x h, 0)

/-- the `RV`-addition of the residue field; junk (`∞`) off `K` -/
def kAdd (t s : RV) : RV := by
  classical
  exact if inK t ∧ inK s then fromK (toK t + toK s) else none

/-- the `RV`-negation of the residue field; junk (`∞`) off `K` -/
def kNeg (t : RV) : RV := by
  classical
  exact if inK t then fromK (-(toK t)) else none

/-- `rv : VF → RV` -/
def rvMap (x : VFT) : RV := by
  classical
  exact if h : x = 0 then none
    else some (Units.mk0 x.leadingCoeff (HahnSeries.leadingCoeff_ne_zero.mpr h), x.order)

/-- the `RV`-element of a nonzero Hahn series: angular component and value -/
theorem rvMap_of_ne {x : VFT} (h : x ≠ 0) :
    rvMap x = some (Units.mk0 x.leadingCoeff (HahnSeries.leadingCoeff_ne_zero.mpr h), x.order) := by
  simp only [rvMap]
  split_ifs with hx
  · exact absurd hx h
  · rfl

theorem rvMap_zero : rvMap 0 = none := by
  simp only [rvMap]
  split_ifs with h
  · rfl
  · exact absurd trivial h

/-! ## 2. The `L_RV`-structure on `VFT ⊕ RV` -/

/-- the interpretation of the twelve function symbols.  The two partial symbols of the
residue field (`kAdd`, `kNeg`) and the `VF`-operations take the junk value `∞` off their
intended domain. -/
def fMap : {n : ℕ} → Fn n → (Fin n → Car) → Car
  | _, .vfZero, _ => mkVF 0
  | _, .vfOne, _ => mkVF 1
  | _, .vfAdd, xs => match xs 0, xs 1 with
      | Sum.inl a, Sum.inl b => mkVF (a + b)
      | _, _ => cRVZero
  | _, .vfNeg, xs => match xs 0 with
      | Sum.inl a => mkVF (-a)
      | _ => cRVZero
  | _, .vfMul, xs => match xs 0, xs 1 with
      | Sum.inl a, Sum.inl b => mkVF (a * b)
      | _, _ => cRVZero
  | _, .rvOne, _ => cRVOne
  | _, .rvZero, _ => cRVZero
  | _, .rvMul, xs => match xs 0, xs 1 with
      | Sum.inr t, Sum.inr s => mkRV (rvMul t s)
      | _, _ => cRVZero
  | _, .kAdd, xs => match xs 0, xs 1 with
      | Sum.inr t, Sum.inr s => mkRV (kAdd t s)
      | _, _ => cRVZero
  | _, .kNeg, xs => match xs 0 with
      | Sum.inr t => mkRV (kNeg t)
      | _ => cRVZero
  | _, .rvMap, xs => match xs 0 with
      | Sum.inl a => mkRV (rvMap a)
      | _ => cRVZero

/-- the valuation of the carrier: junk (`⊤`) off the `RV` sort -/
def valCar (z : Car) : WithTop VG :=
  match z with
  | Sum.inl _ => ⊤
  | Sum.inr t => val t

/-- the interpretation of the four relation symbols.  `≤` is `val t ≤ val s`: the paper's
order with `∞` on top and `K^×` the class of `1`. -/
def rMap : {n : ℕ} → Rel n → (Fin n → Car) → Prop
  | _, .memVF, xs => ∃ x : VFT, xs 0 = mkVF x
  | _, .memRV, xs => ∃ t : RV, xs 0 = mkRV t
  | _, .memUnits, xs => ∃ a : kfˣ, xs 0 = cUnitK a
  | _, .rvLe, xs => valCar (xs 0) ≤ valCar (xs 1)

/-- **the `L_RV`-structure on `VFT ⊕ RV`** -/
instance instStructure : LRV.Structure Car where
  funMap := fMap
  RelMap := rMap

/-! ## 3. Unfolding toolkit -/

/-- the (unique) empty assignment -/
abbrev dflt : Empty → Car := fun e => e.elim

@[simp] theorem RelMap_def {n : ℕ} (r : Rel n) (xs : Fin n → Car) :
    (Structure.RelMap (L := LRV) (M := Car) r xs) = rMap r xs := rfl

@[simp] theorem funMap_def {n : ℕ} (f : Fn n) (xs : Fin n → Car) :
    (Structure.funMap (L := LRV) (M := Car) f xs) = fMap f xs := rfl

/-- `M ⊨ φ.alls` unfolds to the universally quantified bounded formula -/
theorem model_alls {k : ℕ} (φ : LRV.BoundedFormula Empty k) :
    (Car ⊨ φ.alls) ↔ ∀ xs : Fin k → Car, φ.Realize (dflt) xs := by
  rw [Sentence.Realize, BoundedFormula.realize_alls]
  refine forall_congr' (fun xs => ?_)
  exact iff_of_eq (congrArg (fun w => φ.Realize w xs) (Subsingleton.elim _ _))

/-- realization of the variable `&i` -/
theorem realize_bd {k : ℕ} (i : Fin k) (xs : Fin k → Car) :
    Term.realize (Sum.elim dflt xs) (((Term.var ∘ Sum.inr) i : LRV.Tm k)) = xs i := by
  simp only [Function.comp_apply, Term.realize_var, Sum.elim_inr, Fin.eta]

/-- the `VF` sort predicate at a variable -/
theorem realize_pVF {n : ℕ} (i : Fin n) (xs : Fin n → Car) :
    (LRV.pVF (((Term.var ∘ Sum.inr) i : LRV.Tm n))).Realize (dflt) xs ↔
      ∃ x : VFT, xs i = mkVF x := by
  simp only [LRV.pVF, BoundedFormula.realize_rel₁, RelMap_def, rMap, Matrix.cons_val_fin_one,
    realize_bd]

/-- the `RV` sort predicate at a variable -/
theorem realize_pRVsort {n : ℕ} (i : Fin n) (xs : Fin n → Car) :
    (LRV.pRVsort (((Term.var ∘ Sum.inr) i : LRV.Tm n))).Realize (dflt) xs ↔
      ∃ t : RV, xs i = mkRV t := by
  simp only [LRV.pRVsort, BoundedFormula.realize_rel₁, RelMap_def, rMap, Matrix.cons_val_fin_one,
    realize_bd]

/-- `K^×` at a variable -/
theorem realize_pUnits {n : ℕ} (i : Fin n) (xs : Fin n → Car) :
    (LRV.pUnits (((Term.var ∘ Sum.inr) i : LRV.Tm n))).Realize (dflt) xs ↔
      ∃ a : kfˣ, xs i = cUnitK a := by
  simp only [LRV.pUnits, BoundedFormula.realize_rel₁, RelMap_def, rMap, Matrix.cons_val_fin_one,
    realize_bd]

/-- `K = K^× ∪ {0}` at a variable -/
theorem realize_pInK {n : ℕ} (i : Fin n) (xs : Fin n → Car) :
    (LRV.pInK (((Term.var ∘ Sum.inr) i : LRV.Tm n))).Realize (dflt) xs ↔ inKCar (xs i) := by
  simp only [LRV.pInK, BoundedFormula.realize_sup, LRV.pUnits, LRV.pEq, LRV.tRVZero,
    BoundedFormula.realize_rel₁, BoundedFormula.realize_bdEqual, RelMap_def, rMap,
    Term.realize_func, funMap_def, fMap, Matrix.empty_eq, Matrix.cons_val_fin_one,
    realize_bd, inKCar, inK, cUnitK, cRVZero]

/-- `pVF` at the `LRV.tv`-spelled variable (the form used by `sortedHyps`) -/
theorem realize_pVF_term {n : ℕ} (i : Fin n) (xs : Fin n → Car) :
    (LRV.pVF (LRV.tv i.val i.isLt)).Realize (dflt) xs ↔ ∃ x : VFT, xs i = mkVF x := by
  simp only [LRV.tv, Function.comp_apply]
  exact realize_pVF i xs

/-- `pRVsort` at the `LRV.tv`-spelled variable -/
theorem realize_pRVsort_term {n : ℕ} (i : Fin n) (xs : Fin n → Car) :
    (LRV.pRVsort (LRV.tv i.val i.isLt)).Realize (dflt) xs ↔ ∃ t : RV, xs i = mkRV t := by
  simp only [LRV.tv, Function.comp_apply]
  exact realize_pRVsort i xs

/-- `pInK` at the `LRV.tv`-spelled variable (the form used by `kHyps`) -/
theorem realize_pInK_term {n : ℕ} (i : Fin n) (xs : Fin n → Car) :
    (LRV.pInK (LRV.tv i.val i.isLt)).Realize (dflt) xs ↔ inKCar (xs i) := by
  simp only [LRV.tv, Function.comp_apply]
  exact realize_pInK i xs

/-- `VF` sort predicate at a term -/
theorem realize_pVFT {n : ℕ} (A : LRV.Tm n) (xs : Fin n → Car) :
    (LRV.pVF A).Realize (dflt) xs ↔ ∃ x : VFT, Term.realize (Sum.elim dflt xs) A = mkVF x := by
  simp only [LRV.pVF, BoundedFormula.realize_rel₁, RelMap_def, rMap, Matrix.cons_val_fin_one]

/-- `RV` sort predicate at a term -/
theorem realize_pRVsortT {n : ℕ} (A : LRV.Tm n) (xs : Fin n → Car) :
    (LRV.pRVsort A).Realize (dflt) xs ↔ ∃ t : RV, Term.realize (Sum.elim dflt xs) A = mkRV t := by
  simp only [LRV.pRVsort, BoundedFormula.realize_rel₁, RelMap_def, rMap, Matrix.cons_val_fin_one]

/-- `RV ∖ {0}` at a term -/
theorem realize_pRVT {n : ℕ} (A : LRV.Tm n) (xs : Fin n → Car) :
    (LRV.pRV A).Realize (dflt) xs ↔ Term.realize (Sum.elim dflt xs) A ≠ cRVZero := by
  simp only [LRV.pRV, BoundedFormula.realize_not, LRV.pEq, BoundedFormula.realize_bdEqual,
    LRV.tRVZero, Term.realize_func, funMap_def, fMap]

/-- `K = K^× ∪ {0}` at a term -/
theorem realize_pInKT {n : ℕ} (A : LRV.Tm n) (xs : Fin n → Car) :
    (LRV.pInK A).Realize (dflt) xs ↔ inKCar (Term.realize (Sum.elim dflt xs) A) := by
  simp only [LRV.pInK, BoundedFormula.realize_sup, LRV.pUnits, LRV.pEq, LRV.tRVZero,
    BoundedFormula.realize_rel₁, BoundedFormula.realize_bdEqual, RelMap_def, rMap,
    Term.realize_func, funMap_def, fMap, Matrix.empty_eq, Matrix.cons_val_fin_one,
    inKCar, inK, cUnitK, cRVZero]

/-- `≤` at arbitrary terms -/
theorem realize_pLeT {n : ℕ} (A B : LRV.Tm n) (xs : Fin n → Car) :
    (LRV.pLe A B).Realize (dflt) xs ↔
      valCar (Term.realize (Sum.elim dflt xs) A) ≤ valCar (Term.realize (Sum.elim dflt xs) B) := by
  simp only [LRV.pLe, BoundedFormula.realize_rel₂, RelMap_def, rMap, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- `=` at arbitrary terms -/
theorem realize_pEqT {n : ℕ} (A B : LRV.Tm n) (xs : Fin n → Car) :
    (LRV.pEq A B).Realize (dflt) xs ↔
      Term.realize (Sum.elim dflt xs) A = Term.realize (Sum.elim dflt xs) B := by
  simp only [LRV.pEq, BoundedFormula.realize_bdEqual]

/-- realization of `tVFAdd` at two variables -/
theorem realize_tVFAdd_v {n : ℕ} (xs : Fin n → Car) {i j : Fin n} {a b : VFT}
    (ha : xs i = mkVF a) (hb : xs j = mkVF b) :
    Term.realize (Sum.elim dflt xs)
      (LRV.tVFAdd ((Term.var ∘ Sum.inr) i) ((Term.var ∘ Sum.inr) j)) = mkVF (a + b) := by
  rw [LRV.tVFAdd, Term.realize_func, funMap_def]
  simp only [fMap, Matrix.cons_val_zero, Matrix.cons_val_one, realize_bd, ha, hb, mkVF]

/-- realization of `tVFNeg` at a variable -/
theorem realize_tVFNeg_v {n : ℕ} (xs : Fin n → Car) {i : Fin n} {a : VFT}
    (ha : xs i = mkVF a) :
    Term.realize (Sum.elim dflt xs) (LRV.tVFNeg ((Term.var ∘ Sum.inr) i)) = mkVF (-a) := by
  rw [LRV.tVFNeg, Term.realize_func, funMap_def]
  simp only [fMap, Matrix.cons_val_zero, realize_bd, ha, mkVF]

/-- realization of `tVFMul` at two variables -/
theorem realize_tVFMul_v {n : ℕ} (xs : Fin n → Car) {i j : Fin n} {a b : VFT}
    (ha : xs i = mkVF a) (hb : xs j = mkVF b) :
    Term.realize (Sum.elim dflt xs)
      (LRV.tVFMul ((Term.var ∘ Sum.inr) i) ((Term.var ∘ Sum.inr) j)) = mkVF (a * b) := by
  rw [LRV.tVFMul, Term.realize_func, funMap_def]
  simp only [fMap, Matrix.cons_val_zero, Matrix.cons_val_one, realize_bd, ha, hb, mkVF]

/-- realization of `tRVMul` at two variables -/
theorem realize_tRVMul_v {n : ℕ} (xs : Fin n → Car) {i j : Fin n} {t s : RV}
    (ht : xs i = mkRV t) (hs : xs j = mkRV s) :
    Term.realize (Sum.elim dflt xs)
      (LRV.tRVMul ((Term.var ∘ Sum.inr) i) ((Term.var ∘ Sum.inr) j)) = mkRV (rvMul t s) := by
  rw [LRV.tRVMul, Term.realize_func, funMap_def]
  simp only [fMap, Matrix.cons_val_zero, Matrix.cons_val_one, realize_bd, ht, hs, mkRV]

/-- realization of `tKAdd` at two variables -/
theorem realize_tKAdd_v {n : ℕ} (xs : Fin n → Car) {i j : Fin n} {t s : RV}
    (ht : xs i = mkRV t) (hs : xs j = mkRV s) :
    Term.realize (Sum.elim dflt xs)
      (LRV.tKAdd ((Term.var ∘ Sum.inr) i) ((Term.var ∘ Sum.inr) j)) = mkRV (kAdd t s) := by
  rw [LRV.tKAdd, Term.realize_func, funMap_def]
  simp only [fMap, Matrix.cons_val_zero, Matrix.cons_val_one, realize_bd, ht, hs, mkRV]

/-- realization of `tKNeg` at a variable -/
theorem realize_tKNeg_v {n : ℕ} (xs : Fin n → Car) {i : Fin n} {t : RV}
    (ht : xs i = mkRV t) :
    Term.realize (Sum.elim dflt xs) (LRV.tKNeg ((Term.var ∘ Sum.inr) i)) = mkRV (kNeg t) := by
  rw [LRV.tKNeg, Term.realize_func, funMap_def]
  simp only [fMap, Matrix.cons_val_zero, realize_bd, ht, mkRV]

/-- realization of `tRv` at a variable -/
theorem realize_tRv_v {n : ℕ} (xs : Fin n → Car) {i : Fin n} {x : VFT}
    (hx : xs i = mkVF x) :
    Term.realize (Sum.elim dflt xs) (LRV.tRv ((Term.var ∘ Sum.inr) i)) = mkRV (rvMap x) := by
  rw [LRV.tRv, Term.realize_func, funMap_def]
  simp only [fMap, Matrix.cons_val_zero, realize_bd, hx, mkVF, mkRV]

/-- realization of `tVFAdd &0 (tVFNeg &1)` -/
theorem realize_tVFAdd_neg_v {n : ℕ} (xs : Fin n → Car) {i j : Fin n} {a b : VFT}
    (ha : xs i = mkVF a) (hb : xs j = mkVF b) :
    Term.realize (Sum.elim dflt xs)
      (LRV.tVFAdd ((Term.var ∘ Sum.inr) i) (LRV.tVFNeg ((Term.var ∘ Sum.inr) j))) =
        mkVF (a - b) := by
  rw [LRV.tVFAdd, Term.realize_func, funMap_def]
  simp only [fMap, Matrix.cons_val_zero, Matrix.cons_val_one, realize_bd, ha,
    realize_tVFNeg_v _ hb, mkVF]
  rfl

/-- realization of the constants of the encoding -/
@[simp] theorem realize_tRVZero (v : Empty ⊕ Fin n → Car) :
    Term.realize v LRV.tRVZero = cRVZero := rfl
@[simp] theorem realize_tVFZero (v : Empty ⊕ Fin n → Car) :
    Term.realize v LRV.tVFZero = mkVF 0 := rfl
@[simp] theorem realize_tVFOne (v : Empty ⊕ Fin n → Car) :
    Term.realize v LRV.tVFOne = mkVF 1 := rfl
@[simp] theorem realize_tRVOne (v : Empty ⊕ Fin n → Car) :
    Term.realize v LRV.tRVOne = cRVOne := rfl

/-- realizing a `foldr` of conjunctions -/
theorem realize_foldr_inf {ι : Type*} {n : ℕ} (l : List ι)
    (f : ι → LRV.BoundedFormula Empty n) (xs : Fin n → Car) :
    (l.foldr (fun i acc => f i ⊓ acc) ⊤).Realize (dflt) xs ↔ ∀ i ∈ l, (f i).Realize (dflt) xs := by
  induction l with
  | nil => simp [BoundedFormula.realize_top]
  | cons a l ih =>
    simp only [List.foldr_cons, BoundedFormula.realize_inf, ih, List.mem_cons]
    exact ⟨fun ⟨h1, h2⟩ i hi => hi.elim (fun e => e ▸ h1) (h2 i),
      fun h => ⟨h a (Or.inl rfl), fun i hi => h i (Or.inr hi)⟩⟩

theorem realize_sortedHyps {k : ℕ} (ss : Fin k → SortTag) (xs : Fin k → Car) :
    (LRV.sortedHyps ss).Realize (dflt) xs ↔
      ∀ i : Fin k, ((ss i = .vf → ∃ x : VFT, xs i = mkVF x) ∧
        (ss i = .rv → ∃ t : RV, xs i = mkRV t)) := by
  rw [LRV.sortedHyps, realize_foldr_inf]
  constructor
  · intro h i
    have hi := h i (List.mem_finRange i)
    cases hss : ss i with
    | vf =>
      rw [hss] at hi
      rw [LRV.sortPred, realize_pVF_term] at hi
      exact ⟨fun _ => hi, fun hh => by simp at hh⟩
    | rv =>
      rw [hss] at hi
      rw [LRV.sortPred, realize_pRVsort_term] at hi
      exact ⟨fun hh => by simp at hh, fun _ => hi⟩
  · intro h φ _
    rcases h φ with ⟨hvf, hrv⟩
    cases hss : ss φ with
    | vf => rw [LRV.sortPred, realize_pVF_term]; exact hvf hss
    | rv => rw [LRV.sortPred, realize_pRVsort_term]; exact hrv hss

/-- the guarded universal sentence, unfolded -/
theorem model_allSorted {k : ℕ} (ss : Fin k → SortTag) (φ : LRV.BoundedFormula Empty k) :
    (Car ⊨ LRV.allSorted ss φ) ↔
      ∀ xs : Fin k → Car, (∀ i : Fin k, ((ss i = .vf → ∃ x : VFT, xs i = mkVF x) ∧
        (ss i = .rv → ∃ t : RV, xs i = mkRV t))) → φ.Realize (dflt) xs := by
  rw [LRV.allSorted, model_alls]
  refine forall_congr' (fun xs => ?_)
  rw [BoundedFormula.realize_imp]
  exact ⟨fun h hg => h ((realize_sortedHyps ss xs).mpr hg),
    fun h hg => h ((realize_sortedHyps ss xs).mp hg)⟩

/-- `K`-guarded hypotheses -/
theorem realize_kHyps {k : ℕ} (xs : Fin k → Car) :
    (LRV.kHyps (k := k)).Realize (dflt) xs ↔ ∀ i : Fin k, inKCar (xs i) := by
  have hdef : LRV.kHyps (k := k) =
      (List.finRange k).foldr (fun i acc => LRV.pInK (LRV.tv i.val i.isLt) ⊓ acc) ⊤ := rfl
  rw [hdef, realize_foldr_inf]
  exact ⟨fun h i => (realize_pInK_term i xs).mp (h i (List.mem_finRange i)),
    fun h i _ => (realize_pInK_term i xs).mpr (h i)⟩

/-- the `K`-guarded universal sentence, unfolded -/
theorem model_allSortedK {k : ℕ} (ss : Fin k → SortTag) (φ : LRV.BoundedFormula Empty k) :
    (Car ⊨ LRV.allSortedK ss φ) ↔
      ∀ xs : Fin k → Car, (∀ i : Fin k, ((ss i = .vf → ∃ x : VFT, xs i = mkVF x) ∧
        (ss i = .rv → ∃ t : RV, xs i = mkRV t))) →
        (∀ i : Fin k, inKCar (xs i)) → φ.Realize (dflt) xs := by
  rw [LRV.allSortedK, model_alls]
  refine forall_congr' (fun xs => ?_)
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  constructor
  · intro h hg hk
    exact h ⟨(realize_sortedHyps ss xs).mpr hg, (realize_kHyps xs).mpr hk⟩
  · intro h hh
    exact h ((realize_sortedHyps ss xs).mp hh.1) ((realize_kHyps xs).mp hh.2)

macro "prep" : tactic => `(tactic|
  (simp only [FirstOrder.Language.BoundedFormula.realize_rel₁,
    FirstOrder.Language.BoundedFormula.realize_rel₂,
    FirstOrder.Language.BoundedFormula.realize_imp,
    FirstOrder.Language.BoundedFormula.realize_inf,
    FirstOrder.Language.BoundedFormula.realize_sup,
    FirstOrder.Language.BoundedFormula.realize_not,
    FirstOrder.Language.BoundedFormula.realize_bdEqual,
    FirstOrder.Language.BoundedFormula.realize_top,
    FirstOrder.Language.BoundedFormula.realize_bot,
    FirstOrder.Language.BoundedFormula.realize_iff,
    FirstOrder.Language.BoundedFormula.realize_all,
    FirstOrder.Language.BoundedFormula.realize_ex,
    FirstOrder.Language.BoundedFormula.realize_exs,
    FirstOrder.Language.BoundedFormula.realize_alls,
    FirstOrder.Language.Term.realize_func, FirstOrder.Language.Term.realize_var,
    Function.comp_apply,
    LRV.allOne, LRV.sortedHyps, LRV.kHyps, LRV.sortPred, LRV.tv, LRV.exSorted,
    LRV.exSortedK, LRV.allSortedK, LRV.allSorted,
    LRV.pVF, LRV.pRVsort, LRV.pUnits, LRV.pLe, LRV.pEq, LRV.pRV, LRV.pInK, LRV.pK,
    LRV.pGtOne, LRV.tVFZero, LRV.tVFOne, LRV.tVFAdd, LRV.tVFNeg, LRV.tVFMul,
    LRV.tRVOne, LRV.tRVZero, LRV.tRVInfty, LRV.tRVMul, LRV.tKAdd, LRV.tKNeg, LRV.tRv,
    RelMap_def, funMap_def, rMap, fMap, mkVF, mkRV, cRVZero, cRVOne, cUnitK, valCar,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.empty_eq, Fin.snoc_zero, Fin.snoc_castSucc,
    Fin.snoc_last, Fin.forall_fin_one, Fin.forall_fin_two, Fin.forall_fin_zero, Fin.ext_iff,
    Fin.zero_eta, Sum.elim_inl, Sum.elim_inr,
    FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize]))

/-! ## 4. Shape lemmas for the carrier -/

@[simp] theorem mkVF_eq_mkVF {x y : VFT} : mkVF x = mkVF y ↔ x = y :=
  ⟨fun h => Sum.inl.inj h, fun h => by rw [h]⟩

theorem mkVF_ne_mkRV (x : VFT) (t : RV) : mkVF x ≠ mkRV t := by simp [mkVF, mkRV]
theorem mkRV_ne_mkVF (t : RV) (x : VFT) : mkRV t ≠ mkVF x := by simp [mkVF, mkRV]
theorem mkRV_inj {t s : RV} : mkRV t = mkRV s ↔ t = s := ⟨fun h => Sum.inr.inj h, fun h => by rw [h]⟩

@[simp] theorem inK_none : inK (none : RV) := Or.inr rfl
@[simp] theorem inK_some_zero (a : kfˣ) : inK (some (a, 0)) := Or.inl ⟨a, rfl⟩
@[simp] theorem inKCar_mkRV {t : RV} : inKCar (mkRV t) ↔ inK t := by
  simp [inKCar, mkRV, inK, cUnitK, cRVZero]

/-- the residue field inside `RV` is in `K = K^× ∪ {0}` -/
theorem inK_fromK (x : kf) : inK (fromK x) := by
  rw [fromK]
  split_ifs with h
  · exact Or.inr rfl
  · exact Or.inl ⟨_, rfl⟩

/-- `kAdd` of two elements of `K = K^× ∪ {0}` stays in `K` -/
theorem inK_kAdd {t s : RV} (ht : inK t) (hs : inK s) : inK (kAdd t s) := by
  rw [kAdd, if_pos ⟨ht, hs⟩]
  exact inK_fromK _

/-- `rvMul` of two elements of `K = K^× ∪ {0}` stays in `K` -/
theorem inK_rvMul {t s : RV} (ht : inK t) (hs : inK s) : inK (rvMul t s) := by
  rcases ht with ⟨a, rfl⟩ | rfl <;> rcases hs with ⟨b, rfl⟩ | rfl <;>
    simp [inK, rvMul, cUnitK, cRVZero]

/-- `kNeg` of an element of `K` stays in `K` -/
theorem inK_kNeg {t : RV} (ht : inK t) : inK (kNeg t) := by
  rw [kNeg, if_pos ht]
  exact inK_fromK _

/-! ## 5. The sort discipline: `Axioms.sortClosure`, `sdCover`, `sdDisjoint` -/

theorem model_sdVFZero : (Car ⊨ Axioms.sdVFZero) := by
  simp only [Axioms.sdVFZero]; prep
  exact ⟨0, rfl⟩

theorem model_sdVFOne : (Car ⊨ Axioms.sdVFOne) := by
  simp only [Axioms.sdVFOne]; prep
  exact ⟨1, rfl⟩

theorem model_sdVFAdd : (Car ⊨ Axioms.sdVFAdd) := by
  simp only [Axioms.sdVFAdd]
  rw [model_allSorted]; intro xs h
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  obtain ⟨b, hb⟩ := (h 1).1 rfl
  rw [realize_pVFT, realize_tVFAdd_v xs ha hb]
  exact ⟨a + b, rfl⟩

theorem model_sdVFNeg : (Car ⊨ Axioms.sdVFNeg) := by
  simp only [Axioms.sdVFNeg]
  rw [model_allSorted]; intro xs h
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  rw [realize_pVFT, realize_tVFNeg_v xs ha]
  exact ⟨-a, rfl⟩

theorem model_sdVFMul : (Car ⊨ Axioms.sdVFMul) := by
  simp only [Axioms.sdVFMul]
  rw [model_allSorted]; intro xs h
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  obtain ⟨b, hb⟩ := (h 1).1 rfl
  rw [realize_pVFT, realize_tVFMul_v xs ha hb]
  exact ⟨a * b, rfl⟩

theorem model_sdRv : (Car ⊨ Axioms.sdRv) := by
  simp only [Axioms.sdRv]
  rw [model_allSorted]; intro xs h
  obtain ⟨a, ha⟩ := (h 0).1 rfl
  rw [realize_pRVsortT, realize_tRv_v xs ha]
  exact ⟨rvMap a, rfl⟩

theorem model_sdRVZero : (Car ⊨ Axioms.sdRVZero) := by
  simp only [Axioms.sdRVZero]; prep
  exact ⟨none, rfl⟩

theorem model_sdRVOne : (Car ⊨ Axioms.sdRVOne) := by
  simp only [Axioms.sdRVOne]; prep
  exact ⟨some ((1 : kfˣ), 0), rfl⟩

theorem model_sdRVInfty : (Car ⊨ Axioms.sdRVInfty) := by
  simp only [Axioms.sdRVInfty]; prep
  exact ⟨none, rfl⟩

theorem model_sdRVMul : (Car ⊨ Axioms.sdRVMul) := by
  simp only [Axioms.sdRVMul]
  rw [model_allSorted]; intro xs h
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  rw [realize_pRVsortT, realize_tRVMul_v xs ht hs]
  exact ⟨rvMul t s, rfl⟩

theorem model_sdUnits : (Car ⊨ Axioms.sdUnits) := by
  simp only [Axioms.sdUnits]
  rw [model_alls]
  intro xs
  rw [BoundedFormula.realize_imp, realize_pUnits, realize_pRVsort]
  rintro ⟨a, ha⟩
  exact ⟨some (a, 0), by rw [ha]; rfl⟩

theorem model_sdCover : (Car ⊨ Axioms.sdCover) := by
  simp only [Axioms.sdCover]
  rw [model_alls]
  intro xs
  rw [BoundedFormula.realize_sup, realize_pVF, realize_pRVsort]
  match hz : xs 0 with
  | Sum.inl x => exact Or.inl ⟨x, rfl⟩
  | Sum.inr t => exact Or.inr ⟨t, rfl⟩

theorem model_sdDisjoint : (Car ⊨ Axioms.sdDisjoint) := by
  simp only [Axioms.sdDisjoint]
  rw [model_alls]
  intro xs
  rw [BoundedFormula.realize_not, BoundedFormula.realize_inf, realize_pVF, realize_pRVsort]
  rintro ⟨⟨x, hx⟩, t, ht⟩
  rw [hx] at ht
  exact mkVF_ne_mkRV x t ht

theorem model_sdKAdd : (Car ⊨ Axioms.sdKAdd) := by
  simp only [Axioms.sdKAdd]
  rw [model_allSorted]; intro xs h
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp, realize_pInK, realize_pInK]
  rw [show (LRV.pInK (LRV.tKAdd ((Term.var ∘ Sum.inr) (0 : Fin 2))
      ((Term.var ∘ Sum.inr) (1 : Fin 2)))).Realize (dflt) xs ↔
      inKCar (Term.realize (Sum.elim dflt xs)
        (LRV.tKAdd ((Term.var ∘ Sum.inr) (0 : Fin 2))
          ((Term.var ∘ Sum.inr) (1 : Fin 2)))) from realize_pInKT _ _]
  rw [realize_tKAdd_v xs ht hs]
  intro h0 h1
  rw [ht] at h0
  rw [hs] at h1
  rw [inKCar_mkRV] at h0 h1 ⊢
  exact inK_kAdd h0 h1

theorem model_sdKNeg : (Car ⊨ Axioms.sdKNeg) := by
  simp only [Axioms.sdKNeg]
  rw [model_allSorted]; intro xs h
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  rw [BoundedFormula.realize_imp, realize_pInK]
  rw [show (LRV.pInK (LRV.tKNeg ((Term.var ∘ Sum.inr) (0 : Fin 1)))).Realize (dflt) xs ↔
      inKCar (Term.realize (Sum.elim dflt xs)
        (LRV.tKNeg ((Term.var ∘ Sum.inr) (0 : Fin 1)))) from realize_pInKT _ _]
  rw [realize_tKNeg_v xs ht]
  intro h0
  rw [ht] at h0
  rw [inKCar_mkRV] at h0 ⊢
  exact inK_kNeg h0

theorem model_sdKMul : (Car ⊨ Axioms.sdKMul) := by
  simp only [Axioms.sdKMul]
  rw [model_allSorted]; intro xs h
  obtain ⟨t, ht⟩ := (h 0).2 rfl
  obtain ⟨s, hs⟩ := (h 1).2 rfl
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp, realize_pInK, realize_pInK]
  rw [show (LRV.pInK (LRV.tRVMul ((Term.var ∘ Sum.inr) (0 : Fin 2))
      ((Term.var ∘ Sum.inr) (1 : Fin 2)))).Realize (dflt) xs ↔
      inKCar (Term.realize (Sum.elim dflt xs)
        (LRV.tRVMul ((Term.var ∘ Sum.inr) (0 : Fin 2))
          ((Term.var ∘ Sum.inr) (1 : Fin 2)))) from realize_pInKT _ _]
  rw [realize_tRVMul_v xs ht hs]
  intro h0 h1
  rw [ht] at h0
  rw [hs] at h1
  rw [inKCar_mkRV] at h0 h1 ⊢
  exact inK_rvMul h0 h1

theorem model_sortClosure : (Car ⊨ Axioms.sortClosure) := by
  rw [Axioms.sortClosure, Theory.model_iff]
  intro s hs
  simp only [Axioms.ofList, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact model_sdVFZero
  · exact model_sdVFOne
  · exact model_sdVFAdd
  · exact model_sdVFNeg
  · exact model_sdVFMul
  · exact model_sdRv
  · exact model_sdRVZero
  · exact model_sdRVInfty
  · exact model_sdRVOne
  · exact model_sdRVMul
  · exact model_sdUnits
  · exact model_sdKAdd
  · exact model_sdKNeg
  · exact model_sdKMul

theorem model_sortAxioms : (Car ⊨ Axioms.sortAxioms) := by
  rw [Axioms.sortAxioms, Theory.model_union_iff]
  refine ⟨model_sortClosure, ?_⟩
  rw [Theory.model_iff]
  intro s hs
  simp only [Axioms.ofList, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_singleton] at hs
  rcases hs with rfl | rfl
  · exact model_sdCover
  · exact model_sdDisjoint

end

end HahnModel
end Milestone0
end SpecialTransformations
