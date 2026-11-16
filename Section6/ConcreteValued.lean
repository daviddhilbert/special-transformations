module

public import Section6.ConcreteRV
public import Section6.HenselianTheory
public import CanonicalTheory

@[expose] public section

/-! Tagged leading-term structures on ordinary valued fields. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer (iVFZero iVFOne)
open TrivCase (iKNeg)
open SpecialTransformations.Section6.ConcreteRV

namespace SpecialTransformations.Section6.ConcreteValued

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation K Γ)

abbrev Carrier := K ⊕ RVCalc.RV v

def hasSort : SortTag → Carrier v → Prop
  | .vf, .inl _ | .rv, .inr _ => True
  | .vf, .inr _ | .rv, .inl _ => False

def vfValue : Carrier v → K := Sum.elim id (fun _ => 0)

def rvValue : Carrier v → RVCalc.RV v := Sum.elim (fun _ => none) id

def zeroOf : SortTag → Carrier v
  | .vf => .inl 0
  | .rv => .inr none

def decodeResidue (q : RVCalc.RV v) : ConcreteRV.Residue v :=
  if h : q ∈ Set.range (residueCode v) then h.choose else 0

@[simp] theorem decodeResidue_code (r : ConcreteRV.Residue v) :
    decodeResidue v (residueCode v r) = r := by
  have h : residueCode v r ∈ Set.range (residueCode v) := ⟨r, rfl⟩
  rw [decodeResidue, dif_pos h]
  exact residueCode_injective v h.choose_spec

def addResidue (q r : RVCalc.RV v) : RVCalc.RV v :=
  if q ∈ Set.range (residueCode v) ∧ r ∈ Set.range (residueCode v) then
    residueCode v (decodeResidue v q + decodeResidue v r)
  else none

def negResidue (q : RVCalc.RV v) : RVCalc.RV v :=
  if q ∈ Set.range (residueCode v) then residueCode v (-decodeResidue v q) else none

@[simp] theorem addResidue_code (r s : ConcreteRV.Residue v) :
    addResidue v (residueCode v r) (residueCode v s) = residueCode v (r + s) := by
  rw [addResidue, if_pos ⟨⟨r, rfl⟩, ⟨s, rfl⟩⟩, decodeResidue_code, decodeResidue_code]

@[simp] theorem negResidue_code (r : ConcreteRV.Residue v) :
    negResidue v (residueCode v r) = residueCode v (-r) := by
  rw [negResidue, if_pos ⟨r, rfl⟩, decodeResidue_code]

def functionValue : {n : ℕ} → Fn n → (Fin n → Carrier v) → Carrier v
  | _, .vfZero, _ => .inl 0
  | _, .vfOne, _ => .inl 1
  | _, .vfAdd, z => .inl (vfValue v (z 0) + vfValue v (z 1))
  | _, .vfNeg, z => .inl (-vfValue v (z 0))
  | _, .vfMul, z => .inl (vfValue v (z 0) * vfValue v (z 1))
  | _, .rvMap, z => .inr (RVCalc.rv v (vfValue v (z 0)))
  | _, .rvZero, _ => .inr none
  | _, .rvOne, _ => .inr (some 1)
  | _, .rvMul, z => .inr (RVCalc.rvMul v (rvValue v (z 0)) (rvValue v (z 1)))
  | _, .rvInv, z => .inr ((rvValue v (z 0)).map Inv.inv)
  | _, .kAdd, z => .inr (addResidue v (rvValue v (z 0)) (rvValue v (z 1)))
  | _, .kNeg, z => .inr (negResidue v (rvValue v (z 0)))

@[instance_reducible] def nativeStructure : LRV.Structure (Carrier v) where
  funMap f z :=
    if ∀ i, hasSort v (Fn.argSort f i) (z i) then functionValue v f z else zeroOf v (Fn.resSort f)
  RelMap
    | .memVF, z => hasSort v .vf (z 0)
    | .memRV, z => hasSort v .rv (z 0)
    | .memUnits, z => hasSort v .rv (z 0) ∧ RVCalc.vrv v (rvValue v (z 0)) = 1
    | .rvLe, z => (∀ i, hasSort v .rv (z i)) ∧
        RVCalc.vrv v (rvValue v (z 1)) ≤ RVCalc.vrv v (rvValue v (z 0))

local instance : LRV.Structure (Carrier v) := nativeStructure v

@[simp] theorem vf_inl (x : K) : iVF (Sum.inl x : Carrier v) := trivial

@[simp] theorem rv_inr (q : RVCalc.RV v) : iRV (Sum.inr q : Carrier v) := trivial

@[simp] theorem not_vf_inr (q : RVCalc.RV v) : ¬ iVF (Sum.inr q : Carrier v) := not_false

@[simp] theorem not_rv_inl (x : K) : ¬ iRV (Sum.inl x : Carrier v) := not_false

theorem sortEval_iff (s : SortTag) (z : Carrier v) : sortEval s z ↔ hasSort v s z := by
  cases s <;> rfl

theorem of_vf (z : Carrier v) (hz : iVF z) : ∃ x : K, z = .inl x := by
  cases z with
  | inl x => exact ⟨x, rfl⟩
  | inr r => exact (not_vf_inr v r hz).elim

theorem of_rv (z : Carrier v) (hz : iRV z) : ∃ q : RVCalc.RV v, z = .inr q := by
  cases z with
  | inl x => exact (not_rv_inl v x hz).elim
  | inr q => exact ⟨q, rfl⟩

@[simp] theorem units_inr (q : RVCalc.RV v) :
    iUnits (Sum.inr q : Carrier v) ↔ RVCalc.vrv v q = 1 :=
  ⟨And.right, fun h => ⟨trivial, h⟩⟩

@[simp] theorem le_inr (q r : RVCalc.RV v) :
    iLe (Sum.inr q : Carrier v) (.inr r) ↔ RVCalc.vrv v r ≤ RVCalc.vrv v q := by
  apply and_iff_right
  intro i
  fin_cases i <;> trivial

theorem functionValue_sorted {n : ℕ} (f : Fn n) (z : Fin n → Carrier v) :
    hasSort v (Fn.resSort f) (functionValue v f z) := by
  cases f <;> trivial

theorem function_sorted {n : ℕ} (f : Fn n) (z : Fin n → Carrier v) :
    hasSort v (Fn.resSort f) (Structure.funMap (L := LRV) f z) := by
  change hasSort v (Fn.resSort f) (if _ then _ else _)
  split
  · exact functionValue_sorted v f z
  · cases Fn.resSort f <;> trivial

theorem function_of_sorted {n : ℕ} (f : Fn n) (z : Fin n → Carrier v)
    (h : ∀ i, hasSort v (Fn.argSort f i) (z i)) :
    Structure.funMap (L := LRV) f z = functionValue v f z := if_pos h

@[simp] theorem vfZero_eq : iVFZero (M := Carrier v) = .inl 0 := by
  exact function_of_sorted v .vfZero _ (fun i => i.elim0)

@[simp] theorem vfOne_eq : iVFOne (M := Carrier v) = .inl 1 := by
  exact function_of_sorted v .vfOne _ (fun i => i.elim0)

@[simp] theorem rvZero_eq : iRVZero (M := Carrier v) = .inr none := by
  exact function_of_sorted v .rvZero _ (fun i => i.elim0)

@[simp] theorem rvOne_eq : iRVOne (M := Carrier v) = .inr (some 1) := by
  exact function_of_sorted v .rvOne _ (fun i => i.elim0)

@[simp] theorem vfAdd_eq (x y : K) :
    iVFAdd (Sum.inl x : Carrier v) (.inl y) = .inl (x + y) := by
  change (if ∀ i : Fin 2, _ then _ else _) = _
  rw [if_pos (by intro i; fin_cases i <;> trivial)]
  rfl

@[simp] theorem vfNeg_eq (x : K) :
    iVFNeg (Sum.inl x : Carrier v) = .inl (-x) := by
  change (if ∀ i : Fin 1, _ then _ else _) = _
  rw [if_pos (by intro i; fin_cases i; trivial)]
  rfl

@[simp] theorem vfMul_eq (x y : K) :
    iVFMul (Sum.inl x : Carrier v) (.inl y) = .inl (x * y) := by
  change (if ∀ i : Fin 2, _ then _ else _) = _
  rw [if_pos (by intro i; fin_cases i <;> trivial)]
  rfl

@[simp] theorem rvMap_eq (x : K) :
    iRv (Sum.inl x : Carrier v) = .inr (RVCalc.rv v x) := by
  change (if ∀ i : Fin 1, _ then _ else _) = _
  rw [if_pos (by intro i; fin_cases i; trivial)]
  rfl

@[simp] theorem rvMul_eq (q r : RVCalc.RV v) :
    iRVMul (Sum.inr q : Carrier v) (.inr r) = .inr (RVCalc.rvMul v q r) := by
  change (if ∀ i : Fin 2, _ then _ else _) = _
  rw [if_pos (by intro i; fin_cases i <;> trivial)]
  rfl

@[simp] theorem rvInv_eq (q : RVCalc.RV v) :
    iRVInvFn (Sum.inr q : Carrier v) = .inr (q.map Inv.inv) := by
  change (if ∀ i : Fin 1, _ then _ else _) = _
  rw [if_pos (by intro i; fin_cases i; trivial)]
  rfl

@[simp] theorem kAdd_eq (q r : RVCalc.RV v) :
    iKAdd (Sum.inr q : Carrier v) (.inr r) = .inr (addResidue v q r) := by
  change (if ∀ i : Fin 2, _ then _ else _) = _
  rw [if_pos (by intro i; fin_cases i <;> trivial)]
  rfl

@[simp] theorem kNeg_eq (q : RVCalc.RV v) :
    iKNeg (Sum.inr q : Carrier v) = .inr (negResidue v q) := by
  change (if ∀ i : Fin 1, _ then _ else _) = _
  rw [if_pos (by intro i; fin_cases i; trivial)]
  rfl

end SpecialTransformations.Section6.ConcreteValued
