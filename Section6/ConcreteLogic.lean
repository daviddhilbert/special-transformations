module

public import Section6.ConcreteValued

@[expose] public section

/-! Realization of the three guarded contexts in the ordinary tagged model. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer TrivCase RVElim
open SpecialTransformations.Section6.ConcreteRV

namespace SpecialTransformations.Section6.ConcreteValued

theorem residueHyps_realize {M : Type} [LRV.Structure M] {n : ℕ}
    (e : Empty → M) (z : Fin n → M) :
    (kHyps (k := n)).Realize e z ↔ ∀ i, iUnits (z i) ∨ z i = iRVZero := by
  have h (l : List (Fin n)) :
      (l.foldr (fun i acc => pInK (tv i.val i.isLt) ⊓ acc) ⊤).Realize e z ↔
        ∀ i ∈ l, iUnits (z i) ∨ z i = iRVZero := by
    induction l with
    | nil => simp
    | cons i l ih =>
      rw [List.foldr_cons, BoundedFormula.realize_inf, ih, TrivCase.pInK_realize,
        TrivCase.realize_tv_nat]
      constructor
      · rintro ⟨hi, hl⟩ j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hi
        · exact hl j hj
      · intro he
        exact ⟨he i List.mem_cons_self, fun j hj => he j (List.mem_cons_of_mem i hj)⟩
  rw [kHyps, h]
  exact ⟨fun he i => he i (List.mem_finRange i), fun he i _ => he i⟩

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation K Γ)
local instance : LRV.Structure (Carrier v) := nativeStructure v

def inResidue (z : Carrier v) : Prop := iUnits z ∨ z = iRVZero

theorem residue_elements (z : Carrier v) (hz : iRV z) :
    inResidue v z ↔ ∃ r : ConcreteRV.Residue v, z = .inr (residueCode v r) := by
  obtain ⟨q, rfl⟩ := of_rv v z hz
  simp only [inResidue, units_inr, rvZero_eq, Sum.inr.injEq]
  have h : (RVCalc.vrv v q = 1 ∨ q = none) ↔ q ∈ Set.range (residueCode v) := by
    rw [residueCode_range, Set.mem_ofPred_eq, or_comm]
  exact h.trans (exists_congr fun _ => eq_comm)

theorem allVF {n : ℕ} (ss : Fin n → SortTag) (hs : ∀ i, ss i = .vf) (φ : Bf n) :
    Carrier v ⊨ allSorted ss φ ↔
      ∀ x : Fin n → K, φ.Realize (@default (Empty → Carrier v) Unique.instInhabited)
        (fun i => (Sum.inl (x i) : Carrier v)) := by
  simp only [allSorted, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_imp, sortedHyps_realize, hs]
  constructor
  · intro h x
    exact h _ (fun i => vf_inl v (x i))
  · intro h z hz
    choose x hx using fun i => of_vf v (z i) (hz i)
    exact (funext hx).symm ▸ h x

theorem allRV {n : ℕ} (ss : Fin n → SortTag) (hs : ∀ i, ss i = .rv) (φ : Bf n) :
    Carrier v ⊨ allSorted ss φ ↔
      ∀ x : Fin n → RVCalc.RV v, φ.Realize (@default (Empty → Carrier v) Unique.instInhabited)
        (fun i => (Sum.inr (x i) : Carrier v)) := by
  simp only [allSorted, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_imp, sortedHyps_realize, hs]
  constructor
  · intro h x
    exact h _ (fun i => rv_inr v (x i))
  · intro h z hz
    choose x hx using fun i => of_rv v (z i) (hz i)
    exact (funext hx).symm ▸ h x

theorem allResidue {n : ℕ} (ss : Fin n → SortTag) (hs : ∀ i, ss i = .rv) (φ : Bf n) :
    Carrier v ⊨ allSortedK ss φ ↔
      ∀ x : Fin n → ConcreteRV.Residue v,
        φ.Realize (@default (Empty → Carrier v) Unique.instInhabited)
          (fun i => (Sum.inr (residueCode v (x i)) : Carrier v)) := by
  simp only [allSortedK, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_imp, BoundedFormula.realize_inf, sortedHyps_realize, hs]
  have hk (z : Fin n → Carrier v) :
      (kHyps (k := n)).Realize (@default (Empty → Carrier v) Unique.instInhabited) z ↔
        ∀ i, inResidue v (z i) := residueHyps_realize _ _
  simp_rw [hk]
  constructor
  · intro h x
    exact h _ ⟨fun i => rv_inr v _, fun i => (residue_elements v _ (rv_inr v _)).mpr ⟨x i, rfl⟩⟩
  · intro h z hz
    choose x hx using fun i => (residue_elements v (z i) (hz.1 i)).mp (hz.2 i)
    exact (funext hx).symm ▸ h x

theorem exVF {n : ℕ} (φ : Bf (n + 1)) (e : Empty → Carrier v) (z : Fin n → Carrier v) :
    (exSorted .vf φ).Realize e z ↔
      ∃ x : K, φ.Realize e (Fin.snoc z (.inl x)) := by
  simp only [exSorted, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    sortPred_realize, realize_tv_last_snoc]
  constructor
  · rintro ⟨a, ha, hφ⟩
    obtain ⟨x, rfl⟩ := of_vf v a ha
    exact ⟨x, hφ⟩
  · rintro ⟨x, hx⟩
    exact ⟨.inl x, vf_inl v x, hx⟩

theorem exRV {n : ℕ} (φ : Bf (n + 1)) (e : Empty → Carrier v) (z : Fin n → Carrier v) :
    (exSorted .rv φ).Realize e z ↔
      ∃ x : RVCalc.RV v, φ.Realize e (Fin.snoc z (.inr x)) := by
  simp only [exSorted, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    sortPred_realize, realize_tv_last_snoc]
  constructor
  · rintro ⟨a, ha, hφ⟩
    obtain ⟨x, rfl⟩ := of_rv v a ha
    exact ⟨x, hφ⟩
  · rintro ⟨x, hx⟩
    exact ⟨.inr x, rv_inr v x, hx⟩

theorem exResidue {n : ℕ} (φ : Bf (n + 1)) (e : Empty → Carrier v) (z : Fin n → Carrier v) :
    (exSortedK .rv φ).Realize e z ↔
      ∃ x : ConcreteRV.Residue v, φ.Realize e (Fin.snoc z (.inr (residueCode v x))) := by
  simp only [exSortedK, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    sortPred_realize, pInK_realize, realize_tv_last_snoc]
  constructor
  · rintro ⟨a, ⟨ha, ha'⟩, hφ⟩
    obtain ⟨x, rfl⟩ := (residue_elements v a ha).mp ha'
    exact ⟨x, hφ⟩
  · rintro ⟨x, hx⟩
    exact ⟨_, ⟨rv_inr v _, (residue_elements v _ (rv_inr v _)).mpr ⟨x, rfl⟩⟩, hx⟩

theorem canonical : CanonicalStructure.IsCanonical (M := Carrier v) := by
  constructor
  · intro n f z hz
    change (if ∀ i, hasSort v (Fn.argSort f i) (z i) then _ else _) = _
    rw [if_neg (fun h => hz (fun i => (sortEval_iff v _ _).mpr (h i)))]
    cases Fn.resSort f <;> simp [zeroOf, CanonicalStructure.sortZero]
  · intro z hz
    exact fun h => hz (fun i => (sortEval_iff v _ _).mpr (h.1 i))

end SpecialTransformations.Section6.ConcreteValued
