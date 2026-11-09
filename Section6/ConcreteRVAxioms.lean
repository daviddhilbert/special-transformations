import Section6.ConcreteFieldAxioms
import Section6.ConcreteResidueOps
import Section6.ConcreteExtension

/-! Sort, group, order, and valuation-link axioms on ordinary leading terms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer TrivCase RVElim
open SpecialTransformations.Section6.ConcreteRV
open ResidueTranscendentalTransport

namespace SpecialTransformations.Section6.ConcreteValued

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation K Γ)
local instance rvAxiomStructure : LRV.Structure (Carrier v) := nativeStructure v
local notation "emptyVal" => @default (Empty → Carrier v) Unique.instInhabited
local notation "zeroVal" => @default (Fin 0 → Carrier v) Unique.instInhabited

theorem allOne_iff (φ : Bf 1) : Carrier v ⊨ allOne φ ↔
    ∀ z : Carrier v, φ.Realize emptyVal ![z] := by
  simp only [allOne, Sentence.Realize, BoundedFormula.realize_alls]
  constructor
  · intro h z
    exact h ![z]
  · intro h z
    have he : (![z 0] : Fin 1 → Carrier v) = z := by
      funext i
      fin_cases i
      rfl
    exact he ▸ h (z 0)

theorem units_sorted {z : Carrier v} (hz : iUnits z) : iRV z := hz.1

@[simp] theorem rv_one : RVCalc.rv v (1 : K) = some 1 := by
  rw [RVCalc.rv_of_ne one_ne_zero, Units.mk0_one, map_one]

@[simp] theorem value_one : RVCalc.vrv v (some 1) = 1 := by
  rw [← rv_one v, RVCalc.vrv_rv, map_one]

theorem value_eq_zero {q : RVCalc.RV v} : RVCalc.vrv v q = 0 ↔ q = none := by
  cases q with
  | none => simp only [RVCalc.vrv_none]
  | some q =>
    rw [RVCalc.vrv_some]
    exact iff_of_false (RVGroupGraph.vrvUnit_ne_zero v q) (by simp)

theorem rvMul_assoc (p q r : RVCalc.RV v) :
    RVCalc.rvMul v (RVCalc.rvMul v p q) r = RVCalc.rvMul v p (RVCalc.rvMul v q r) := by
  cases p <;> cases q <;> cases r <;> simp [RVCalc.rvMul]
  exact mul_assoc (_ : RVCalc.RVUnit v) _ _

theorem rvMul_comm (p q : RVCalc.RV v) : RVCalc.rvMul v p q = RVCalc.rvMul v q p := by
  cases p with
  | none => cases q <;> rfl
  | some p =>
    cases q with
    | none => rfl
    | some q => exact congrArg some (mul_comm p q)

@[simp] theorem one_rvMul (p : RVCalc.RV v) : RVCalc.rvMul v (some 1) p = p := by
  cases p with
  | none => rfl
  | some p => exact congrArg some (one_mul p)

@[simp] theorem rvMul_none (p : RVCalc.RV v) : RVCalc.rvMul v p none = none := by
  cases p <;> rfl

theorem inv_rvMul (p : RVCalc.RV v) (hp : p ≠ none) :
    RVCalc.rvMul v (p.map Inv.inv) p = some 1 := by
  cases p with
  | none => exact (hp rfl).elim
  | some p => simp [RVCalc.rvMul]

theorem value_rvInv (p : RVCalc.RV v) :
    RVCalc.vrv v (p.map Inv.inv) = (RVCalc.vrv v p)⁻¹ := by
  obtain ⟨x, rfl⟩ := rv_surjective v p
  have he : (RVCalc.rv v x).map Inv.inv = RVCalc.rv v x⁻¹ := by
    rw [rv_inv]
    cases RVCalc.rv v x <;> rfl
  rw [he, RVCalc.vrv_rv, RVCalc.vrv_rv, map_inv₀]

theorem residueCode_closed_add {p q : RVCalc.RV v}
    (hp : inResidue v (.inr p)) (hq : inResidue v (.inr q)) :
    inResidue v (.inr (addResidue v p q)) := by
  obtain ⟨r, hr⟩ := (residue_elements v _ (rv_inr v p)).mp hp
  obtain ⟨s, hs⟩ := (residue_elements v _ (rv_inr v q)).mp hq
  obtain rfl := Sum.inr.inj hr
  obtain rfl := Sum.inr.inj hs
  rw [addResidue_code]
  exact (residue_elements v _ (rv_inr v _)).mpr ⟨_, rfl⟩

theorem residueCode_closed_mul {p q : RVCalc.RV v}
    (hp : inResidue v (.inr p)) (hq : inResidue v (.inr q)) :
    inResidue v (.inr (RVCalc.rvMul v p q)) := by
  obtain ⟨r, hr⟩ := (residue_elements v _ (rv_inr v p)).mp hp
  obtain ⟨s, hs⟩ := (residue_elements v _ (rv_inr v q)).mp hq
  obtain rfl := Sum.inr.inj hr
  obtain rfl := Sum.inr.inj hs
  rw [← residueCode_mul]
  exact (residue_elements v _ (rv_inr v _)).mpr ⟨_, rfl⟩

theorem residueCode_closed_neg {p : RVCalc.RV v} (hp : inResidue v (.inr p)) :
    inResidue v (.inr (negResidue v p)) := by
  obtain ⟨r, hr⟩ := (residue_elements v _ (rv_inr v p)).mp hp
  obtain rfl := Sum.inr.inj hr
  rw [negResidue_code]
  exact (residue_elements v _ (rv_inr v _)).mpr ⟨_, rfl⟩

private theorem snoc_zero_one {M : Type} (z : Fin 1 → M) (a : M) :
    (Fin.snoc z a : Fin 2 → M) 0 = z 0 := by
  exact Fin.snoc_castSucc (α := fun _ : Fin 2 => M) a z (0 : Fin 1)

private theorem snoc_last_one {M : Type} (z : Fin 1 → M) (a : M) :
    (Fin.snoc z a : Fin 2 → M) 1 = a := by
  change (Fin.snoc z a : Fin 2 → M) (Fin.last 1) = a
  exact Fin.snoc_last (α := fun _ : Fin 2 => M) a z

private theorem snoc_last_zero {M : Type} (z : Fin 0 → M) (a : M) :
    (Fin.snoc z a : Fin 1 → M) 0 = a := by
  change (Fin.snoc z a : Fin 1 → M) (Fin.last 0) = a
  exact Fin.snoc_last (α := fun _ : Fin 1 => M) a z

macro "native_rv_simp" : tactic =>
  `(tactic| simp only [pEq, BoundedFormula.realize_bdEqual, BoundedFormula.realize_sup,
      BoundedFormula.realize_inf, BoundedFormula.realize_imp, BoundedFormula.realize_not,
      BoundedFormula.realize_iff, RVCalc.realize_var_inr, ne_eq,
      snoc_zero_one, snoc_last_one, snoc_last_zero,
      pVF_realize, pRVsort_realize, pRV_realize, pUnits_realize, realize_pLe,
      realize_tVFZero, realize_tVFOne, realize_tVFAdd, realize_tVFNeg, realize_tVFMul,
      realize_tRv, realize_tRVZero, tRVInfty, realize_tRVOne_T, realize_tRVMul,
      CanonicalStructure.realize_tRVInv, realize_tKAdd, realize_tKNeg,
      vfZero_eq, vfOne_eq, vfAdd_eq, vfNeg_eq, vfMul_eq, rvMap_eq, rvZero_eq, rvOne_eq,
      rvMul_eq, rvInv_eq, kAdd_eq, kNeg_eq, units_inr, le_inr,
      Sum.inl.injEq, Sum.inr.injEq, vf_inl, rv_inr, RVCalc.vrv_none])

theorem model_sortAxioms : Carrier v ⊨ Axioms.sortAxioms := by
  constructor
  intro σ hσ
  rcases hσ with hσ | hσ
  · simp only [Axioms.sortClosure, Axioms.ofList, Set.mem_setOf_eq,
      List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (pVF (tVFZero : Tm 0)).Realize emptyVal zeroVal
      native_rv_simp
    · change (pVF (tVFOne : Tm 0)).Realize emptyVal zeroVal
      native_rv_simp
    · rw [Axioms.sdVFAdd, allVF v _ (by intro i; fin_cases i <;> rfl)]
      intro x
      native_rv_simp
    · rw [Axioms.sdVFNeg, allVF v _ (by intro i; fin_cases i <;> rfl)]
      intro x
      native_rv_simp
    · rw [Axioms.sdVFMul, allVF v _ (by intro i; fin_cases i <;> rfl)]
      intro x
      native_rv_simp
    · rw [Axioms.sdRv, allVF v _ (by intro i; fin_cases i <;> rfl)]
      intro x
      native_rv_simp
    · change (pRVsort (tRVZero : Tm 0)).Realize emptyVal zeroVal
      native_rv_simp
    · change (pRVsort (tRVInfty : Tm 0)).Realize emptyVal zeroVal
      native_rv_simp
    · change (pRVsort (tRVOne : Tm 0)).Realize emptyVal zeroVal
      native_rv_simp
    · rw [Axioms.sdRVMul, allRV v _ (by intro i; fin_cases i <;> rfl)]
      intro x
      native_rv_simp
    · rw [Axioms.sdRVInv, allRV v _ (by intro i; fin_cases i <;> rfl)]
      intro x
      native_rv_simp
    · rw [Axioms.sdUnits, allOne_iff]
      intro z
      native_rv_simp
      exact units_sorted v
    · rw [Axioms.sdKAdd, allRV v _ (by intro i; fin_cases i <;> rfl)]
      intro x
      simp only [BoundedFormula.realize_imp, pInK_realize, RVCalc.realize_var_inr, realize_tKAdd, kAdd_eq]
      exact residueCode_closed_add v
    · rw [Axioms.sdKNeg, allRV v _ (by intro i; fin_cases i <;> rfl)]
      intro x
      simp only [BoundedFormula.realize_imp, pInK_realize, RVCalc.realize_var_inr, realize_tKNeg, kNeg_eq]
      exact residueCode_closed_neg v
    · rw [Axioms.sdKMul, allRV v _ (by intro i; fin_cases i <;> rfl)]
      intro x
      simp only [BoundedFormula.realize_imp, pInK_realize, RVCalc.realize_var_inr, realize_tRVMul, rvMul_eq]
      exact residueCode_closed_mul v
  · simp only [Axioms.ofList, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl
    · rw [Axioms.sdCover, allOne_iff]
      intro z
      native_rv_simp
      cases z <;> simp
    · rw [Axioms.sdDisjoint, allOne_iff]
      intro z
      native_rv_simp
      cases z <;> simp

theorem model_preorderRV : Carrier v ⊨ Axioms.preorderRV := by
  constructor
  intro σ hσ
  simp only [Axioms.preorderRV, Axioms.ofList, Set.mem_setOf_eq,
    List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Axioms.leRefl, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    exact fun _ => le_rfl
  · rw [Axioms.leTrans, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    exact fun _ _ _ h₁ h₂ => h₂.trans h₁
  · rw [Axioms.leTotal, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    exact fun _ _ => le_total _ _
  · rw [Axioms.leTop, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    exact fun _ => zero_le
  · rw [Axioms.leInftyEq, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    exact fun _ h => (value_eq_zero v).mp (le_antisymm h (zero_le))
  · rw [Axioms.leClassOne, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    rw [value_one]
    exact fun _ => ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
  · rw [Axioms.leMulCompat, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    simp only [RVCalc.vrv_mul]
    exact fun _ _ _ h₁ h₂ => by simpa only [h₁, mul_one] using h₂

theorem model_rvGroupBase : Carrier v ⊨ HenselianTheory.rvGroupBase := by
  constructor
  intro σ hσ
  simp only [HenselianTheory.rvGroupBase, Axioms.ofList, Set.mem_setOf_eq,
    List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (pUnits (tRVOne : Tm 0)).Realize emptyVal zeroVal
    native_rv_simp
    exact value_one v
  · rw [Axioms.rvMulMem, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    intro h₁ h₂
    rw [RVCalc.vrv_mul, h₁, h₂, one_mul]
  · rw [Axioms.rvMulAssoc, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    exact rvMul_assoc v ..
  · rw [Axioms.rvMulComm, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    exact rvMul_comm v ..
  · rw [Axioms.rvMulOne, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    exact fun _ => one_rvMul v _
  · rw [Axioms.rvMulInv, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    simp only [BoundedFormula.realize_imp, exRV]
    native_rv_simp
    change RVCalc.vrv v (x 0) = 1 →
      ∃ q, RVCalc.vrv v q = 1 ∧ RVCalc.rvMul v q (x 0) = some 1
    intro hx
    refine ⟨(x 0).map Inv.inv, ?_, inv_rvMul v _ ?_⟩
    · rw [value_rvInv, hx, inv_one]
    · intro h
      exact zero_ne_one ((value_eq_zero v).mpr h |>.symm.trans hx)
  · rw [Axioms.rvMulZeroK, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    exact fun _ => rvMul_none v _
  · rw [Axioms.rvMulInfty, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    exact rvMul_none v _

theorem model_rvAxioms : Carrier v ⊨ Axioms.rvAxioms := by
  constructor
  intro σ hσ
  simp only [Axioms.rvAxioms, Axioms.ofList, Set.mem_setOf_eq,
    List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl
  · change (pEq (tRv tVFZero : Tm 0) tRVInfty).Realize emptyVal zeroVal
    native_rv_simp
    exact RVCalc.rv_zero
  · rw [Axioms.rvEqInfty, allVF v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    exact RVCalc.rv_eq_none_iff.mp
  · rw [Axioms.rvMulHom, allVF v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    exact rv_mul_all v ..
  · rw [Axioms.rvSurj, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    simp only [BoundedFormula.realize_imp, exVF]
    native_rv_simp
    change x 0 ≠ none → ∃ a : K, RVCalc.rv v a = x 0
    exact fun _ => rv_surjective v _
  · rw [Axioms.rvUltrametric, allVF v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    simp only [RVCalc.vrv_rv]
    exact le_max_iff.mp (v.map_add _ _)

theorem rv_eq_iff_close (x y : K) (hy : y ≠ 0) :
    RVCalc.rv v x = RVCalc.rv v y ↔ v (x - y) < v y := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [RVCalc.rv_zero, zero_sub, Valuation.map_neg]
    exact iff_of_false (fun h => hy (RVCalc.rv_eq_none_iff.mp h.symm)) (lt_irrefl _)
  · rw [eq_comm, RVCalc.rv_eq_iff hy hx, ← neg_sub x y, Valuation.map_neg]

private theorem residueGuard (q : RVCalc.RV v) :
    (iUnits (Sum.inr q : Carrier v) ∨ q = none) ↔ inResidue v (Sum.inr q) := by
  rw [inResidue, rvZero_eq, Sum.inr.injEq]

theorem model_repairRV (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) :
    Carrier v ⊨ Axioms.repairRV := by
  constructor
  intro σ hσ
  simp only [Axioms.repairRV, Axioms.ofList, Set.mem_setOf_eq,
    List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Axioms.rvMulOneRV, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    exact fun _ => one_rvMul v _
  · rw [Axioms.rvMulInvRV, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    simp only [BoundedFormula.realize_imp, exRV]
    native_rv_simp
    change x 0 ≠ none → ∃ q, q ≠ none ∧ RVCalc.rvMul v q (x 0) = some 1
    intro h
    refine ⟨(x 0).map Inv.inv, ?_, inv_rvMul v _ h⟩
    cases hx : x 0 <;> simp_all
  · rw [Axioms.leMulCompatFull, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    simp only [RVCalc.vrv_mul]
    exact fun h => (mul_le_mul_iff_left₀ (pos_iff_ne_zero.mpr (h ∘ (value_eq_zero v).mp))).symm
  · rw [Axioms.kAddLink, allVF v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    simp only [RVCalc.vrv_rv]
    intro hx hy
    rw [addResidue_rv v _ _ hx hy]
    exact ⟨fun h => if_pos h, fun h => if_neg h⟩
  · rw [Axioms.kNegLink, allVF v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    rw [RVCalc.vrv_rv]
    exact negResidue_rv v _
  · rw [Axioms.rvEqLink, allVF v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    simp only [RVCalc.vrv_rv, not_le, ← sub_eq_add_neg]
    exact rv_eq_iff_close v _ _
  · rw [Axioms.kJunkZero, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup, BoundedFormula.realize_not,
      pInK_realize, RVCalc.realize_var_inr, pEq,
      BoundedFormula.realize_bdEqual, realize_tKAdd, realize_tRVZero, kAdd_eq, rvZero_eq, Sum.inr.injEq]
    simp only [residueGuard v]
    intro h
    apply if_neg
    rintro ⟨h₁, h₂⟩
    obtain ⟨r, hr⟩ := h₁
    obtain ⟨s, hs⟩ := h₂
    exact h.elim
      (fun hn => hn ((residue_elements v _ (rv_inr v _)).mpr ⟨r, congrArg Sum.inr hr.symm⟩))
      (fun hn => hn ((residue_elements v _ (rv_inr v _)).mpr ⟨s, congrArg Sum.inr hs.symm⟩))
  · rw [Axioms.kNegJunkZero, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    simp only [BoundedFormula.realize_imp, BoundedFormula.realize_not, pInK_realize,
      RVCalc.realize_var_inr, pEq, BoundedFormula.realize_bdEqual,
      realize_tKNeg, realize_tRVZero, kNeg_eq, rvZero_eq, Sum.inr.injEq]
    simp only [residueGuard v]
    intro h
    apply if_neg
    rintro ⟨r, hr⟩
    exact h ((residue_elements v _ (rv_inr v _)).mpr ⟨r, congrArg Sum.inr hr.symm⟩)
  · change (exSorted .vf (∼(pEq &0 tVFZero) ⊓ ∼(pLe (tRv &0) (tRv tVFOne)))).Realize
      emptyVal zeroVal
    rw [exVF]
    native_rv_simp
    simpa only [RVCalc.vrv_rv, map_one, not_le] using hnt
  · change (pEq (tRVInv tRVZero : Tm 0) tRVZero).Realize emptyVal zeroVal
    native_rv_simp
    rfl
  · rw [Axioms.rvInvMul, allRV v _ (by intro i; fin_cases i <;> rfl)]
    intro x
    native_rv_simp
    exact inv_rvMul v _

theorem model_valuedField (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) :
    Carrier v ⊨ HenselianTheory.valuedField := by
  constructor
  intro σ hσ
  rcases hσ with ((((((h | h) | h) | h) | h) | h) | h)
  · exact (model_sortAxioms v).realize_of_mem σ h
  · exact (model_vfField v).realize_of_mem σ h
  · exact (model_rvGroupBase v).realize_of_mem σ h
  · exact (model_kField v).realize_of_mem σ h
  · exact (model_preorderRV v).realize_of_mem σ h
  · exact (model_rvAxioms v).realize_of_mem σ h
  · exact (model_repairRV v hnt).realize_of_mem σ h

end SpecialTransformations.Section6.ConcreteValued
