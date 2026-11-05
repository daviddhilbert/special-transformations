import TypedModelMap
import CanonicalRV

set_option backward.isDefEq.respectTransparency false

/-! A map of the valued VF fields determines the entire sorted LRV embedding.
The only map hypothesis besides being a field homomorphism is preservation and
reflection of the valuation preorder. The RV map and its residue operations are
derived from the frozen ACVF axioms. -/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV

namespace ValuedModelMap

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

def zeroRV : RVSort M := ⟨iRVZero, rv_zero_mem hM⟩
def oneRV : RVSort M := ⟨iRVOne, rv_one_mem hM⟩
def mulRV (a b : RVSort M) : RVSort M := ⟨iRVMul a.1 b.1, rv_mul_mem hM a.2 b.2⟩
def addK (a b : RVSort M) : RVSort M :=
  ⟨iKAdd a.1 b.1, CanonicalStructure.kAdd_mem hM a.2 b.2⟩
def negK (a : RVSort M) : RVSort M :=
  ⟨TrivCase.iKNeg a.1, CanonicalStructure.kNeg_mem hM a.2⟩
def inK (a : RVSort M) : Prop := iUnits a.1 ∨ a = zeroRV

@[simp] theorem encodedRv_zero : encodedRv (0 : VFType (M := M)) = zeroRV :=
  Subtype.ext (RVCalc.rv_zero_eq hM)
@[simp] theorem encodedRv_one : encodedRv (1 : VFType (M := M)) = oneRV :=
  Subtype.ext (RVCalc.rv_one hM)
theorem encodedRv_mul (a b : VFType (M := M)) :
    encodedRv (a * b) = mulRV (encodedRv a) (encodedRv b) :=
  Subtype.ext (rv_mul_hom_of_model hM a.2 b.2)

section Map

variable (F : VFType (M := M) →+* VFType (M := N))
variable (hF : ∀ a b, VFValued.predV (F a) (F b) ↔ VFValued.predV a b)

include hF

theorem same_fibers (a b : VFType (M := M)) :
    encodedRv (F a) = encodedRv (F b) ↔ encodedRv a = encodedRv b := by
  rw [Subtype.ext_iff, Subtype.ext_iff]
  change iRv (F a).1 = iRv (F b).1 ↔ iRv a.1 = iRv b.1
  by_cases hb : b = 0
  · subst b
    rw [map_zero, show iRv (0 : VFType (M := N)).1 = iRVZero from RVCalc.rv_zero_eq hN,
      show iRv (0 : VFType (M := M)).1 = iRVZero from RVCalc.rv_zero_eq hM,
      encodedRv_zero_iff, encodedRv_zero_iff]
    exact map_eq_zero_iff F F.injective
  have hFb : F b ≠ 0 := fun h => hb ((map_eq_zero_iff F F.injective).mp h)
  rw [encoded_eq_iff_close (F a).2 (F b).2 (fun he => hFb (Subtype.ext he)),
    encoded_eq_iff_close a.2 b.2 (fun he => hb (Subtype.ext he))]
  change (¬ VFValued.predV (F b) (F a - F b)) ↔ ¬ VFValued.predV b (a - b)
  rw [← map_sub, hF]

omit hF in
noncomputable def rvMap (a : RVSort M) : RVSort N :=
  encodedRv (F (Classical.choose (encodedRv_surjective a)))

@[simp] theorem rvMap_encodedRv (a : VFType (M := M)) :
    rvMap F (encodedRv a) = encodedRv (F a) :=
  (same_fibers F hF _ _).mpr (Classical.choose_spec (encodedRv_surjective (encodedRv a)))

theorem rvMap_injective : Function.Injective (rvMap F) := by
  intro a b hab
  have he := (same_fibers F hF _ _).mp hab
  exact (Classical.choose_spec (encodedRv_surjective a)).symm.trans
    (he.trans (Classical.choose_spec (encodedRv_surjective b)))

noncomputable def rvEmbedding : RVSort M ↪ RVSort N :=
  ⟨rvMap F, rvMap_injective F hF⟩

@[simp] theorem rvMap_zero : rvMap F (zeroRV (M := M)) = zeroRV := by
  rw [← encodedRv_zero, rvMap_encodedRv F hF, map_zero, encodedRv_zero]

@[simp] theorem rvMap_one : rvMap F (oneRV (M := M)) = oneRV := by
  rw [← encodedRv_one, rvMap_encodedRv F hF, map_one, encodedRv_one]

theorem rvMap_mul (a b : RVSort M) :
    rvMap F (mulRV a b) = mulRV (rvMap F a) (rvMap F b) := by
  obtain ⟨x, rfl⟩ := encodedRv_surjective a
  obtain ⟨y, rfl⟩ := encodedRv_surjective b
  rw [← encodedRv_mul, rvMap_encodedRv F hF, map_mul, encodedRv_mul,
    rvMap_encodedRv F hF, rvMap_encodedRv F hF]

theorem rvMap_order (a b : RVSort M) :
    iLe (rvMap F a).1 (rvMap F b).1 ↔ iLe a.1 b.1 := by
  obtain ⟨x, rfl⟩ := encodedRv_surjective a
  obtain ⟨y, rfl⟩ := encodedRv_surjective b
  rw [rvMap_encodedRv F hF, rvMap_encodedRv F hF]
  exact hF y x

@[simp] theorem rvMap_eq_zero (a : RVSort M) : rvMap F a = zeroRV ↔ a = zeroRV := by
  rw [← rvMap_zero F hF]
  exact (rvMap_injective F hF).eq_iff

end Map

/-! Small semantic extraction lemmas. These are consequences of ACVF, rather
than extra assumptions on a valued-field map. -/

theorem units_ne_zero {a : M} (ha : iUnits a) : a ≠ iRVZero := by
  have hr := iRV_of_inK hM (Or.inl ha)
  have hmem : Axioms.rvMulInv ∈ Axioms.ACVF :=
    mem_ACVF_of_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pUnits &0 ⟹ exSorted .rv (pUnits &1 ⊓ pEq (tRVMul &1 &0) tRVOne)))
    hmem ![a] (by intro i; fin_cases i; simpa using hr)
  rw [BoundedFormula.realize_imp] at h
  have h2 := h ((pUnits_realize (M := M) &0 (default : Empty → M) ![a]).mpr
    (by simpa using ha))
  have hh : ∃ b : M, iRV b ∧ (iUnits b ∧ iRVMul b a = iRVOne) := by
    simpa [exSorted, sortPred, sortPred_realize, pRVsort_realize,
      BoundedFormula.realize_ex, BoundedFormula.realize_inf, pUnits_realize,
      pEq, BoundedFormula.realize_bdEqual, realize_tRVMul, realize_tRVOne_T,
      RVCalc.realize_var_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] using h2
  intro h0
  obtain ⟨b, hb, -, he⟩ := hh
  rw [h0, rv_mul_zero_right_of_model hM hb] at he
  exact RVCalc.rv_one_ne_zero hM he.symm

theorem kHyps_realize {k : ℕ} (v : Empty → M) (x : Fin k → M) :
    (kHyps (k := k)).Realize v x ↔ ∀ i, iUnits (x i) ∨ x i = iRVZero := by
  have hfold : ∀ l : List (Fin k),
      (l.foldr (fun i acc => pInK (tv i.val i.isLt) ⊓ acc) ⊤).Realize v x ↔
        ∀ i ∈ l, iUnits (x i) ∨ x i = iRVZero := by
    intro l
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
  rw [kHyps, hfold]
  exact ⟨fun h i => h i (List.mem_finRange i), fun h i _ => h i⟩

theorem allK_realize {k : ℕ} {φ : Bf k}
    (hmem : allSortedK (fun _ => .rv) φ ∈ Axioms.ACVF)
    (x : Fin k → M) (hx : ∀ i, iUnits (x i) ∨ x i = iRVZero) :
    φ.Realize (default : Empty → M) x := by
  have h := hM.realize_of_mem _ hmem
  simp only [allSortedK, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_imp] at h
  apply h x
  rw [BoundedFormula.realize_inf]
  exact ⟨(sortedHyps_realize _ _ _).mpr (fun i => iRV_of_inK hM (hx i)),
    (kHyps_realize _ _).mpr hx⟩

theorem kField_mem {s : LRV.Sentence} (h : s ∈ Axioms.kField) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union] at *
  tauto

theorem addK_zero (a : RVSort M) (ha : inK a) : addK a zeroRV = a := by
  have ha' : iUnits a.1 ∨ a.1 = iRVZero := ha.imp id (congrArg Subtype.val)
  have hm : allSortedK (fun _ : Fin 1 => .rv) (pEq (tKAdd &0 tRVZero) &0) ∈ Axioms.ACVF :=
    kField_mem (by
      rw [show (fun _ : Fin 1 => SortTag.rv) = ![SortTag.rv] from by funext i; fin_cases i; rfl]
      simp [Axioms.kField, Axioms.ofList])
  apply Subtype.ext
  change iKAdd a.1 iRVZero = a.1
  have h := allK_realize hm ![a.1] (by intro i; fin_cases i; simpa using ha')
  simpa only [pEq, BoundedFormula.realize_bdEqual, TrivCase.realize_tKAdd,
    realize_tRVZero, RVCalc.realize_var_inr, Matrix.cons_val_zero, Matrix.head_cons] using h

theorem addK_comm (a b : RVSort M) (ha : inK a) (hb : inK b) : addK a b = addK b a := by
  have ha' : iUnits a.1 ∨ a.1 = iRVZero := ha.imp id (congrArg Subtype.val)
  have hb' : iUnits b.1 ∨ b.1 = iRVZero := hb.imp id (congrArg Subtype.val)
  have hm : allSortedK (fun _ : Fin 2 => .rv) (pEq (tKAdd &0 &1) (tKAdd &1 &0)) ∈ Axioms.ACVF :=
    kField_mem (by
      rw [show (fun _ : Fin 2 => SortTag.rv) = ![SortTag.rv, SortTag.rv] from by
        funext i; fin_cases i <;> rfl]
      simp [Axioms.kField, Axioms.ofList])
  apply Subtype.ext
  change iKAdd a.1 b.1 = iKAdd b.1 a.1
  have h := allK_realize hm ![a.1, b.1] (by intro i; fin_cases i <;> simp [ha', hb'])
  simpa only [pEq, BoundedFormula.realize_bdEqual, TrivCase.realize_tKAdd,
    RVCalc.realize_var_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

theorem zero_addK (a : RVSort M) (ha : inK a) : addK zeroRV a = a := by
  rw [addK_comm _ _ (Or.inr rfl) ha, addK_zero a ha]

theorem negK_inK (a : RVSort M) (ha : inK a) : inK (negK a) := by
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pInK &0 ⟹ pInK (tKNeg &0)))
    (mem_ACVF_sortClosure (s := Axioms.sdKNeg)
      (by simp [Axioms.sortClosure, Axioms.ofList]))
    ![a.1] (by intro i; fin_cases i; simpa using a.2)
  have ha' : iUnits a.1 ∨ a.1 = iRVZero := ha.imp id (congrArg Subtype.val)
  have hh : iUnits (TrivCase.iKNeg a.1) ∨ TrivCase.iKNeg a.1 = iRVZero := by
    simpa [BoundedFormula.realize_imp, TrivCase.pInK_realize, TrivCase.realize_tKNeg,
      realize_tv, ha'] using h
  exact hh.imp id Subtype.ext

theorem negK_zero : negK (zeroRV (M := M)) = zeroRV := by
  have hm : allSortedK (fun _ : Fin 1 => .rv)
      (pEq (tKAdd &0 (tKNeg &0)) tRVZero) ∈ Axioms.ACVF :=
    kField_mem (by
      rw [show (fun _ : Fin 1 => SortTag.rv) = ![SortTag.rv] from by funext i; fin_cases i; rfl]
      simp [Axioms.kField, Axioms.ofList])
  have h := allK_realize hm ![iRVZero (M := M)] (by intro i; fin_cases i; exact Or.inr rfl)
  have hh : addK zeroRV (negK (zeroRV (M := M))) = zeroRV := by
    apply Subtype.ext
    change iKAdd iRVZero (TrivCase.iKNeg (iRVZero (M := M))) = iRVZero
    simpa only [pEq, BoundedFormula.realize_bdEqual, TrivCase.realize_tKAdd,
      TrivCase.realize_tKNeg, realize_tRVZero, RVCalc.realize_var_inr,
      Matrix.cons_val_zero, Matrix.head_cons] using h
  rwa [zero_addK _ (negK_inK _ (Or.inr rfl))] at hh

theorem addK_junk (a b : RVSort M) (h : ¬ inK a ∨ ¬ inK b) : addK a b = zeroRV := by
  have hh := allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv])
    (φ := ((∼(pInK &0) ⊔ ∼(pInK &1)) ⟹ pEq (tKAdd &0 &1) tRVZero))
    (mem_ACVF_repairRV (s := Axioms.kJunkZero)
      (by simp [Axioms.repairRV, Axioms.ofList]))
    ![a.1, b.1] (by intro i; fin_cases i <;> simp [a.2, b.2])
  have h' : ¬ (iUnits a.1 ∨ a.1 = iRVZero) ∨ ¬ (iUnits b.1 ∨ b.1 = iRVZero) :=
    h.imp (fun ha hc => ha (hc.imp id Subtype.ext))
      (fun hb hc => hb (hc.imp id Subtype.ext))
  apply Subtype.ext
  have hh' : (¬ (iUnits a.1 ∨ a.1 = iRVZero) ∨ ¬ (iUnits b.1 ∨ b.1 = iRVZero)) →
      iKAdd a.1 b.1 = iRVZero := by
    simpa [BoundedFormula.realize_imp, TrivCase.pInK_realize, TrivCase.realize_tKAdd,
      realize_tRVZero, realize_tv, pEq] using hh
  exact hh' h'

theorem negK_junk (a : RVSort M) (h : ¬ inK a) : negK a = zeroRV := by
  have hh := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (∼(pInK &0) ⟹ pEq (tKNeg &0) tRVZero))
    (mem_ACVF_repairRV (s := Axioms.kNegJunkZero)
      (by simp [Axioms.repairRV, Axioms.ofList]))
    ![a.1] (by intro i; fin_cases i; simpa using a.2)
  have h' : ¬ (iUnits a.1 ∨ a.1 = iRVZero) := fun hc => h (hc.imp id Subtype.ext)
  apply Subtype.ext
  change TrivCase.iKNeg a.1 = iRVZero
  simpa [BoundedFormula.realize_imp, TrivCase.pInK_realize, TrivCase.realize_tKNeg,
    realize_tRVZero, realize_tv, pEq, h'] using hh

theorem addK_units (a b : VFType (M := M)) (ha : iUnits (iRv a.1)) (hb : iUnits (iRv b.1)) :
    addK (encodedRv a) (encodedRv b) =
      if iUnits (iRv (a + b).1) then encodedRv (a + b) else zeroRV := by
  have h := allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf])
    (φ := (pUnits (tRv &0) ⟹ (pUnits (tRv &1) ⟹
      ((pUnits (tRv (tVFAdd &0 &1)) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) (tRv (tVFAdd &0 &1))) ⊓
        (∼(pUnits (tRv (tVFAdd &0 &1))) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) tRVZero)))))
    (mem_ACVF_repairRV (s := Axioms.kAddLink)
      (by simp [Axioms.repairRV, Axioms.ofList]))
    ![a.1, b.1] (by intro i; fin_cases i <;> simp [a.2, b.2])
  have hh : (iUnits (iRv (a + b).1) → iKAdd (iRv a.1) (iRv b.1) = iRv (a + b).1) ∧
      (¬ iUnits (iRv (a + b).1) → iKAdd (iRv a.1) (iRv b.1) = iRVZero) := by
    change (iUnits (iRv (iVFAdd a.1 b.1)) → iKAdd (iRv a.1) (iRv b.1) = iRv (iVFAdd a.1 b.1)) ∧
      (¬ iUnits (iRv (iVFAdd a.1 b.1)) → iKAdd (iRv a.1) (iRv b.1) = iRVZero)
    simpa [BoundedFormula.realize_imp, BoundedFormula.realize_inf, pUnits_realize,
      pEq, BoundedFormula.realize_bdEqual, realize_tRv, TrivCase.realize_tKAdd,
      realize_tVFAdd, realize_tRVZero, RVCalc.realize_var_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ha, hb] using h
  split_ifs with hs
  · exact Subtype.ext (hh.1 hs)
  · exact Subtype.ext (hh.2 hs)

theorem negK_units (a : VFType (M := M)) (ha : iUnits (iRv a.1)) :
    negK (encodedRv a) = encodedRv (-a) := by
  have h := allSorted_realize hM (ss := ![SortTag.vf])
    (φ := (pUnits (tRv &0) ⟹ pEq (tKNeg (tRv &0)) (tRv (tVFNeg &0))))
    RVCalc.mem_ACVF_kNegLink ![a.1] (by intro i; fin_cases i; simpa using a.2)
  apply Subtype.ext
  change TrivCase.iKNeg (iRv a.1) = iRv (iVFNeg a.1)
  simpa [BoundedFormula.realize_imp, pUnits_realize, pEq, BoundedFormula.realize_bdEqual,
    realize_tRv, TrivCase.realize_tKNeg, realize_tVFNeg, RVCalc.realize_var_inr,
    Matrix.cons_val_zero, ha] using h

section Assemble

variable (F : VFType (M := M) →+* VFType (M := N))
variable (hF : ∀ a b, VFValued.predV (F a) (F b) ↔ VFValued.predV a b)

include hF

theorem rvMap_units (a : RVSort M) : iUnits (rvMap F a).1 ↔ iUnits a.1 := by
  by_cases ha : a = zeroRV
  · subst a
    rw [rvMap_zero F hF]
    exact iff_of_false (fun h => units_ne_zero h rfl) (fun h => units_ne_zero h rfl)
  have ha0 : a.1 ≠ iRVZero := fun he => ha (Subtype.ext he)
  have hf0 : (rvMap F a).1 ≠ iRVZero :=
    fun he => ha ((rvMap_eq_zero F hF a).mp (Subtype.ext he))
  rw [RVCalc.units_iff_le_one hN (rvMap F a).2 hf0,
    RVCalc.units_iff_le_one hM a.2 ha0]
  change (iLe (oneRV (M := N)).1 (rvMap F a).1 ∧
    iLe (rvMap F a).1 (oneRV (M := N)).1) ↔
      (iLe (oneRV (M := M)).1 a.1 ∧ iLe a.1 (oneRV (M := M)).1)
  rw [← rvMap_one F hF, rvMap_order F hF, rvMap_order F hF]

theorem rvMap_inK (a : RVSort M) : inK (rvMap F a) ↔ inK a := by
  unfold inK
  rw [rvMap_units F hF, rvMap_eq_zero F hF]

theorem rvMap_addK (a b : RVSort M) :
    rvMap F (addK a b) = addK (rvMap F a) (rvMap F b) := by
  by_cases ha : inK a
  · by_cases hb : inK b
    · rcases ha with ha | rfl
      · rcases hb with hb | rfl
        · obtain ⟨x, rfl⟩ := encodedRv_surjective a
          obtain ⟨y, rfl⟩ := encodedRv_surjective b
          have hFx : iUnits (iRv (F x).1) := by
            have hu := (rvMap_units F hF (encodedRv x)).mpr ha
            rw [rvMap_encodedRv F hF] at hu
            change iUnits (iRv (F x).1) at hu
            exact hu
          have hFy : iUnits (iRv (F y).1) := by
            have hu := (rvMap_units F hF (encodedRv y)).mpr hb
            rw [rvMap_encodedRv F hF] at hu
            change iUnits (iRv (F y).1) at hu
            exact hu
          have hsum : iUnits (iRv (F x + F y).1) ↔ iUnits (iRv (x + y).1) := by
            have hu := rvMap_units F hF (encodedRv (x + y))
            rw [rvMap_encodedRv F hF, map_add] at hu
            change iUnits (iRv (F x + F y).1) ↔ iUnits (iRv (x + y).1) at hu
            exact hu
          rw [addK_units x y ha hb, rvMap_encodedRv F hF, rvMap_encodedRv F hF,
            addK_units (F x) (F y) hFx hFy]
          by_cases hs : iUnits (iRv (x+y).1)
          · rw [if_pos hs, if_pos (hsum.mpr hs), rvMap_encodedRv F hF, map_add]
          · rw [if_neg hs, if_neg (fun h => hs (hsum.mp h)), rvMap_zero F hF]
        · rw [addK_zero a (Or.inl ha), rvMap_zero F hF,
            addK_zero _ ((rvMap_inK F hF a).mpr (Or.inl ha))]
      · rw [zero_addK b hb, rvMap_zero F hF,
          zero_addK _ ((rvMap_inK F hF b).mpr hb)]
    · rw [addK_junk a b (Or.inr hb), rvMap_zero F hF,
        addK_junk _ _ (Or.inr (fun h => hb ((rvMap_inK F hF b).mp h)))]
  · rw [addK_junk a b (Or.inl ha), rvMap_zero F hF,
      addK_junk _ _ (Or.inl (fun h => ha ((rvMap_inK F hF a).mp h)))]

theorem rvMap_negK (a : RVSort M) : rvMap F (negK a) = negK (rvMap F a) := by
  by_cases ha : inK a
  · rcases ha with ha | rfl
    · obtain ⟨x, rfl⟩ := encodedRv_surjective a
      have hFx : iUnits (iRv (F x).1) := by
        have hu := (rvMap_units F hF (encodedRv x)).mpr ha
        rw [rvMap_encodedRv F hF] at hu
        change iUnits (iRv (F x).1) at hu
        exact hu
      rw [negK_units x ha, rvMap_encodedRv F hF, rvMap_encodedRv F hF,
        negK_units (F x) hFx, map_neg]
    · rw [negK_zero, rvMap_zero F hF, negK_zero]
  · rw [negK_junk a ha, rvMap_zero F hF,
      negK_junk _ (fun h => ha ((rvMap_inK F hF a).mp h))]

/-- All sorted language data are consequences of a valued-field homomorphism. -/
noncomputable def components : TypedModelMap.Components M N where
  vf := F
  rv := rvEmbedding F hF
  rv_zero := congrArg Subtype.val (rvMap_zero F hF)
  rv_one := congrArg Subtype.val (rvMap_one F hF)
  rv_mul a b := congrArg Subtype.val (rvMap_mul F hF a b)
  k_add a b := congrArg Subtype.val (rvMap_addK F hF a b)
  k_neg a := congrArg Subtype.val (rvMap_negK F hF a)
  rv_map a := congrArg Subtype.val (rvMap_encodedRv F hF a)
  units_iff := rvMap_units F hF
  order_iff := rvMap_order F hF

noncomputable def toSortedEmbedding : CanonicalStructure.SortedEmbedding M N :=
  (components F hF).toSortedEmbedding

noncomputable def toCanonicalEmbedding :
    @FirstOrder.Language.Embedding LRV M N
      (CanonicalStructure.normalize (M := M)) (CanonicalStructure.normalize (M := N)) :=
  (components F hF).toCanonicalEmbedding

end Assemble
end ValuedModelMap

#print axioms ValuedModelMap.same_fibers
#print axioms ValuedModelMap.rvMap_addK
#print axioms ValuedModelMap.toSortedEmbedding
#print axioms ValuedModelMap.toCanonicalEmbedding
