import Enc
import QF2Fragment
import FragmentTransfer

/-! Canonical totalization of the author-corrected tagged language, including
named RV inversion. This construction itself does not alter its theory or
well-sorted QE target. -/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace CanonicalStructure

variable {M : Type} [sM : LRV.Structure M]

def sortZero (s : SortTag) : M :=
  match s with
  | .vf => Transfer.iVFZero
  | .rv => iRVZero

/-- Correctly sorted applications retain their original interpretation.
Wrong-sort applications return the named zero of the result sort. -/
@[instance_reducible]
noncomputable def normalize : LRV.Structure M where
  funMap f xs := if ∀ i, sortEval (Fn.argSort f i) (xs i) then
    Structure.funMap (L := LRV) f xs else sortZero (Fn.resSort f)
  RelMap r xs := match r with
    | .memVF => Structure.RelMap (L := LRV) Rel.memVF xs
    | .memRV => Structure.RelMap (L := LRV) Rel.memRV xs
    | .memUnits => Structure.RelMap (L := LRV) Rel.memUnits xs
    | .rvLe => (∀ i, sortEval .rv (xs i)) ∧ Structure.RelMap (L := LRV) Rel.rvLe xs

@[simp] theorem sortEval_normalize (s : SortTag) (x : M) :
    @sortEval M (normalize (M := M)) s x ↔ sortEval s x := by
  cases s <;> rfl

@[simp] theorem normalize_unary (r : Rel 1) (xs : Fin 1 → M) :
    @Structure.RelMap LRV M (normalize (M := M)) 1 r xs ↔
      @Structure.RelMap LRV M sM 1 r xs := by
  cases r <;> rfl

theorem normalize_fun {k : ℕ} (f : Fn k) (xs : Fin k → M)
    (h : ∀ i, sortEval (Fn.argSort f i) (xs i)) :
    @Structure.funMap LRV M (normalize (M := M)) k f xs = Structure.funMap (L := LRV) f xs := by
  exact if_pos h

theorem normalize_rel {k : ℕ} (r : Rel k) (xs : Fin k → M)
    (h : ∀ i, sortEval (Rel.argSort r i) (xs i)) :
    @Structure.RelMap LRV M (normalize (M := M)) k r xs ↔ Structure.RelMap (L := LRV) r xs := by
  cases r with
  | memVF => rfl
  | memRV => rfl
  | memUnits => rfl
  | rvLe => exact and_iff_right h

private theorem binary_eta (xs : Fin 2 → M) : xs = ![xs 0, xs 1] := by
  funext i; fin_cases i <;> rfl

private theorem unary_eta (xs : Fin 1 → M) : xs = ![xs 0] := by
  funext i; fin_cases i; rfl

private theorem nullary_eta (xs : Fin 0 → M) : xs = fun i => i.elim0 := by
  funext i; exact i.elim0

@[simp] theorem realize_tRVInv {n : ℕ} (t : Tm n) (v : Empty ⊕ Fin n → M) :
    (tRVInv t).realize v = iRVInvFn (t.realize v) := by
  show Structure.funMap (L := LRV) Fn.rvInv
    (fun i => Term.realize v (![t] i)) = iRVInvFn (t.realize v)
  rw [show (fun i => Term.realize v (![t] i)) = ![t.realize v] from by
    funext i; fin_cases i; rfl]
  rfl

section Soundness

variable (hM : M ⊨ Axioms.ACVF)
include hM

/-- Closure under the named inverse, including at zero. -/
theorem rvInv_mem {a : M} (ha : iRV a) : iRV (iRVInvFn a) := by
  have h := Transfer.allSorted_realize hM
    (ss := ![SortTag.rv]) (φ := pRVsort (tRVInv &0))
    (Transfer.mem_ACVF_sortClosure (s := Axioms.sdRVInv)
      (by simp [Axioms.sortClosure, Axioms.ofList]))
    ![a] (by intro i; fin_cases i; simpa using ha)
  simpa only [Transfer.pRVsort_realize, realize_tRVInv, Transfer.realize_tv,
    Function.comp_apply, Term.realize_var, Sum.elim_inr, Matrix.cons_val_zero] using h

theorem rvInv_zero : iRVInvFn (iRVZero : M) = iRVZero := by
  have h := hM.realize_of_mem Axioms.rvInvZero
    (Transfer.mem_ACVF_repairRV (s := Axioms.rvInvZero)
      (by simp [Axioms.repairRV, Axioms.ofList]))
  simpa [Axioms.rvInvZero, Sentence.Realize, Formula.Realize, pEq, realize_tRVInv,
    Transfer.realize_tRVZero] using h

theorem rvInv_mul {a : M} (ha : iRV a) (ha0 : a ≠ iRVZero) :
    iRVMul (iRVInvFn a) a = iRVOne := by
  have h := Transfer.allSorted_realize hM
    (ss := ![SortTag.rv]) (φ := pRV &0 ⟹ pEq (tRVMul (tRVInv &0) &0) tRVOne)
    (Transfer.mem_ACVF_repairRV (s := Axioms.rvInvMul)
      (by simp [Axioms.repairRV, Axioms.ofList]))
    ![a] (by intro i; fin_cases i; simpa using ha)
  have h' : a ≠ iRVZero → iRVMul (iRVInvFn a) a = iRVOne := by
    simpa [Transfer.pRV_realize, pEq, Transfer.realize_tRVMul, realize_tRVInv,
      Transfer.realize_tRVOne_T, Transfer.realize_tv, Matrix.cons_val_zero] using h
  exact h' ha0

/-- The new symbol agrees with the inverse already used by the algebraic API. -/
theorem rvInv_eq_chosen {a : M} (ha : iRV a) :
    iRVInvFn a = Transfer.iRVInv hM a := by
  by_cases ha0 : a = iRVZero
  · subst a
    rw [rvInv_zero hM, Transfer.iRVInv, dif_neg (by intro h; exact h.2 rfl)]
  · exact Transfer.rv_mul_left_cancel_of_model hM (rvInv_mem hM ha) ha ha0
      (Transfer.iRVInv_mem hM ha)
      ((rvInv_mul hM ha ha0).trans (Transfer.iRVInv_mul_cancel hM ha ha0).symm)

theorem kAdd_mem {a b : M} (ha : iRV a) (hb : iRV b) : iRV (iKAdd a b) := by
  classical
  by_cases hka : iUnits a ∨ a = iRVZero
  · by_cases hkb : iUnits b ∨ b = iRVZero
    · have h := Transfer.allSorted_realize hM
        (ss := ![SortTag.rv, SortTag.rv])
        (φ := (pInK &0 ⟹ (pInK &1 ⟹ pInK (tKAdd &0 &1))))
        (Transfer.mem_ACVF_sortClosure (s := Axioms.sdKAdd)
          (by simp [Axioms.sortClosure, Axioms.ofList]))
        ![a, b] (by intro i; fin_cases i <;> simp [ha, hb])
      simp only [BoundedFormula.realize_imp, TrivCase.pInK_realize,
        TrivCase.realize_tKAdd, Transfer.realize_tv,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
      exact Transfer.iRV_of_inK hM (h hka hkb)
    · have h := Transfer.allSorted_realize hM
        (ss := ![SortTag.rv, SortTag.rv])
        (φ := ((∼(pInK &0) ⊔ ∼(pInK &1)) ⟹ pEq (tKAdd &0 &1) tRVZero))
        (Transfer.mem_ACVF_repairRV (s := Axioms.kJunkZero)
          (by simp [Axioms.repairRV, Axioms.ofList]))
        ![a, b] (by intro i; fin_cases i <;> simp [ha, hb])
      have heq : iKAdd a b = iRVZero := by
        simpa [BoundedFormula.realize_imp, TrivCase.pInK_realize,
          TrivCase.realize_tKAdd, Transfer.realize_tRVZero,
          Transfer.realize_tv, pEq, hkb] using h
      rw [heq]; exact Transfer.rv_zero_mem hM
  · have h := Transfer.allSorted_realize hM
      (ss := ![SortTag.rv, SortTag.rv])
      (φ := ((∼(pInK &0) ⊔ ∼(pInK &1)) ⟹ pEq (tKAdd &0 &1) tRVZero))
      (Transfer.mem_ACVF_repairRV (s := Axioms.kJunkZero)
        (by simp [Axioms.repairRV, Axioms.ofList]))
      ![a, b] (by intro i; fin_cases i <;> simp [ha, hb])
    have heq : iKAdd a b = iRVZero := by
      simpa [BoundedFormula.realize_imp, TrivCase.pInK_realize,
        TrivCase.realize_tKAdd, Transfer.realize_tRVZero,
        Transfer.realize_tv, pEq, hka] using h
    rw [heq]; exact Transfer.rv_zero_mem hM

theorem kNeg_mem {a : M} (ha : iRV a) : iRV (TrivCase.iKNeg a) := by
  classical
  by_cases hka : iUnits a ∨ a = iRVZero
  · have h := Transfer.allSorted_realize hM
      (ss := ![SortTag.rv]) (φ := (pInK &0 ⟹ pInK (tKNeg &0)))
      (Transfer.mem_ACVF_sortClosure (s := Axioms.sdKNeg)
        (by simp [Axioms.sortClosure, Axioms.ofList]))
      ![a] (by intro i; fin_cases i; simpa using ha)
    simp only [BoundedFormula.realize_imp, TrivCase.pInK_realize,
      TrivCase.realize_tKNeg, Transfer.realize_tv,
      Matrix.cons_val_zero] at h
    exact Transfer.iRV_of_inK hM (h hka)
  · have h := Transfer.allSorted_realize hM
      (ss := ![SortTag.rv]) (φ := (∼(pInK &0) ⟹ pEq (tKNeg &0) tRVZero))
      (Transfer.mem_ACVF_repairRV (s := Axioms.kNegJunkZero)
        (by simp [Axioms.repairRV, Axioms.ofList]))
      ![a] (by intro i; fin_cases i; simpa using ha)
    have heq : TrivCase.iKNeg a = iRVZero := by
      simpa [BoundedFormula.realize_imp, TrivCase.pInK_realize,
        TrivCase.realize_tKNeg, Transfer.realize_tRVZero,
        Transfer.realize_tv, pEq, hka] using h
    rw [heq]; exact Transfer.rv_zero_mem hM

/-- The missing general sort-soundness interface follows from the theory, including
the repaired residue-operation totalizations on the RV sort. -/
theorem function_sort {k : ℕ} (f : Fn k) (xs : Fin k → M)
    (h : ∀ i, sortEval (Fn.argSort f i) (xs i)) :
    sortEval (Fn.resSort f) (Structure.funMap (L := LRV) f xs) := by
  cases f with
  | vfZero => rw [nullary_eta xs]; exact Transfer.vf_zero_mem hM
  | vfOne => rw [nullary_eta xs]; exact Transfer.vf_one_mem hM
  | rvZero => rw [nullary_eta xs]; exact Transfer.rv_zero_mem hM
  | rvOne => rw [nullary_eta xs]; exact Transfer.rv_one_mem hM
  | vfAdd => rw [binary_eta xs]; exact Transfer.vf_add_mem hM (h 0) (h 1)
  | vfMul => rw [binary_eta xs]; exact Transfer.vf_mul_mem hM (h 0) (h 1)
  | vfNeg => rw [unary_eta xs]; exact Transfer.vf_neg_mem hM (h 0)
  | rvMul => rw [binary_eta xs]; exact Transfer.rv_mul_mem hM (h 0) (h 1)
  | rvInv => rw [unary_eta xs]; exact rvInv_mem hM (h 0)
  | kAdd => rw [binary_eta xs]; exact kAdd_mem hM (h 0) (h 1)
  | kNeg => rw [unary_eta xs]; exact kNeg_mem hM (h 0)
  | rvMap => rw [unary_eta xs]; exact Transfer.rv_mem hM (h 0)

theorem term_sort {α : Type} {n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag)
    (v : α → M) (xs : Fin n → M)
    (hv : ∀ a, sortEval (sα a) (v a)) (hx : ∀ i, sortEval (sn i) (xs i))
    (t : LRV.Term (α ⊕ Fin n)) {s : SortTag} (ht : TmSort sα sn t = some s) :
    sortEval s (t.realize (Sum.elim v xs)) := by
  induction t generalizing s with
  | var a =>
      cases a with
      | inl a => cases Option.some.inj ht; exact hv a
      | inr i => cases Option.some.inj ht; exact hx i
  | func f ts ih =>
      obtain ⟨hargs, rfl⟩ := (tmSort_func_iff sα sn f ts).mp ht
      exact function_sort hM f _ (fun i => ih i (hargs i))

theorem term_normalize {α : Type} {n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag)
    (v : α → M) (xs : Fin n → M)
    (hv : ∀ a, sortEval (sα a) (v a)) (hx : ∀ i, sortEval (sn i) (xs i))
    (t : LRV.Term (α ⊕ Fin n)) {s : SortTag} (ht : TmSort sα sn t = some s) :
    @Term.realize LRV M (normalize (M := M)) (α ⊕ Fin n) (Sum.elim v xs) t =
      t.realize (Sum.elim v xs) := by
  induction t generalizing s with
  | var a => rfl
  | func f ts ih =>
      obtain ⟨hargs, rfl⟩ := (tmSort_func_iff sα sn f ts).mp ht
      change @Structure.funMap LRV M (normalize (M := M)) _ f
        (fun i => @Term.realize LRV M (normalize (M := M)) _ (Sum.elim v xs) (ts i)) = _
      have heq : (fun i => @Term.realize LRV M (normalize (M := M)) _ (Sum.elim v xs) (ts i)) =
          fun i => (ts i).realize (Sum.elim v xs) := funext fun i => ih i (hargs i)
      rw [heq]
      exact normalize_fun f _ (fun i => term_sort hM sα sn v xs hv hx (ts i) (hargs i))

end Soundness

section Formulas

variable (hM : M ⊨ Axioms.ACVF)
include hM

/-- Canonical totalization preserves the realization of every well-sorted formula
at assignments respecting its declared sorts. -/
theorem realize_normalize {α : Type} (sα : α → SortTag) (v : α → M)
    (hv : ∀ a, sortEval (sα a) (v a)) :
    ∀ {n : ℕ} (φ : LRV.BoundedFormula α n) (sn : Fin n → SortTag) (xs : Fin n → M),
      WellSorted sα sn φ → (∀ i, sortEval (sn i) (xs i)) →
      (@BoundedFormula.Realize LRV M (normalize (M := M)) α n φ v xs ↔ φ.Realize v xs) := by
  intro n φ
  refine BoundedFormula.rec (motive := fun k φ =>
    ∀ (sn : Fin k → SortTag) (xs : Fin k → M), WellSorted sα sn φ →
      (∀ i, sortEval (sn i) (xs i)) →
      (@BoundedFormula.Realize LRV M (normalize (M := M)) α k φ v xs ↔ φ.Realize v xs))
    ?_ ?_ ?_ ?_ ?_ φ
  · intro k sn xs hφ hx
    rfl
  · intro k t u sn xs hφ hx
    cases hφ with
    | equal _ ht hu =>
        change (@Term.realize LRV M (normalize (M := M)) _ (Sum.elim v xs) t =
          @Term.realize LRV M (normalize (M := M)) _ (Sum.elim v xs) u) ↔ _
        rw [term_normalize hM sα sn v xs hv hx t ht,
          term_normalize hM sα sn v xs hv hx u hu]
        rfl
  · intro k l r ts sn xs hφ hx
    cases hφ with
    | rel _ _ _ hts =>
        change @Structure.RelMap LRV M (normalize (M := M)) l r
          (fun i => @Term.realize LRV M (normalize (M := M)) _ (Sum.elim v xs) (ts i)) ↔ _
        have heq : (fun i => @Term.realize LRV M (normalize (M := M)) _
              (Sum.elim v xs) (ts i)) = fun i => (ts i).realize (Sum.elim v xs) :=
          funext fun i => term_normalize hM sα sn v xs hv hx (ts i) (hts i)
        rw [heq]
        exact normalize_rel r _ (fun i => term_sort hM sα sn v xs hv hx (ts i) (hts i))
  · intro k φ ψ ihφ ihψ sn xs hφψ hx
    cases hφψ with
    | imp _ hφ hψ =>
        change ((@BoundedFormula.Realize LRV M (normalize (M := M)) α k φ v xs →
          @BoundedFormula.Realize LRV M (normalize (M := M)) α k ψ v xs) ↔
          (φ.Realize v xs → ψ.Realize v xs))
        exact imp_congr (ihφ sn xs hφ hx) (ihψ sn xs hψ hx)
  · intro k χ ih sn xs hφ hx
    cases hφ with
    | @all _ _ s _ hχ hg hj =>
        change (∀ a : M, @BoundedFormula.Realize LRV M (normalize (M := M)) α (k + 1)
          χ v (Fin.snoc xs a)) ↔ ∀ a : M, χ.Realize v (Fin.snoc xs a)
        apply forall_congr'
        intro a
        by_cases ha : sortEval s a
        · exact ih (Fin.snoc sn s) (Fin.snoc xs a) hχ (TransferComp.sorted_snoc hx ha)
        · have hOrig : χ.Realize v (Fin.snoc xs a) :=
            TransferComp.guardTrue_realize s hj v (Fin.snoc xs a)
              (by simpa only [Fin.snoc_last] using ha)
          have hNorm : @BoundedFormula.Realize LRV M (normalize (M := M)) α (k + 1)
              χ v (Fin.snoc xs a) := by
            apply @TransferComp.guardTrue_realize M (normalize (M := M)) α s
              (k + 1) (Fin.last k) χ hj v (Fin.snoc xs a)
            simpa only [Fin.snoc_last, sortEval_normalize] using ha
          exact iff_of_true hNorm hOrig

theorem sentence_normalize (φ : LRV.Sentence) (hφ : Audit.WSSent φ) :
    @Sentence.Realize LRV M (normalize (M := M)) φ ↔ M ⊨ φ := by
  simpa only [Sentence.Realize, Formula.Realize] using
    realize_normalize hM (fun a : Empty => a.elim) (default : Empty → M)
    (fun a => a.elim) φ (fun i : Fin 0 => i.elim0) (default : Fin 0 → M)
    hφ (fun i => i.elim0)

/-- The three encoding-discipline axioms rejected by WellSorted only use the
globally unchanged predicates; all remaining axioms transfer by the syntax audit. -/
theorem normalized_model : @Theory.Model LRV M (normalize (M := M)) Axioms.ACVF := by
  apply (@Theory.model_iff LRV M (normalize (M := M)) Axioms.ACVF).mpr
  intro φ hφ
  by_cases hcov : φ = Axioms.sdCover
  · subst φ
    simpa [Sentence.Realize, Axioms.sdCover, allOne,
      pVF, pRVsort, Relations.boundedFormula₁, Relations.boundedFormula, BoundedFormula.realize_rel,
      BoundedFormula.Realize, Term.realize, normalize] using hM.realize_of_mem _ hφ
  by_cases hdis : φ = Axioms.sdDisjoint
  · subst φ
    simpa [Sentence.Realize, Axioms.sdDisjoint, allOne,
      pVF, pRVsort, Relations.boundedFormula₁, Relations.boundedFormula, BoundedFormula.realize_rel,
      BoundedFormula.Realize, Term.realize, normalize] using hM.realize_of_mem _ hφ
  by_cases hunits : φ = Axioms.sdUnits
  · subst φ
    simpa [Sentence.Realize, Axioms.sdUnits, allOne,
      pUnits, pRVsort, Relations.boundedFormula₁, Relations.boundedFormula, BoundedFormula.realize_rel,
      BoundedFormula.Realize, Term.realize, normalize] using hM.realize_of_mem _ hφ
  exact (sentence_normalize hM φ (Audit.wellSorted_ACVF hφ hcov hdis hunits)).mpr
    (hM.realize_of_mem _ hφ)

end Formulas

/-- The off-sort choices used by the canonical totalization. The three unary
predicates retain the constraints already imposed by the sort axioms. -/
def IsCanonical : Prop :=
  (∀ {k : ℕ} (f : Fn k) (xs : Fin k → M),
      ¬ (∀ i, sortEval (Fn.argSort f i) (xs i)) →
      Structure.funMap (L := LRV) f xs = sortZero (Fn.resSort f)) ∧
  (∀ xs : Fin 2 → M, ¬ (∀ i, sortEval .rv (xs i)) →
      ¬ Structure.RelMap (L := LRV) Rel.rvLe xs)

@[simp] theorem sortZero_normalize (s : SortTag) :
    @sortZero M (normalize (M := M)) s = sortZero s := by
  cases s with
  | vf => exact normalize_fun Fn.vfZero (fun i => i.elim0) (fun i => i.elim0)
  | rv => exact normalize_fun Fn.rvZero (fun i => i.elim0) (fun i => i.elim0)

theorem normalize_isCanonical : @IsCanonical M (normalize (M := M)) := by
  constructor
  · intro k f xs h
    have h' : ¬ (∀ i, sortEval (Fn.argSort f i) (xs i)) := by
      simpa only [sortEval_normalize] using h
    change (if ∀ i, sortEval (Fn.argSort f i) (xs i) then
      Structure.funMap (L := LRV) f xs else sortZero (Fn.resSort f)) = _
    rw [if_neg h', sortZero_normalize]
  · intro xs h
    have h' : ¬ (∀ i, sortEval .rv (xs i)) := by
      simpa only [sortEval_normalize] using h
    exact fun hrel => h' hrel.1

/-- Uniform well-sorted QE on the canonical models. The formula witness is chosen
before the model, exactly as in the encoding's HasQE definition. -/
def HasQEOnCanonical (T : LRV.Theory) : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (φ : LRV.BoundedFormula α n), WellSorted sα sn φ →
    ∃ ψ : LRV.BoundedFormula α n, ψ.IsQF ∧ WellSorted sα sn ψ ∧
      ∀ (M : Type) [LRV.Structure M], M ⊨ T → IsCanonical (M := M) →
        ∀ (v : α → M) (xs : Fin n → M),
          (∀ a, sortEval (sα a) (v a)) → (∀ i, sortEval (sn i) (xs i)) →
          (φ.Realize v xs ↔ ψ.Realize v xs)

/-- Canonical totalization is a conservative reduction for the well-sorted QE target;
this theorem proves no quantifier-elimination input by itself. -/
theorem hasQE_of_canonical (h : HasQEOnCanonical Axioms.ACVF) : HasQE Axioms.ACVF := by
  intro α sα n sn φ hφ
  obtain ⟨ψ, hq, hψ, heq⟩ := h α sα n sn φ hφ
  refine ⟨ψ, hq, hψ, ?_⟩
  intro M sM hM v xs hv hx
  have hv' : ∀ a, @sortEval M (normalize (M := M)) (sα a) (v a) := by
    simpa only [sortEval_normalize] using hv
  have hx' : ∀ i, @sortEval M (normalize (M := M)) (sn i) (xs i) := by
    simpa only [sortEval_normalize] using hx
  have hcanon := @heq M (normalize (M := M)) (normalized_model hM)
    normalize_isCanonical v xs hv' hx'
  exact (realize_normalize hM sα v hv φ sn xs hφ hx).symm.trans
    (hcanon.trans (realize_normalize hM sα v hv ψ sn xs hψ hx))

end CanonicalStructure

#print axioms CanonicalStructure.rvInv_mul
#print axioms CanonicalStructure.rvInv_eq_chosen
#print axioms CanonicalStructure.term_normalize
#print axioms CanonicalStructure.realize_normalize
#print axioms CanonicalStructure.normalized_model
#print axioms CanonicalStructure.normalize_isCanonical
#print axioms CanonicalStructure.hasQE_of_canonical
