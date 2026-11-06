import Section6.ExpandedLogic

/-! Finite free-variable restriction in the actual expanded syntax,
preserving both the sorted fragment and absence of VF quantifiers. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.ExpandedRestriction
open RVTermSupport ExpandedLogic

variable {E : _root_.FirstOrder.Language.{0, 0}} {I J : Type} [DecidableEq I]

theorem term_sort {n : ℕ} (sI : I → SortTag) (sJ : J → SortTag) (sn : Fin n → SortTag)
    (t : (Expanded E).Term (I ⊕ Fin n)) (f : t.varFinsetLeft → J)
    (hf : ∀ a, sJ (f a) = sI a.val) :
    termSort (Sum.elim sJ sn) (t.restrictVarLeft f) = termSort (Sum.elim sI sn) t := by
  induction t with
  | var a =>
    cases a with
    | inl a => exact congrArg some (hf ⟨a, by simp⟩)
    | inr a => rfl
  | func g ts ih =>
    simp only [Term.restrictVarLeft, termSort]
    congr 1
    apply propext
    apply forall_congr'
    intro i
    rw [ih i _ (fun a => hf _)]

theorem guard {n : ℕ} (s : SortTag) (i : Fin n)
    (f : (ExpandedLogic.guardAtom (E := E) (α := I) s i).freeVarFinset → J) :
    (ExpandedLogic.guardAtom (E := E) (α := I) s i).restrictFreeVar f = ExpandedLogic.guardAtom (E := E) (α := J) s i := by
  unfold ExpandedLogic.guardAtom
  simp only [BoundedFormula.restrictFreeVar]
  congr 1
  funext j
  fin_cases j
  rfl

theorem isVFQF {n : ℕ} (φ : (Expanded E).BoundedFormula I n) (hφ : ExpandedLogic.IsVFQF φ)
    (f : φ.freeVarFinset → J) : ExpandedLogic.IsVFQF (φ.restrictFreeVar f) := by
  induction hφ with
  | falsum => exact .falsum
  | atomic h => cases h with
    | equal t u => exact .atomic (.equal _ _)
    | rel r ts => exact .atomic (.rel _ _)
  | imp hφ hψ ihφ ihψ => exact .imp (ihφ _) (ihψ _)
  | @all_rv n φ hφ ih =>
    have h := ih (f ∘ Set.inclusion Finset.subset_union_right)
    simpa only [ExpandedLogic.allSorted, BoundedFormula.restrictFreeVar, guard] using h.all_rv

theorem wellSorted {n : ℕ} (sI : I → SortTag) (sJ : J → SortTag) (sn : Fin n → SortTag)
    (φ : (Expanded E).BoundedFormula I n) (hφ : ExpandedLogic.WellSorted sI sn φ)
    (f : φ.freeVarFinset → J) (hf : ∀ a, sJ (f a) = sI a.val) :
    ExpandedLogic.WellSorted sJ sn (φ.restrictFreeVar f) := by
  induction hφ with
  | falsum sn => exact .falsum _
  | equal ht hu =>
    exact .equal ((term_sort sI sJ _ _ _ (fun a => hf _)).trans ht)
      ((term_sort sI sJ _ _ _ (fun a => hf _)).trans hu)
  | rel r ts hts =>
    apply ExpandedLogic.WellSorted.rel
    intro i
    exact (term_sort sI sJ _ _ _ (fun a => hf _)).trans (hts i)
  | imp hφ hψ ihφ ihψ => exact .imp (ihφ _ (fun a => hf _)) (ihψ _ (fun a => hf _))
  | @all n sn s φ hφ ih =>
    have h := ih (f ∘ Set.inclusion Finset.subset_union_right) (fun a => hf _)
    simpa only [ExpandedLogic.allSorted, BoundedFormula.restrictFreeVar, guard] using h.all

end SpecialTransformations.Section6.ExpandedRestriction

namespace SpecialTransformations.Section6.ExpandedFreeRenaming
open RVTermSupport

variable {E : _root_.FirstOrder.Language.{0, 0}} {I J : Type}

def rename (f : I → J) {n : ℕ} (φ : (Expanded E).BoundedFormula I n) :
    (Expanded E).BoundedFormula J n :=
  φ.mapTermRel (g := id) (fun _ t => t.relabel (Sum.map f id)) (fun _ => id) (fun _ => id)

theorem guard (f : I → J) {n : ℕ} (s : SortTag) (i : Fin n) :
    rename f (ExpandedLogic.guardAtom (E := E) s i) =
      ExpandedLogic.guardAtom (E := E) s i := by
  change BoundedFormula.rel (ExpandedLogic.sortRelation s) _ = _
  congr 1
  funext j
  fin_cases j
  rfl

theorem allSorted (f : I → J) {n : ℕ} (s : SortTag)
    (φ : (Expanded E).BoundedFormula I (n + 1)) :
    rename f (ExpandedLogic.allSorted s φ) = ExpandedLogic.allSorted s (rename f φ) := by
  change (rename f (ExpandedLogic.guardAtom s (Fin.last n)) ⟹ rename f φ).all = _
  rw [guard]
  rfl

theorem isVFQF (f : I → J) {n : ℕ} (φ : (Expanded E).BoundedFormula I n)
    (hφ : ExpandedLogic.IsVFQF φ) : ExpandedLogic.IsVFQF (rename f φ) := by
  induction hφ with
  | falsum => exact .falsum
  | atomic h => cases h with
    | equal t u => exact .atomic (.equal _ _)
    | rel r ts => exact .atomic (.rel _ _)
  | imp hφ hψ ihφ ihψ => exact .imp ihφ ihψ
  | all_rv hφ ih => rw [allSorted]; exact .all_rv ih

theorem term_sort (f : I → J) (sI : I → SortTag) (sJ : J → SortTag)
    (hf : ∀ i, sJ (f i) = sI i) {n : ℕ} (sn : Fin n → SortTag)
    (t : (Expanded E).Term (I ⊕ Fin n)) :
    termSort (Sum.elim sJ sn) (t.relabel (Sum.map f id)) =
      termSort (Sum.elim sI sn) t := by
  apply GuardedLift.termSort_relabel
  intro j
  cases j with
  | inl i => exact hf i
  | inr i => rfl

theorem wellSorted (f : I → J) (sI : I → SortTag) (sJ : J → SortTag)
    (hf : ∀ i, sJ (f i) = sI i) {n : ℕ} (sn : Fin n → SortTag)
    (φ : (Expanded E).BoundedFormula I n) (hφ : ExpandedLogic.WellSorted sI sn φ) :
    ExpandedLogic.WellSorted sJ sn (rename f φ) := by
  induction hφ with
  | falsum sn => exact .falsum _
  | equal ht hu =>
    exact .equal ((term_sort f sI sJ hf _ _).trans ht) ((term_sort f sI sJ hf _ _).trans hu)
  | rel r ts hts =>
    apply ExpandedLogic.WellSorted.rel
    intro i
    exact (term_sort f sI sJ hf _ _).trans (hts i)
  | imp hφ hψ ihφ ihψ => exact .imp ihφ ihψ
  | all hφ ih => rw [allSorted]; exact .all ih

theorem realize (f : I → J) {n : ℕ} (φ : (Expanded E).BoundedFormula I n)
    {M : Type} [(Expanded E).Structure M] (v : J → M) (x : Fin n → M) :
    (rename f φ).Realize v x ↔ φ.Realize (v ∘ f) x := by
  apply BoundedFormula.realize_mapTermRel_id
  · intro k t y
    simp only [Term.realize_relabel, Sum.elim_comp_map, Function.comp_id]
  · intro k r y
    rfl

end SpecialTransformations.Section6.ExpandedFreeRenaming

namespace SpecialTransformations.Section6.FiniteContextLogic
open RVTermSupport

/-- The finitary one-step statement. The next theorem discharges the
passage to arbitrary free-variable types by actual finite support. -/
def FiniteOneStep {E : _root_.FirstOrder.Language.{0, 0}} (T : (Expanded E).Theory) : Prop :=
  ∀ (I : Type) [Finite I] (s : I → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (φ : (Expanded E).BoundedFormula I (n + 1)),
    ExpandedLogic.WellSorted s (Fin.snoc sn .vf) φ → ExpandedLogic.IsVFQF φ →
    ∃ ψ : (Expanded E).BoundedFormula I n,
      ExpandedLogic.IsVFQF ψ ∧ ExpandedLogic.WellSorted s sn ψ ∧
      ∀ (M : Type) [(Expanded E).Structure M], M ⊨ T → ∀ (v : I → M) (x : Fin n → M),
        (∀ i, ExpandedLogic.tagEval (E := E) (s i) (v i)) →
        (∀ i, ExpandedLogic.tagEval (E := E) (sn i) (x i)) →
        ((∃ a : M, ExpandedLogic.tagEval (E := E) .vf a ∧ φ.Realize v (Fin.snoc x a)) ↔
          ψ.Realize v x)

theorem oneStep_of_finite {E : _root_.FirstOrder.Language.{0, 0}} (T : (Expanded E).Theory)
    (hstep : FiniteOneStep T) : ExpandedLogic.OneStep T := by
  intro I s n sn φ hsφ hφ
  let θ := φ.restrictFreeVar (id : φ.freeVarFinset → φ.freeVarFinset)
  have hθ : ExpandedLogic.IsVFQF θ := ExpandedRestriction.isVFQF φ hφ id
  have hsθ : ExpandedLogic.WellSorted (s ∘ Subtype.val) (Fin.snoc sn .vf) θ :=
    ExpandedRestriction.wellSorted s (s ∘ Subtype.val) (Fin.snoc sn .vf) φ hsφ id (fun _ => rfl)
  obtain ⟨ψ, hψ, hsψ, he⟩ := hstep φ.freeVarFinset (s ∘ Subtype.val) n sn θ hsθ hθ
  refine ⟨ExpandedFreeRenaming.rename Subtype.val ψ,
    ExpandedFreeRenaming.isVFQF Subtype.val ψ hψ,
    ExpandedFreeRenaming.wellSorted Subtype.val (s ∘ Subtype.val) s (fun _ => rfl) sn ψ hsψ, ?_⟩
  intro M _ hM v x hv hx
  rw [ExpandedFreeRenaming.realize]
  have hθsem (y : Fin (n + 1) → M) :
      θ.Realize (v ∘ Subtype.val) y ↔ φ.Realize v y :=
    BoundedFormula.realize_restrictFreeVar v (fun _ => rfl)
  refine Iff.trans ?_ (he M hM (v ∘ Subtype.val) x (fun i => hv i.val) hx)
  apply exists_congr
  intro a
  exact and_congr Iff.rfl (hθsem (Fin.snoc x a)).symm

theorem hasVFQE_of_finite {E : _root_.FirstOrder.Language.{0, 0}} (T : (Expanded E).Theory)
    (hstep : FiniteOneStep T) : ExpandedLogic.HasVFQE T :=
  ExpandedLogic.hasVFQE_of_oneStep T (oneStep_of_finite T hstep)

end SpecialTransformations.Section6.FiniteContextLogic

