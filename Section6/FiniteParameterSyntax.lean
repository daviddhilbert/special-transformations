import Section6.RVAbstraction

/-! Finite extraction of the original parameter names in a normalized
RV-fragment formula. The two finite lists contain VF and RV parameters
separately. Extraction is syntactic and works below every RV binder. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.FiniteParameterSyntax
open RVTermSupport RVAbstraction

variable {E : Language} {V R V' R' : Type}

theorem termSort_restrict [DecidableEq V] [DecidableEq R] {k : ℕ}
    (t : (Expanded E).Term ((V ⊕ R) ⊕ Fin k))
    (f : t.varFinsetLeft → V' ⊕ R')
    (hf : ∀ a, Sum.elim (fun _ => SortTag.vf) (fun _ => .rv) (f a) =
      Sum.elim (fun _ => SortTag.vf) (fun _ => .rv) a.val) :
    termSort sourceSort (t.restrictVarLeft f) = termSort sourceSort t := by
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

theorem guard_restrict {I J : Type} [DecidableEq I] (k : ℕ)
    (f : (RVAbstraction.guard (E := E) (I := I) k).freeVarFinset → J) :
    (RVAbstraction.guard (E := E) (I := I) k).restrictFreeVar f =
      RVAbstraction.guard (E := E) (I := J) k := by
  unfold RVAbstraction.guard
  simp only [BoundedFormula.restrictFreeVar]
  congr 1
  funext i
  fin_cases i
  rfl

theorem fragment_restrict [DecidableEq V] [DecidableEq R] {k : ℕ}
    (φ : (Expanded E).BoundedFormula (V ⊕ R) k)
    (hφ : Fragment φ) (f : φ.freeVarFinset → V' ⊕ R')
    (hf : ∀ a, Sum.elim (fun _ => SortTag.vf) (fun _ => .rv) (f a) =
      Sum.elim (fun _ => SortTag.vf) (fun _ => .rv) a.val) :
    Fragment (φ.restrictFreeVar f) := by
  induction hφ with
  | falsum => exact .falsum
  | equal t u ht hu =>
    apply Fragment.equal
    · exact (termSort_restrict t _ (fun a => hf _)).trans ht
    · exact (termSort_restrict u _ (fun a => hf _)).trans hu
  | rel r ts hs =>
    apply Fragment.rel r
    intro i
    exact (termSort_restrict (ts i) _ (fun a => hf _)).trans (hs i)
  | imp hφ hψ ihφ ihψ =>
    exact .imp (ihφ _ (fun a => hf _)) (ihψ _ (fun a => hf _))
  | @all k φ hφ ih =>
    have h := ih (f ∘ Set.inclusion Finset.subset_union_right) (fun a => hf _)
    simpa only [BoundedFormula.restrictFreeVar, guard_restrict] using h.all

variable {PV PR B : Type} {n : ℕ}

def vfSupport (φ : (Expanded E).Formula ((PV ⊕ Fin n) ⊕ (PR ⊕ B))) : Finset PV :=
  φ.freeVarFinset.toLeft.toLeft

def rvSupport (φ : (Expanded E).Formula ((PV ⊕ Fin n) ⊕ (PR ⊕ B))) : Finset PR :=
  φ.freeVarFinset.toRight.toLeft

def vfEnumeration (φ : (Expanded E).Formula ((PV ⊕ Fin n) ⊕ (PR ⊕ B))) :
    Fin (vfSupport φ).card ≃ vfSupport φ := (Finset.equivFin _).symm

def rvEnumeration (φ : (Expanded E).Formula ((PV ⊕ Fin n) ⊕ (PR ⊕ B))) :
    Fin (rvSupport φ).card ≃ rvSupport φ := (Finset.equivFin _).symm

def replacement (φ : (Expanded E).Formula ((PV ⊕ Fin n) ⊕ (PR ⊕ B))) :
    φ.freeVarFinset → (Fin (vfSupport φ).card ⊕ Fin n) ⊕ (Fin (rvSupport φ).card ⊕ B)
  | ⟨.inl (.inl p), hp⟩ => .inl (.inl ((vfEnumeration φ).symm ⟨p, by
      simpa [vfSupport] using hp⟩))
  | ⟨.inl (.inr i), _⟩ => .inl (.inr i)
  | ⟨.inr (.inl p), hp⟩ => .inr (.inl ((rvEnumeration φ).symm ⟨p, by
      simpa [rvSupport] using hp⟩))
  | ⟨.inr (.inr b), _⟩ => .inr (.inr b)

def formula (φ : (Expanded E).Formula ((PV ⊕ Fin n) ⊕ (PR ⊕ B))) :
    (Expanded E).Formula ((Fin (vfSupport φ).card ⊕ Fin n) ⊕ (Fin (rvSupport φ).card ⊕ B)) :=
  φ.restrictFreeVar (replacement φ)

theorem formula_fragment (φ : (Expanded E).Formula ((PV ⊕ Fin n) ⊕ (PR ⊕ B)))
    (hφ : Fragment φ) : Fragment (formula φ) := by
  unfold formula
  apply fragment_restrict φ hφ (replacement φ)
  rintro ⟨a, ha⟩
  rcases a with (a | i) | (a | b) <;> rfl

theorem formula_realize {M : Type} [(Expanded E).Structure M]
    (φ : (Expanded E).Formula ((PV ⊕ Fin n) ⊕ (PR ⊕ B)))
    (c : PV → M) (x : Fin n → M) (d : PR → M) (b : B → M) :
    (formula φ).Realize (Sum.elim
      (Sum.elim (fun i => c (vfEnumeration φ i).val) x)
      (Sum.elim (fun i => d (rvEnumeration φ i).val) b)) ↔
        φ.Realize (Sum.elim (Sum.elim c x) (Sum.elim d b)) := by
  apply BoundedFormula.realize_restrictFreeVar (Sum.elim (Sum.elim c x) (Sum.elim d b))
  rintro ⟨a, ha⟩
  rcases a with (a | i) | (a | b)
  · simp only [replacement, Sum.elim_inl]
    congr 1
    exact congrArg Subtype.val ((vfEnumeration φ).apply_symm_apply _)
  · rfl
  · simp only [replacement, Sum.elim_inr, Sum.elim_inl]
    congr 1
    exact congrArg Subtype.val ((rvEnumeration φ).apply_symm_apply _)
  · rfl

end SpecialTransformations.Section6.FiniteParameterSyntax
