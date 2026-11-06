import Section6.FragmentCompactness
import Section6.ExpandedLogic

/-! Apply ordinary fragment compactness to the genuinely sorted expanded
language. Free-variable guards are finite and belong to the same Boolean
fragment. Thus ill-sorted assignments cause no gap in the compactness
argument. The valued-field application must still prove type invariance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.SortedFragment
open RVTermSupport ExpandedLogic FragmentCompactness

variable {E : _root_.FirstOrder.Language.{0, 0}} {α : Type}

def fragment (sα : α → SortTag) (φ : (Expanded E).Formula α) : Prop :=
  ExpandedLogic.IsVFQF φ ∧ ExpandedLogic.WellSorted sα (fun _ => .rv) φ

theorem fragment_boolean (sα : α → SortTag) : BooleanClosed (fragment (E := E) sα) where
  top := ⟨ExpandedLogic.IsVFQF.not .falsum, ExpandedLogic.WellSorted.not (.falsum _)⟩
  not h := ⟨h.1.not, h.2.not⟩
  inf hφ hψ :=
    ⟨ExpandedLogic.IsVFQF.not (ExpandedLogic.IsVFQF.imp hφ.1 hψ.1.not),
      ExpandedLogic.WellSorted.not (ExpandedLogic.WellSorted.imp hφ.2 hψ.2.not)⟩

def guardOne (sα : α → SortTag) (a : α) : (Expanded E).Formula α :=
  (sortRelation (sα a)).formula₁ (.var a)

theorem guardOne_mem (sα : α → SortTag) (a : α) :
    fragment (E := E) sα (guardOne (E := E) sα a) := by
  constructor
  · exact .atomic (.rel _ _)
  · apply ExpandedLogic.WellSorted.rel
    intro i
    fin_cases i
    cases h : sα a <;> simp [guardOne, Relations.formula₁, Relations.formula,
      Relations.boundedFormula, sortRelation, relationSort, Term.relabel, termSort, Rel.argSort, h]

theorem guardOne_realize (sα : α → SortTag) (a : α)
    {M : Type} [(Expanded E).Structure M] (v : α → M) :
    (guardOne (E := E) sα a).Realize v ↔ tagEval (E := E) (sα a) (v a) := by
  simp [guardOne, Relations.formula₁, Relations.formula, Relations.boundedFormula,
    Formula.Realize, BoundedFormula.Realize, Term.realize, Term.realize_relabel, tagEval]
  have he : (fun _ : Fin 1 => v a) = ![v a] := by
    funext i
    fin_cases i
    rfl
  rw [he]

def guards (sα : α → SortTag) (l : List α) : (Expanded E).Formula α :=
  (l.map (guardOne (E := E) sα)).foldr (· ⊓ ·) ⊤

theorem guards_mem (sα : α → SortTag) (l : List α) : fragment (E := E) sα (guards (E := E) sα l) := by
  induction l with
  | nil => exact (fragment_boolean (E := E) sα).top
  | cons a l ih => exact (fragment_boolean (E := E) sα).inf (guardOne_mem (E := E) sα a) ih

theorem guards_realize (sα : α → SortTag) (l : List α)
    {M : Type} [(Expanded E).Structure M] (v : α → M) :
    (guards (E := E) sα l).Realize v ↔ ∀ a ∈ l, tagEval (E := E) (sα a) (v a) := by
  induction l with
  | nil => simp [guards]
  | cons a l ih =>
    simpa only [guards, List.map_cons, List.foldr_cons, Formula.realize_inf,
      guardOne_realize, List.mem_cons, forall_eq_or_imp] using and_congr Iff.rfl ih

/-- Type invariance on sorted tuples gives a single sorted VF-free
formula, selected before the model and assignment. -/
theorem definable_of_sorted_type_invariant [Finite α]
    (T : (Expanded E).Theory) (sα : α → SortTag) (φ : (Expanded E).Formula α)
    (hinvariant : ∀ (M N : T.ModelType.{0, 0, 0}) (v : α → M) (w : α → N),
      (∀ a, tagEval (E := E) (sα a) (v a)) →
      (∀ a, tagEval (E := E) (sα a) (w a)) →
      (∀ ψ, fragment (E := E) sα ψ → (ψ.Realize v ↔ ψ.Realize w)) →
      (φ.Realize v ↔ φ.Realize w)) :
    ∃ ψ, fragment (E := E) sα ψ ∧ ∀ (M : T.ModelType.{0, 0, 0}) (v : α → M),
      (∀ a, tagEval (E := E) (sα a) (v a)) → (φ.Realize v ↔ ψ.Realize v) := by
  letI := Fintype.ofFinite α
  let l := (Finset.univ : Finset α).toList
  let G : (Expanded E).Formula α := guards (E := E) sα l
  have hG : fragment (E := E) sα G := guards_mem (E := E) sα l
  have hGsem {M : Type} [(Expanded E).Structure M] (v : α → M) :
      G.Realize v ↔ ∀ a, tagEval (E := E) (sα a) (v a) := by
    simpa only [G, guards_realize, l, Finset.mem_toList, Finset.mem_univ, forall_const]
  obtain ⟨ψ, hψ, he⟩ := definable_of_type_invariant (fragment_boolean (E := E) sα) T (G.imp φ)
    (fun M N v w ht => by
      have hGG := ht G hG
      simp only [Formula.realize_imp]
      by_cases hv : G.Realize v
      · have hw := hGG.mp hv
        exact imp_congr hGG (hinvariant M N v w ((hGsem v).mp hv) ((hGsem w).mp hw) ht)
      · have hw : ¬ G.Realize w := fun h => hv (hGG.mpr h)
        simp only [hv, hw, false_implies])
  refine ⟨ψ, hψ, ?_⟩
  intro M v hv
  have hg := (hGsem v).mpr hv
  simpa only [Formula.realize_imp, hg, true_implies] using he M v

end SpecialTransformations.Section6.SortedFragment
