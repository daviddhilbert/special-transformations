import CanonicalStructure

set_option backward.isDefEq.respectTransparency false

/-! An elementary class for the canonical totalization of the tagged language.

The auxiliary theory adds explicit first-order sentences fixing only the
interpretations at incorrectly sorted arguments. It retains the author-corrected
`Axioms.ACVF`, including named RV inversion, and conservatively reduces its
well-sorted QE target. No elimination or extension principle is assumed here.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace CanonicalTheory

/-- The named zero of the declared result sort. -/
def zeroTerm {k : ℕ} (s : SortTag) : Tm k :=
  match s with
  | .vf => tVFZero
  | .rv => tRVZero

/-- A symbol applied to the entire tuple of bound variables. -/
def functionTerm {k : ℕ} (f : Fn k) : Tm k :=
  Term.func f (fun i => Term.var (Sum.inr i))

/-- Universal closure is deliberately unguarded: the implication constrains
exactly the tuples that fail the symbol's argument-sort profile. -/
def functionAxiom {k : ℕ} (f : Fn k) : LRV.Sentence :=
  BoundedFormula.alls
    ((sortedHyps (Fn.argSort f)).not.imp
      (BoundedFormula.equal (functionTerm f) (zeroTerm (Fn.resSort f))))

/-- The RV order relation is false unless both arguments lie in RV. -/
def orderAxiom : LRV.Sentence :=
  BoundedFormula.alls
    ((sortedHyps (fun _ : Fin 2 => SortTag.rv)).not.imp
      (BoundedFormula.rel Rel.rvLe (fun i => Term.var (Sum.inr i))).not)

/-- The sentences specifying canonical off-sort interpretations. -/
def totalization : LRV.Theory :=
  {φ | (∃ (k : ℕ) (f : Fn k), φ = functionAxiom f) ∨ φ = orderAxiom}

/-- An auxiliary ordinary first-order theory, retaining every corrected ACVF axiom. -/
def CanonicalACVF : LRV.Theory := Axioms.ACVF ∪ totalization

variable {M : Type} [LRV.Structure M]

@[simp] theorem realize_zeroTerm {k : ℕ} (s : SortTag)
    (v : Empty → M) (xs : Fin k → M) :
    (zeroTerm s : Tm k).realize (Sum.elim v xs) =
      CanonicalStructure.sortZero (M := M) s := by
  cases s with
  | vf => exact Transfer.realize_tVFZero (Sum.elim v xs)
  | rv => exact Transfer.realize_tRVZero (Sum.elim v xs)

@[simp] theorem realize_functionTerm {k : ℕ} (f : Fn k)
    (v : Empty → M) (xs : Fin k → M) :
    (functionTerm f).realize (Sum.elim v xs) =
      Structure.funMap (L := LRV) f xs := rfl

theorem functionAxiom_realize {k : ℕ} (f : Fn k) :
    (M ⊨ functionAxiom f) ↔
      ∀ xs : Fin k → M, ¬ (∀ i, sortEval (Fn.argSort f i) (xs i)) →
        Structure.funMap (L := LRV) f xs =
          CanonicalStructure.sortZero (Fn.resSort f) := by
  rw [functionAxiom, Sentence.Realize, BoundedFormula.realize_alls]
  apply forall_congr'
  intro xs
  have hs : (sortedHyps (Fn.argSort f)).Realize (default : Empty → M) xs ↔
      ∀ i, sortEval (Fn.argSort f i) (xs i) := by
    refine (Transfer.sortedHyps_realize (Fn.argSort f) (default : Empty → M) xs).trans ?_
    apply forall_congr'
    intro i
    cases Fn.argSort f i <;> rfl
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_not, hs]
  apply imp_congr Iff.rfl
  change ((functionTerm f).realize (Sum.elim (default : Empty → M) xs) =
    (zeroTerm (Fn.resSort f) : Tm k).realize (Sum.elim (default : Empty → M) xs)) ↔ _
  rw [realize_functionTerm, realize_zeroTerm]

theorem orderAxiom_realize :
    (M ⊨ orderAxiom) ↔
      ∀ xs : Fin 2 → M, ¬ (∀ i, sortEval .rv (xs i)) →
        ¬ Structure.RelMap (L := LRV) Rel.rvLe xs := by
  rw [orderAxiom, Sentence.Realize, BoundedFormula.realize_alls]
  apply forall_congr'
  intro xs
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_not,
    Transfer.sortedHyps_realize]
  rfl

theorem model_totalization_iff :
    (M ⊨ totalization) ↔ CanonicalStructure.IsCanonical (M := M) := by
  constructor
  · intro h
    constructor
    · intro k f xs hxs
      have hf : M ⊨ functionAxiom f :=
        h.realize_of_mem _ (Or.inl ⟨k, f, rfl⟩)
      exact (functionAxiom_realize f).mp hf xs hxs
    · intro xs hxs
      have ho : M ⊨ orderAxiom := h.realize_of_mem _ (Or.inr rfl)
      exact orderAxiom_realize.mp ho xs hxs
  · intro h
    apply (@Theory.model_iff LRV M inferInstance totalization).mpr
    intro φ hφ
    rcases hφ with ⟨k, f, rfl⟩ | rfl
    · exact (functionAxiom_realize f).mpr (h.1 f)
    · exact orderAxiom_realize.mpr h.2

/-- Thus canonical ACVF models form an elementary class, with precisely the
off-sort convention used in `CanonicalStructure.normalize`. -/
theorem model_CanonicalACVF_iff :
    (M ⊨ CanonicalACVF) ↔
      (M ⊨ Axioms.ACVF) ∧ CanonicalStructure.IsCanonical (M := M) := by
  rw [CanonicalACVF, Theory.model_union_iff, model_totalization_iff]

theorem acvf_of_model (h : M ⊨ CanonicalACVF) : M ⊨ Axioms.ACVF :=
  model_CanonicalACVF_iff.mp h |>.1

theorem canonical_of_model (h : M ⊨ CanonicalACVF) :
    CanonicalStructure.IsCanonical (M := M) :=
  model_CanonicalACVF_iff.mp h |>.2

/-- Every frozen model yields a canonical model on the same carrier;
well-sorted realization is preserved by the imported normalization theorem. -/
theorem normalized_model (hM : M ⊨ Axioms.ACVF) :
    @Theory.Model LRV M (CanonicalStructure.normalize (M := M)) CanonicalACVF := by
  exact (@model_CanonicalACVF_iff M (CanonicalStructure.normalize (M := M))).mpr
    ⟨CanonicalStructure.normalized_model hM, CanonicalStructure.normalize_isCanonical⟩

end CanonicalTheory

#print axioms CanonicalTheory.functionAxiom_realize
#print axioms CanonicalTheory.orderAxiom_realize
#print axioms CanonicalTheory.model_CanonicalACVF_iff
#print axioms CanonicalTheory.normalized_model
