import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Sum

/-!
Finite abstraction and existential assembly in an arbitrary auxiliary
language. When its carrier is RV, every quantifier below is an RV
quantifier. These are Mathlib formulas, not a second valued-field language.
The left variables stand for the occurring terms rv(F); restriction of
free variables proves replacement even below arbitrarily many RV binders.
-/

noncomputable section
open Classical
open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.RVFormula

variable {L : Language} {A B : Type}

def leftSupport (φ : L.Formula (A ⊕ B)) : Finset A := by
  classical
  exact φ.freeVarFinset.toLeft

def enumeration (φ : L.Formula (A ⊕ B)) :
    Fin (leftSupport φ).card ≃ leftSupport φ := (Finset.equivFin _).symm

def replacement (φ : L.Formula (A ⊕ B)) :
    φ.freeVarFinset → Fin (leftSupport φ).card ⊕ B
  | ⟨.inl p, hp⟩ => .inl ((enumeration φ).symm ⟨p, by simpa [leftSupport] using hp⟩)
  | ⟨.inr b, _⟩ => .inr b

def abstractLeft (φ : L.Formula (A ⊕ B)) :
    L.Formula (Fin (leftSupport φ).card ⊕ B) := by
  classical
  exact φ.restrictFreeVar (replacement φ)

/-- The finite occurrence list and its replacement formula are chosen from
syntax alone, before a structure or a variable assignment is supplied. -/
theorem abstractLeft_realize (φ : L.Formula (A ⊕ B))
    {R : Type} [L.Structure R] (a : A → R) (b : B → R) :
    (abstractLeft φ).Realize
      (Sum.elim (fun i => a ((enumeration φ i).val)) b) ↔
      φ.Realize (Sum.elim a b) := by
  classical
  apply BoundedFormula.realize_restrictFreeVar (Sum.elim a b)
  rintro ⟨p | q, hp⟩
  · simp only [replacement, Sum.elim_inl]
    congr 1
    exact congrArg Subtype.val ((enumeration φ).apply_symm_apply _)
  · rfl

/-- Bind a finite auxiliary tuple, retaining all other free variables. -/
def existsLeft {k : ℕ} (φ : L.Formula (Fin k ⊕ B)) : L.Formula B :=
  Formula.iExs (Fin k) (φ.relabel Sum.swap)

theorem existsLeft_realize {k : ℕ} (φ : L.Formula (Fin k ⊕ B))
    {R : Type} [L.Structure R] (b : B → R) :
    (existsLeft φ).Realize b ↔ ∃ z : Fin k → R, φ.Realize (Sum.elim z b) := by
  simp only [existsLeft, Formula.realize_iExs, Formula.realize_relabel]
  apply exists_congr
  intro z
  have he : Sum.elim b z ∘ Sum.swap = Sum.elim z b := by
    funext i
    cases i <;> rfl
  rw [he]

/-- The domain is part of the graph formula, including when k=0. -/
def assemble {k q : ℕ} (graph : L.Formula (Fin q ⊕ Fin k ⊕ B))
    (body : L.Formula (Fin k ⊕ B)) : L.Formula B :=
  existsLeft (existsLeft (graph ⊓ body.relabel Sum.inr))

theorem assemble_realize {k q : ℕ}
    (graph : L.Formula (Fin q ⊕ Fin k ⊕ B)) (body : L.Formula (Fin k ⊕ B))
    {R : Type} [L.Structure R] (b : B → R) :
    (assemble graph body).Realize b ↔
      ∃ z : Fin k → R, ∃ u : Fin q → R,
        graph.Realize (Sum.elim u (Sum.elim z b)) ∧ body.Realize (Sum.elim z b) := by
  simp only [assemble, existsLeft_realize, Formula.realize_inf, Formula.realize_relabel,
    Sum.elim_comp_inr]

end SpecialTransformations.Section6.RVFormula
