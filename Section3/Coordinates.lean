import Section3.Parameters

/-!
# Notation 2.10: coordinates, projections and fibres

Coordinates retain their sort through a dependent tuple. A mixed VF^n × RV^m
tuple uses the disjoint index type `Fin n ⊕ Fin m`. Fibres below are sets on
the complementary coordinates, rather than ambiguous subsets of the whole
ambient product. Assembly identifies these with their embedded fibres.
-/

open SpecialTransformations.Milestone0

namespace SpecialTransformations.Section3.Coordinates

variable {M : Type} [LRV.Structure M] {ι : Type}

abbrev Tuple (σ : ι → SortTag) := ∀ i, {x : M // sortEval (σ i) x}

def mixedSort {n m : ℕ} : Fin n ⊕ Fin m → SortTag :=
  Sum.elim (fun _ => .vf) (fun _ => .rv)

abbrev MixedTuple (M : Type) [LRV.Structure M] (n m : ℕ) :=
  Tuple (M := M) (mixedSort (n := n) (m := m))

def project {σ : ι → SortTag} (E : Set ι) (x : Tuple (M := M) σ) :
    Tuple (M := M) (σ ∘ (Subtype.val : E → ι)) := fun i => x i

def projection {σ : ι → SortTag} (E : Set ι) (A : Set (Tuple (M := M) σ)) :=
  project E '' A

noncomputable def assemble {σ : ι → SortTag} (E : Set ι)
    (x : Tuple (M := M) (σ ∘ (Subtype.val : E → ι)))
    (a : Tuple (M := M) (σ ∘ (Subtype.val : ↥(Eᶜ) → ι))) : Tuple (M := M) σ := by
  classical
  exact fun i => if h : i ∈ E then x ⟨i, h⟩ else a ⟨i, h⟩

def fibre {σ : ι → SortTag} (A : Set (Tuple (M := M) σ)) (E : Set ι)
    (a : Tuple (M := M) (σ ∘ (Subtype.val : ↥(Eᶜ) → ι))) :=
  {x | assemble E x a ∈ A}

@[simp] theorem project_assemble {σ : ι → SortTag} (E : Set ι)
    (x : Tuple (M := M) (σ ∘ (Subtype.val : E → ι)))
    (a : Tuple (M := M) (σ ∘ (Subtype.val : ↥(Eᶜ) → ι))) :
    project E (assemble E x a) = x := by
  funext i
  simp [project, assemble, i.property]

@[simp] theorem project_compl_assemble {σ : ι → SortTag} (E : Set ι)
    (x : Tuple (M := M) (σ ∘ (Subtype.val : E → ι)))
    (a : Tuple (M := M) (σ ∘ (Subtype.val : ↥(Eᶜ) → ι))) :
    project Eᶜ (assemble E x a) = a := by
  funext i
  have hi : (i : ι) ∉ E := i.property
  simp [project, assemble, hi]

@[simp] theorem assemble_projects {σ : ι → SortTag} (E : Set ι)
    (x : Tuple (M := M) σ) : assemble E (project E x) (project Eᶜ x) = x := by
  funext i
  simp [assemble, project]

theorem fibre_nonempty_iff {σ : ι → SortTag} (E : Set ι)
    (A : Set (Tuple (M := M) σ))
    (a : Tuple (M := M) (σ ∘ (Subtype.val : ↥(Eᶜ) → ι))) :
    (fibre A E a).Nonempty ↔ a ∈ projection Eᶜ A := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨assemble E x a, hx, project_compl_assemble E x a⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨project E x, by simpa [fibre] using hx⟩

/-- Composition of coordinate restrictions, with the subset inclusion explicit. -/
theorem project_comp {σ : ι → SortTag} (E : Set ι) (F : Set E)
    (x : Tuple (M := M) σ) :
    project F (project E x) = (fun i : F => x i.val.val) := rfl

end SpecialTransformations.Section3.Coordinates
