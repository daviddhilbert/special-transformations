module

public import Section3.Parameters

@[expose] public section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M]

def sortAtom {α : Type} {n : ℕ} (s : SortTag) (i : Fin n) : LRV.BoundedFormula α n :=
  match s with
  | .vf => .rel Rel.memVF ![.var (.inr i)]
  | .rv => .rel Rel.memRV ![.var (.inr i)]

theorem realize_sortAtom {α : Type} {n : ℕ} (s : SortTag) (i : Fin n)
    (v : α → M) (x : Fin n → M) : (sortAtom s i).Realize v x ↔ sortEval s (x i) := by
  have he : (fun _ : Fin 1 => x i) = ![x i] := by
    funext j; fin_cases j; rfl
  cases s <;> simp [sortAtom, BoundedFormula.Realize, sortEval, he]

def tupleGuard {α : Type} {n : ℕ} (sn : Fin n → SortTag) : LRV.BoundedFormula α n :=
  (List.finRange n).foldr (fun i acc => sortAtom (sn i) i ⊓ acc) ⊤

theorem realize_tupleGuard {α : Type} {n : ℕ} (sn : Fin n → SortTag)
    (v : α → M) (x : Fin n → M) : (tupleGuard sn).Realize v x ↔
      ∀ i, sortEval (sn i) (x i) := by
  have h (l : List (Fin n)) :
      (l.foldr (fun i acc => sortAtom (sn i) i ⊓ acc) (⊤ : LRV.BoundedFormula α n)).Realize v x ↔
      ∀ i ∈ l, sortEval (sn i) (x i) := by
    induction l with
    | nil => simp
    | cons i l ih => simp [realize_sortAtom, ih]
  simpa [tupleGuard] using h (List.finRange n)

theorem DefinableOver.raw_definable {A : Set M} {n : ℕ} {sn : Fin n → SortTag}
    {s : Set (Fin n → M)} (hs : DefinableOver A sn s) : A.Definable LRV s := by
  classical
  obtain ⟨p, φ, hφ, rfl⟩ := hs
  rw [Set.definable_iff_exists_formula_sum]
  let g : (Fin p.length ⊕ Fin n) → (A ⊕ Fin n) :=
    Sum.map (fun i => ⟨p.values i, p.mem_base i⟩) id
  refine ⟨((tupleGuard sn ⊓ φ).toFormula).relabel g, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Formula.realize_relabel, BoundedFormula.realize_toFormula,
    BoundedFormula.realize_inf]
  change ((∀ i, sortEval (sn i) (x i)) ∧ φ.Realize p.values x) ↔
    (tupleGuard sn).Realize p.values x ∧ φ.Realize p.values x
  rw [realize_tupleGuard]

theorem DefinableAt.raw_definable {A : Set M} {σ : SortTag} {s : Set M}
    (hs : DefinableAt A σ s) : A.Definable₁ LRV s :=
  hs.1.raw_definable

theorem AlgebraicAt.raw_finite_witness {A : Set M} {σ : SortTag} {x : M}
    (hx : AlgebraicAt A σ x) :
    ∃ s : Set M, A.Definable₁ LRV s ∧ s.Finite ∧ x ∈ s := by
  obtain ⟨s, hs, hf, hx⟩ := hx
  exact ⟨s, hs.raw_definable, hf, hx⟩
end SpecialTransformations.Section3
