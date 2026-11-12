module

public import Enc

@[expose] public section

/-!
# Parameters and closure over an arbitrary base

The base `A` is a set, not a finite tuple. Each formula uses a finite list of
elements of `A`, with declared sorts. This is the usual finite-parameter
definition of definability in the paper's two-sorted language. No statement
about saturation, exchange or C-minimality is included in these definitions.

The language and its well-sorted fragment are the released ACVF-QE definitions.
In particular this module does not import the legacy targets with placeholders.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section3

variable {M : Type} [LRV.Structure M]

/-- A finite parameter witness inside a possibly infinite base set. -/
structure Parameters (A : Set M) where
  length : ℕ
  values : Fin length → M
  sorts : Fin length → SortTag
  sorted : ∀ i, sortEval (sorts i) (values i)
  mem_base : ∀ i, values i ∈ A

/-- Adding parameters preserves each existing finite witness. -/
def Parameters.mono {A B : Set M} (p : Parameters A) (h : A ⊆ B) : Parameters B :=
  { p with mem_base := fun i => h (p.mem_base i) }

/-- Definability over the full base `A`, at the indicated tuple of sorts. -/
def DefinableOver (A : Set M) {n : ℕ} (sn : Fin n → SortTag)
    (s : Set (Fin n → M)) : Prop :=
  ∃ p : Parameters A, ∃ φ : LRV.BoundedFormula (Fin p.length) n,
    WellSorted p.sorts sn φ ∧
    s = {x | (∀ i, sortEval (sn i) (x i)) ∧ φ.Realize p.values x}

/-- Unary definability, over the same arbitrary base and at a declared sort. -/
def DefinableAt (A : Set M) (σ : SortTag) (s : Set M) : Prop :=
  DefinableOver A (fun _ : Fin 1 => σ) {x | x 0 ∈ s} ∧
    s ⊆ {x | sortEval σ x}

/-- Algebraicity is membership in a finite definable set of the declared sort. -/
def AlgebraicAt (A : Set M) (σ : SortTag) (x : M) : Prop :=
  ∃ s : Set M, DefinableAt A σ s ∧ s.Finite ∧ x ∈ s

/-- Definable closure means a singleton definable over the original base. -/
def DefinableClosureAt (A : Set M) (σ : SortTag) (x : M) : Prop :=
  DefinableAt A σ {x}

theorem DefinableOver.mono {A B : Set M} (h : A ⊆ B) {n : ℕ}
    {sn : Fin n → SortTag} {s : Set (Fin n → M)} (hs : DefinableOver A sn s) :
    DefinableOver B sn s := by
  obtain ⟨p, φ, hφ, rfl⟩ := hs
  exact ⟨p.mono h, φ, hφ, rfl⟩

theorem DefinableAt.mono {A B : Set M} (h : A ⊆ B) {σ : SortTag} {s : Set M}
    (hs : DefinableAt A σ s) : DefinableAt B σ s :=
  ⟨hs.1.mono h, hs.2⟩

theorem AlgebraicAt.mono {A B : Set M} (h : A ⊆ B) {σ : SortTag} {x : M}
    (hx : AlgebraicAt A σ x) : AlgebraicAt B σ x := by
  obtain ⟨s, hs, hf, hx⟩ := hx
  exact ⟨s, hs.mono h, hf, hx⟩

theorem DefinableClosureAt.algebraic {A : Set M} {σ : SortTag} {x : M}
    (hx : DefinableClosureAt A σ x) : AlgebraicAt A σ x :=
  ⟨{x}, hx, Set.finite_singleton x, Set.mem_singleton x⟩

theorem AlgebraicAt.sorted {A : Set M} {σ : SortTag} {x : M}
    (hx : AlgebraicAt A σ x) : sortEval σ x := by
  obtain ⟨s, hs, _, hx⟩ := hx
  exact hs.2 hx

/-- Finite character of definability over a base set. This does not identify the
whole base with a finite tuple: the finite subset depends on the defining formula. -/
theorem DefinableOver.finite_character {A : Set M} {n : ℕ} {sn : Fin n → SortTag}
    {s : Set (Fin n → M)} (hs : DefinableOver A sn s) :
    ∃ B : Set M, B.Finite ∧ B ⊆ A ∧ DefinableOver B sn s := by
  obtain ⟨p, φ, hφ, hs⟩ := hs
  let q : Parameters (Set.range p.values) :=
    { p with mem_base := fun i => Set.mem_range_self i }
  exact ⟨Set.range p.values, Set.finite_range _,
    by rintro _ ⟨i, rfl⟩; exact p.mem_base i, q, φ, hφ, hs⟩

theorem DefinableAt.finite_character {A : Set M} {σ : SortTag} {s : Set M}
    (hs : DefinableAt A σ s) :
    ∃ B : Set M, B.Finite ∧ B ⊆ A ∧ DefinableAt B σ s := by
  obtain ⟨B, hf, hB, hdef⟩ := hs.1.finite_character
  exact ⟨B, hf, hB, hdef, hs.2⟩

theorem AlgebraicAt.finite_character {A : Set M} {σ : SortTag} {x : M}
    (hx : AlgebraicAt A σ x) :
    ∃ B : Set M, B.Finite ∧ B ⊆ A ∧ AlgebraicAt B σ x := by
  obtain ⟨s, hs, hf, hx⟩ := hx
  obtain ⟨B, hB, hBA, hsB⟩ := hs.finite_character
  exact ⟨B, hB, hBA, s, hsB, hf, hx⟩

/-- Every sorted base element is definable over that base, without naming any
element outside it. -/
theorem definableClosureAt_of_mem {A : Set M} {σ : SortTag} {x : M}
    (hx : x ∈ A) (hs : sortEval σ x) : DefinableClosureAt A σ x := by
  let p : Parameters A :=
    ⟨1, ![x], fun _ => σ, by intro i; fin_cases i; exact hs,
      by intro i; fin_cases i; exact hx⟩
  refine ⟨⟨p, .equal (.var (.inr 0)) (.var (.inl 0)),
    WellSorted.equal _ rfl rfl, ?_⟩, ?_⟩
  · ext y
    change y 0 = x ↔ (∀ i : Fin 1, sortEval σ (y i)) ∧ y 0 = x
    constructor
    · intro h
      exact ⟨by intro i; fin_cases i; simpa [h] using hs, h⟩
    · exact fun h => h.2
  · rintro y rfl
    exact hs

theorem algebraicAt_of_mem {A : Set M} {σ : SortTag} {x : M}
    (hx : x ∈ A) (hs : sortEval σ x) : AlgebraicAt A σ x :=
  (definableClosureAt_of_mem hx hs).algebraic

theorem definableAt_sort (A : Set M) (σ : SortTag) :
    DefinableAt A σ {x | sortEval σ x} := by
  let p : Parameters A := ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  refine ⟨⟨p, ⊤, wellSorted_top p.sorts _, ?_⟩, Set.Subset.rfl⟩
  ext x
  simp only [Set.mem_ofPred_eq, BoundedFormula.realize_top, and_true]
  exact ⟨fun h i => by fin_cases i; exact h, fun h => h 0⟩

end SpecialTransformations.Section3
