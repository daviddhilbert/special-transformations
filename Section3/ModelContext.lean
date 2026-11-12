module

public import Section3.Parameters

@[expose] public section

/-!
# The standing model and base context after Definition 2.4

The saturation/homogeneity definitions follow the audited generic interfaces
in `Archive/Milestone0/Saturation.lean` (Marker, Model Theory: An Introduction,
types and saturated models). They assert realization of finitely satisfiable
types and extension of partial elementary maps, not any of Yin's conclusions.
`BaseContext` retains the actual substructure and its cardinal bound.
The nontrivial-value assumption is an explicit pair of elements with distinct
finite values; it is not inequality of their RV representatives.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section3

variable {M : Type} [LRV.Structure M]

def FinitelySatisfiable {α : Type} {n : ℕ} (v : α → M)
    (p : Set (LRV.BoundedFormula α n)) : Prop :=
  ∀ l : List (LRV.BoundedFormula α n), (∀ φ ∈ l, φ ∈ p) →
    ∃ x : Fin n → M, ∀ φ ∈ l, φ.Realize v x

def Saturated (M : Type) [LRV.Structure M] (κ : Cardinal) : Prop :=
  ∀ (α : Type) (v : α → M), Cardinal.mk α < κ →
    ∀ {n : ℕ} (p : Set (LRV.BoundedFormula α n)), FinitelySatisfiable v p →
      ∃ x : Fin n → M, ∀ φ ∈ p, φ.Realize v x

def PartialElementary {α : Type} (v w : α → M) : Prop :=
  ∀ {n : ℕ} (φ : LRV.BoundedFormula α n) (a : Fin n → α),
    φ.Realize v (v ∘ a) ↔ φ.Realize w (w ∘ a)

def StronglyHomogeneous (M : Type) [LRV.Structure M] (κ : Cardinal) : Prop :=
  ∀ (α : Type) (v w : α → M), Cardinal.mk α < κ → PartialElementary v w →
    ∃ e : M ≃[LRV] M, ∀ a, e (v a) = w a

theorem small_insert {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (S : Set M) (hS : Cardinal.mk S < κ) (b : M) :
    Cardinal.mk ↥(insert b S) < κ :=
  Cardinal.mk_insert_le.trans_lt
    (Cardinal.add_lt_of_lt hκ hS (Cardinal.one_lt_aleph0.trans_le hκ))

/-- The compactness consequence of genuine saturation, with the parameter-size
bound visible. An unrealizable type over a small base has a finite
unrealizable part. This is a theorem, not a field of the saturation context. -/
theorem Saturated.finite_inconsistent {κ : Cardinal} (hs : Saturated M κ)
    {α : Type} (v : α → M) (hsmall : Cardinal.mk α < κ) {n : ℕ}
    (p : Set (LRV.BoundedFormula α n))
    (hp : ¬ ∃ x : Fin n → M, ∀ φ ∈ p, φ.Realize v x) :
    ∃ l : List (LRV.BoundedFormula α n), (∀ φ ∈ l, φ ∈ p) ∧
      ¬ ∃ x : Fin n → M, ∀ φ ∈ l, φ.Realize v x := by
  classical
  by_contra hn
  apply hp
  apply hs α v hsmall p
  intro l hl
  by_contra hbad
  exact hn ⟨l, hl, hbad⟩

/-- Paper's ambient pure-characteristic-zero model and small named base.
No Section 3 theorem is a field of this structure. -/
structure BaseContext (M : Type) [LRV.Structure M] where
  model00 : M ⊨ Axioms.ACVF00
  κ : Cardinal
  uncountable : Cardinal.aleph0 < κ
  saturated : Saturated M κ
  homogeneous : StronglyHomogeneous M κ
  base : LRV.Substructure M
  small : Cardinal.mk base < κ
  nontrivial_values : ∃ a b : base, iRV (a : M) ∧ iRV (b : M) ∧
    (a : M) ≠ iRVZero ∧ (b : M) ≠ iRVZero ∧
    ¬ (iLe (a : M) (b : M) ∧ iLe (b : M) (a : M))

theorem BaseContext.model (C : BaseContext M) : M ⊨ Axioms.ACVF :=
  C.model00.mono (by intro φ hφ; exact Or.inl (Or.inl hφ))

theorem BaseContext.namedModel (C : BaseContext M) :
    M ⊨ SubstructureTheory.ACVF_S C.base := by
  haveI := C.model00
  refine ⟨fun φ hφ => ?_⟩
  rcases hφ with htheory | hdiagram
  · obtain ⟨ψ, hψ, rfl⟩ := htheory
    exact (LRV.lhomWithConstants (C.base : Set M)).realize_onSentence (M := M) ψ
      |>.mpr (Axioms.ACVF00.realize_sentence_of_mem hψ)
  · rcases hdiagram with hpos | hneg
    · exact hpos.2
    · obtain ⟨ψ, _, rfl, hψ⟩ := hneg
      exact hψ

end SpecialTransformations.Section3
