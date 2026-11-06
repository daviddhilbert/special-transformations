/-
Portions adapted from QuantifierElimination.lean, Mathlib PR #40561.
Copyright (c) 2026 Yağız Kaan Aydoğdu, Yusuf Demir, Salih Erdem Koçak.
Released under Apache 2.0; the license text is retained in
Section4/Imported/Mathlib-LICENSE.
-/
import Section6.FiniteCover

/-!
# Boolean-fragment definability by compactness

The two-model argument generalizes the quantifier-free argument in
Mathlib PR #40561, `QuantifierElimination.lean`, by Yağız Kaan Aydoğdu,
Yusuf Demir and Salih Erdem Koçak (2026, Apache-2.0). The imported pinned
Mathlib lacks that module. Its new elementary-extension-pair dependency
is unnecessary here: the compactness core is derived from our checked
finite_formula_cover, and the fragment is an arbitrary Boolean fragment.
No valued-field or Section 6 elimination premise enters this theorem.
-/

noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.FragmentCompactness

variable {L : Language.{0, 0}} {α : Type}

/-- Syntactic closure requirements, independent of any theory or models. -/
structure BooleanClosed (F : L.Formula α → Prop) : Prop where
  top : F ⊤
  not : ∀ {φ}, F φ → F φ.not
  inf : ∀ {φ ψ}, F φ → F ψ → F (φ ⊓ ψ)

def Implies (T : L.Theory) (φ ψ : L.Formula α) : Prop :=
  ∀ M : T.ModelType.{0, 0, 0}, ∀ v : α → M, φ.Realize v → ψ.Realize v

def Equivalent (T : L.Theory) (φ ψ : L.Formula α) : Prop :=
  ∀ M : T.ModelType.{0, 0, 0}, ∀ v : α → M, φ.Realize v ↔ ψ.Realize v

def conjunction {F P : L.Formula α → Prop}
    (l : List {ψ : L.Formula α // F ψ ∧ P ψ}) : L.Formula α :=
  (l.map Subtype.val).foldr (· ⊓ ·) ⊤

theorem conjunction_mem {F P : L.Formula α → Prop} (hF : BooleanClosed F)
    (l : List {ψ : L.Formula α // F ψ ∧ P ψ}) : F (conjunction l) := by
  induction l with
  | nil => exact hF.top
  | cons q l ih => exact hF.inf q.property.1 ih

theorem conjunction_realize {F P : L.Formula α → Prop}
    (l : List {ψ : L.Formula α // F ψ ∧ P ψ})
    {M : Type} [L.Structure M] (v : α → M) :
    (conjunction l).Realize v ↔ ∀ q ∈ l, q.val.Realize v := by
  induction l with
  | nil => simp [conjunction]
  | cons q l ih => simpa only [conjunction, List.map_cons, List.foldr_cons,
      Formula.realize_inf, List.mem_cons, forall_eq_or_imp] using and_congr Iff.rfl ih

/-- A model realizing a seed and a fragment type, from finite consistency.
This is ordinary first-order compactness, proved through finite covers. -/
theorem realize_type {F : L.Formula α → Prop} (T : L.Theory)
    (P : L.Formula α → Prop) (extra : L.Formula α)
    (hkey : ∀ l : List {ψ : L.Formula α // F ψ ∧ P ψ},
      ¬ Implies T extra (conjunction l).not) :
    ∃ (M : T.ModelType.{0, 0, 0}) (v : α → M), extra.Realize v ∧
      ∀ q : {ψ : L.Formula α // F ψ ∧ P ψ}, q.val.Realize v := by
  by_contra hn
  let Q := {ψ : L.Formula α // F ψ ∧ P ψ}
  let θ : Option Q → L.Formula α
    | none => extra.not
    | some q => q.val.not
  have hcover : ∀ M : T.ModelType.{0, 0, 0}, ∀ v : α → M, ∃ i, (θ i).Realize v := by
    intro M v
    by_cases he : extra.Realize v
    · have hp : ¬ ∀ q : Q, q.val.Realize v := fun h => hn ⟨M, v, he, h⟩
      push Not at hp
      obtain ⟨q, hq⟩ := hp
      exact ⟨some q, hq⟩
    · exact ⟨none, he⟩
  obtain ⟨s, hs⟩ := finite_formula_cover T θ hcover
  let qs : Finset Q := s.filterMap id (by intro a b c ha hb; simpa using ha.trans hb.symm)
  apply hkey qs.toList
  intro M v he hconj
  have hall := (conjunction_realize qs.toList v).mp hconj
  obtain ⟨i, hi, hθ⟩ := hs M v
  cases i with
  | none => exact hθ he
  | some q =>
    have hq : q ∈ qs.toList := by
      simpa [qs] using hi
    exact hθ (hall q hq)

/-- If no fragment formula is equivalent to φ, there are two models with
the same complete fragment type on their tuples but opposite φ values. -/
theorem countermodels {F : L.Formula α → Prop} (hF : BooleanClosed F)
    (T : L.Theory) (φ : L.Formula α)
    (hn : ¬ ∃ ψ, F ψ ∧ Equivalent T φ ψ) :
    ∃ (M N : T.ModelType.{0, 0, 0}) (v : α → M) (w : α → N),
      ¬ φ.Realize v ∧ φ.Realize w ∧
      ∀ ψ, F ψ → (ψ.Realize v ↔ ψ.Realize w) := by
  obtain ⟨M, v, hv, hc⟩ :=
    realize_type T (fun ψ => Implies T φ ψ) φ.not (fun l hl => by
      apply hn
      refine ⟨conjunction l, conjunction_mem hF l, ?_⟩
      intro M v
      constructor
      · intro hφ
        exact (conjunction_realize l v).mpr (fun q _ => q.property.2 M v hφ)
      · intro hθ
        by_contra hφ
        exact hl M v hφ hθ)
  obtain ⟨N, w, hw, ht⟩ :=
    realize_type T (fun ψ => ψ.Realize v) φ (fun l hl => by
      have hθ : (conjunction l).Realize v :=
        (conjunction_realize l v).mpr (fun q _ => q.property.2)
      exact hc ⟨(conjunction l).not, hF.not (conjunction_mem hF l), hl⟩ hθ)
  refine ⟨M, N, v, w, hv, hw, ?_⟩
  intro ψ hψ
  constructor
  · intro hψv
    exact ht ⟨ψ, hψ, hψv⟩
  · intro hψw
    by_contra hψv
    exact ht ⟨ψ.not, hF.not hψ, hψv⟩ hψw

/-- A Boolean-fragment formula exists uniformly in the model and tuple
when truth depends only on the complete fragment type. -/
theorem definable_of_type_invariant {F : L.Formula α → Prop} (hF : BooleanClosed F)
    (T : L.Theory) (φ : L.Formula α)
    (hinvariant : ∀ (M N : T.ModelType.{0, 0, 0}) (v : α → M) (w : α → N),
      (∀ ψ, F ψ → (ψ.Realize v ↔ ψ.Realize w)) → (φ.Realize v ↔ φ.Realize w)) :
    ∃ ψ, F ψ ∧ Equivalent T φ ψ := by
  by_contra hn
  obtain ⟨M, N, v, w, hv, hw, he⟩ := countermodels hF T φ hn
  exact hv ((hinvariant M N v w he).mpr hw)

end SpecialTransformations.Section6.FragmentCompactness
