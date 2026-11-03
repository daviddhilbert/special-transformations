/-
A quantifier-elimination criterion in Mathlib's first-order syntax, with no
model-theoretic saturation.

`HasQEb T` says: every bounded formula is `T`-equivalent to a quantifier-free one.
`QEAllStep T` / `QEExStep T` say: one universal / existential quantifier applied to a
quantifier-free formula can be removed.

Main results:
* `QEAllStep_iff_QEExStep`  -- the two steps are equivalent;
* `hasQEb_iff_QEAllStep`    -- either step is *equivalent* to full QE;
* `hasQE_of_QEAllStep`      -- the step gives QE for `Formula` (the frozen notion).

# Where the criterion halves meet, and where they do not

This file is the **syntactic half** of the join between Johnson's criterion and the frozen
target. `QE/Johnson_criterion.lean` produces, from prime models + amalgamation + 1-ec, the
semantic statement that a quantifier-free type determines the truth of an existential over a
quantifier-free formula. `QE/QF_type_bridge.lean` turns *full* quantifier-free-type invariance
into `HasQE`. Between them sits `QEExStep` — one existential over a quantifier-free formula is
`T`-equivalent to a quantifier-free one — and this file proves that `QEExStep` gives `HasQE`.

What is still missing is `QFExDetermined → QEExStep`, and the obstruction is concrete:
`BoundedFormula.toFormula : BoundedFormula α n → Formula (α ⊕ Fin n)` has no converse in
Mathlib. The compactness argument (as in `QF_type_bridge.lean`) produces a quantifier-free
`ψ : Formula (α ⊕ Fin n)`, and turning it back into a `BoundedFormula α n` — the direction this
file's `QEExStep` consumes — requires either an inverse of `toFormula` on quantifier-free
formulas or a version of the compactness machinery stated for bounded formulas directly.
-/

import Mathlib
set_option linter.unusedVariables false

open FirstOrder FirstOrder.Language

namespace QECriterion

variable {L : Language}

/-- A theory `T` of `L` admits **quantifier elimination on bounded formulas**: every
bounded formula with `n` bound variables is `T`-equivalent to a quantifier-free formula
with the same `n` bound variables. -/
def HasQEb (T : L.Theory) : Prop :=
  ∀ (α : Type) (n : ℕ) (φ : L.BoundedFormula α n),
    ∃ ψ : L.BoundedFormula α n, ψ.IsQF ∧ Theory.Iff T φ ψ

/-- **The universal QE step.**  One universal quantifier in front of a quantifier-free
formula can be removed, modulo `T`. -/
def QEAllStep (T : L.Theory) : Prop :=
  ∀ (α : Type) (n : ℕ) (θ : L.BoundedFormula α (n + 1)), θ.IsQF →
    ∃ ψ : L.BoundedFormula α n, ψ.IsQF ∧ Theory.Iff T θ.all ψ

/-- **The existential QE step.**  One existential quantifier in front of a
quantifier-free formula can be removed, modulo `T`. -/
def QEExStep (T : L.Theory) : Prop :=
  ∀ (α : Type) (n : ℕ) (θ : L.BoundedFormula α (n + 1)), θ.IsQF →
    ∃ ψ : L.BoundedFormula α n, ψ.IsQF ∧ Theory.Iff T θ.ex ψ

/-- `∀ x θ` is `¬∃x ¬θ`. -/
theorem all_iff_ex_not {T : L.Theory} {α : Type} {n : ℕ} (θ : L.BoundedFormula α (n + 1)) :
    Theory.Iff T θ.all θ.not.ex.not := by
  intro M v xs
  simp only [BoundedFormula.realize_iff, BoundedFormula.realize_all, BoundedFormula.realize_not,
    BoundedFormula.realize_ex]
  simp

/-- `∃ x θ` is `¬∀x ¬θ`. -/
theorem ex_iff_all_not {T : L.Theory} {α : Type} {n : ℕ} (θ : L.BoundedFormula α (n + 1)) :
    Theory.Iff T θ.ex θ.not.all.not := by
  intro M v xs
  simp only [BoundedFormula.realize_iff, BoundedFormula.realize_ex, BoundedFormula.realize_not,
    BoundedFormula.realize_all]
  simp

/-- The universal step and the existential step are equivalent. -/
theorem QEAllStep_iff_QEExStep {T : L.Theory} : QEAllStep T ↔ QEExStep T := by
  constructor
  · intro h α n θ hθ
    obtain ⟨ψ, hψ, hψ'⟩ := h α n θ.not hθ.not
    exact ⟨ψ.not, hψ.not, (ex_iff_all_not θ).trans (Theory.Iff.not hψ')⟩
  · intro h α n θ hθ
    obtain ⟨ψ, hψ, hψ'⟩ := h α n θ.not hθ.not
    exact ⟨ψ.not, hψ.not, (all_iff_ex_not θ).trans (Theory.Iff.not hψ')⟩

/-- The universal step gives quantifier elimination, by induction on formulas. -/
theorem hasQEb_of_QEAllStep {T : L.Theory} (h : QEAllStep T) : HasQEb T := by
  intro α n φ
  induction φ with
  | falsum => exact ⟨⊥, BoundedFormula.isQF_bot, Theory.Iff.refl _⟩
  | equal t₁ t₂ => exact ⟨_, BoundedFormula.IsAtomic.equal t₁ t₂ |>.isQF, Theory.Iff.refl _⟩
  | rel R ts => exact ⟨_, BoundedFormula.IsAtomic.rel R ts |>.isQF, Theory.Iff.refl _⟩
  | imp φ₁ φ₂ ih₁ ih₂ =>
      obtain ⟨ψ₁, h₁, h₁'⟩ := ih₁
      obtain ⟨ψ₂, h₂, h₂'⟩ := ih₂
      exact ⟨ψ₁.imp ψ₂, h₁.imp h₂, h₁'.imp h₂'⟩
  | all φ ih =>
      obtain ⟨ψ, hqf, heq⟩ := ih
      obtain ⟨χ, hχqf, hχ⟩ := h α _ ψ hqf
      exact ⟨χ, hχqf, (Theory.Iff.all heq).trans hχ⟩

/-- Conversely, full QE gives the universal step. -/
theorem QEAllStep_of_hasQEb {T : L.Theory} (h : HasQEb T) : QEAllStep T := by
  intro α n θ _
  obtain ⟨ψ, hψ, hψ'⟩ := h α n θ.all
  exact ⟨ψ, hψ, hψ'⟩

/-- **The criterion**: `T` admits quantifier elimination if and only if one universal
quantifier in front of a quantifier-free formula can always be removed. -/
theorem hasQEb_iff_QEAllStep {T : L.Theory} : HasQEb T ↔ QEAllStep T :=
  ⟨QEAllStep_of_hasQEb, hasQEb_of_QEAllStep⟩

theorem hasQEb_iff_QEExStep {T : L.Theory} : HasQEb T ↔ QEExStep T :=
  hasQEb_iff_QEAllStep.trans QEAllStep_iff_QEExStep

/-- Quantifier elimination as it is stated in `Milestone0/Encoding.lean`
(`SpecialTransformations.Milestone0.HasQE`): every `Formula` (i.e. every bounded formula
with no bound variables in scope) is `T`-equivalent to a quantifier-free formula. -/
def HasQE (T : L.Theory) : Prop :=
  ∀ (α : Type) (φ : L.Formula α), ∃ ψ : L.Formula α, ψ.IsQF ∧ Theory.Iff T φ ψ

theorem HasQE_of_hasQEb {T : L.Theory} (h : HasQEb T) : HasQE T :=
  fun α φ => h α 0 φ

/-- **The reduction**: the universal QE step gives quantifier elimination. -/
theorem HasQE_of_QEAllStep {T : L.Theory} (h : QEAllStep T) : HasQE T :=
  HasQE_of_hasQEb (hasQEb_of_QEAllStep h)

/-- **The reduction**, in the existential form. -/
theorem HasQE_of_QEExStep {T : L.Theory} (h : QEExStep T) : HasQE T :=
  HasQE_of_QEAllStep (QEAllStep_iff_QEExStep.2 h)

/-! ### Non-vacuity of the hypothesis

The step hypothesis is not vacuous: it holds for every inconsistent theory.  (This
records that `QEAllStep`/`QEExStep` are satisfiable, so the criterion is not an
unprovable-in-principle formulation.) -/

theorem iff_of_inconsistent {T : L.Theory} (h : (⊥ : L.Sentence) ∈ T)
    {α : Type} {n : ℕ} {φ ψ : L.BoundedFormula α n} : Theory.Iff T φ ψ :=
  fun M _ _ => absurd (Theory.realize_sentence_of_mem (T := T) h) (Sentence.not_realize_bot M)

theorem QEExStep_of_inconsistent {T : L.Theory} (h : (⊥ : L.Sentence) ∈ T) : QEExStep T :=
  fun _ _ _ _ => ⟨⊥, BoundedFormula.isQF_bot, iff_of_inconsistent h⟩

theorem HasQEb_of_inconsistent {T : L.Theory} (h : (⊥ : L.Sentence) ∈ T) : HasQEb T :=
  hasQEb_of_QEAllStep (QEAllStep_iff_QEExStep.2 (QEExStep_of_inconsistent h))

/-! ### Consequence: embeddings of models are elementary

This is the easy half of Shoenfield's test (QE `⟹` every `L`-embedding between models is
elementary, i.e. model completeness), and it shows that the QE notion used above is the
real one.  The proof is the standard one: reduce to a quantifier-free formula and use that
`L`-embeddings preserve quantifier-free formulas both ways. -/

theorem realize_embedding_of_HasQEb {T : L.Theory} (h : HasQEb T)
    {M : Type*} [L.Structure M] [Nonempty M] [M ⊨ T]
    {N : Type*} [L.Structure N] [Nonempty N] [N ⊨ T]
    (f : M ↪[L] N) {α : Type} {n : ℕ} (φ : L.BoundedFormula α n)
    {v : α → M} {xs : Fin n → M} :
    (φ.Realize v xs ↔ φ.Realize (f ∘ v) (f ∘ xs)) := by
  obtain ⟨ψ, hψ, hψ'⟩ := h α n φ
  rw [hψ'.realize_bd_iff (M := M), hψ'.realize_bd_iff (M := N), ← hψ.realize_embedding f]

/-- **Quantifier elimination means the quantifier-free type determines the type** — the
easy half of the back-and-forth / Shoenfield criterion, and the form in which the criterion
meets `PartialEquiv`-based assembly. -/
theorem realize_of_qfType_of_HasQEb {T : L.Theory} (h : HasQEb T)
    {M : Type*} [L.Structure M] [Nonempty M] [M ⊨ T]
    {N : Type*} [L.Structure N] [Nonempty N] [N ⊨ T]
    {α : Type} {n : ℕ} {v : α → M} {xs : Fin n → M} {w : α → N} {ys : Fin n → N}
    (hQF : ∀ ψ : L.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys))
    (φ : L.BoundedFormula α n) : (φ.Realize v xs ↔ φ.Realize w ys) := by
  obtain ⟨ψ, hψ, hψ'⟩ := h α n φ
  rw [hψ'.realize_bd_iff (M := M), hψ'.realize_bd_iff (M := N)]
  exact hQF ψ hψ

/-- **Quantifier elimination makes every embedding between models elementary.** -/
theorem elementary_of_HasQEb {T : L.Theory} (h : HasQEb T)
    {M : Type*} [L.Structure M] [Nonempty M] [M ⊨ T]
    {N : Type*} [L.Structure N] [Nonempty N] [N ⊨ T]
    (f : M ↪[L] N) (φ : L.Sentence) : M ⊨ φ → N ⊨ φ := by
  intro hφ
  have h2 := (realize_embedding_of_HasQEb (T := T) h f φ
    (v := (default : Empty → M)) (xs := (default : Fin 0 → M))).1 hφ
  have e1 : (⇑f ∘ (default : Empty → M)) = (default : Empty → N) := Subsingleton.elim _ _
  have e2 : (⇑f ∘ (default : Fin 0 → M)) = (default : Fin 0 → N) := Subsingleton.elim _ _
  rw [e1, e2] at h2
  simpa [Sentence.Realize, Formula.Realize] using h2


/-! ### The model-theoretic hypotheses

`Saturated`, `ExtensionProperty` (Proposition 3.9 of arXiv:1006.1393) and `SaturationExists`
are stated here as ordinary `Prop`s, so that the paper's hypothesis can be named exactly.
`QFTypeDetermines` is the type-theoretic statement that QE is classically routed through. -/

/-- `N` is **saturated** (realises every type over itself): every theory in the language
`L` with constants for the elements of `N` that is finitely satisfiable is satisfied by `N`.
This is the standard saturation hypothesis of Shoenfeld's test, stated in the form that needs
no cardinal arithmetic; it implies `#N⁺`-saturation at every use below. -/
def Saturated (N : Type*) [L.Structure N] : Prop :=
  ∀ (p : L[[N]].Theory),
    (∀ p₀ : Finset (L[[N]].Sentence), (↑p₀ : L[[N]].Theory) ⊆ p →
      Theory.IsSatisfiable (↑p₀ : (L[[N]]).Theory)) → N ⊨ p

/-- **Proposition 3.9 of arXiv:1006.1393 (`lrv:mono:lift`)**, as a `Prop`: for models
`M, N` of `T` with `N` saturated, every monomorphism into `N` from a substructure of `M`
extends to a monomorphism defined on all of `M`. -/
def ExtensionProperty (T : L.Theory) : Prop :=
  ∀ (M : Type*) [L.Structure M] [Nonempty M], M ⊨ T →
  ∀ (N : Type*) [L.Structure N] [Nonempty N], N ⊨ T → @Saturated L N _ →
  ∀ (S : L.Substructure M) (f : S ↪[L] N), ∃ (g : M ↪[L] N), ∀ s : S, g s = f s

/-- Every model of `T` has a saturated elementary extension.  This is a general theorem of
first-order logic (compactness plus ultrapowers); it is **not** formalised here. -/
def SaturationExists (T : L.Theory) : Prop :=
  ∀ (M : Type*) [L.Structure M] [Nonempty M], M ⊨ T →
    ∃ (N : Type*) (i : L.Structure N), Nonempty N ∧ @Theory.Model L N i T ∧
      @Saturated L N i ∧ Nonempty (FirstOrder.Language.ElementaryEmbedding L M N)

/-- The quantifier-free type of a tuple determines its type. -/
def QFTypeDetermines (T : L.Theory) : Prop :=
  ∀ (α : Type) (n : ℕ) (M : Type*) [L.Structure M] [Nonempty M], M ⊨ T →
  ∀ (N : Type*) [L.Structure N] [Nonempty N], N ⊨ T →
  ∀ (v : α → M) (xs : Fin n → M) (w : α → N) (ys : Fin n → N),
    (∀ ψ : L.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
    ∀ φ : L.BoundedFormula α n, (φ.Realize v xs ↔ φ.Realize w ys)

/-- The trivial half of the type criterion: QE makes the quantifier-free type of a tuple
determine its type. -/
theorem QFTypeDetermines_of_HasQEb {T : L.Theory} (h : HasQEb T) : QFTypeDetermines T :=
  fun α n M _ _ hM N _ _ hN v xs w ys hQF φ =>
    realize_of_qfType_of_HasQEb (T := T) h hQF φ

/-- **Shoenfield's test**, stated as a single `Prop`: the extension property of
Proposition 3.9 of arXiv:1006.1393, together with the existence of saturated elementary
extensions, implies quantifier elimination.  **This is the one implication of the paper's
Section 3 that is not formalised here**; everything downstream of it is
`HasQE_of_QEExStep`. -/
def ShoenfieldTest (T : L.Theory) : Prop :=
  SaturationExists T → ExtensionProperty T → QEExStep T

/-- The reduction, with the paper's hypothesis in place. -/
theorem HasQE_of_ShoenfieldTest {T : L.Theory} (h : ShoenfieldTest T) (hSat : SaturationExists T)
    (hEP : ExtensionProperty T) : HasQE T :=
  HasQE_of_QEExStep (h hSat hEP)

/-! ### A sanity instance

The theory of a one-element structure in the empty language admits QE, and both routes
give it: directly, and through the criterion above.  This checks that the step hypothesis
is satisfiable and that the criterion reproduces a known answer.  (A serious validation on
DLO or ACF is *not* attempted here.) -/

namespace OneElement

/-- The empty language. -/
def L0 : Language := ⟨fun _ => Empty, fun _ => Empty⟩

instance (M : Type) : L0.Structure M where
  funMap {_} f := f.elim
  RelMap {_} R := R.elim

/-- `x = y`, with both variables in scope. -/
def sub2 : L0.BoundedFormula Empty 2 :=
  BoundedFormula.equal (Term.var (Sum.inr (0 : Fin 2))) (Term.var (Sum.inr (1 : Fin 2)))

/-- `∀ x ∀ y, x = y`. -/
def subsingletonSentence : L0.Sentence := sub2.alls

/-- The theory of a one-element structure. -/
def T0 : L0.Theory := {subsingletonSentence}

theorem subsingleton_of_model {M : Type*} [L0.Structure M] [M ⊨ T0] : Subsingleton M := by
  have h : Formula.Realize sub2.alls (default : Empty → M) :=
    Theory.realize_sentence_of_mem (T := T0) (φ := subsingletonSentence) (M := M)
      (by simp [T0])
  have h0 : ∀ xs : Fin 2 → M, sub2.Realize (default : Empty → M) xs := by
    simpa only [BoundedFormula.realize_alls] using h
  exact ⟨fun a b => h0 ![a, b]⟩

/-- Every `L0`-formula is either true in every model of `T0` under every valuation, or
false in every model of `T0` under every valuation. -/
theorem valid_or_refutable {α : Type} {n : ℕ} (φ : L0.BoundedFormula α n) :
    T0 ⊨ᵇ φ ∨ T0 ⊨ᵇ φ.not := by
  induction φ with
  | falsum => exact Or.inr fun _ _ _ h => h
  | equal t₁ t₂ =>
      exact Or.inl fun M _ _ => by
        have hsub := subsingleton_of_model (M := M)
        exact hsub.elim _ _
  | rel R _ => exact R.elim
  | imp φ₁ φ₂ ih₁ ih₂ =>
      rcases ih₁ with h₁ | h₁
      · rcases ih₂ with h₂ | h₂
        · exact Or.inl fun M v xs _ => h₂ M v xs
        · exact Or.inr fun M v xs hp => h₂ M v xs (hp (h₁ M v xs))
      · exact Or.inl fun M v xs hp => absurd hp (h₁ M v xs)
  | all φ ih =>
      rcases ih with h | h
      · exact Or.inl fun M v xs => fun a => h M v (Fin.snoc xs a)
      · exact Or.inr fun M v xs hall =>
          h M v (Fin.snoc xs (Classical.arbitrary M)) (hall _)

theorem HasQEb_T0 : HasQEb T0 := by
  intro α n φ
  rcases valid_or_refutable φ with h | h
  · exact ⟨⊤, BoundedFormula.IsQF.top, fun M v xs => by
      rw [BoundedFormula.realize_iff, BoundedFormula.realize_top]
      exact iff_true_intro (h M v xs)⟩
  · exact ⟨⊥, BoundedFormula.isQF_bot, fun M v xs => by
      rw [BoundedFormula.realize_iff, BoundedFormula.realize_bot]
      exact iff_false_intro (h M v xs)⟩

theorem QEExStep_T0 : QEExStep T0 := by
  intro α n θ _
  rcases valid_or_refutable θ.ex with h | h
  · exact ⟨⊤, BoundedFormula.IsQF.top, fun M v xs => by
      rw [BoundedFormula.realize_iff, BoundedFormula.realize_top]
      exact iff_true_intro (h M v xs)⟩
  · exact ⟨⊥, BoundedFormula.isQF_bot, fun M v xs => by
      rw [BoundedFormula.realize_iff, BoundedFormula.realize_bot]
      exact iff_false_intro (h M v xs)⟩

/-- The criterion reproduces the direct proof of QE for `T0`. -/
theorem HasQEb_T0_via_criterion : HasQEb T0 :=
  hasQEb_of_QEAllStep (QEAllStep_iff_QEExStep.2 QEExStep_T0)

end OneElement

end QECriterion

#print axioms QECriterion.hasQEb_iff_QEExStep
#print axioms QECriterion.HasQE_of_QEExStep
#print axioms QECriterion.QEAllStep_iff_QEExStep
