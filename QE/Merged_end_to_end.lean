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


namespace ShoenfieldQE

variable {L : FirstOrder.Language.{u, v}}

/-!
# The compactness argument for bounded formulas

`BoundedFormula.toFormula : BoundedFormula α n → Formula (α ⊕ Fin n)` has no converse in
Mathlib, and the formula-level compactness argument produces its output on the `Formula` side
while `QEExStep` consumes `BoundedFormula α n`. This file removes that obstruction by running
the whole argument in `BoundedFormula α n`, using `toFormula` **only on the way into**
compactness: given a finite set of `Formula`s in the image, the corresponding bounded formulas
are chosen by `Finset.attach` plus choice, and the witness is pushed forward again. No inverse
of `toFormula` is needed.

Contents, all in `BoundedFormula α n`:
* `exists_realize_bounded` — compactness for bounded formulas;
* `lifsup`/`liinf` with `isQF_lifsup`/`isQF_liinf` and `realize_lifsup`/`realize_liinf`;
* `exists_qf_imp_bounded` — isolation: under QF-type invariance for `β`, an assignment
  satisfying `β` is separated from its complement by a QF formula implying `β`.

Not yet done: the cover and the final `QEExStep` assembly, which is mechanical given
`exists_qf_imp_bounded` and `exists_realize_bounded`.
-/

/-! ## Quantifier elimination, formula level

`HasQE T` is the formula-level statement that every `L`-formula is `T`-equivalent to a
quantifier-free one.  It has the same shape as `SpecialTransformations.Milestone0.HasQE`
(`Milestone0/Encoding.lean`), only at a general language `L`. -/

/-- `T` admits quantifier elimination. -/
def HasQE (T : L.Theory) : Prop :=
  ∀ (α : Type u) (φ : L.Formula α), ∃ ψ : L.Formula α, ψ.IsQF ∧ T ⊨ᵇ (φ ⇔ ψ)

/-! ## Finite conjunctions and disjunctions -/

section Finite

variable {α : Type u} {β : Type*}

lemma isQF_listFoldr_sup (l : List β) (f : β → L.Formula α) (h : ∀ b ∈ l, (f b).IsQF) :
    (l.map f).foldr (· ⊔ ·) ⊥ |>.IsQF := by
  induction l with
  | nil => exact BoundedFormula.isQF_bot
  | cons a l ih =>
      rw [List.map_cons, List.foldr_cons]
      exact (h a (by simp)).sup (ih (fun b hb => h b (by simp [hb])))

lemma isQF_listFoldr_inf (l : List β) (f : β → L.Formula α)
    (h : ∀ b ∈ l, (f b).IsQF) : (l.map f).foldr (· ⊓ ·) ⊤ |>.IsQF := by
  induction l with
  | nil => exact BoundedFormula.IsQF.top
  | cons a l ih =>
      rw [List.map_cons, List.foldr_cons]
      exact (h a (by simp)).inf (ih (fun b hb => h b (by simp [hb])))

/-- A finite disjunction of quantifier-free formulas is quantifier-free. -/
lemma isQF_iSup {β : Type*} [Finite β] (f : β → L.Formula α) (h : ∀ b, (f b).IsQF) :
    (Formula.iSup f).IsQF := by
  classical
  rw [Formula.iSup, BoundedFormula.iSup]
  exact isQF_listFoldr_sup _ f (fun b _ => h b)

/-- A finite conjunction of quantifier-free formulas is quantifier-free. -/
lemma isQF_iInf {β : Type*} [Finite β] (f : β → L.Formula α) (h : ∀ b, (f b).IsQF) :
    (Formula.iInf f).IsQF := by
  classical
  rw [Formula.iInf, BoundedFormula.iInf]
  exact isQF_listFoldr_inf _ f (fun b _ => h b)

/-- The realization of a finite disjunction of formulas. -/
lemma realize_iSup {β : Type*} [Finite β] (f : β → L.Formula α) {M : Type*} [L.Structure M]
    (v : α → M) : (Formula.iSup f).Realize v ↔ ∃ b, (f b).Realize v :=
  BoundedFormula.realize_iSup

/-- The realization of a finite conjunction of formulas. -/
lemma realize_iInf {β : Type*} [Finite β] (f : β → L.Formula α) {M : Type*} [L.Structure M]
    (v : α → M) : (Formula.iInf f).Realize v ↔ ∀ b, (f b).Realize v :=
  BoundedFormula.realize_iInf

end Finite

/-! ## Compactness for a set of formulas with free variables -/

/-- **Compactness, realization form.** If every finite set of formulas taken from `Γ` can be
realized together with `φ` in a model of `T`, then `Γ` itself can be realized together with `φ`. -/
theorem exists_model_realize_of_finset {α : Type u} {T : L.Theory} {Γ : Set (L.Formula α)}
    {φ : L.Formula α}
    (h : ∀ Γ0 : Finset (L.Formula α), (∀ ψ ∈ Γ0, ψ ∈ Γ) →
      ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier),
        (∀ ψ ∈ Γ0, ψ.Realize v) ∧ φ.Realize v) :
    ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier),
      (∀ ψ ∈ Γ, ψ.Realize v) ∧ φ.Realize v := by
  classical
  set U : (L[[α]]).Theory :=
    (L.lhomWithConstants α).onTheory T ∪ Formula.equivSentence '' Γ ∪
      {Formula.equivSentence φ} with hUdef
  have hfin : U.IsFinitelySatisfiable := by
    intro U0 hU0
    -- the part of `Γ` that shows up in `U0`
    set Γ0 : Finset (L.Formula α) :=
      (U0.filter (fun s => s ∈ Formula.equivSentence '' Γ)).image
        (fun s => Formula.equivSentence.symm s) with hΓ0def
    have hΓ0 : ∀ ψ ∈ Γ0, ψ ∈ Γ := by
      intro ψ hψ
      obtain ⟨s, hs, hseq⟩ := Finset.mem_image.mp hψ
      obtain ⟨-, hs2⟩ := Finset.mem_filter.mp hs
      obtain ⟨ψ', hψ', hψ'eq⟩ := (Set.mem_image _ _ _).mp hs2
      rw [← hseq, ← hψ'eq, Equiv.symm_apply_apply]
      exact hψ'
    obtain ⟨M, v, hv, hφv⟩ := h Γ0 hΓ0
    letI : (constantsOn α).Structure M.Carrier := constantsOn.structure v
    have hmem : ∀ s ∈ U0, M.Carrier ⊨ s := by
      intro s hs
      have hsU : s ∈ U := hU0 hs
      simp only [hUdef, Set.mem_union, Set.mem_image, Set.mem_singleton_iff] at hsU
      rcases hsU with (hsT | ⟨ψ, hψ, hψs⟩) | hφs
      · exact ((LHom.onTheory_model (L.lhomWithConstants α) T).2 M.is_model).realize_of_mem s hsT
      · rw [← hψs] at hs ⊢
        refine (Formula.realize_equivSentence M.Carrier ψ).2 (hv ψ ?_)
        rw [hΓ0def]
        exact Finset.mem_image.mpr
          ⟨Formula.equivSentence ψ, Finset.mem_filter.mpr ⟨hs, ⟨ψ, hψ, rfl⟩⟩, by simp⟩
      · rw [hφs]
        exact (Formula.realize_equivSentence M.Carrier φ).2 hφv
    haveI : M.Carrier ⊨ (U0 : (L[[α]]).Theory) := ⟨fun s hs => hmem s hs⟩
    exact Theory.Model.isSatisfiable M.Carrier
  obtain ⟨N⟩ := Theory.isSatisfiable_iff_isFinitelySatisfiable.2 hfin
  have hNU : ∀ s ∈ U, N.Carrier ⊨ s := fun s hs => N.is_model.realize_of_mem s hs
  letI : L.Structure N.Carrier := (L.lhomWithConstants α).reduct N.Carrier
  have hNT : N.Carrier ⊨ T :=
    (LHom.onTheory_model (L.lhomWithConstants α) T).1
      ⟨fun s hs => hNU s (by rw [hUdef]; exact Or.inl (Or.inl hs))⟩
  refine ⟨Theory.ModelType.of T N.Carrier, fun a => (L.con a : N.Carrier), ?_, ?_⟩
  · intro ψ hψ
    refine (Formula.realize_equivSentence N.Carrier ψ).1 (hNU _ ?_)
    rw [hUdef]
    exact Or.inl (Or.inr ⟨ψ, hψ, rfl⟩)
  · refine (Formula.realize_equivSentence N.Carrier φ).1 (hNU _ ?_)
    rw [hUdef]
    exact Or.inr rfl


end ShoenfieldQE

namespace BoundedQE

open ShoenfieldQE

variable {L : FirstOrder.Language.{u, v}}

/-- `T`-equivalence of bounded formulas with the same context. -/
def IffB (T : L.Theory) {α : Type u} {n : ℕ} (φ ψ : L.BoundedFormula α n) : Prop :=
  ∀ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier),
    (φ.Realize v xs ↔ ψ.Realize v xs)

/-- One existential quantifier in front of a quantifier-free formula can be removed. -/
def QEExStep (T : L.Theory) : Prop :=
  ∀ (α : Type u) (n : ℕ) (θ : L.BoundedFormula α (n + 1)), θ.IsQF →
    ∃ ψ : L.BoundedFormula α n, ψ.IsQF ∧ IffB T θ.ex ψ

/-- **Compactness for bounded formulas.** Only the *forward* map `toFormula` is used: finite sets
are pulled back along membership in its image by choice, which needs no inverse. -/
theorem exists_realize_bounded {α : Type u} {n : ℕ} {T : L.Theory}
    {Γ : Set (L.BoundedFormula α n)} {β : L.BoundedFormula α n}
    (h : ∀ Γ0 : Finset (L.BoundedFormula α n), (∀ ψ ∈ Γ0, ψ ∈ Γ) →
      ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier),
        (∀ ψ ∈ Γ0, ψ.Realize v xs) ∧ β.Realize v xs) :
    ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier),
      (∀ ψ ∈ Γ, ψ.Realize v xs) ∧ β.Realize v xs := by
  classical
  set Γ' : Set (L.Formula (α ⊕ Fin n)) := BoundedFormula.toFormula '' Γ with hΓ'def
  have hfin : ∀ Γ0 : Finset (L.Formula (α ⊕ Fin n)), (∀ ψ ∈ Γ0, ψ ∈ Γ') →
      ∃ (M : Theory.ModelType.{u, v, max u v} T) (V : α ⊕ Fin n → M.Carrier),
        (∀ ψ ∈ Γ0, ψ.Realize V) ∧ β.toFormula.Realize V := by
    intro Γ0 hΓ0
    choose f hfΓ hfeq using fun (ψ : ↥Γ0) => (Set.mem_image _ _ _).mp (hΓ0 ψ.1 ψ.2)
    set Γ0' : Finset (L.BoundedFormula α n) := Γ0.attach.image f with hΓ0'def
    have hΓ0'mem : ∀ ψ ∈ Γ0', ψ ∈ Γ := by
      intro ψ hψ
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hψ
      exact hfΓ j
    obtain ⟨M, v, xs, hall, hβ⟩ := h Γ0' hΓ0'mem
    refine ⟨M, Sum.elim v xs, ?_, ?_⟩
    · intro ψ hψ
      have hmem : f ⟨ψ, hψ⟩ ∈ Γ0' :=
        Finset.mem_image.mpr ⟨⟨ψ, hψ⟩, Finset.mem_attach _ _, rfl⟩
      have h1 := hall _ hmem
      have h2 : (f ⟨ψ, hψ⟩).toFormula = ψ := hfeq ⟨ψ, hψ⟩
      rw [← h2, BoundedFormula.realize_toFormula]
      simpa using h1
    · rw [BoundedFormula.realize_toFormula]
      simpa using hβ
  obtain ⟨M, V, hV, hβV⟩ :=
    ShoenfieldQE.exists_model_realize_of_finset (T := T) (Γ := Γ') (φ := β.toFormula) hfin
  refine ⟨M, V ∘ Sum.inl, V ∘ Sum.inr, ?_, ?_⟩
  · intro ψ hψ
    have h1 := hV _ (Set.mem_image_of_mem _ hψ)
    rwa [BoundedFormula.realize_toFormula] at h1
  · have h1 := hβV
    rwa [BoundedFormula.realize_toFormula] at h1

end BoundedQE

namespace BoundedQE

open ShoenfieldQE

variable {L : FirstOrder.Language.{u, v}}

/-- Finite disjunction of bounded formulas, by a list fold. -/
noncomputable def lifsup {α : Type u} {n : ℕ} (l : List (L.BoundedFormula α n)) :
    L.BoundedFormula α n :=
  l.foldr (· ⊔ ·) ⊥

/-- Finite conjunction of bounded formulas, by a list fold. -/
noncomputable def liinf {α : Type u} {n : ℕ} (l : List (L.BoundedFormula α n)) :
    L.BoundedFormula α n :=
  l.foldr (· ⊓ ·) ⊤

theorem isQF_lifsup {α : Type u} {n : ℕ} {l : List (L.BoundedFormula α n)}
    (h : ∀ ψ ∈ l, ψ.IsQF) : (lifsup l).IsQF := by
  induction l with
  | nil => exact BoundedFormula.isQF_bot
  | cons a t ih =>
    exact BoundedFormula.IsQF.sup (h a (List.mem_cons_self))
      (ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))

theorem isQF_liinf {α : Type u} {n : ℕ} {l : List (L.BoundedFormula α n)}
    (h : ∀ ψ ∈ l, ψ.IsQF) : (liinf l).IsQF := by
  induction l with
  | nil => exact BoundedFormula.IsQF.top
  | cons a t ih =>
    exact BoundedFormula.IsQF.inf (h a (List.mem_cons_self))
      (ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))

theorem realize_lifsup {α : Type u} {n : ℕ} {l : List (L.BoundedFormula α n)}
    {M : Type*} [L.Structure M] (v : α → M) (xs : Fin n → M) :
    (lifsup l).Realize v xs ↔ ∃ ψ ∈ l, ψ.Realize v xs := by
  induction l with
  | nil => simp [lifsup, BoundedFormula.realize_bot]
  | cons a t ih =>
    rw [show lifsup (a :: t) = a ⊔ lifsup t from rfl, BoundedFormula.realize_sup, ih]
    simp only [List.mem_cons]
    constructor
    · rintro (h | ⟨ψ, hψ, hreal⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨ψ, Or.inr hψ, hreal⟩
    · rintro ⟨ψ, (rfl | hψ), hreal⟩
      · exact Or.inl hreal
      · exact Or.inr ⟨ψ, hψ, hreal⟩

theorem realize_liinf {α : Type u} {n : ℕ} {l : List (L.BoundedFormula α n)}
    {M : Type*} [L.Structure M] (v : α → M) (xs : Fin n → M) :
    (liinf l).Realize v xs ↔ ∀ ψ ∈ l, ψ.Realize v xs := by
  induction l with
  | nil => simp [liinf, BoundedFormula.realize_top]
  | cons a t ih =>
    rw [show liinf (a :: t) = a ⊓ liinf t from rfl, BoundedFormula.realize_inf, ih]
    simp only [List.mem_cons]
    constructor
    · rintro ⟨h, ht⟩ ψ (rfl | hψ)
      · exact h
      · exact ht ψ hψ
    · intro h
      exact ⟨h a (Or.inl rfl), fun ψ hψ => h ψ (Or.inr hψ)⟩

/-- **Isolation**, bounded form. -/
theorem exists_qf_imp_bounded {α : Type u} {n : ℕ} {T : L.Theory} {β : L.BoundedFormula α n}
    (Hβ : ∀ (M N : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier)
      (xs : Fin n → M.Carrier) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
      (∀ ψ : L.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
      (β.Realize v xs ↔ β.Realize w ys))
    (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier)
    (hβ : β.Realize v xs) :
    ∃ ψ : L.BoundedFormula α n, ψ.IsQF ∧ ψ.Realize v xs ∧
      ∀ (N : Theory.ModelType.{u, v, max u v} T) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
        ψ.Realize w ys → β.Realize w ys := by
  classical
  by_contra hcon
  push Not at hcon
  set Γ : Set (L.BoundedFormula α n) := {ψ | ψ.IsQF ∧ ψ.Realize v xs} with hΓdef
  have hfin : ∀ Γ0 : Finset (L.BoundedFormula α n), (∀ ψ ∈ Γ0, ψ ∈ Γ) →
      ∃ (N : Theory.ModelType.{u, v, max u v} T) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
        (∀ ψ ∈ Γ0, ψ.Realize w ys) ∧ β.not.Realize w ys := by
    intro Γ0 hΓ0
    have hq : ∀ ψ ∈ Γ0.val.toList, ψ.IsQF :=
      fun ψ hψ => (hΓ0 ψ (Finset.mem_val.mp (Multiset.mem_toList.mp hψ))).1
    have hr : ∀ ψ ∈ Γ0.val.toList, ψ.Realize v xs :=
      fun ψ hψ => (hΓ0 ψ (Finset.mem_val.mp (Multiset.mem_toList.mp hψ))).2
    obtain ⟨N, w, ys, h1, h2⟩ :=
      hcon _ (isQF_liinf hq) ((realize_liinf v xs).2 hr)
    exact ⟨N, w, ys,
      fun ψ hψ => (realize_liinf w ys).1 h1 ψ
        (Multiset.mem_toList.mpr (Finset.mem_val.mpr hψ)),
      (BoundedFormula.realize_not).2 h2⟩
  obtain ⟨N, w, ys, hw, hnβ⟩ := exists_realize_bounded (T := T) hfin
  have htypes : ∀ ψ : L.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys) := by
    intro ψ hψ
    constructor
    · intro hvψ
      exact hw ψ ⟨hψ, hvψ⟩
    · intro hwψ
      by_contra hvψ
      have hcontr := hw ψ.not ⟨hψ.not, (BoundedFormula.realize_not).2 hvψ⟩
      rw [BoundedFormula.realize_not] at hcontr
      exact hcontr hwψ
  have hiff := Hβ M N v xs w ys htypes
  rw [BoundedFormula.realize_not] at hnβ
  exact hnβ (hiff.mp hβ)

/-! ## The cover and the assembly -/

/-- **`QFExDetermined` gives `QEExStep`.** The cover is produced by contradiction: if no finite
set of quantifier-free consequences covered `θ.ex`, bounded compactness would give a tuple
satisfying `θ.ex` and falsifying every quantifier-free consequence of it, contradicting the
isolation lemma. -/
theorem qeExStep_of_qfDet {T : L.Theory}
    (H : ∀ (α : Type u) (n : ℕ) (θ : L.BoundedFormula α (n + 1)), θ.IsQF →
      ∀ (M N : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier)
        (xs : Fin n → M.Carrier) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
        (∀ ψ : L.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
        ((θ.ex).Realize v xs ↔ (θ.ex).Realize w ys)) :
    QEExStep (L := L) T := by
  intro α n θ hθ
  classical
  have Hβ := H α n θ hθ
  set Ψ : Set (L.BoundedFormula α n) :=
    {ψ | ψ.IsQF ∧ ∀ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier)
      (xs : Fin n → M.Carrier), ψ.Realize v xs → (θ.ex).Realize v xs} with hΨdef
  have hcov : ∃ Ψ0 : Finset (L.BoundedFormula α n), (∀ ψ ∈ Ψ0, ψ ∈ Ψ) ∧
      ∀ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier),
        (θ.ex).Realize v xs → (lifsup Ψ0.val.toList).Realize v xs := by
    by_contra hno
    push Not at hno
    set Γ : Set (L.BoundedFormula α n) := {η | ∃ ψ ∈ Ψ, ψ.not = η} with hΓdef
    have hfin : ∀ Γ0 : Finset (L.BoundedFormula α n), (∀ η ∈ Γ0, η ∈ Γ) →
        ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier)
          (xs : Fin n → M.Carrier),
          (∀ η ∈ Γ0, η.Realize v xs) ∧ (θ.ex).Realize v xs := by
      intro Γ0 hΓ0
      have hchoice : ∀ η : ↥Γ0, ∃ ψ ∈ Ψ, ψ.not = η.1 := fun η => hΓ0 η.1 η.2
      choose f hfΨ hfeq using hchoice
      set Ψ0 : Finset (L.BoundedFormula α n) := Γ0.attach.image f with hΨ0def
      have hΨ0 : ∀ ψ ∈ Ψ0, ψ ∈ Ψ := by
        intro ψ hψ
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hψ
        exact hfΨ j
      obtain ⟨M, v, xs, hθex, hnoψ⟩ := hno Ψ0 hΨ0
      refine ⟨M, v, xs, ?_, hθex⟩
      intro η hη
      have hmem : f ⟨η, hη⟩ ∈ Ψ0 :=
        Finset.mem_image.mpr ⟨⟨η, hη⟩, Finset.mem_attach _ _, rfl⟩
      have hfalse : ¬ (f ⟨η, hη⟩).Realize v xs := by
        intro htrue
        exact hnoψ ((realize_lifsup v xs).2 ⟨_, Multiset.mem_toList.mpr hmem, htrue⟩)
      have heq : (f ⟨η, hη⟩).not = η := hfeq ⟨η, hη⟩
      rw [← heq, BoundedFormula.realize_not]
      exact hfalse
    obtain ⟨M, v, xs, hΓ0, hθex⟩ := exists_realize_bounded (T := T) hfin
    obtain ⟨ψ0, hqf0, htrue0, himp0⟩ := exists_qf_imp_bounded (T := T) Hβ M v xs hθex
    have hmemΨ : ψ0 ∈ Ψ := ⟨hqf0, himp0⟩
    have hnotmem : ψ0.not ∈ Γ := ⟨ψ0, hmemΨ, rfl⟩
    have hcontra := hΓ0 ψ0.not hnotmem
    rw [BoundedFormula.realize_not] at hcontra
    exact hcontra htrue0
  obtain ⟨Ψ0, hΨ0, hcov⟩ := hcov
  refine ⟨lifsup Ψ0.val.toList,
    isQF_lifsup (fun ψ hψ => (hΨ0 ψ (Multiset.mem_toList.mp hψ)).1), ?_⟩
  intro M v xs
  constructor
  · intro h
    exact hcov M v xs h
  · intro h
    obtain ⟨ψ, hψl, hψtrue⟩ := (realize_lifsup v xs).1 h
    exact (hΨ0 ψ (Multiset.mem_toList.mp hψl)).2 M v xs hψtrue

end BoundedQE


#print axioms BoundedQE.exists_realize_bounded
#print axioms BoundedQE.exists_qf_imp_bounded
#print axioms BoundedQE.isQF_lifsup
#print axioms BoundedQE.realize_liinf

namespace BoundedQE

open QECriterion

/-- **The join.** `QEExStep` in the form `QE_step_induction.lean` consumes, from the
quantifier-free-existential determinism that Johnson's criterion produces.

Stated at `L₀ : Language.{0, 0}` and `α : Type`, the universe level of `QECriterion.QEExStep`. -/
theorem qeExStep_theoryIff {L₀ : FirstOrder.Language.{0, 0}} {T : L₀.Theory}
    (H : ∀ (α : Type) (n : ℕ) (θ : L₀.BoundedFormula α (n + 1)), θ.IsQF →
      ∀ (M N : Theory.ModelType.{0, 0, 0} T) (v : α → M.Carrier)
        (xs : Fin n → M.Carrier) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
        (∀ ψ : L₀.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
        ((θ.ex).Realize v xs ↔ (θ.ex).Realize w ys)) :
    QECriterion.QEExStep (L := L₀) T := by
  intro α n θ hθ
  obtain ⟨ψ, hqf, hiffB⟩ := qeExStep_of_qfDet (L := L₀) H α n θ hθ
  refine ⟨ψ, hqf, ?_⟩
  intro M v xs
  rw [BoundedFormula.realize_iff]
  exact hiffB M v xs

end BoundedQE

/-- **End to end**: quantifier-free-existential determinism gives quantifier elimination, in the
shape stated in `Milestone0/Encoding.lean`.

Stated at `L : Language.{0, 0}` and `α : Type`, which is the universe level at which
`QECriterion.HasQE` (and the frozen `SpecialTransformations.Milestone0.HasQE`) live. -/
theorem hasQE_of_qfDet {L₀ : FirstOrder.Language.{0, 0}} {T : L₀.Theory}
    (H : ∀ (α : Type) (n : ℕ) (θ : L₀.BoundedFormula α (n + 1)), θ.IsQF →
      ∀ (M N : Theory.ModelType.{0, 0, 0} T) (v : α → M.Carrier)
        (xs : Fin n → M.Carrier) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
        (∀ ψ : L₀.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
        ((θ.ex).Realize v xs ↔ (θ.ex).Realize w ys)) :
    QECriterion.HasQE (L := L₀) T :=
  QECriterion.HasQE_of_QEExStep (BoundedQE.qeExStep_theoryIff (L₀ := L₀) H)

#print axioms hasQE_of_qfDet
