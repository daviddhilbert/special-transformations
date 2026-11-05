import Mathlib

/-!
Johnson's generic quantifier-elimination criterion and its compactness proof.

Extracted from `QE/Assembly_val.lean`, section 20, preserving the existing
proofs and declaration names. This module is independent of the valued-field
language and of the RV encoding. The unused legacy saturation/test examples,
the separate ACF validation, and the duplicated RV snapshot are excluded.

The proof derives existential quantifier-free type invariance from prime models
over substructures, amalgamation, and one-variable existential closedness.
Mathlib compactness then produces uniform quantifier-free formulas, and a
syntactic induction eliminates all quantifiers. No model-theoretic result is
introduced as a new axiom or an external theorem hypothesis.
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-! ## Semantic form of Johnson's criterion -/

namespace JohnsonCriterion

universe u v w w'

variable {L : FirstOrder.Language.{u, v}}

/-! ## 1. Quantifier-free formulas are preserved and reflected by embeddings

The following lemmas prove preservation and reflection for arbitrary embeddings,
without assuming surjectivity. -/

section QFPreserve

variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

theorem embedding_realize_isAtomic (g : M ↪[L] N) {α : Type*} {n : ℕ}
    {φ : L.BoundedFormula α n} (h : φ.IsAtomic) (v : α → M) (xs : Fin n → M) :
    φ.Realize (fun a => g (v a)) (fun i => g (xs i)) ↔ φ.Realize v xs := by
  have hcomp : (Sum.elim (fun a => g (v a)) (fun i => g (xs i)))
      = (fun s => g (Sum.elim v xs s)) := by
    funext s; cases s <;> rfl
  have key : ∀ t : L.Term (α ⊕ Fin n),
      t.realize (Sum.elim (fun a => g (v a)) (fun i => g (xs i)))
        = g (t.realize (Sum.elim v xs)) := by
    intro t; rw [hcomp]; exact HomClass.realize_term g
  cases h with
  | equal t₁ t₂ =>
    simp only [BoundedFormula.realize_bdEqual]
    rw [key t₁, key t₂, g.injective.eq_iff]
  | rel R ts =>
    simp only [BoundedFormula.realize_rel]
    have hrs : (fun i => (ts i).realize (Sum.elim (fun a => g (v a)) (fun i => g (xs i))))
        = (fun i => g ((ts i).realize (Sum.elim v xs))) := by
      funext i; exact key (ts i)
    rw [hrs]
    exact StrongHomClass.map_rel (r := R) g (fun i => (ts i).realize (Sum.elim v xs))

theorem embedding_realize_isQF (g : M ↪[L] N) {α : Type*} {n : ℕ}
    {φ : L.BoundedFormula α n} (h : φ.IsQF) :
    ∀ (v : α → M) (xs : Fin n → M),
      φ.Realize (fun a => g (v a)) (fun i => g (xs i)) ↔ φ.Realize v xs := by
  induction h with
  | falsum => intro v xs; exact Iff.rfl
  | of_isAtomic ha => exact fun v xs => embedding_realize_isAtomic g ha v xs
  | imp _ _ ih1 ih2 => intro v xs; simp only [BoundedFormula.realize_imp, ih1 v xs, ih2 v xs]

end QFPreserve

/-! ## 2. Substituting parameters for terms preserves quantifier-freeness

Needed to move a formula's parameters along an embedding: `OneECIn` is stated for parameters in
the model, while the comparison below happens over a smaller base `S`. -/

section Subst

theorem isAtomic_subst {α β : Type*} {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsAtomic)
    (tf : α → L.Term β) : (φ.subst tf).IsAtomic := by
  cases h with
  | equal t₁ t₂ => exact BoundedFormula.IsAtomic.equal _ _
  | rel R ts => exact BoundedFormula.IsAtomic.rel _ _

theorem isQF_subst {α β : Type*} {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsQF)
    (tf : α → L.Term β) : (φ.subst tf).IsQF := by
  induction h with
  | falsum => exact BoundedFormula.isQF_bot
  | of_isAtomic ha => exact BoundedFormula.IsAtomic.isQF (isAtomic_subst ha tf)
  | imp _ _ ih1 ih2 => exact ih1.imp ih2

end Subst

/-! ## 3. The three hypotheses of Lemma 2.1.4

All three are stated for models of `T₀` bundled as `T₀.ModelType`; the models of `T` are
carried along by an explicit hypothesis `⊨ T`, which is legitimate because `T₀ ⊆ T` in every
application (models of `T` are models of `T₀`, so no generality is lost and no coercion
between bundled models of different theories is ever needed). -/

section Criterion

/-- **1-ec** (Johnson, Definition 2.1.3): `S` is 1-ec in `N` along the embedding `i` if every
non-empty quantifier-free `S`-definable subset of `N` in one variable meets `S`. -/
def OneECIn {S : Type w} {N : Type w'} [L.Structure S] [L.Structure N] (i : S ↪[L] N) : Prop :=
  ∀ (φ : L.BoundedFormula S 1), φ.IsQF →
    (∃ a, φ.Realize (fun s => i s) (fun _ => a)) →
      ∃ s : S, φ.Realize (fun s' => i s') (fun _ => i s)

/-- **Prime models over substructures** (Johnson, Definition 2.1.1): every structure `S`
that embeds into a model of `T` has an extension `S'` modelling `T₀` which embeds into
every model of `T₀` under `S`. The initial embedding assumption restricts the bases `S`;
the universal property quantifies over all models of `T₀`. -/
def HasPrimeModels (T₀ T : L.Theory) : Prop :=
  ∀ (S : Type w) [L.Structure S],
    (∃ (M : T₀.ModelType.{u, v, w}), M ⊨ T ∧ Nonempty (S ↪[L] M)) →
    ∃ (S' : T₀.ModelType.{u, v, w}) (e : S ↪[L] S'),
      ∀ (N : T₀.ModelType.{u, v, w}) (f : S ↪[L] N), ∃ g : S' ↪[L] N, g.comp e = f

/-- **The amalgamation property** (Johnson, Definition 2.1.2). -/
def HasAmalgamation (T : L.Theory) : Prop :=
  ∀ (A B C : T.ModelType.{u, v, w}) (i : A ↪[L] B) (j : A ↪[L] C),
    ∃ (D : T.ModelType.{u, v, w}) (i' : B ↪[L] D) (j' : C ↪[L] D), i'.comp i = j'.comp j

/-- The **conclusion of Lemma 2.1.4**, in the semantic form which the proof establishes:
quantifier-free definable sets over a base have, in any two models of `T`, the same
one-variable existential theory. -/
theorem qfDetermined {T₀ T : L.Theory} (hsub : T₀ ⊆ T)
    (hprime : HasPrimeModels.{u, v, w} T₀ T) (hamal : HasAmalgamation.{u, v, w} T₀)
    (h1ec : ∀ (M N : T₀.ModelType.{u, v, w}) (f : M ↪[L] N), M ⊨ T → OneECIn f)
    (S : Type w) [L.Structure S] (M N : T₀.ModelType.{u, v, w}) (hM : M ⊨ T) (hN : N ⊨ T)
    (i : S ↪[L] M) (j : S ↪[L] N) (φ : L.BoundedFormula S 1) (hφ : φ.IsQF) :
    (∃ a : M, φ.Realize (fun s => i s) (fun _ => a)) ↔
      ∃ b : N, φ.Realize (fun s => j s) (fun _ => b) := by
  -- the prime model of `T₀` over the base `S`
  obtain ⟨S', e, huniv⟩ := hprime S ⟨M, hM, ⟨i⟩⟩
  obtain ⟨gM, hgM⟩ := huniv M i
  obtain ⟨gN, hgN⟩ := huniv N j
  -- amalgamate the two embeddings of `S'` into `M` and `N`
  obtain ⟨D, kM, kN, hcomm⟩ := hamal S' M N gM gN
  -- the formula `φ`, with its parameters moved along the embedding of `S'` into `N`
  set ψ : L.BoundedFormula N 1 := φ.subst (fun s => Term.var (gN.comp e s)) with hψdef
  have hψqf : ψ.IsQF := isQF_subst hφ _
  have hMN : ∀ s, kN ((gN.comp e) s) = kM ((gM.comp e) s) := by
    intro s
    have h := congrArg (fun g : ↑S' ↪[L] ↑D => g (e s)) hcomm
    simpa only [FirstOrder.Language.Embedding.comp_apply] using h.symm
  have hMi : ∀ s, (gM.comp e) s = i s := by
    intro s
    exact congrArg (fun g : S ↪[L] ↑M => g s) hgM
  have hψreal : ∀ a : M, ψ.Realize (fun n => kN n) (fun _ => kM a) ↔
      φ.Realize (fun s => i s) (fun _ => a) := by
    intro a
    rw [hψdef, BoundedFormula.realize_subst]
    simp only [Term.realize_var]
    have hfun : (fun s => kN ((gN.comp e) s)) = (fun s => kM (i s)) := by
      funext s
      rw [hMN s, hMi s]
    rw [hfun]
    exact embedding_realize_isQF kM hφ (fun s => i s) (fun _ => a)
  have hψunfold : ∀ a : N, ψ.Realize (fun n => kN n) (fun _ => kN a) ↔
      φ.Realize (fun s => kN ((gN.comp e) s)) (fun _ => kN a) := by
    intro a
    rw [hψdef, BoundedFormula.realize_subst]
    simp only [Term.realize_var]
  constructor
  · rintro ⟨a, ha⟩
    -- transport the witness to `D`, then use that `N` is 1-ec in `D`
    have hD : ψ.Realize (fun n => kN n) (fun _ => kM a) := (hψreal a).2 ha
    obtain ⟨n₀, hn₀⟩ := h1ec N D kN hN ψ hψqf ⟨kM a, hD⟩
    have h1 : φ.Realize (fun s => kN ((gN.comp e) s)) (fun _ => kN n₀) := (hψunfold n₀).1 hn₀
    have h2 : φ.Realize (fun s => (gN.comp e) s) (fun _ => n₀) :=
      (embedding_realize_isQF kN hφ (fun s => (gN.comp e) s) (fun _ => n₀)).1 h1
    exact ⟨n₀, by rwa [hgN] at h2⟩
  · rintro ⟨b, hb⟩
    -- transport the witness to `D`, now with the parameters written via `M`
    have hb' : φ.Realize (fun s => (gN.comp e) s) (fun _ => b) := by
      rwa [← hgN] at hb
    have hD : φ.Realize (fun s => kN ((gN.comp e) s)) (fun _ => kN b) :=
      (embedding_realize_isQF kN hφ (fun s => (gN.comp e) s) (fun _ => b)).2 hb'
    have hfun : (fun s => kM (i s)) = (fun s => kN ((gN.comp e) s)) := by
      funext s; rw [hMN s, hMi s]
    set χ : L.BoundedFormula M 1 := φ.subst (fun s => Term.var (i s)) with hχdef
    have hχqf : χ.IsQF := isQF_subst hφ _
    have hD' : χ.Realize (fun m => kM m) (fun _ => kN b) := by
      rw [hχdef, BoundedFormula.realize_subst]
      simp only [Term.realize_var]
      rw [hfun]
      exact hD
    -- `M` is a model of `T`, hence 1-ec in every model of `T₀`, in particular in `D`
    obtain ⟨m₀, hm₀⟩ := h1ec M D kM hM χ hχqf ⟨kN b, hD'⟩
    refine ⟨m₀, ?_⟩
    rw [hχdef, BoundedFormula.realize_subst] at hm₀
    simp only [Term.realize_var] at hm₀
    exact (embedding_realize_isQF kM hφ (fun s => i s) (fun _ => m₀)).1 hm₀

end Criterion

end JohnsonCriterion

#print axioms JohnsonCriterion.qfDetermined
#print axioms JohnsonCriterion.embedding_realize_isQF

/-!
## Part 2 — the last mile: from `qfDetermined` to the hypothesis `H`

`JohnsonCriterion.qfDetermined` (Part 1) is the semantic statement: over a structure `S` embedded
in two models `M`, `N` of `T` (with `T₀ ⊆ T`), a one-variable quantifier-free formula with
parameters in `S` has a solution in `M` iff it has one in `N`.

`H` says: the quantifier-free type of a tuple `(v, xs)` in `M` and `(w, ys)` in `N` determines the
truth of `∃ y, θ(v, xs, y)` for quantifier-free `θ`.

The reduction carried out here (nothing about `L` is assumed beyond `Language.{0,0}`):

* let `S₀` be the `L`-substructure of `M` whose carrier is the set of values of *all* `L`-terms
  under the assignment `gM = (v, xs)`;
* the quantifier-free type hypothesis says exactly that "evaluate the same term under
  `gN = (w, ys)`" is a well defined function `S₀ → N`, and that it preserves and reflects
  function and relation symbols: an `L`-embedding `Φ : S₀ ↪[L] N` (`termSubEmb`);
* the first `n` bound variables of `θ` are then substituted by parameters of `S₀` (and the free
  variables `α` by parameters of `S₀` too), leaving a one-variable quantifier-free formula
  `φ : L.BoundedFormula S₀ 1` whose solution set is that of `θ.ex` (`exists_qf_collapse`);
* `qfDetermined` applied to `φ`, the inclusion `S₀ ↪[L] M` and `Φ : S₀ ↪[L] N` gives the claim.

-/

namespace HQEDerive

variable {L : FirstOrder.Language.{0, 0}}

/-! ### 0. Two `Fin.snoc` evaluation lemmas -/

section Snoc

variable {P : Type} {n : ℕ}

/-- `Fin.snoc xs a` is the case analysis `Fin.lastCases a xs`. -/
theorem snoc_eq_lastCases (xs : Fin n → P) (a : P) :
    Fin.snoc (α := fun _ => P) xs a
      = Fin.lastCases (motive := fun _ => P) a xs := by
  funext i
  cases i using Fin.lastCases with
  | last => rw [Fin.snoc_last, Fin.lastCases_last]
  | cast j => rw [Fin.snoc_castSucc, Fin.lastCases_castSucc]

end Snoc

/-! ### 1. The substructure of values of terms -/

section TermSub

variable {M : Type} {N : Type} [L.Structure M] [L.Structure N] {γ : Type*}

/-- The `L`-substructure of `M` consisting of the values of all `L`-terms under the assignment
`g : γ → M`.  (It is the substructure generated by the range of `g`.) -/
def termSub (g : γ → M) : L.Substructure M where
  carrier := Set.range fun t : L.Term γ => t.realize g
  fun_mem := by
    intro k f x hx
    classical
    choose t ht using hx
    refine ⟨Term.func f t, ?_⟩
    show Structure.funMap f (fun i => (t i).realize g) = Structure.funMap f x
    simp only [ht]

theorem mem_termSub {g : γ → M} {x : M} :
    x ∈ (termSub g : L.Substructure M) ↔ ∃ t : L.Term γ, t.realize g = x :=
  Iff.rfl

theorem realize_mem_termSub {g : γ → M} (t : L.Term γ) :
    t.realize g ∈ (termSub g : L.Substructure M) :=
  ⟨t, rfl⟩

/-- The element of `termSub g` given by the variable `x`. -/
def termSubMk (g : γ → M) (x : γ) : termSub (L := L) g :=
  ⟨g x, Term.var x, rfl⟩

@[simp]
theorem termSubMk_val {g : γ → M} (x : γ) : (termSubMk (L := L) g x : M) = g x :=
  rfl

/-- The "same term, evaluated in `g'`" map, as a function on the term-substructure of `g`.  It is
well defined as soon as the two assignments have the same quantifier-free type in the form
`hker`. -/
noncomputable def termSubMap (g : γ → M) (g' : γ → N)
    (hker : ∀ t t' : L.Term γ, (t.realize g = t'.realize g ↔ t.realize g' = t'.realize g')) :
    termSub (L := L) g → N :=
  fun s => (Classical.choose (mem_termSub.1 s.2)).realize g'

theorem termSubMap_eq {g : γ → M} {g' : γ → N}
    {hker : ∀ t t' : L.Term γ,
      (t.realize g = t'.realize g ↔ t.realize g' = t'.realize g')}
    {s : termSub (L := L) g} {t : L.Term γ} (ht : t.realize g = (s : M)) :
    termSubMap (L := L) g g' hker s = t.realize g' :=
  (hker (Classical.choose (mem_termSub.1 s.2)) t).1
    ((Classical.choose_spec (mem_termSub.1 s.2)).trans ht.symm)

theorem termSubMap_injective {g : γ → M} {g' : γ → N}
    {hker : ∀ t t' : L.Term γ,
      (t.realize g = t'.realize g ↔ t.realize g' = t'.realize g')} :
    Function.Injective (termSubMap (L := L) g g' hker) := by
  intro s s' h
  have h2 : (Classical.choose (mem_termSub.1 s.2)).realize g
      = (Classical.choose (mem_termSub.1 s'.2)).realize g :=
    (hker _ _).2 h
  exact Subtype.ext ((Classical.choose_spec (mem_termSub.1 s.2)).symm.trans
    (h2.trans (Classical.choose_spec (mem_termSub.1 s'.2))))

theorem termSubMap_map_fun {g : γ → M} {g' : γ → N}
    {hker : ∀ t t' : L.Term γ,
      (t.realize g = t'.realize g ↔ t.realize g' = t'.realize g')}
    {k : ℕ} (f : L.Functions k) (x : Fin k → termSub (L := L) g) :
    termSubMap (L := L) g g' hker (Structure.funMap f x)
      = Structure.funMap f (fun i => termSubMap g g' hker (x i)) := by
  classical
  choose t ht using fun i => mem_termSub.1 (x i).2
  have hc : (Term.func f t).realize g = ((Structure.funMap f x : termSub g) : M) := by
    show Structure.funMap f (fun i => (t i).realize g) = Structure.funMap f (fun i => ((x i : termSub g) : M))
    simp only [ht]
  rw [termSubMap_eq (hker := hker) hc]
  show Structure.funMap f (fun i => (t i).realize g') = Structure.funMap f (fun i => termSubMap g g' hker (x i))
  congr 1
  funext i
  exact (termSubMap_eq (hker := hker) (s := x i) (t := t i) (ht i)).symm

theorem termSubMap_map_rel {g : γ → M} {g' : γ → N}
    {hker : ∀ t t' : L.Term γ,
      (t.realize g = t'.realize g ↔ t.realize g' = t'.realize g')}
    (hrel : ∀ {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term γ),
      (Structure.RelMap R (fun i => (ts i).realize g) ↔
        Structure.RelMap R (fun i => (ts i).realize g')))
    {k : ℕ} (R : L.Relations k) (x : Fin k → termSub (L := L) g) :
    Structure.RelMap R (fun i => termSubMap g g' hker (x i)) ↔ Structure.RelMap R x := by
  classical
  choose t ht using fun i => mem_termSub.1 (x i).2
  have hx : (fun i => ((x i : termSub g) : M)) = fun i => (t i).realize g := by
    funext i
    exact (ht i).symm
  have hN : (fun i => termSubMap g g' hker (x i)) = fun i => (t i).realize g' := by
    funext i
    exact termSubMap_eq (hker := hker) (s := x i) (t := t i) (ht i)
  rw [hN]
  show Structure.RelMap R (fun i => (t i).realize g')
    ↔ Structure.RelMap R (fun i => ((x i : termSub g) : M))
  rw [hx]
  exact (hrel R t).symm

/-- The induced `L`-embedding of the term-substructure of `g` into `N`, for two assignments with
the same quantifier-free type. -/
noncomputable def termSubEmb (g : γ → M) (g' : γ → N)
    (hker : ∀ t t' : L.Term γ,
      (t.realize g = t'.realize g ↔ t.realize g' = t'.realize g'))
    (hrel : ∀ {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term γ),
      (Structure.RelMap R (fun i => (ts i).realize g) ↔
        Structure.RelMap R (fun i => (ts i).realize g'))) :
    termSub (L := L) g ↪[L] N where
  toFun := termSubMap g g' hker
  inj' := termSubMap_injective (hker := hker)
  map_fun' := fun {k} f x => termSubMap_map_fun (hker := hker) f x
  map_rel' := fun {k} R x => termSubMap_map_rel (hker := hker) hrel R x

theorem termSubEmb_apply_var (g : γ → M) (g' : γ → N)
    (hker : ∀ t t' : L.Term γ,
      (t.realize g = t'.realize g ↔ t.realize g' = t'.realize g'))
    (hrel : ∀ {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term γ),
      (Structure.RelMap R (fun i => (ts i).realize g) ↔
        Structure.RelMap R (fun i => (ts i).realize g')))
    (x : γ) : termSubEmb (L := L) g g' hker hrel (termSubMk g x) = g' x :=
  termSubMap_eq (hker := hker) (s := termSubMk g x) (t := Term.var x) rfl

end TermSub

/-! ### 2. Collapsing bound variables to parameters -/

/-- `Sum.elim` of the two components of `ρ` is `ρ`. -/
theorem sumElim_self {γ δ P : Type*} (ρ : γ ⊕ δ → P) :
    Sum.elim (fun a => ρ (Sum.inl a)) (fun b => ρ (Sum.inr b)) = ρ := by
  funext x
  cases x <;> rfl

section Collapse

variable {α β : Type*} {n : ℕ}

/-- **Replacing every variable by a term.**  If every variable of the quantifier-free formula
`θ : L.BoundedFormula α (n+1)` is replaced by the term `σ` (a term over the free variables `β`
and one bound variable), the result is a quantifier-free formula `φ : L.BoundedFormula β 1` whose
truth under the assignment `ρ` is the truth of `θ` under the induced assignment. -/
theorem exists_qf_collapse (σ : α ⊕ Fin (n + 1) → L.Term (β ⊕ Fin 1))
    {θ : L.BoundedFormula α (n + 1)} (hθ : θ.IsQF) :
    ∃ φ : L.BoundedFormula β 1, φ.IsQF ∧
      ∀ (P : Type) [L.Structure P] (ρ : β ⊕ Fin 1 → P),
        (φ.Realize (fun b => ρ (Sum.inl b)) (fun i => ρ (Sum.inr i)) ↔
          θ.Realize (fun a => (σ (Sum.inl a)).realize ρ)
            (fun i => (σ (Sum.inr i)).realize ρ)) := by
  induction hθ with
  | falsum => exact ⟨⊥, BoundedFormula.isQF_bot, fun P _ ρ => Iff.rfl⟩
  | of_isAtomic h =>
      induction h with
      | equal t₁ t₂ =>
          exact ⟨Term.bdEqual (t₁.subst σ) (t₂.subst σ),
            (BoundedFormula.IsAtomic.equal _ _).isQF,
            fun P _ ρ => by
              simp only [BoundedFormula.realize_bdEqual, Term.realize_subst]
              rw [sumElim_self ρ, sumElim_self (fun a => Term.realize ρ (σ a))]⟩
      | rel R ts =>
          exact ⟨R.boundedFormula (fun i => (ts i).subst σ),
            (BoundedFormula.IsAtomic.rel _ _).isQF,
            fun P _ ρ => by
              simp only [BoundedFormula.realize_rel, Term.realize_subst]
              rw [sumElim_self ρ, sumElim_self (fun a => Term.realize ρ (σ a))]⟩
  | imp h1 h2 ih1 ih2 =>
      obtain ⟨φ₁, hφ₁, hr₁⟩ := ih1
      obtain ⟨φ₂, hφ₂, hr₂⟩ := ih2
      exact ⟨φ₁.imp φ₂, hφ₁.imp hφ₂, fun P _ ρ => by
        simp only [BoundedFormula.realize_imp, hr₁ P ρ, hr₂ P ρ]⟩

end Collapse

/-! ### 3. The main derivation: Johnson's criterion implies `H` -/

section Main

variable {T₀ T : L.Theory}

/-- **The last mile.**  Johnson's criterion (`JohnsonCriterion.qfDetermined`) and its three
hypotheses give the hypothesis `H` consumed by `hasQE_of_qfDet`
(`QE/Merged_end_to_end.lean`): the quantifier-free type of a tuple determines the truth of one
existential quantifier in front of a quantifier-free formula.

The statement is *exactly* the hypothesis `H` of `hasQE_of_qfDet` at `L : Language.{0,0}`,
`α : Type`, models `Theory.ModelType.{0,0,0}`. -/
theorem H_of_qfDetermined (hsub : T₀ ⊆ T)
    (hprime : JohnsonCriterion.HasPrimeModels.{0, 0, 0} T₀ T)
    (hamal : JohnsonCriterion.HasAmalgamation.{0, 0, 0} T₀)
    (h1ec : ∀ (M N : T₀.ModelType.{0, 0, 0}) (f : M ↪[L] N), M ⊨ T →
      JohnsonCriterion.OneECIn f) :
    ∀ (α : Type) (n : ℕ) (θ : L.BoundedFormula α (n + 1)), θ.IsQF →
      ∀ (M N : Theory.ModelType.{0, 0, 0} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier)
        (w : α → N.Carrier) (ys : Fin n → N.Carrier),
        (∀ ψ : L.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
        ((θ.ex).Realize v xs ↔ (θ.ex).Realize w ys) := by
  intro α n θ hθ M N v xs w ys hQF
  classical
  -- the two assignments
  let gM : (α ⊕ Fin n) → M.Carrier := Sum.elim v xs
  let gN : (α ⊕ Fin n) → N.Carrier := Sum.elim w ys
  -- the substructure of `M` consisting of the values of the terms in the tuple
  let S₀ : L.Substructure M.Carrier := termSub (L := L) gM
  -- the quantifier-free type hypothesis, in the two forms used below
  have hker : ∀ t t' : L.Term (α ⊕ Fin n),
      (t.realize gM = t'.realize gM ↔ t.realize gN = t'.realize gN) := by
    intro t t'
    have h := hQF (Term.bdEqual t t') (BoundedFormula.IsAtomic.equal t t' |>.isQF)
    simpa only [BoundedFormula.realize_bdEqual, gM, gN] using h
  have hrel : ∀ {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin n)),
      (Structure.RelMap R (fun i => (ts i).realize gM) ↔
        Structure.RelMap R (fun i => (ts i).realize gN)) := by
    intro k R ts
    have h := hQF (R.boundedFormula ts) (BoundedFormula.IsAtomic.rel R ts |>.isQF)
    simpa only [BoundedFormula.realize_rel, gM, gN] using h
  -- the two embeddings of the base substructure into `M` and into `N`
  let incl : S₀ ↪[L] M.Carrier := S₀.subtype
  let Φ : S₀ ↪[L] N.Carrier := termSubEmb (L := L) gM gN hker hrel
  -- replace every variable of `θ` by a term: parameters of `S₀` for `α` and for the first `n`
  -- bound variables, and the single remaining bound variable for the last one
  let σ : α ⊕ Fin (n + 1) → L.Term (S₀ ⊕ Fin 1) := fun x =>
    match x with
    | Sum.inl a => Term.var (Sum.inl (termSubMk (L := L) gM (Sum.inl a)))
    | Sum.inr i =>
        Fin.lastCases (motive := fun _ => L.Term (S₀ ⊕ Fin 1)) (Term.var (Sum.inr 0))
          (fun j : Fin n => Term.var (Sum.inl (termSubMk (L := L) gM (Sum.inr j)))) i
  obtain ⟨φ, hφqf, hφreal⟩ := exists_qf_collapse (L := L) (β := S₀) σ hθ
  -- the two sides of `qfDetermined` are the two sides of `H`
  have hMreal : ∀ a : M.Carrier,
      (φ.Realize (fun s : S₀ => (incl s : M.Carrier)) (fun _ => a) ↔
        θ.Realize v (Fin.snoc xs a)) := by
    intro a
    let ρM : S₀ ⊕ Fin 1 → M.Carrier :=
      Sum.elim (fun s : S₀ => (s : M.Carrier)) (fun _ : Fin 1 => a)
    have h1 := hφreal M.Carrier ρM
    have hval1 : (fun a' => (σ (Sum.inl a')).realize ρM) = v := by
      funext a'
      show (termSubMk (L := L) gM (Sum.inl a') : M.Carrier) = v a'
      rfl
    have hval2 : (fun i => (σ (Sum.inr i)).realize ρM) = Fin.snoc xs a := by
      have h2 : (fun i => (σ (Sum.inr i)).realize ρM)
          = Fin.lastCases (motive := fun _ => M.Carrier) a xs := by
        funext i
        cases i using Fin.lastCases with
        | last =>
            simp only [σ, Fin.lastCases_last]
            rfl
        | cast j =>
            simp only [σ, Fin.lastCases_castSucc]
            rfl
      exact h2.trans (snoc_eq_lastCases xs a).symm
    exact h1.trans (by rw [hval1, hval2])
  have hNreal : ∀ b : N.Carrier,
      (φ.Realize (fun s : S₀ => (Φ s : N.Carrier)) (fun _ => b) ↔
        θ.Realize w (Fin.snoc ys b)) := by
    intro b
    let ρN : S₀ ⊕ Fin 1 → N.Carrier :=
      Sum.elim (fun s : S₀ => (Φ s : N.Carrier)) (fun _ : Fin 1 => b)
    have h1 := hφreal N.Carrier ρN
    have hval1 : (fun a' => (σ (Sum.inl a')).realize ρN) = w := by
      funext a'
      show (Φ (termSubMk (L := L) gM (Sum.inl a')) : N.Carrier) = w a'
      exact termSubEmb_apply_var (L := L) gM gN hker hrel (Sum.inl a')
    have hval2 : (fun i => (σ (Sum.inr i)).realize ρN) = Fin.snoc ys b := by
      have h2 : (fun i => (σ (Sum.inr i)).realize ρN)
          = Fin.lastCases (motive := fun _ => N.Carrier) b ys := by
        funext i
        cases i using Fin.lastCases with
        | last =>
            simp only [σ, Fin.lastCases_last]
            rfl
        | cast j =>
            simp only [σ, Fin.lastCases_castSucc]
            exact termSubEmb_apply_var (L := L) gM gN hker hrel (Sum.inr j)
      exact h2.trans (snoc_eq_lastCases ys b).symm
    exact h1.trans (by rw [hval1, hval2])
  -- the two models, now bundled over `T₀`
  haveI hMT₀ : M.Carrier ⊨ T₀ := Theory.Model.mono (Theory.ModelType.is_model (self := M)) hsub
  haveI hNT₀ : N.Carrier ⊨ T₀ := Theory.Model.mono (Theory.ModelType.is_model (self := N)) hsub
  let M' : T₀.ModelType.{0, 0, 0} := Theory.ModelType.of T₀ M.Carrier
  let N' : T₀.ModelType.{0, 0, 0} := Theory.ModelType.of T₀ N.Carrier
  have hM'T : M' ⊨ T := Theory.ModelType.is_model (self := M)
  have hN'T : N' ⊨ T := Theory.ModelType.is_model (self := N)
  -- Johnson's criterion, over the base `S₀`
  have hdet := JohnsonCriterion.qfDetermined (L := L) hsub hprime hamal h1ec
    S₀ M' N' hM'T hN'T incl Φ φ hφqf
  rw [BoundedFormula.realize_ex, BoundedFormula.realize_ex]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨a', ha'⟩ := hdet.1 ⟨a, (hMreal a).2 ha⟩
    exact ⟨a', (hNreal a').1 ha'⟩
  · rintro ⟨b, hb⟩
    obtain ⟨b', hb'⟩ := hdet.2 ⟨b, (hNreal b).2 hb⟩
    exact ⟨b', (hMreal b').1 hb'⟩

end Main

end HQEDerive

#print axioms HQEDerive.H_of_qfDetermined
/-!
## From one-step elimination to full quantifier elimination

`HasQEb T` says: every bounded formula is `T`-equivalent to a quantifier-free one.
`QEAllStep T` / `QEExStep T` say: one universal / existential quantifier applied to a
quantifier-free formula can be removed.

Main results:
* `QEAllStep_iff_QEExStep`  -- the two steps are equivalent;
* `hasQEb_iff_QEAllStep`    -- either step is *equivalent* to full QE;
* `HasQE_of_QEAllStep`     -- the step gives QE for `Formula`.

The compactness argument below derives `QEExStep` from existential quantifier-free
type determinacy. It works directly with bounded formulas, and the syntactic
induction here then eliminates all quantifiers. No saturation assumption is used.
-/

set_option linter.unusedVariables false

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

/-- Formula-level quantifier elimination: every formula, with arbitrary free-variable
type, is `T`-equivalent to a quantifier-free formula. `HasQEb` above retains the
stronger presentation allowing any number of bound variables already in scope. -/
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

end QECriterion


namespace ShoenfieldQE

variable {L : FirstOrder.Language.{u, v}}

/-!
# The compactness argument for bounded formulas

The formula-level compactness interface consumes `Formula`, while `QEExStep` needs
`BoundedFormula α n`. The argument below works in `BoundedFormula α n`, using
`toFormula` **only on the way into**
compactness: given a finite set of `Formula`s in the image, the corresponding bounded formulas
are chosen by `Finset.attach` plus choice, and the witness is pushed forward again. No inverse
of `toFormula` is needed.

Contents, all in `BoundedFormula α n`:
* `exists_realize_bounded` — compactness for bounded formulas;
* `lifsup`/`liinf` with `isQF_lifsup`/`isQF_liinf` and `realize_lifsup`/`realize_liinf`;
* `exists_qf_imp_bounded` — isolation: under QF-type invariance for `β`, an assignment
  satisfying `β` is separated from its complement by a QF formula implying `β`.

The finite cover and the final `QEExStep` assembly are also proved below.
-/

/-! ## Quantifier elimination, formula level

`HasQE T` is the formula-level statement that every `L`-formula is `T`-equivalent to a
quantifier-free one, for an arbitrary language `L`. -/

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

/-- **End to end**: existential quantifier-free type determinacy gives ordinary
formula-level quantifier elimination. The universe-zero formulation matches the
valued-field application of `QECriterion.HasQE`. -/
theorem hasQE_of_qfDet {L₀ : FirstOrder.Language.{0, 0}} {T : L₀.Theory}
    (H : ∀ (α : Type) (n : ℕ) (θ : L₀.BoundedFormula α (n + 1)), θ.IsQF →
      ∀ (M N : Theory.ModelType.{0, 0, 0} T) (v : α → M.Carrier)
        (xs : Fin n → M.Carrier) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
        (∀ ψ : L₀.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
        ((θ.ex).Realize v xs ↔ (θ.ex).Realize w ys)) :
    QECriterion.HasQE (L := L₀) T :=
  QECriterion.HasQE_of_QEExStep (BoundedQE.qeExStep_theoryIff (L₀ := L₀) H)

#print axioms hasQE_of_qfDet

/-! ## The join: Johnson's hypotheses give quantifier elimination -/

namespace HQEDerive

variable {L : FirstOrder.Language.{0, 0}} {T₀ T : L.Theory}

/-- **Johnson's Lemma 2.1.4, syntactically**: prime models over substructures, amalgamation and
`T`-models 1-ec in models of `T₀` give ordinary formula-level quantifier elimination for `T`.

No hypothesis beyond Johnson's three is left over: the last mile `H` is
`HQEDerive.H_of_qfDetermined` (proved above) and the compactness join is `hasQE_of_qfDet`. -/
theorem hasQE_of_johnson (hsub : T₀ ⊆ T)
    (hprime : JohnsonCriterion.HasPrimeModels.{0, 0, 0} T₀ T)
    (hamal : JohnsonCriterion.HasAmalgamation.{0, 0, 0} T₀)
    (h1ec : ∀ (M N : T₀.ModelType.{0, 0, 0}) (f : M ↪[L] N), M ⊨ T →
      JohnsonCriterion.OneECIn f) :
    QECriterion.HasQE (L := L) T :=
  hasQE_of_qfDet (L₀ := L) (T := T) (H_of_qfDetermined hsub hprime hamal h1ec)

end HQEDerive

#print axioms HQEDerive.hasQE_of_johnson

