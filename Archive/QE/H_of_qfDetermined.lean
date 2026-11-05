/-
  Johnson's saturation-free criterion for quantifier elimination
  (Lemma 2.1.4 of W. Johnson, *Fun with Fields*, Chapter 2; extracted at
  `.ultramath/refs/johnson-ch2.txt`).

  Johnson's Lemma 2.1.4: let `T₀` be a theory with (i) prime models over substructures and
  (ii) the amalgamation property.  Suppose the 1-ec models of `T₀` are an elementary class,
  axiomatized by a theory `T`.  Then `T` has quantifier elimination.

  Here the conclusion is proved in the *semantic* form that Johnson's proof produces, and
  which is the substantive half of quantifier elimination:

    for any structure `S`, any two models `M`, `N` of `T` containing `S`, and any
    quantifier-free formula `φ(x; s)` with one free variable and parameters in `S`,
    `φ` has a solution in `M` iff it has a solution in `N`.

  ("Models of `T` are determined, over any base, by quantifier-free behaviour.")  The
  passage from this to the syntactic statement "every formula is `T`-equivalent to a
  quantifier-free formula" is a compactness argument; see the notes at the end.

  Nothing about `L` is assumed: this is the abstract criterion.  It is instantiated at
  `L = Language.ring`, `T₀ = Theory.field` and `T` = the theory of algebraically closed
  fields in `ACF.lean`, which is the validation asked for by the task.

  Only import: Mathlib.
-/
import Mathlib

open FirstOrder FirstOrder.Language
open scoped FirstOrder

set_option linter.style.haveILetI false

namespace JohnsonCriterion

universe u v w w'

variable {L : FirstOrder.Language.{u, v}}

/-! ## 1. Quantifier-free formulas are preserved and reflected by embeddings

Mathlib has `StrongHomClass.realize_boundedFormula`, but only for `EquivLike` maps (surjective
ones).  For a general embedding only quantifier-free formulas are preserved, and that lemma is
not in Mathlib.  (The same lemma is `embedding_realize_isQF` in
`QE/Semantics_saturation.lean`; it is restated here so that the file is self-contained.) -/

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

/-- **Prime models over substructures** (Johnson, Definition 2.1.1), in the restricted form in
which the definition is used in the proof: every structure `S` that embeds into a model of `T`
has an extension `S'` modelling `T₀` which embeds into every model of `T₀` under `S`.  (In
Johnson's definition the last quantifier runs over all models of `T₀`; here only over models
that are themselves models of `T`, which is all the proof needs.) -/
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

Only `import Mathlib`.
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder

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
