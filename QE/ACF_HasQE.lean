/-
  **Quantifier elimination for algebraically closed fields — unconditional.**

  Main theorem (end of the file):

    `HQEDerive.HasQE_acf : QECriterion.HasQE (L := Language.ring) ACFValidation.acf`

  with its frozen-shape forms `HasQE_acf_frozen`
  (`∀ α φ, ∃ ψ, ψ.IsQF ∧ acf ⊨ᵇ (φ ⇔ ψ)`), `hasQE_frozen_acf` (`ShoenfieldQE.HasQE acf`) and the
  bounded form `HasQEb_acf`.

  The file is self-contained (`import Mathlib` only) and consists of verbatim copies of compiled
  artifacts, in this order:

  * `QE/Johnson_criterion.lean` — Johnson's Lemma 2.1.4 in the semantic form his argument
    produces (`JohnsonCriterion.qfDetermined`), §0–§3 of that file.
  * namespace `HQEDerive` (§ "Part 2", "Part 3" of this file) — **the last mile**: the hypothesis
    `H` of `hasQE_of_qfDet` is derived from `qfDetermined` (`H_of_qfDetermined`), and Johnson's
    three hypotheses are turned into `QECriterion.HasQE T` for any `L : Language.{0,0}`
    (`hasQE_of_johnson`).
  * `QE/Merged_end_to_end.lean` — the compactness join `hasQE_of_qfDet` (`QECriterion` and
    `BoundedQE` namespaces).
  * `QE/ACF_validation.lean` — the three ACF hypotheses (`field_subset_acf`,
    `amalgamation_field` = Johnson §2.2, `oneEC_field_acf` = Johnson Claim 2.1.5).
  * member m3's `.ultramath/smw0bll3t/m3/PrimeModels_full.lean`, wrapped in `namespace M3` —
    `HasPrimeModels Theory.field acf` unconditionally (gap (B)).
  * §5 — the assembly.

  No `sorry`, no `axiom`, no `native_decide`; `#print axioms` on each headline theorem gives
  `[propext, Classical.choice, Quot.sound]` (see the end of the file).

  Check: `cd repo && lean .ultramath/smw0bll3t/m1/ACF_HasQE_unconditional.lean` prints nothing and
  exits 0.
-/

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

/-! ## The join: Johnson's hypotheses give quantifier elimination -/

namespace HQEDerive

variable {L : FirstOrder.Language.{0, 0}} {T₀ T : L.Theory}

/-- **Johnson's Lemma 2.1.4, syntactically**: prime models over substructures, amalgamation and
`T`-models 1-ec in models of `T₀` give quantifier elimination for `T`, in the frozen shape
(`QECriterion.HasQE`, the same as `SpecialTransformations.Milestone0.HasQE`).

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
/-
  **Validation of the criterion at ACF**: quantifier elimination for algebraically closed
  fields through Johnson's Lemma 2.1.4 (`Criterion.lean`), with `T₀` = the theory of fields and
  `T` = the theory of algebraically closed fields.  This is Johnson's Claim 2.1.5 together with
  the one-page derivation in Chapter 2 §2.1 of *Fun with Fields*.

  The three hypotheses of the criterion are proved here:
  * prime models over substructures: the fraction field of a domain (`IsFractionRing.lift`);
  * amalgamation: `K₁ ⊗_{K₀} K₂` is nontrivial and a quotient by a maximal ideal is a field
    (`Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain`);
  * 1-ec = algebraically closed: a quantifier-free `K`-definable set in a field extension of an
    algebraically closed `K` is finite or cofinite *with the finite set inside `K`*, because a
    nonzero polynomial over `K` splits over `K` and hence has all its roots in `K`.

  Only import: Mathlib.
-/

open FirstOrder FirstOrder.Language
open FirstOrder.Ring
open Polynomial
open scoped FirstOrder

set_option linter.style.haveILetI false

set_option backward.isDefEq.respectTransparency false

namespace ACFValidation

/-! ## 1. The theory of algebraically closed fields (no characteristic fixed) -/

/-- The theory of algebraically closed fields, as a theory in the language of rings
(characteristic is not fixed: `Theory.ACF p` for a fixed `p` is not the class of 1-ec fields,
since a field of characteristic `0` is 1-ec in the theory of fields and does not model
`Theory.ACF p` for `p > 0`). -/
noncomputable def acf : Theory Language.ring :=
  Theory.field ∪ Field.genericMonicPolyHasRoot '' {n : ℕ | 0 < n}

theorem field_subset_acf : Theory.field ⊆ acf := Set.subset_union_left

instance acfModel {K : Type*} [Field K] [CompatibleRing K] [IsAlgClosed K] : acf.Model K := by
  refine Theory.model_union_iff.2 ⟨inferInstance, ?_⟩
  simp only [Theory.model_iff, Set.mem_image, forall_exists_index, and_imp]
  rintro _ n hn0 rfl
  simp only [Field.realize_genericMonicPolyHasRoot]
  rintro ⟨p, _, rfl⟩
  exact IsAlgClosed.exists_root p
    (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.1 hn0))

/-- A model of `acf` (with its ring structure made compatible) is algebraically closed. -/
theorem isAlgClosed_of_model_acf (K : Type*) [Field K] [CompatibleRing K] [h : acf.Model K] :
    IsAlgClosed K := by
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hpi
  have h' : K ⊨ Field.genericMonicPolyHasRoot '' {n : ℕ | 0 < n} :=
    Theory.Model.mono h (by simp [acf])
  simp only [Theory.model_iff, Set.mem_image, forall_exists_index, and_imp] at h'
  have hp := h' _ p.natDegree (Polynomial.natDegree_pos_iff_degree_pos.2
    (Polynomial.degree_pos_of_irreducible hpi)) rfl
  rw [Field.realize_genericMonicPolyHasRoot] at hp
  exact hp ⟨p, hpm, rfl⟩

/-! ## 2. Ring homomorphisms and `Language.ring`-embeddings -/

section Conversions

variable {A B : Type*} [CommRing A] [CommRing B] [CompatibleRing A] [CompatibleRing B]

theorem ringHom_map_fun (f : A →+* B) {n : ℕ} (g : Language.ring.Functions n)
    (x : Fin n → A) : f (Structure.funMap g x) = Structure.funMap g (f ∘ x) := by
  cases g <;> simp

/-- A ring homomorphism is a homomorphism for the language of rings. -/
def homOfRingHom (f : A →+* B) : A →[Language.ring] B where
  toFun := f
  map_fun' := ringHom_map_fun f
  map_rel' := by intro n R; exact isEmptyElim R

/-- An injective ring homomorphism is an embedding for the language of rings. -/
def embeddingOfInjectiveRingHom (f : A →+* B) (hf : Function.Injective f) :
    A ↪[Language.ring] B where
  toFun := f
  inj' := hf
  map_fun' := ringHom_map_fun f
  map_rel' := by intro n R; exact isEmptyElim R

/-- An embedding for the language of rings gives a ring homomorphism. -/
def ringHomOfEmbedding (f : A ↪[Language.ring] B) : A →+* B where
  toFun := f
  map_zero' := by simpa using f.map_fun (zeroFunc) (fun i => i.elim0)
  map_one' := by simpa using f.map_fun (oneFunc) (fun i => i.elim0)
  map_add' x y := by
    have h := f.map_fun (addFunc) ![x, y]
    simpa using h
  map_mul' x y := by
    have h := f.map_fun (mulFunc) ![x, y]
    simpa using h

theorem ringHomOfEmbedding_injective (f : A ↪[Language.ring] B) :
    Function.Injective (ringHomOfEmbedding f) := fun x y h => f.injective h

end Conversions

/-! ## 3. Terms are polynomials, and roots of a polynomial over an algebraically closed field
lie in the field -/

section Poly

variable {K : Type*} [CommRing K]

/-- Read a term of the language of rings (with parameters in `K` and one free variable) in the
free commutative ring on the parameters and the variable. -/
noncomputable def termToFreeCommRing (t : Language.ring.Term (K ⊕ Fin 1)) :
    FreeCommRing (K ⊕ Fin 1) :=
  letI : CompatibleRing (FreeCommRing (K ⊕ Fin 1)) := compatibleRingOfRing _
  t.realize FreeCommRing.of

/-- The polynomial in one variable represented by a term of the language of rings with
parameters in `K` and a single free variable: send the free variable to `X` and the parameters
to constants. -/
noncomputable def termToPoly (t : Language.ring.Term (K ⊕ Fin 1)) : K[X] :=
  FreeCommRing.lift (Sum.elim (fun k => Polynomial.C k) (fun _ => Polynomial.X))
    (termToFreeCommRing t)

variable {N : Type*} [CommRing N] [CompatibleRing N]

theorem realize_eq_lift (t : Language.ring.Term (K ⊕ Fin 1)) (v : K ⊕ Fin 1 → N) :
    t.realize v = FreeCommRing.lift v (termToFreeCommRing t) := by
  letI : CompatibleRing (FreeCommRing (K ⊕ Fin 1)) := compatibleRingOfRing _
  induction t with
  | var s => simp [termToFreeCommRing]
  | func g ts ih =>
    cases g with
    | add => simp only [termToFreeCommRing, Term.realize_func, CompatibleRing.funMap_add,
        map_add, ih]
    | mul => simp only [termToFreeCommRing, Term.realize_func, CompatibleRing.funMap_mul,
        map_mul, ih]
    | neg => simp only [termToFreeCommRing, Term.realize_func, CompatibleRing.funMap_neg,
        map_neg, ih]
    | zero => simp only [termToFreeCommRing, Term.realize_func, CompatibleRing.funMap_zero,
        map_zero]
    | one => simp only [termToFreeCommRing, Term.realize_func, CompatibleRing.funMap_one,
        map_one]

theorem eval₂_termToPoly (f : K →+* N) (t : Language.ring.Term (K ⊕ Fin 1)) (β : N) :
    t.realize (Sum.elim (fun k => f k) (fun _ => β)) = (termToPoly t).eval₂ f β := by
  rw [realize_eq_lift, termToPoly]
  have key : ∀ y : FreeCommRing (K ⊕ Fin 1),
      (FreeCommRing.lift (Sum.elim (fun k => Polynomial.C k) (fun _ => Polynomial.X)) y).eval₂ f β
        = FreeCommRing.lift (Sum.elim (fun k => f k) (fun _ => β)) y := by
    intro y
    induction y using FreeCommRing.induction_on with
    | neg_one => simp
    | of a =>
      cases a with
      | inl k => simp
      | inr i => fin_cases i; simp
    | add x y hx hy => simp [hx, hy]
    | mul x y hx hy => simp [hx, hy]
  exact (key (termToFreeCommRing t)).symm

end Poly

section Roots

variable {K : Type*} [Field K] [IsAlgClosed K]
variable {N : Type*} [Field N]

/-- Over an algebraically closed field, the roots in an extension of a nonzero polynomial are
finite and lie in the base field. -/
theorem finite_rootSet (f : K →+* N) (q : K[X]) (hq : q ≠ 0) :
    {β : N | q.eval₂ f β = 0}.Finite ∧ {β : N | q.eval₂ f β = 0} ⊆ Set.range f := by
  suffices H : ∀ (n : ℕ) (q : K[X]), q.natDegree ≤ n → q ≠ 0 →
      ({β : N | q.eval₂ f β = 0}.Finite ∧
        {β : N | q.eval₂ f β = 0} ⊆ Set.range f) by
    exact H q.natDegree q le_rfl hq
  intro n
  induction n with
  | zero =>
    intro q hn hq
    have hdeg : q.natDegree = 0 := Nat.le_zero.mp hn
    have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have hc : q.coeff 0 ≠ 0 := by
      intro h; apply hq; rw [hqC, h, Polynomial.C_0]
    have hempty : {β : N | q.eval₂ f β = 0} = ∅ := by
      ext β
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rw [hqC, Polynomial.eval₂_C]
      intro h
      exact hc (f.injective (by simpa using h))
    rw [hempty]
    exact ⟨Set.finite_empty, Set.empty_subset _⟩
  | succ n ih =>
    intro q hn hq
    rcases Nat.eq_zero_or_pos q.natDegree with h0 | hpos
    · have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
      have hc : q.coeff 0 ≠ 0 := by
        intro h; apply hq; rw [hqC, h, Polynomial.C_0]
      have hempty : {β : N | q.eval₂ f β = 0} = ∅ := by
        ext β
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rw [hqC, Polynomial.eval₂_C]
        intro h
        exact hc (f.injective (by simpa using h))
      rw [hempty]
      exact ⟨Set.finite_empty, Set.empty_subset _⟩
    · have hdeg : q.degree ≠ 0 := by
        rw [Polynomial.degree_eq_natDegree hq]
        simpa using hpos.ne'
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_root q hdeg
      obtain ⟨q₁, hq₁⟩ := (Polynomial.dvd_iff_isRoot (p := q)).2 hr
      have hq₁ne : q₁ ≠ 0 := by
        rintro rfl; rw [mul_zero] at hq₁; exact hq hq₁
      have hdegq : q.natDegree = q₁.natDegree + 1 := by
        rw [hq₁, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hq₁ne,
          Polynomial.natDegree_X_sub_C, add_comm]
      have hle : q₁.natDegree ≤ n := by omega
      obtain ⟨hfin, hsub⟩ := ih q₁ hle hq₁ne
      have hset : {β : N | q.eval₂ f β = 0}
          = {f r} ∪ {β : N | q₁.eval₂ f β = 0} := by
        ext β
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
        rw [hq₁]
        simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X,
          Polynomial.eval₂_C]
        constructor
        · intro h
          rcases mul_eq_zero.mp h with h' | h'
          · exact Or.inl (sub_eq_zero.mp h')
          · exact Or.inr h'
        · rintro (h' | h')
          · rw [h', sub_self, zero_mul]
          · rw [h', mul_zero]
      rw [hset]
      exact ⟨(Set.finite_singleton _).union hfin,
        Set.union_subset (fun x hx => ⟨r, hx.symm⟩) hsub⟩

end Roots

/-! ## 4. Claim 2.1.5: a quantifier-free definable set over an algebraically closed field

The substantive half: if `K` is algebraically closed and `f : K →+* N` is an injection into a
field, every non-empty quantifier-free `K`-definable subset of `N` in one variable meets `K`. -/

section OneEC

variable {K : Type*} [Field K] [IsAlgClosed K]
variable {N : Type*} [Field N] [CompatibleRing N]

/-- The Boolean algebra of "good" subsets of an extension `N` of `K`: finite sets inside `K`, or
complements of such.  Johnson's Claim 2.1.5 is that quantifier-free `K`-definable sets are
good; the point of the notion is that a non-empty good set meets `K`. -/
def Good (f : K →+* N) (S : Set N) : Prop :=
  (S.Finite ∧ S ⊆ Set.range f) ∨ (Sᶜ.Finite ∧ Sᶜ ⊆ Set.range f)

theorem good_empty (f : K →+* N) : Good f ∅ :=
  Or.inl ⟨Set.finite_empty, Set.empty_subset _⟩

theorem good_compl {f : K →+* N} {S : Set N} (h : Good f S) : Good f Sᶜ := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨by simpa using h1, by simpa using h2⟩
  · exact Or.inl ⟨by simpa using h1, by simpa using h2⟩

theorem good_univ (f : K →+* N) : Good f (Set.univ : Set N) := by
  simpa using good_compl (good_empty f)

theorem good_union {f : K →+* N} {S T : Set N} (hS : Good f S) (hT : Good f T) :
    Good f (S ∪ T) := by
  have hsub : (S ∪ T)ᶜ ⊆ Sᶜ := Set.compl_subset_compl.mpr (Set.subset_union_left)
  have hsub' : (S ∪ T)ᶜ ⊆ Tᶜ := Set.compl_subset_compl.mpr (Set.subset_union_right)
  rcases hS with ⟨hS1, hS2⟩ | ⟨hS1, hS2⟩
  · rcases hT with ⟨hT1, hT2⟩ | ⟨hT1, hT2⟩
    · exact Or.inl ⟨hS1.union hT1, Set.union_subset hS2 hT2⟩
    · exact Or.inr ⟨hT1.subset hsub', fun x hx => hT2 (hsub' hx)⟩
  · rcases hT with ⟨hT1, hT2⟩ | ⟨hT1, hT2⟩
    · exact Or.inr ⟨hS1.subset hsub, fun x hx => hS2 (hsub hx)⟩
    · exact Or.inr ⟨hS1.subset hsub, fun x hx => hS2 (hsub hx)⟩

/-- A non-empty good set meets the image of `K` (this is where infinitude of `K` is used). -/
theorem exists_mem_range_of_good {f : K →+* N} {S : Set N} (hS : Good f S)
    (hne : S.Nonempty) : ∃ k : K, f k ∈ S := by
  rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨k, hk⟩ := h2 ha
    exact ⟨k, hk ▸ ha⟩
  · obtain ⟨a, ha⟩ := hne
    have hcoe : ((h1.toFinset : Finset N) : Set N) = Sᶜ := h1.coe_toFinset
    have hpre : (f ⁻¹' Sᶜ).Finite := by
      have hsub : f ⁻¹' Sᶜ ⊆ ((h1.toFinset.preimage f (fun x _ y _ h => f.injective h) : Finset K) : Set K) := by
        intro k hk
        simp only [Set.mem_preimage] at hk
        refine Finset.mem_preimage.mpr ?_
        have hmem : f k ∈ (h1.toFinset : Set N) := by rw [hcoe]; exact hk
        simpa using hmem
      exact (h1.toFinset.preimage f (fun x _ y _ h => f.injective h)).finite_toSet.subset hsub
    obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset
      (h1.toFinset.preimage f (fun x _ y _ h => f.injective h))
    exact ⟨k, by simpa using hk⟩

/-- **Quantifier-free definable sets over an algebraically closed field are good.** -/
theorem good_solSet {f : K →+* N} (φ : Language.ring.BoundedFormula K 1) (hφ : φ.IsQF) :
    Good f {a : N | φ.Realize (fun k => f k) (fun _ => a)} := by
  refine BoundedFormula.IsQF.recOn
    (motive := fun ψ _ => Good f {a : N | ψ.Realize (fun k => f k) (fun _ => a)}) hφ ?_ ?_ ?_
  · -- `⊥`
    have hset : {a : N | (BoundedFormula.falsum : Language.ring.BoundedFormula K 1).Realize
        (fun k => f k) (fun _ => a)} = ∅ := by
      ext a
      exact ⟨fun h => h, fun h => h.elim⟩
    rw [hset]; exact good_empty f
  · -- atomic
    intro ψ ha
    cases ha with
    | equal t₁ t₂ =>
      set p : K[X] := termToPoly t₁ - termToPoly t₂ with hp
      have hset : {a : N | (Term.bdEqual t₁ t₂).Realize (fun k => f k) (fun _ => a)}
          = {a : N | p.eval₂ f a = 0} := by
        ext a
        simp only [BoundedFormula.realize_bdEqual, Set.mem_setOf_eq, hp]
        rw [eval₂_termToPoly f t₁ a, eval₂_termToPoly f t₂ a,
          Polynomial.eval₂_sub, sub_eq_zero]
      rw [hset]
      by_cases hp0 : p = 0
      · have huniv : {a : N | p.eval₂ f a = 0} = Set.univ := by
          ext a; simp [hp0]
        rw [huniv]; exact good_univ f
      · exact Or.inl (finite_rootSet f p hp0)
    | rel R ts => exact isEmptyElim R
  · -- `⟹`
    intro φ₁ φ₂ _ _ ih1 ih2
    have hset : {a : N | (φ₁.imp φ₂).Realize (fun k => f k) (fun _ => a)}
        = {a : N | φ₁.Realize (fun k => f k) (fun _ => a)}ᶜ
          ∪ {a : N | φ₂.Realize (fun k => f k) (fun _ => a)} := by
      ext a
      simp only [BoundedFormula.realize_imp, Set.mem_setOf_eq, Set.mem_union,
        Set.mem_compl_iff]
      tauto
    rw [hset]
    exact good_union (good_compl ih1) ih2

/-- **Claim 2.1.5, hard direction**: an algebraically closed field is 1-ec in every field
extension, for quantifier-free formulas in one variable. -/
theorem exists_solution_in_range {f : K →+* N} (φ : Language.ring.BoundedFormula K 1)
    (hφ : φ.IsQF) (h : ∃ a : N, φ.Realize (fun k => f k) (fun _ => a)) :
    ∃ k : K, φ.Realize (fun k' => f k') (fun _ => f k) := by
  obtain ⟨k, hk⟩ := exists_mem_range_of_good (good_solSet φ hφ) ⟨_, h.choose_spec⟩
  exact ⟨k, hk⟩

end OneEC


/-! ## 5. The criterion of Lemma 2.1.4 (self-contained copy of `Criterion.lean`)

`Criterion.lean` proves Johnson's Lemma 2.1.4 for an arbitrary language, with
`import Mathlib` as its only import.  It is copied here so that this file, too, has
`import Mathlib` as its only import and can instantiate the criterion at ACF. -/

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


/-! ## 6. Discharging the hypotheses at ACF -/


section Hypotheses

open scoped TensorProduct

/-! ### 6.1 Models of `acf` are 1-ec in every field extension (Claim 2.1.5, via §4) -/

theorem oneEC_field_acf (M N : Theory.field.ModelType) (f : M ↪[Language.ring] N)
    (hM : M ⊨ acf) : JohnsonCriterion.OneECIn f := by
  letI : Field M := FirstOrder.Field.fieldOfModelField M
  letI : CompatibleRing M := FirstOrder.Field.compatibleRingOfModelField M
  letI : Field N := FirstOrder.Field.fieldOfModelField N
  letI : CompatibleRing N := FirstOrder.Field.compatibleRingOfModelField N
  haveI : acf.Model M := hM
  haveI : IsAlgClosed M := isAlgClosed_of_model_acf M
  intro φ hφ h
  exact exists_solution_in_range (f := ringHomOfEmbedding f) φ hφ h

/-! ### 6.2 Amalgamation of the theory of fields (§2.2: `K₁ ⊗_{K₀} K₂`) -/

universe u

theorem ringHom_injective_of_field {F R : Type*} [Field F] [CommRing R] [Nontrivial R]
    (g : F →+* R) : Function.Injective g := by
  intro x y hxy
  have h : g (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h' : x - y = 0 := by
    by_contra hne
    have hunit : IsUnit (x - y) := isUnit_iff_ne_zero.mpr hne
    have hunit' : IsUnit (g (x - y)) := hunit.map g
    rw [h] at hunit'
    exact not_isUnit_zero hunit'
  exact sub_eq_zero.mp h'

theorem amalgamation_field (A B C : Theory.field.ModelType.{0, 0, u})
    (i : A ↪[Language.ring] B) (j : A ↪[Language.ring] C) :
    ∃ (D : Theory.field.ModelType.{0, 0, u}) (i' : B ↪[Language.ring] D)
      (j' : C ↪[Language.ring] D), i'.comp i = j'.comp j := by
  letI : Field A := FirstOrder.Field.fieldOfModelField A
  letI : CompatibleRing A := FirstOrder.Field.compatibleRingOfModelField A
  letI : Field B := FirstOrder.Field.fieldOfModelField B
  letI : CompatibleRing B := FirstOrder.Field.compatibleRingOfModelField B
  letI : Field C := FirstOrder.Field.fieldOfModelField C
  letI : CompatibleRing C := FirstOrder.Field.compatibleRingOfModelField C
  let fA : A →+* B := ringHomOfEmbedding i
  let fB : A →+* C := ringHomOfEmbedding j
  letI : Algebra A B := fA.toAlgebra
  letI : Algebra A C := fB.toAlgebra
  have hfA : Function.Injective (algebraMap A B) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact ringHomOfEmbedding_injective i
  have hfB : Function.Injective (algebraMap A C) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact ringHomOfEmbedding_injective j
  haveI : Nontrivial (B ⊗[A] C) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain A B C hfA hfB
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (B ⊗[A] C)
  haveI : m.IsMaximal := hm
  letI : Field ((B ⊗[A] C) ⧸ m) := Ideal.Quotient.field m
  letI : CompatibleRing ((B ⊗[A] C) ⧸ m) := compatibleRingOfRing _
  let D : Theory.field.ModelType.{0, 0, u} :=
    Theory.ModelType.of Theory.field ((B ⊗[A] C) ⧸ m)
  let iB : B →+* ((B ⊗[A] C) ⧸ m) :=
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom (R := A))
  let jC : C →+* ((B ⊗[A] C) ⧸ m) :=
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight.toRingHom)
  have hiB : Function.Injective iB := ringHom_injective_of_field iB
  have hjC : Function.Injective jC := ringHom_injective_of_field jC
  refine ⟨D, embeddingOfInjectiveRingHom iB hiB, embeddingOfInjectiveRingHom jC hjC, ?_⟩
  ext a
  show iB (fA a) = jC (fB a)
  have h1 : iB (fA a) = Ideal.Quotient.mk m (algebraMap A B a ⊗ₜ[A] 1) := by
    simp [iB, Algebra.TensorProduct.includeLeft_apply, RingHom.algebraMap_toAlgebra]
  have h2 : jC (fB a) = Ideal.Quotient.mk m (1 ⊗ₜ[A] algebraMap A C a) := by
    simp [jC, Algebra.TensorProduct.includeRight_apply, RingHom.algebraMap_toAlgebra]
  rw [h1, h2, Algebra.TensorProduct.tmul_one_eq_one_tmul]

end Hypotheses


/-! ## 7. Quantifier elimination for ACF through the criterion

The instance of Lemma 2.1.4 used here takes the **base to be a model of `T₀`** (a field): that
is the standard formulation of quantifier elimination for ACF (`E` a field, `M`, `N`
algebraically closed extensions of `E`), and for such bases the prime-model hypothesis of
Definition 2.1.1 is trivial (`S' = S`).  The general hypothesis — prime models over *arbitrary*
substructures of models of `T`, i.e. `S' = Frac(S)` for an abstract integral domain `S` in the
language of rings — is not discharged in this file; see the notes at the end. -/

namespace JohnsonCriterion

universe uq vq wq

/-- Lemma 2.1.4 with the base required to be a model of `T₀` (for such a base the
prime-model hypothesis is automatic). -/
theorem qfDetermined_base_model {L : FirstOrder.Language.{uq, vq}}
    {T₀ T : L.Theory}
    (hamal : HasAmalgamation.{uq, vq, wq} T₀)
    (h1ec : ∀ (M N : T₀.ModelType.{uq, vq, wq}) (f : M ↪[L] N), M ⊨ T → OneECIn f)
    (E : T₀.ModelType.{uq, vq, wq}) (M N : T₀.ModelType.{uq, vq, wq}) (hM : M ⊨ T) (hN : N ⊨ T)
    (i : E ↪[L] M) (j : E ↪[L] N) (φ : L.BoundedFormula E 1) (hφ : φ.IsQF) :
    (∃ a : M, φ.Realize (fun s => i s) (fun _ => a)) ↔
      ∃ b : N, φ.Realize (fun s => j s) (fun _ => b) := by
  obtain ⟨D, kM, kN, hcomm⟩ := hamal E M N i j
  set ψ : L.BoundedFormula N 1 := φ.subst (fun s => Term.var (j s)) with hψdef
  have hψqf : ψ.IsQF := isQF_subst hφ _
  have hMN : ∀ s : E, kN (j s) = kM (i s) := by
    intro s
    have h := congrArg (fun g : E ↪[L] D => g s) hcomm
    simpa only [FirstOrder.Language.Embedding.comp_apply] using h.symm
  have hψunfold : ∀ d : D, ψ.Realize (fun n => kN n) (fun _ => d) ↔
      φ.Realize (fun s => kN (j s)) (fun _ => d) := by
    intro d
    rw [hψdef, BoundedFormula.realize_subst]
    simp only [Term.realize_var]
  have hψreal : ∀ a : M, ψ.Realize (fun n => kN n) (fun _ => kM a) ↔
      φ.Realize (fun s => i s) (fun _ => a) := by
    intro a
    rw [hψunfold]
    have hfun : (fun s => kN (j s)) = (fun s => kM (i s)) := funext hMN
    rw [hfun]
    exact embedding_realize_isQF kM hφ (fun s => i s) (fun _ => a)
  constructor
  · rintro ⟨a, ha⟩
    have hD : ψ.Realize (fun n => kN n) (fun _ => kM a) := (hψreal a).2 ha
    obtain ⟨n₀, hn₀⟩ := h1ec N D kN hN ψ hψqf ⟨kM a, hD⟩
    have h1 : φ.Realize (fun s => kN (j s)) (fun _ => kN n₀) := (hψunfold (kN n₀)).1 hn₀
    have h2 : φ.Realize (fun s => j s) (fun _ => n₀) :=
      (embedding_realize_isQF kN hφ (fun s => j s) (fun _ => n₀)).1 h1
    exact ⟨n₀, h2⟩
  · rintro ⟨b, hb⟩
    have hb' : φ.Realize (fun s => kN (j s)) (fun _ => kN b) :=
      (embedding_realize_isQF kN hφ (fun s => j s) (fun _ => b)).2 hb
    have hfun : (fun s => kM (i s)) = (fun s => kN (j s)) := by
      funext s; exact (hMN s).symm
    set χ : L.BoundedFormula M 1 := φ.subst (fun s => Term.var (i s)) with hχdef
    have hχqf : χ.IsQF := isQF_subst hφ _
    have hD' : χ.Realize (fun m => kM m) (fun _ => kN b) := by
      rw [hχdef, BoundedFormula.realize_subst]
      simp only [Term.realize_var]
      rw [hfun]
      exact hb'
    obtain ⟨m₀, hm₀⟩ := h1ec M D kM hM χ hχqf ⟨kN b, hD'⟩
    refine ⟨m₀, ?_⟩
    rw [hχdef, BoundedFormula.realize_subst] at hm₀
    simp only [Term.realize_var] at hm₀
    exact (embedding_realize_isQF kM hφ (fun s => i s) (fun _ => m₀)).1 hm₀

end JohnsonCriterion


universe uacf

theorem hasAmalgamation_field : JohnsonCriterion.HasAmalgamation Theory.field :=
  fun A B C i j => amalgamation_field A B C i j

/-- **Quantifier elimination for algebraically closed fields**, in the form the criterion
yields: over any base field `E`, the one-variable quantifier-free definable sets have the same
existential theory in any two algebraically closed fields containing `E`. -/
theorem acf_qfDetermined (E M N : Theory.field.ModelType.{0, 0, uacf})
    (hM : M ⊨ acf) (hN : N ⊨ acf)
    (i : E ↪[Language.ring] M) (j : E ↪[Language.ring] N)
    (φ : Language.ring.BoundedFormula E 1) (hφ : φ.IsQF) :
    (∃ a : M, φ.Realize (fun s => i s) (fun _ => a)) ↔
      ∃ b : N, φ.Realize (fun s => j s) (fun _ => b) :=
  JohnsonCriterion.qfDetermined_base_model hasAmalgamation_field oneEC_field_acf
    E M N hM hN i j φ hφ


/-- **Prime models over field bases**: for a base that is itself a model of `Theory.field`, the
prime-model hypothesis of Definition 2.1.1 is trivially satisfied (`S' = S`).  This is the form
of the hypothesis used by `qfDetermined_base_model`. -/
theorem primeModels_over_field_model (S : Theory.field.ModelType.{0, 0, uacf})
    (M : Theory.field.ModelType.{0, 0, uacf}) (hM : M ⊨ acf)
    (i : S ↪[Language.ring] M) :
    ∃ (S' : Theory.field.ModelType.{0, 0, uacf}) (e : S ↪[Language.ring] S'),
      ∀ (N : Theory.field.ModelType.{0, 0, uacf}) (f : S ↪[Language.ring] N),
        ∃ g : S' ↪[Language.ring] N, g.comp e = f :=
  ⟨S, FirstOrder.Language.Embedding.refl Language.ring S, fun N f =>
    ⟨f, by simp only [FirstOrder.Language.Embedding.comp_refl]⟩⟩

/-- **The general form of Lemma 2.1.4 at ACF**, conditional on the one hypothesis not discharged
here: prime models over *arbitrary* substructures of models of `T` (Johnson's Definition 2.1.1).
Granting it, the criterion gives quantifier-free type determinism over an arbitrary base
structure `S`, not merely over a base field. -/
theorem acf_qfDetermined_general
    (hprime : JohnsonCriterion.HasPrimeModels.{0, 0, uacf} Theory.field acf)
    (S : Type uacf) [Language.ring.Structure S]
    (M N : Theory.field.ModelType.{0, 0, uacf}) (hM : M ⊨ acf) (hN : N ⊨ acf)
    (i : S ↪[Language.ring] M) (j : S ↪[Language.ring] N)
    (φ : Language.ring.BoundedFormula S 1) (hφ : φ.IsQF) :
    (∃ a : M, φ.Realize (fun s => i s) (fun _ => a)) ↔
      ∃ b : N, φ.Realize (fun s => j s) (fun _ => b) :=
  JohnsonCriterion.qfDetermined field_subset_acf hprime hasAmalgamation_field
    oneEC_field_acf S M N hM hN i j φ hφ

#print axioms ACFValidation.acf_qfDetermined
#print axioms ACFValidation.exists_solution_in_range
#print axioms JohnsonCriterion.qfDetermined

end ACFValidation

/-! ## The ACF instantiation: `HasQE acf` from the prime-model hypothesis alone -/

namespace HQEDerive

/-- **Quantifier elimination for algebraically closed fields** via Johnson's Lemma 2.1.4, with
every hypothesis discharged except the prime-model statement
`JohnsonCriterion.HasPrimeModels Theory.field acf` (gap B).

The three inputs are `ACFValidation.field_subset_acf`, `ACFValidation.amalgamation_field`
(Johnson §2.2, tensor product of fields) and `ACFValidation.oneEC_field_acf`
(Johnson Claim 2.1.5: an algebraically closed field is 1-ec in every field extension). The last
mile `H` is `HQEDerive.H_of_qfDetermined` and the compactness join is `hasQE_of_qfDet`. -/
theorem HasQE_acf_of_primeModels
    (hprime : JohnsonCriterion.HasPrimeModels.{0, 0, 0} Theory.field ACFValidation.acf) :
    QECriterion.HasQE (L := Language.ring) ACFValidation.acf :=
  hasQE_of_johnson (L := Language.ring) ACFValidation.field_subset_acf hprime
    (fun A B C i j => ACFValidation.amalgamation_field A B C i j)
    (fun M N f hM => ACFValidation.oneEC_field_acf M N f hM)

end HQEDerive

#print axioms HQEDerive.HasQE_acf_of_primeModels

namespace HQEDerive

/-- The prime-model hypothesis in the namespace where `QE/ACF_validation.lean` states its own
copy of the criterion (`ACFValidation.JohnsonCriterion`), plugged into the one used by
`H_of_qfDetermined` (top-level `JohnsonCriterion`).  The two definitions have the same body, so
this is a definitional-equality bridge: whichever form gap (B) is proved in, it plugs in. -/
theorem hasPrimeModels_of_ACFValidation
    (h : ACFValidation.JohnsonCriterion.HasPrimeModels.{0, 0, 0} Theory.field ACFValidation.acf) :
    JohnsonCriterion.HasPrimeModels.{0, 0, 0} Theory.field ACFValidation.acf :=
  h

/-- **Quantifier elimination for `acf`, in the frozen shape of `Milestone0/Encoding.lean`**:
every `Language.ring`-formula is `acf`-equivalent to a quantifier-free one, stated with `⊨ᵇ`
and `⇔` as in the frozen `SpecialTransformations.Milestone0.HasQE`.  (This is the same
proposition as `HasQE_acf_of_primeModels`: `Theory.Iff T φ ψ` *is* `T ⊨ᵇ (φ ⇔ ψ)`.) -/
theorem HasQE_acf_frozen_of_primeModels
    (hprime : JohnsonCriterion.HasPrimeModels.{0, 0, 0} Theory.field ACFValidation.acf) :
    ∀ (α : Type) (φ : Language.ring.Formula α),
      ∃ ψ : Language.ring.Formula α, ψ.IsQF ∧ ACFValidation.acf ⊨ᵇ (φ ⇔ ψ) :=
  HasQE_acf_of_primeModels hprime

/-- The same, as `ShoenfieldQE.HasQE` (the frozen shape at general `α`). -/
theorem hasQE_frozen_acf_of_primeModels
    (hprime : JohnsonCriterion.HasPrimeModels.{0, 0, 0} Theory.field ACFValidation.acf) :
    ShoenfieldQE.HasQE (L := Language.ring) ACFValidation.acf :=
  HasQE_acf_of_primeModels hprime

end HQEDerive

#print axioms HQEDerive.HasQE_acf_frozen_of_primeModels
#print axioms HQEDerive.hasQE_frozen_acf_of_primeModels

namespace HQEDerive

/-- Bounded quantifier elimination for `acf` from the same single hypothesis: every bounded
formula with `n` bound variables is `acf`-equivalent to a quantifier-free one. -/
theorem HasQEb_acf_of_primeModels
    (hprime : JohnsonCriterion.HasPrimeModels.{0, 0, 0} Theory.field ACFValidation.acf) :
    QECriterion.HasQEb (L := Language.ring) ACFValidation.acf :=
  QECriterion.hasQEb_of_QEAllStep (QECriterion.QEAllStep_iff_QEExStep.2
    (BoundedQE.qeExStep_theoryIff (L₀ := Language.ring)
      (H_of_qfDetermined ACFValidation.field_subset_acf hprime
        (fun A B C i j => ACFValidation.amalgamation_field A B C i j)
        (fun M N f hM => ACFValidation.oneEC_field_acf M N f hM))))

end HQEDerive

#print axioms HQEDerive.HasQEb_acf_of_primeModels

/-! ## 4. Gap (B): prime models over substructures of models of `acf`

The content of this section is the compiled file `.ultramath/smw0bll3t/m3/PrimeModels_full.lean`
of member m3 of this swarm, copied verbatim and wrapped in `namespace M3` so that its own copies
of `acf` and of `JohnsonCriterion.HasPrimeModels` do not clash with the ones used above.  Both
copies are the same definitions, so the bridge used in §5 is a definitional equality.

m3's theorem: `M3.hasPrimeModels_field_acf :
JohnsonCriterion.HasPrimeModels.{0,0,u} Theory.field acf`, proved by taking the fraction field of
`FreeCommRing S` modulo the kernel of the polynomial relations of an embedding of `S` into a field
(`PrimeField.primeField`), with universality from `IsFractionRing.lift` and independence of the
embedding from `PrimeField.ker_lift_eq`. -/

namespace M3

/-
  **Prime models over arbitrary substructures of fields** (Johnson, *Fun with Fields*,
  Definition 2.1.1) for `T₀ = Theory.field`, `T = acf`: `HasPrimeModels Theory.field acf`,
  unconditionally.  This closes the only hypothesis of `ACFValidation.acf_qfDetermined_general`
  that was left open in `QE/ACF_validation.lean`.

  Given an abstract `S : Type u` with `Language.ring.Structure S` that embeds into a field `M`
  (`e : S ↪[Language.ring] M`), let

    `R := FreeCommRing S ⧸ ker (FreeCommRing.lift (fun s => e s))`   (`coordRing`)

  be the coordinate ring of `S`: the free commutative ring on the generators `S` modulo the
  polynomial relations that hold in `M`.  `R` is a domain, and the prime model of the theory of
  fields over `S` is its fraction field

    `F := FractionRing R`   (`primeField`)

  together with `S ↪[Language.ring] F`, `s ↦ of s / 1` (`primeEmbedding`), which is an embedding
  because `S ↪ M` is injective.

  The universal property (`primeField_universal`): for every field `N` and every embedding
  `f : S ↪[Language.ring] N` there is `g : F ↪[Language.ring] N` with `g.comp e₀ = f`.  Proof:
  `FreeCommRing.lift f` and `FreeCommRing.lift e` have the SAME kernel (`ker_lift_eq`: the
  polynomial relations of `S` do not depend on the field it is embedded into), so the induced
  map `R →+* N` is injective, and `IsFractionRing.lift` extends it to `F →+* N`; a ring
  homomorphism out of a field into a nontrivial ring is injective.

  This file is self-contained (`import Mathlib` only).  The definitions `HasPrimeModels` and
  `acf` are copies of those in `QE/Johnson_criterion.lean` and `QE/ACF_validation.lean` (same
  definitions), so that the final statement is literally
  `JohnsonCriterion.HasPrimeModels Theory.field acf`.

  Main results:
  * `PrimeField.primeEmbedding`, `PrimeField.primeField_universal`
  * `hasPrimeModels_field_acf : JohnsonCriterion.HasPrimeModels Theory.field acf`

  No `sorry`, no `axiom`; axioms are checked at the end of the file.
-/

open FirstOrder FirstOrder.Language
open FirstOrder.Ring
open scoped FirstOrder

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-! ## 0. Copies of the two definitions appearing in the statement -/

/-- Copy of `ACFValidation.acf` (`QE/ACF_validation.lean`): the theory of algebraically closed
fields, characteristic not fixed. -/
noncomputable def acf : Theory Language.ring :=
  Theory.field ∪ Field.genericMonicPolyHasRoot '' {n : ℕ | 0 < n}

namespace JohnsonCriterion

universe u v w

variable {L : FirstOrder.Language.{u, v}}

/-- Copy of `JohnsonCriterion.HasPrimeModels` (`QE/Johnson_criterion.lean`), with the same
universe signature.  Prime models over substructures (Johnson, Definition 2.1.1): every structure
`S` that embeds into a model of `T` has an extension `S'` modelling `T₀` which embeds into every
model of `T₀` under `S`. -/
def HasPrimeModels (T₀ T : L.Theory) : Prop :=
  ∀ (S : Type w) [L.Structure S],
    (∃ (M : T₀.ModelType.{u, v, w}), M ⊨ T ∧ Nonempty (S ↪[L] M)) →
    ∃ (S' : T₀.ModelType.{u, v, w}) (e : S ↪[L] S'),
      ∀ (N : T₀.ModelType.{u, v, w}) (f : S ↪[L] N),
        ∃ g : S' ↪[L] N, g.comp e = f

end JohnsonCriterion

namespace PrimeField

universe u

/-! ## 1. Ring homomorphisms and `Language.ring`-embeddings

(Copied from `QE/PrimeModels_partial.lean`, where the same lemmas are proved.) -/

section Conversions

variable {A B : Type*} [CommRing A] [CommRing B] [CompatibleRing A] [CompatibleRing B]

theorem ringHom_map_fun (f : A →+* B) {n : ℕ} (g : Language.ring.Functions n)
    (x : Fin n → A) : f (Structure.funMap g x) = Structure.funMap g (f ∘ x) := by
  cases g <;> simp

/-- An injective ring homomorphism is an embedding for the language of rings. -/
def embeddingOfInjectiveRingHom (f : A →+* B) (hf : Function.Injective f) :
    A ↪[Language.ring] B where
  toFun := f
  inj' := hf
  map_fun' := ringHom_map_fun f
  map_rel' := by intro n R; exact isEmptyElim R

end Conversions

/-! ## 2. Two embeddings of one structure have the same polynomial relations

(Copied from `QE/PrimeModels_partial.lean`.) -/

section Kernel

variable {S : Type u} [Language.ring.Structure S]
variable {M : Type u} [CommRing M] [CompatibleRing M]
variable {N : Type u} [CommRing N] [CompatibleRing N]

/-- `FreeCommRing.lift (fun s => e s) p` only depends on the term that `p` represents. -/
theorem lift_eq_apply_term (e : S ↪[Language.ring] M) (p : FreeCommRing S) :
    FreeCommRing.lift (fun s => e s) p
      = e (Term.realize (fun s => s) (Ring.termOfFreeCommRing p)) := by
  rw [← Ring.realize_termOfFreeCommRing p (fun s => e s)]
  exact HomClass.realize_term (g := e) (v := fun s => s)

/-- The zero of `S`, described intrinsically (as the value of the zero term), so that no ring
structure on `S` is needed. -/
def zeroTerm : Language.ring.Term S :=
  Term.func (FirstOrder.Ring.zeroFunc) (fun i => (i.elim0 : Language.ring.Term S))

theorem apply_zeroTerm {R : Type u} [CommRing R] [CompatibleRing R] (g : S ↪[Language.ring] R) :
    g (Term.realize (fun s => s) (zeroTerm (S := S))) = 0 := by
  rw [zeroTerm, Term.realize_func]
  rw [g.map_fun (FirstOrder.Ring.zeroFunc)]
  exact CompatibleRing.funMap_zero _

theorem apply_eq_zero_iff {R : Type u} [CommRing R] [CompatibleRing R]
    (g : S ↪[Language.ring] R) (w : S) :
    g w = 0 ↔ w = Term.realize (fun s => s) (zeroTerm (S := S)) := by
  constructor
  · intro h
    apply g.injective
    rw [h, apply_zeroTerm]
  · intro h
    rw [h, apply_zeroTerm]

/-- **The polynomial relations of an abstract structure are the same in every field it embeds
into.** -/
theorem ker_lift_eq (e : S ↪[Language.ring] M) (f : S ↪[Language.ring] N) :
    RingHom.ker (FreeCommRing.lift (fun s => e s))
      = RingHom.ker (FreeCommRing.lift (fun s => f s)) := by
  ext p
  rw [RingHom.mem_ker, RingHom.mem_ker, lift_eq_apply_term e, lift_eq_apply_term f,
    apply_eq_zero_iff e, apply_eq_zero_iff f]

end Kernel

/-! ## 3. The prime model of `Theory.field` over `S`: the fraction field of the coordinate ring -/

section Construction

variable {S : Type u} [Language.ring.Structure S]
variable {M : Type u} [CommRing M] [CompatibleRing M] [IsDomain M]

/-- The ideal of polynomial relations of `S`, computed in `M`. -/
noncomputable abbrev relIdeal (e : S ↪[Language.ring] M) : Ideal (FreeCommRing S) :=
  RingHom.ker (FreeCommRing.lift (fun s => e s))

/-- The coordinate ring of `S` relative to an embedding into a field `M`: the free commutative
ring on the generators `S` modulo the polynomial relations holding in `M`.  By `ker_lift_eq` it
does not depend on `M`. -/
noncomputable abbrev coordRing (e : S ↪[Language.ring] M) : Type u :=
  FreeCommRing S ⧸ relIdeal e

/-- The relations of `S` form a prime ideal, because they are the kernel of a homomorphism into
the domain `M`. -/
instance relIdeal.isPrime (e : S ↪[Language.ring] M) : (relIdeal e).IsPrime :=
  RingHom.ker_isPrime _

noncomputable instance coordRing.instCommRing (e : S ↪[Language.ring] M) :
    CommRing (coordRing e) :=
  inferInstanceAs (CommRing (FreeCommRing S ⧸ relIdeal e))

noncomputable instance coordRing.instIsDomain (e : S ↪[Language.ring] M) :
    IsDomain (coordRing e) :=
  inferInstanceAs (IsDomain (FreeCommRing S ⧸ relIdeal e))

noncomputable instance coordRing.instCompatibleRing (e : S ↪[Language.ring] M) :
    CompatibleRing (coordRing e) :=
  compatibleRingOfRing _

/-- The prime model of the theory of fields over `S`: the fraction field of the coordinate
ring. -/
noncomputable abbrev primeField (e : S ↪[Language.ring] M) : Type u :=
  FractionRing (coordRing e)

noncomputable instance primeField.instField (e : S ↪[Language.ring] M) : Field (primeField e) :=
  inferInstanceAs (Field (FractionRing (coordRing e)))

noncomputable instance primeField.instCompatibleRing (e : S ↪[Language.ring] M) :
    CompatibleRing (primeField e) :=
  compatibleRingOfRing _

/-- The map from `S` to its prime model, `s ↦ of s / 1`. -/
noncomputable abbrev primeMapFun (e : S ↪[Language.ring] M) : S → primeField e :=
  fun s => algebraMap (coordRing e) (primeField e)
    (Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of s))

/-- In the coordinate ring, evaluating a term built from `x` in `S` agrees with the ring
operation on the images: for every function symbol `g` of the language of rings,
`of (g(x)) = g(of x)` holds modulo the relations.  This is where the choice of the relations
(as the kernel of an embedding into a domain) is used. -/
theorem mk_of_funMap (e : S ↪[Language.ring] M) {n : ℕ}
    (g : Language.ring.Functions n) (x : Fin n → S) :
    Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (Structure.funMap g x))
      = Structure.funMap g
          (fun i => Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (x i))) := by
  letI : CompatibleRing (FreeCommRing S) := compatibleRingOfRing _
  have hq := ringHom_map_fun (Ideal.Quotient.mk (relIdeal e)) g
    (fun i => FreeCommRing.of (x i))
  simp only [Function.comp_def] at hq
  rw [← hq]
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, RingHom.mem_ker, map_sub, FreeCommRing.lift_of]
  have h2 : FreeCommRing.lift (fun s => e s)
      (Structure.funMap g (fun i => FreeCommRing.of (x i)))
        = e (Structure.funMap g x) := by
    have he := ringHom_map_fun (FreeCommRing.lift (fun s => e s)) g
      (fun i => FreeCommRing.of (x i))
    simp only [Function.comp_def, FreeCommRing.lift_of] at he
    have he2 := e.map_fun g x
    simp only [Function.comp_def] at he2
    exact he.trans he2.symm
  rw [h2, sub_self]

@[simp]
theorem primeMapFun_apply (e : S ↪[Language.ring] M) (s : S) :
    primeMapFun e s = algebraMap (coordRing e) (primeField e)
      (Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of s)) := rfl

/-- The map `s ↦ of s / 1` commutes with the ring operations of the language. -/
theorem primeMapFun_funMap (e : S ↪[Language.ring] M) {n : ℕ}
    (g : Language.ring.Functions n) (x : Fin n → S) :
    primeMapFun e (Structure.funMap g x)
      = Structure.funMap g (fun i => primeMapFun e (x i)) := by
  have hq := ringHom_map_fun (algebraMap (coordRing e) (primeField e)) g
    (fun i => Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (x i)))
  simp only [Function.comp_def] at hq
  rw [primeMapFun_apply, mk_of_funMap e g x]
  simpa only [primeMapFun_apply] using hq

/-- The same statement in the shape of `Language.Embedding.map_fun'`. -/
theorem primeMapFun_comp (e : S ↪[Language.ring] M) {n : ℕ}
    (g : Language.ring.Functions n) (x : Fin n → S) :
    primeMapFun e (Structure.funMap g x) = Structure.funMap g (primeMapFun e ∘ x) := by
  rw [primeMapFun_funMap e g x]
  simp only [Function.comp_def]

/-- **The embedding of `S` into its prime model.** -/
noncomputable def primeEmbedding (e : S ↪[Language.ring] M) :
    S ↪[Language.ring] primeField e where
  toFun := primeMapFun e
  inj' := by
    intro a b hab
    have h1 : Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of a)
        = Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of b) :=
      IsFractionRing.injective (coordRing e) (primeField e) hab
    have h2 : FreeCommRing.of a - FreeCommRing.of b ∈ relIdeal e :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := relIdeal e) (x := FreeCommRing.of a) (y := FreeCommRing.of b)).mp h1
    have h3 : FreeCommRing.lift (fun s => e s)
        (FreeCommRing.of a - FreeCommRing.of b) = 0 := RingHom.mem_ker.mp h2
    rw [map_sub, FreeCommRing.lift_of, FreeCommRing.lift_of, sub_eq_zero] at h3
    exact e.injective h3
  map_fun' := fun {n} g x => primeMapFun_comp e g x
  map_rel' := by intro n R; exact isEmptyElim R

/-! ## 4. The universal property of the prime model -/

section Universal

variable {N : Type u} [Field N] [CompatibleRing N]

/-- **The prime model of `Theory.field` over `S` embeds into every field over `S`.** -/
theorem primeField_universal (e : S ↪[Language.ring] M) (f : S ↪[Language.ring] N) :
    ∃ g : primeField e ↪[Language.ring] N, g.comp (primeEmbedding e) = f := by
  have hker : relIdeal e = relIdeal f := ker_lift_eq e f
  -- the map on coordinate rings induced by `f`, well defined because the kernels agree
  let rHom : coordRing e →+* N :=
    Ideal.Quotient.lift (relIdeal e) (FreeCommRing.lift (fun s => f s)) (fun a ha => by
      rw [hker] at ha
      exact RingHom.mem_ker.mp ha)
  have rHom_inj : Function.Injective rHom := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [rHom, Ideal.Quotient.lift_mk] at hxy
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, hker, RingHom.mem_ker, map_sub, hxy, sub_self]
  -- extend it to the fraction field
  let gHom : primeField e →+* N :=
    IsFractionRing.lift (A := coordRing e) (K := primeField e) (L := N) rHom_inj
  have gHom_inj : Function.Injective gHom := by
    intro x y hxy
    have h : gHom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    by_contra hne
    have hne' : x - y ≠ 0 := sub_ne_zero.mpr hne
    have h1 : gHom (x - y) * gHom ((x - y)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hne', map_one]
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  have hgl : ∀ z : coordRing e,
      gHom (algebraMap (coordRing e) (primeField e) z) = rHom z :=
    fun z => IsFractionRing.lift_algebraMap rHom_inj z
  refine ⟨embeddingOfInjectiveRingHom gHom gHom_inj, ?_⟩
  refine FirstOrder.Language.Embedding.ext ?_
  intro s
  simp only [FirstOrder.Language.Embedding.comp_apply]
  have h7 : (embeddingOfInjectiveRingHom gHom gHom_inj : primeField e ↪[Language.ring] N)
      (primeEmbedding e s) = gHom (primeMapFun e s) := rfl
  rw [h7]
  have h4 : rHom (Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of s))
      = FreeCommRing.lift (fun s => f s) (FreeCommRing.of s) := by
    simp only [rHom, Ideal.Quotient.lift_mk]
  rw [primeMapFun_apply, hgl, h4, FreeCommRing.lift_of]

end Universal

end Construction

end PrimeField

/-! ## 5. `HasPrimeModels Theory.field acf` -/

universe u

theorem hasPrimeModels_field_acf :
    JohnsonCriterion.HasPrimeModels.{0, 0, u} Theory.field acf := by
  intro S inst hS
  letI := inst
  obtain ⟨M, _hMacf, ⟨e⟩⟩ := hS
  letI : Field M := FirstOrder.Field.fieldOfModelField M
  letI : CompatibleRing M := FirstOrder.Field.compatibleRingOfModelField M
  refine ⟨Theory.ModelType.of Theory.field (PrimeField.primeField e), PrimeField.primeEmbedding e, ?_⟩
  intro N f
  letI : Field N := FirstOrder.Field.fieldOfModelField N
  letI : CompatibleRing N := FirstOrder.Field.compatibleRingOfModelField N
  exact PrimeField.primeField_universal e f

#print axioms hasPrimeModels_field_acf
#print axioms PrimeField.primeField_universal
#print axioms PrimeField.primeEmbedding
#print axioms PrimeField.mk_of_funMap
#print axioms PrimeField.ker_lift_eq

end M3

/-! ## 5. Quantifier elimination for `acf`, unconditional -/

namespace HQEDerive

/-- **Quantifier elimination for algebraically closed fields**: every `Language.ring`-formula is
`acf`-equivalent to a quantifier-free one, in the frozen shape.

Chain: Johnson's Lemma 2.1.4 (`JohnsonCriterion.qfDetermined`, Part 1)
→ the last mile `H_of_qfDetermined` (Part 2/3)
→ the compactness join `hasQE_of_qfDet`
→ the ACF hypotheses `field_subset_acf`, `amalgamation_field`, `oneEC_field_acf`
→ and the prime-model statement `M3.hasPrimeModels_field_acf` (member m3's compiled
`PrimeModels_full.lean`, wrapped in `namespace M3`), whose only mismatch with this file is the
pair of copied definitions `acf` and `JohnsonCriterion.HasPrimeModels`, which are definitionally
the same. -/
theorem HasQE_acf : QECriterion.HasQE (L := Language.ring) ACFValidation.acf :=
  HasQE_acf_of_primeModels
    (show JohnsonCriterion.HasPrimeModels.{0, 0, 0} Theory.field ACFValidation.acf from
      M3.hasPrimeModels_field_acf)

/-- The frozen shape of `Milestone0/Encoding.lean`: every `Language.ring`-formula is
`acf`-equivalent to a quantifier-free one, stated with `⊨ᵇ` and `⇔`. -/
theorem HasQE_acf_frozen :
    ∀ (α : Type) (φ : Language.ring.Formula α),
      ∃ ψ : Language.ring.Formula α, ψ.IsQF ∧ ACFValidation.acf ⊨ᵇ (φ ⇔ ψ) :=
  HasQE_acf

/-- The same as `ShoenfieldQE.HasQE` (frozen shape at general `α`). -/
theorem hasQE_frozen_acf : ShoenfieldQE.HasQE (L := Language.ring) ACFValidation.acf :=
  HasQE_acf

/-- Bounded quantifier elimination for `acf`. -/
theorem HasQEb_acf : QECriterion.HasQEb (L := Language.ring) ACFValidation.acf :=
  QECriterion.hasQEb_of_QEAllStep (QECriterion.QEAllStep_iff_QEExStep.2
    (BoundedQE.qeExStep_theoryIff (L₀ := Language.ring)
      (H_of_qfDetermined ACFValidation.field_subset_acf M3.hasPrimeModels_field_acf
        (fun A B C i j => ACFValidation.amalgamation_field A B C i j)
        (fun M N f hM => ACFValidation.oneEC_field_acf M N f hM))))

end HQEDerive

#print axioms HQEDerive.HasQE_acf
#print axioms HQEDerive.HasQE_acf_frozen
#print axioms HQEDerive.hasQE_frozen_acf
#print axioms HQEDerive.HasQEb_acf
