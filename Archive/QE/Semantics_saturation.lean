/-
  Saturation and the semantic core of Remark 3.1 (qe.tex, arXiv:1006.1393).

  Direction (B)/(b1) of the swarm task: what Shoenfield's test needs from
  "N is |M|⁺-saturated", and what Weispfenning's QE (an explicit hypothesis here)
  contributes to it.

  Everything is stated for Mathlib's general `FirstOrder.Language`, so it can be
  instantiated at the frozen encoding `LRV` of Milestone0/Encoding.lean.

  Only import: Mathlib.  Formulas range over `α : Type` (universe 0), which is all
  the encoding needs.
-/
import Mathlib

open FirstOrder FirstOrder.Language
open FirstOrder.Language.Structure
open scoped FirstOrder

namespace QESat

/-! ## 1. Quantifier-free formulas are preserved by embeddings

Mathlib has `StrongHomClass.realize_boundedFormula`, but only under `EquivLike`
(surjective maps).  For a general embedding only quantifier-free formulas are
preserved, and that lemma is not in Mathlib.  It is the syntactic half of
Remark 3.1 of the paper: an `L_RV`-monomorphism preserves the quantifier-free
`L_v`-formulas, so with QE it preserves all formulas. -/

section QF

variable {L : Language} {M : Type*} {N : Type*} [L.Structure M] [L.Structure N]
variable {α : Type*} {n : ℕ}

theorem embedding_realize_isAtomic (g : M ↪[L] N) {φ : L.BoundedFormula α n}
    (h : φ.IsAtomic) (v : α → M) (xs : Fin n → M) :
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

theorem embedding_realize_isQF (g : M ↪[L] N) {φ : L.BoundedFormula α n} (h : φ.IsQF) :
    ∀ (v : α → M) (xs : Fin n → M),
      φ.Realize (fun a => g (v a)) (fun i => g (xs i)) ↔ φ.Realize v xs := by
  induction h with
  | falsum => intro v xs; exact Iff.rfl
  | of_isAtomic ha => exact fun v xs => embedding_realize_isAtomic g ha v xs
  | imp _ _ ih1 ih2 => intro v xs; simp only [BoundedFormula.realize_imp, ih1 v xs, ih2 v xs]

theorem embedding_realize_formula_isQF (g : M ↪[L] N) {φ : L.Formula α} (h : φ.IsQF)
    (v : α → M) : φ.Realize (fun a => g (v a)) ↔ φ.Realize v := by
  have h0 : (fun i : Fin 0 => g ((default : Fin 0 → M) i)) = (default : Fin 0 → N) :=
    Subsingleton.elim _ _
  have h1 := embedding_realize_isQF (n := 0) g h v (default : Fin 0 → M)
  rw [h0] at h1
  exact h1

end QF

/-! ## 2. Quantifier elimination as an explicit hypothesis -/

section HasQE

variable {L : Language}

/-- A theory admits quantifier elimination: every formula is equivalent over `T`
to a quantifier-free formula.  This is verbatim the `HasQE` of
`Milestone0/Encoding.lean`, for a general language. -/
def HasQE (T : L.Theory) : Prop :=
  ∀ (α : Type) (φ : L.Formula α), ∃ ψ : L.Formula α, ψ.IsQF ∧ (φ ⇔[T] ψ)

/-- Quantifier elimination is inherited by any stronger theory: if `T ⊆ T'` then
`T'` has fewer models, so every `T`-equivalence is also a `T'`-equivalence.
This is what makes QE pass from `ACVF` to `ACVF_S` (the axioms plus the atomic
diagram of a substructure `S`) in the paper. -/
theorem HasQE.mono {T T' : L.Theory} (h : HasQE T) (hsub : T ⊆ T') : HasQE T' := by
  intro α φ
  obtain ⟨ψ, hqf, hiff⟩ := h α φ
  refine ⟨ψ, hqf, fun M v xs => ?_⟩
  have hMT' : ↑M ⊨ T' := inferInstance
  have hMT : ↑M ⊨ T := hMT'.mono hsub
  exact hiff (Theory.ModelType.of T ↑M) v xs

variable {T : L.Theory} {M : Type*} {N : Type*} [L.Structure M] [L.Structure N]
  {α : Type}

/-- **QE gives partial elementarity**: if `T` has QE, `M, N ⊨ T`, `S ⊆ M` is a
substructure and `f : S ↪[L] N` is an `L`-monomorphism, then `f` preserves *all*
formulas with parameters in `S`.  This is the semantic content of Remark 3.1 of
the paper (`L:v:and:L:RV`): QE upgrades a monomorphism to a partial elementary map.

No hypothesis `S ⊨ T` is needed: the quantifier-free steps are transported along
the embeddings `S ↪ M` and `S ↪ N`. -/
theorem realize_iff_of_hasQE (hT : HasQE T) (hM : M ⊨ T) (hN : N ⊨ T)
    [Nonempty M] [Nonempty N] (S : L.Substructure M) (f : S ↪[L] N)
    (φ : L.Formula α) (v : α → S) :
    φ.Realize (fun x => (v x : M)) ↔ φ.Realize (fun x => f (v x)) := by
  obtain ⟨ψ, hψqf, hψ⟩ := hT α φ
  have h1 : φ.Realize (fun x => (v x : M)) ↔ ψ.Realize (fun x => (v x : M)) :=
    hψ.realize_iff (M := M)
  have h2 : ψ.Realize (fun x => (v x : M)) ↔ ψ.Realize v :=
    embedding_realize_formula_isQF (Substructure.subtype S) hψqf v
  have h3 : ψ.Realize v ↔ ψ.Realize (fun x => f (v x)) :=
    (embedding_realize_formula_isQF f hψqf v).symm
  have h4 : ψ.Realize (fun x => f (v x)) ↔ φ.Realize (fun x => f (v x)) :=
    (hψ.realize_iff (M := N)).symm
  exact h1.trans (h2.trans (h3.trans h4))

/-- **QE gives model completeness**: if `T` has QE then every embedding between
models of `T` is elementary. -/
theorem embedding_realize_iff_of_hasQE (hT : HasQE T) (hM : M ⊨ T) (hN : N ⊨ T)
    [Nonempty M] [Nonempty N] (f : M ↪[L] N) (φ : L.Formula α) (v : α → M) :
    φ.Realize v ↔ φ.Realize (fun x => f (v x)) := by
  obtain ⟨ψ, hψqf, hψ⟩ := hT α φ
  constructor
  · intro hv
    exact (hψ.realize_iff (M := N)).2
      ((embedding_realize_formula_isQF f hψqf v).2 ((hψ.realize_iff (M := M)).1 hv))
  · intro hv
    exact (hψ.realize_iff (M := M)).2
      ((embedding_realize_formula_isQF f hψqf v).1 ((hψ.realize_iff (M := N)).1 hv))

end HasQE

/-! ## 3. Saturation: types, finite satisfiability, and the one-element step

This is the precise content of "N is |M|⁺-saturated" as used in the paper: at
each step of the back-and-forth one has to realize *one* type over the parameters
already mapped.  `finitelySatisfiableIn_typeOf` below shows that this type is
finitely satisfiable, and that proof is exactly where the hypothesis `HasQE T`
(Weispfenning's theorem, in the paper) is consumed. -/

section Saturation

variable {L : Language} {T : L.Theory} {M : Type} {N : Type}
  [L.Structure M] [L.Structure N]
variable {A : Type} {n : ℕ}

/-- The type of the tuple `a : Fin n → M` over the parameters `v : A → M`. -/
def typeOf (v : A → M) (a : Fin n → M) : Set (L.BoundedFormula A n) :=
  {φ | φ.Realize v a}

@[simp]
theorem mem_typeOf {v : A → M} {a : Fin n → M} {φ : L.BoundedFormula A n} :
    φ ∈ typeOf v a ↔ φ.Realize v a :=
  Iff.rfl

/-- `p` is finitely satisfiable under the parameters `v`: every finite list of
members of `p` has a common solution. -/
def FinitelySatisfiableIn (v : A → M) (p : Set (L.BoundedFormula A n)) : Prop :=
  ∀ l : List (L.BoundedFormula A n), (∀ φ ∈ l, φ ∈ p) →
    ∃ xs : Fin n → M, ∀ φ ∈ l, φ.Realize v xs

/-- `N` realizes every finitely satisfiable type over the parameters `v`. -/
def RealizesTypesOver (v : A → N) : Prop :=
  ∀ {n : ℕ} (p : Set (L.BoundedFormula A n)), FinitelySatisfiableIn v p →
    ∃ xs : Fin n → N, ∀ φ ∈ p, φ.Realize v xs

/-- Quantifier-free formulas are preserved between the two embeddings of a
substructure used in the paper: the inclusion `S ↪ M` and the monomorphism
`f : S ↪ N`. -/
theorem realize_iff_of_qf_substructure {S : L.Substructure M} {φ : L.Formula S}
    (h : φ.IsQF) (f : S ↪[L] N) :
    φ.Realize (fun s : S => (s : M)) ↔ φ.Realize (fun s : S => f s) := by
  have h1 : φ.Realize (fun s : S => (s : M)) ↔ φ.Realize (id : S → S) :=
    embedding_realize_formula_isQF (Substructure.subtype S) h id
  have h2 : φ.Realize (fun s : S => f s) ↔ φ.Realize (id : S → S) :=
    embedding_realize_formula_isQF f h id
  exact h1.trans h2.symm

/-- **The type of a tuple is finitely satisfiable in the target**, given `HasQE T`.

This is precisely where QE (Weispfenning's theorem in the paper) is used: a
finite piece of the type of `a` over `S` is, after taking its existential
closure, a formula over `S`; QE replaces it by a quantifier-free formula; that
formula is transported along the monomorphism `f : S ↪ N` (quantifier-free
formulas are preserved by embeddings) and read back as a solution in `N`. -/
theorem finitelySatisfiableIn_typeOf (hT : HasQE T) (hM : M ⊨ T) (hN : N ⊨ T)
    [Nonempty M] [Nonempty N] (S : L.Substructure M) (f : S ↪[L] N) (a : Fin n → M) :
    FinitelySatisfiableIn (L := L) (fun s : S => f s)
      (typeOf (L := L) (M := M) (fun s : S => (s : M)) a) := by
  intro l hl
  set ψ : L.BoundedFormula S n := l.foldr (· ⊓ ·) ⊤ with hψ
  have hψa : ψ.Realize (fun s : S => (s : M)) a := by
    rw [hψ]
    exact (BoundedFormula.realize_foldr_inf l (fun s : S => (s : M)) a).2 hl
  obtain ⟨χ, hχqf, hχ⟩ := hT S ψ.exs
  have hMex : (ψ.exs).Realize (fun s : S => (s : M)) :=
    BoundedFormula.realize_exs.2 ⟨a, hψa⟩
  have hMχ : χ.Realize (fun s : S => (s : M)) := (hχ.realize_iff (M := M)).1 hMex
  have hNχ : χ.Realize (fun s : S => f s) := (realize_iff_of_qf_substructure hχqf f).1 hMχ
  have hNex : (ψ.exs).Realize (fun s : S => f s) := (hχ.realize_iff (M := N)).2 hNχ
  obtain ⟨xs, hxs⟩ := BoundedFormula.realize_exs.1 hNex
  refine ⟨xs, fun φ hφ => ?_⟩
  rw [hψ] at hxs
  exact (BoundedFormula.realize_foldr_inf l (fun s : S => f s) xs).1 hxs φ hφ

/-- **The back-and-forth step, from saturation, at any finite tuple.**  If `N`
realizes all types over the parameters `f '' S`, then the partial elementary map
`f : S → N` is matched by some tuple `xs : Fin n → N` that preserves *every*
formula with the new parameters.  This is the paper's use of "`N` is
`M`-saturated", stated for `n` new elements at once. -/
theorem exists_extension_of_realizesTypesOver (hT : HasQE T) (hM : M ⊨ T) (hN : N ⊨ T)
    [Nonempty M] [Nonempty N] (S : L.Substructure M) (f : S ↪[L] N) (a : Fin n → M)
    (hsat : RealizesTypesOver (L := L) (N := N) (fun s : S => f s)) :
    ∃ xs : Fin n → N, ∀ φ : L.BoundedFormula S n,
      (φ.Realize (fun s : S => f s) xs ↔ φ.Realize (fun s : S => (s : M)) a) := by
  obtain ⟨xs, hxs⟩ :=
    hsat (typeOf (L := L) (M := M) (fun s : S => (s : M)) a)
      (finitelySatisfiableIn_typeOf hT hM hN S f a)
  refine ⟨xs, fun φ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra hcon
    have hmem : φ.not ∈ typeOf (L := L) (M := M) (fun s : S => (s : M)) a := by
      simp only [mem_typeOf, BoundedFormula.realize_not]
      exact hcon
    exact (BoundedFormula.realize_not.mp (hxs φ.not hmem)) h
  · exact hxs φ h

/-- `N` is `κ`-saturated: every finitely satisfiable type over fewer than `κ`
parameters is realized in `N`.  The paper's hypothesis is `κ = |M|⁺`. -/
def IsSaturated (κ : Cardinal.{0}) : Prop :=
  ∀ (A : Type) (v : A → N), Cardinal.mk A < κ → RealizesTypesOver (L := L) (N := N) v

/-- **Saturation supplies the extension step**: for `N` `κ`-saturated with
`Cardinal.mk S < κ` (in the paper: `S ⊆ M` and `κ = ‖M‖⁺`), every monomorphism
`f : S ↪ N` can be matched at any `n` further elements of `M`. -/
theorem exists_extension_of_saturated (hT : HasQE T) (hM : M ⊨ T) (hN : N ⊨ T)
    [Nonempty M] [Nonempty N] (S : L.Substructure M) (f : S ↪[L] N) (a : Fin n → M)
    {κ : Cardinal.{0}} (hsat : IsSaturated (L := L) (N := N) κ) (hS : Cardinal.mk S < κ) :
    ∃ xs : Fin n → N, ∀ φ : L.BoundedFormula S n,
      (φ.Realize (fun s : S => f s) xs ↔ φ.Realize (fun s : S => (s : M)) a) :=
  exists_extension_of_realizesTypesOver hT hM hN S f a (hsat S (fun s => f s) hS)

/-- The paper's hypothesis "`‖M‖⁺`-saturated" is enough: a substructure `S ⊆ M` is
always smaller than `‖M‖⁺`. -/
theorem exists_extension_of_saturated_succ (hT : HasQE T) (hM : M ⊨ T) (hN : N ⊨ T)
    [Nonempty M] [Nonempty N] (S : L.Substructure M) (f : S ↪[L] N) (a : Fin n → M)
    (hsat : IsSaturated (L := L) (N := N) (Order.succ (Cardinal.mk M))) :
    ∃ xs : Fin n → N, ∀ φ : L.BoundedFormula S n,
      (φ.Realize (fun s : S => f s) xs ↔ φ.Realize (fun s : S => (s : M)) a) := by
  refine exists_extension_of_saturated hT hM hN S f a hsat ?_
  exact lt_of_le_of_lt (Cardinal.mk_le_of_injective (Subtype.coe_injective)) (Order.lt_succ _)

end Saturation

/-! ## 4. Packaging: from the formula-level step to an embedding of the
generated substructure

`exists_embedding_closure` turns the `Fin n`-formula-level statement of §3 into a
genuine `L`-embedding of `closure L (↑S ∪ range a)` into `N`, extending `f` and
sending `a i` to `xs i`.  This is the shape Mathlib's back-and-forth machinery
consumes (`Language.isExtensionPair_iff_exists_embedding_closure_singleton_sup`),
so together with §3 it is the one-element step of the paper's Proposition 3.9. -/

section Packaging

variable {L : Language} {M : Type} {N : Type} [L.Structure M] [L.Structure N] {n : ℕ}

/-- **Packaging of the one-element step.**  Suppose the monomorphism `f : S ↪[L] N`
is matched at the tuple `a : Fin n → M` by `xs : Fin n → N` at the level of *all*
formulas over `S`.  Then `f` extends to an embedding of the substructure generated
by `S` and `a` into `N`, sending `a` to `xs`. -/
theorem exists_embedding_closure (S : L.Substructure M) (f : S ↪[L] N)
    (a : Fin n → M) (xs : Fin n → N)
    (hxs : ∀ φ : L.BoundedFormula S n,
      (φ.Realize (fun s : S => f s) xs ↔ φ.Realize (fun s : S => (s : M)) a)) :
    ∃ g : (↥(Substructure.closure L ((↑S : Set M) ∪ Set.range a))) ↪[L] N,
      (∀ s : S, g ⟨s, Substructure.subset_closure (Or.inl s.2)⟩ = f s) ∧
      (∀ i, g ⟨a i, Substructure.subset_closure (Or.inr ⟨i, rfl⟩)⟩ = xs i) := by
  classical
  set C : L.Substructure M := Substructure.closure L ((↑S : Set M) ∪ Set.range a) with hC
  set u : S ⊕ Fin n → M := Sum.elim (fun s : S => (s : M)) a with hu
  set u' : S ⊕ Fin n → N := Sum.elim (fun s : S => f s) xs with hu'
  -- every value of a term over the generating tuple is in `C`
  have mem_term : ∀ t : L.Term (S ⊕ Fin n), t.realize u ∈ C := by
    intro t
    induction t with
    | var w =>
        have hw : u w ∈ (↑S : Set M) ∪ Set.range a := by
          rcases w with s | i
          · exact Or.inl s.2
          · exact Or.inr ⟨i, rfl⟩
        exact Substructure.subset_closure hw
    | func F ts ih => exact C.fun_mem F (fun i => (ts i).realize u) ih
  -- conversely, every element of `C` is the value of a term
  have hgen : (↑S : Set M) ∪ Set.range a ⊆ {x | ∃ t : L.Term (S ⊕ Fin n), t.realize u = x} := by
    rintro y (hy | ⟨i, hi⟩)
    · exact ⟨Term.var (Sum.inl ⟨y, hy⟩), rfl⟩
    · exact ⟨Term.var (Sum.inr i), by show u (Sum.inr i) = y; rw [hu]; exact hi⟩
  have hclos : ∀ {m : ℕ} (F : L.Functions m) (x : Fin m → M),
      (∀ i, x i ∈ {y | ∃ t : L.Term (S ⊕ Fin n), t.realize u = y}) →
      funMap F x ∈ {y | ∃ t : L.Term (S ⊕ Fin n), t.realize u = y} := by
    intro m F x ih
    choose t ht using ih
    exact ⟨Term.func F t, by simp only [Term.realize]; rw [funext ht]⟩
  have exists_term : ∀ x ∈ C, ∃ t : L.Term (S ⊕ Fin n), t.realize u = x := by
    intro x hx
    have hle : C ≤ (⟨{y | ∃ t : L.Term (S ⊕ Fin n), t.realize u = y},
        fun F x ih => hclos F x ih⟩ : L.Substructure M) := by
      rw [hC]
      exact Substructure.closure_le.2 hgen
    exact hle hx
  -- equalities of terms transfer from `u` to `u'`
  have term_eq_iff : ∀ t₁ t₂ : L.Term (S ⊕ Fin n),
      (t₁.realize u = t₂.realize u ↔ t₁.realize u' = t₂.realize u') := by
    intro t₁ t₂
    have h := hxs (t₁.bdEqual t₂)
    simpa only [BoundedFormula.realize_bdEqual, hu, hu'] using h.symm
  -- the candidate map
  set G : (↥C) → N := fun x => (Classical.choose (exists_term x.1 x.2)).realize u' with hG
  have G_eq : ∀ (t : L.Term (S ⊕ Fin n)), G ⟨t.realize u, mem_term t⟩ = t.realize u' := by
    intro t
    have hspec := Classical.choose_spec (exists_term (t.realize u) (mem_term t))
    exact (term_eq_iff _ t).1 hspec
  have G_inj : Function.Injective G := by
    intro x y hxy
    obtain ⟨tx, htx⟩ := exists_term x.1 x.2
    obtain ⟨ty, hty⟩ := exists_term y.1 y.2
    have hx' : G x = tx.realize u' := by
      conv_lhs => rw [show x = ⟨tx.realize u, mem_term tx⟩ from Subtype.ext htx.symm]
      exact G_eq tx
    have hy' : G y = ty.realize u' := by
      conv_lhs => rw [show y = ⟨ty.realize u, mem_term ty⟩ from Subtype.ext hty.symm]
      exact G_eq ty
    have h1 : tx.realize u = ty.realize u := (term_eq_iff tx ty).2 (by rw [← hx', ← hy']; exact hxy)
    exact Subtype.ext (by rw [← htx, ← hty]; exact h1)
  have G_fun : ∀ {m : ℕ} (F : L.Functions m) (x : Fin m → ↥C),
      G (funMap F x) = funMap F (fun i => G (x i)) := by
    intro m F x
    choose t ht using fun i => exists_term (x i).1 (x i).2
    have hcoe : (funMap F x : ↥C) = ⟨(Term.func F t).realize u, mem_term _⟩ := by
      refine Subtype.ext ?_
      show funMap F (fun i => ((x i : ↥C) : M)) = funMap F (fun i => (t i).realize u)
      rw [funext fun i => (ht i).symm]
    rw [hcoe, G_eq]
    simp only [Term.realize]
    congr 1
    funext i
    rw [show x i = (⟨Term.realize u (t i), mem_term (t i)⟩ : ↥C) from Subtype.ext (ht i).symm]
    exact (G_eq (t i)).symm
  have G_rel : ∀ {m : ℕ} (R : L.Relations m) (x : Fin m → ↥C),
      RelMap R (G ∘ x) ↔ RelMap R x := by
    intro m R x
    choose t ht using fun i => exists_term (x i).1 (x i).2
    have h1 : RelMap R x ↔ RelMap R (fun i => (t i).realize u) := by
      rw [show x = (fun i => (⟨(t i).realize u, mem_term (t i)⟩ : ↥C)) from
        funext fun i => Subtype.ext (Subtype.ext_iff.1 rfl ▸ (ht i).symm)]
      exact Iff.rfl
    have h2 : RelMap R (fun i => (t i).realize u') ↔ RelMap R (fun i => (t i).realize u) := by
      have h := hxs (R.boundedFormula t)
      simpa only [BoundedFormula.realize_rel, hu, hu'] using h
    have h3 : RelMap R (G ∘ x) ↔ RelMap R (fun i => (t i).realize u') := by
      have hfun : (G ∘ x) = (fun i => (t i).realize u') := by
        funext i
        simp only [Function.comp_apply]
        rw [show x i = (⟨(t i).realize u, mem_term (t i)⟩ : ↥C) from
          Subtype.ext (by simpa using (ht i).symm)]
        exact G_eq (t i)
      rw [hfun]
    exact h3.trans (h2.trans h1.symm)
  have G_incl : ∀ s : S, G ⟨s, Substructure.subset_closure (Or.inl s.2)⟩ = f s := by
    intro s
    have h1 : (⟨s, Substructure.subset_closure (Or.inl s.2)⟩ : ↥C)
        = ⟨(Term.var (Sum.inl s)).realize u, mem_term _⟩ := by
      refine Subtype.ext ?_
      show (s : M) = u (Sum.inl s)
      rw [hu]; rfl
    rw [h1, G_eq]
    show u' (Sum.inl s) = f s
    rw [hu']; rfl
  have G_a : ∀ i, G ⟨a i, Substructure.subset_closure (Or.inr ⟨i, rfl⟩)⟩ = xs i := by
    intro i
    have h1 : (⟨a i, Substructure.subset_closure (Or.inr ⟨i, rfl⟩)⟩ : ↥C)
        = ⟨(Term.var (Sum.inr i)).realize u, mem_term _⟩ := by
      refine Subtype.ext ?_
      show a i = u (Sum.inr i)
      rw [hu]; rfl
    rw [h1, G_eq]
    show u' (Sum.inr i) = xs i
    rw [hu']; rfl
  exact ⟨⟨⟨G, G_inj⟩, fun {m} F x => G_fun F x, fun {m} R x => G_rel R x⟩, G_incl, G_a⟩

end Packaging
section Corollaries

variable {L : Language} {T : L.Theory} {M : Type} {N : Type} [L.Structure M] [L.Structure N]
  {n : ℕ}

/-- **The paper's one-element step, packaged as an embedding.**  Saturation plus
`HasQE` give an embedding of the substructure generated by `S` and the tuple `a`
into `N`, extending `f` and sending `a i` to `xs i`.  This is the shape consumed
by Mathlib's back-and-forth toolkit
(`Language.isExtensionPair_iff_exists_embedding_closure_singleton_sup`,
`Language.embedding_from_cg`). -/
theorem exists_embedding_closure_of_saturated
    (hT : HasQE T) (hM : M ⊨ T) (hN : N ⊨ T) [Nonempty M] [Nonempty N]
    (S : L.Substructure M) (f : S ↪[L] N) (a : Fin n → M) {κ : Cardinal.{0}}
    (hsat : IsSaturated (L := L) (N := N) κ) (hS : Cardinal.mk S < κ) :
    ∃ xs : Fin n → N, ∃ g : (↥(Substructure.closure L ((↑S : Set M) ∪ Set.range a))) ↪[L] N,
      (∀ s : S, g ⟨s, Substructure.subset_closure (Or.inl s.2)⟩ = f s) ∧
      (∀ i, g ⟨a i, Substructure.subset_closure (Or.inr ⟨i, rfl⟩)⟩ = xs i) := by
  obtain ⟨xs, hxs⟩ := exists_extension_of_saturated hT hM hN S f a hsat hS
  obtain ⟨g, hg⟩ := exists_embedding_closure S f a xs hxs
  exact ⟨xs, g, hg⟩

/-- The same with the paper's hypothesis `N` is `‖M‖⁺`-saturated. -/
theorem exists_embedding_closure_of_saturated_succ
    (hT : HasQE T) (hM : M ⊨ T) (hN : N ⊨ T) [Nonempty M] [Nonempty N]
    (S : L.Substructure M) (f : S ↪[L] N) (a : Fin n → M)
    (hsat : IsSaturated (L := L) (N := N) (Order.succ (Cardinal.mk M))) :
    ∃ xs : Fin n → N, ∃ g : (↥(Substructure.closure L ((↑S : Set M) ∪ Set.range a))) ↪[L] N,
      (∀ s : S, g ⟨s, Substructure.subset_closure (Or.inl s.2)⟩ = f s) ∧
      (∀ i, g ⟨a i, Substructure.subset_closure (Or.inr ⟨i, rfl⟩)⟩ = xs i) := by
  obtain ⟨xs, hxs⟩ := exists_extension_of_saturated_succ hT hM hN S f a hsat
  obtain ⟨g, hg⟩ := exists_embedding_closure S f a xs hxs
  exact ⟨xs, g, hg⟩

end Corollaries

end QESat


/-! ## 5. Axiom check -/

#print axioms QESat.HasQE.mono
#print axioms QESat.embedding_realize_isQF
#print axioms QESat.realize_iff_of_hasQE
#print axioms QESat.embedding_realize_iff_of_hasQE
#print axioms QESat.realize_iff_of_qf_substructure
#print axioms QESat.finitelySatisfiableIn_typeOf
#print axioms QESat.exists_extension_of_realizesTypesOver
#print axioms QESat.exists_extension_of_saturated
#print axioms QESat.exists_extension_of_saturated_succ
#print axioms QESat.exists_embedding_closure
#print axioms QESat.exists_embedding_closure_of_saturated
#print axioms QESat.exists_embedding_closure_of_saturated_succ
