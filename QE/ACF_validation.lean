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
import Mathlib

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
