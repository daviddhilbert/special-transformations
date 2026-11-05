import JohnsonCriterion

/-!
The ACF-specific part of Johnson's field-theoretic QE argument, extracted
from QE/ACF_HasQE.lean (the ACFValidation sections). The all-characteristic
theory, polynomial calculation, one-variable existential closedness, and
field amalgamation proofs are retained. The duplicate generic criterion is
omitted: this module uses the already checked JohnsonCriterion directly.
-/

open FirstOrder FirstOrder.Language FirstOrder.Ring Polynomial
open scoped FirstOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
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
end ACFValidation

#print axioms ACFValidation.acfModel
#print axioms ACFValidation.oneEC_field_acf
#print axioms ACFValidation.amalgamation_field