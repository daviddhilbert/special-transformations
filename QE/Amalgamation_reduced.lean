import Mathlib

/-!
# Johnson, Chapter 2, §2.2: amalgamation of valued fields

This file formalizes the ring-theoretic core of §2.2 of Will Johnson's thesis
"A direct proof of quantifier elimination and C-minimality in ACVF", the section which supplies
hypothesis (ii) (the amalgamation property) of the criterion Lemma 2.1.4.

Main results:

* `Johnson22.chevalley_subring` — **Chevalley's Lemma 2.2.1(1)**: for a subring `R` of a field
  `K` and a prime ideal `p` of `R` there is a valuation subring `O` of `K` with `R ≤ O` and
  `m_O ∩ R = p`, in the form `x ∈ p ↔ v_O x < 1` for `x ∈ R`.
  It is proved from `LocalSubring.exists_le_valuationSubring` (Mathlib's Chevalley).
* `Johnson22.valuedEmbedding_of_localHom` — **Remark 2.2.2**: an injective ring hom
  `O → O'` of valuation rings which pulls the maximal ideal back to the maximal ideal is induced
  by an embedding of valued fields `Frac O → Frac O'`, and that embedding preserves the relation
  `v x ≤ v y` of the language `L_val`.
* `Johnson22.amalgamation_of_ring_amalgamation` — **Lemma 2.2.7, reduced to its ring-theoretic
  content**: the amalgamation property for valued fields follows from the amalgamation statement
  `star` for valuation rings (which Johnson obtains from Lemmas 2.2.4-2.2.6, i.e. flatness of
  torsion-free modules over a valuation ring and minimal primes of `O₁ ⊗_{O₀} O₂`).
-/

open IsLocalRing

set_option linter.style.haveILetI false

namespace Johnson22

/-! ### Chevalley's lemma -/

/-- In a local ring, the maximal ideal is the set of non-units. -/
lemma mem_maximalIdeal_iff_not_isUnit {A : Type*} [CommSemiring A] [IsLocalRing A] (a : A) :
    a ∈ maximalIdeal A ↔ ¬ IsUnit a := by
  rw [mem_maximalIdeal, mem_nonunits_iff]

/-- **Chevalley's Lemma 2.2.1(1)** (subring form). Let `R` be a subring of a field `K` and let
`p` be a prime ideal of `R`. Then there is a valuation subring `O` of `K` containing `R` whose
maximal ideal meets `R` in `p`, expressed as: `x ∈ R` lies in `p` iff `v_O x < 1`. -/
theorem chevalley_subring {K : Type*} [Field K] (R : Subring K) (p : Ideal R) [p.IsPrime] :
    ∃ O : ValuationSubring K, R ≤ O.toSubring ∧ ∀ x : R, O.valuation (x : K) < 1 ↔ x ∈ p := by
  classical
  obtain ⟨O, hO⟩ := (LocalSubring.ofPrime R p).exists_le_valuationSubring
  set L := (LocalSubring.ofPrime R p).toSubring with hL
  refine ⟨O, fun x hx => hO.1 (LocalSubring.le_ofPrime R p hx), ?_⟩
  -- units and non-units agree for an inclusion `L ≤ O` of local subrings
  have hnonunit : ∀ (a : K) (ha : a ∈ L),
      (¬ IsUnit (⟨a, ha⟩ : L)) ↔ (¬ IsUnit (⟨a, hO.1 ha⟩ : O)) := by
    intro a ha
    have hEq : (Subring.inclusion hO.1 (⟨a, ha⟩ : L)) = (⟨a, hO.1 ha⟩ : O) := Subtype.ext rfl
    constructor
    · intro h u
      exact h (hO.2.map_nonunit _ (hEq ▸ u))
    · intro h u
      exact h (hEq ▸ u.map (Subring.inclusion hO.1))
  intro x
  have hxL : (x : K) ∈ L := LocalSubring.le_ofPrime R p x.2
  have hxO : (x : K) ∈ O := hO.1 hxL
  have halg : (algebraMap R L x) = (⟨(x : K), hxL⟩ : L) := Subtype.ext rfl
  have h1 : (⟨(x : K), hxO⟩ : O) ∈ maximalIdeal O ↔ ¬ IsUnit (⟨(x : K), hxO⟩ : O) :=
    mem_maximalIdeal_iff_not_isUnit _
  have h2 : ¬ IsUnit (⟨(x : K), hxO⟩ : O) ↔ ¬ IsUnit (⟨(x : K), hxL⟩ : L) :=
    (hnonunit _ hxL).symm
  have h3 : ¬ IsUnit (⟨(x : K), hxL⟩ : L) ↔ (⟨(x : K), hxL⟩ : L) ∈ maximalIdeal L :=
    (mem_maximalIdeal_iff_not_isUnit _).symm
  have h4 : (⟨(x : K), hxL⟩ : L) ∈ maximalIdeal L ↔ x ∈ p := by
    rw [← halg]; exact IsLocalization.AtPrime.to_map_mem_maximal_iff L p x
  rw [← ValuationSubring.valuation_lt_one_iff O ⟨(x : K), hxO⟩]
  exact h1.trans (h2.trans (h3.trans h4))

/-! ### Remark 2.2.2 -/

section Remark222

variable {K K' : Type*} [Field K] [Field K']

/-- Injectivity of `O → O' → K'`. -/
lemma comp_subtype_injective (O : ValuationSubring K) (O' : ValuationSubring K')
    (f : O →+* O') (hinj : Function.Injective f) :
    Function.Injective ⇑(O'.subtype.comp f) :=
  fun x y hxy => hinj (Subtype.ext (show ((f x : O') : K') = ((f y : O') : K') from hxy))

/-- The map of fraction fields induced by a ring hom of valuation rings. -/
noncomputable def fracLift (O : ValuationSubring K) (O' : ValuationSubring K')
    (f : O →+* O') (hinj : Function.Injective f) : K →+* K' :=
  IsFractionRing.lift (g := O'.subtype.comp f) (comp_subtype_injective O O' f hinj)

lemma fracLift_apply (O : ValuationSubring K) (O' : ValuationSubring K')
    (f : O →+* O') (hinj : Function.Injective f) (x : O) :
    fracLift O O' f hinj (x : K) = (f x : K') := by
  have h : fracLift O O' f hinj (algebraMap O K x) = (O'.subtype.comp f) x :=
    IsFractionRing.lift_algebraMap (A := O) (K := K) (L := K') (g := O'.subtype.comp f)
      (comp_subtype_injective O O' f hinj) x
  simpa [fracLift] using h

lemma fracLift_injective (O : ValuationSubring K) (O' : ValuationSubring K')
    (f : O →+* O') (hinj : Function.Injective f) :
    Function.Injective (fracLift O O' f hinj) := by
  intro x y hxy
  have hz : fracLift O O' f hinj (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hzero : x - y = 0 := by
    by_contra hne
    have h1 : fracLift O O' f hinj ((x - y) * (x - y)⁻¹) = 1 := by
      rw [mul_inv_cancel₀ hne, map_one]
    rw [map_mul, map_inv₀, hz] at h1
    simp at h1
  exact sub_eq_zero.mp hzero

/-- The fraction-field map preserves membership in the valuation ring. -/
lemma fracLift_mem_iff (O : ValuationSubring K) (O' : ValuationSubring K')
    (f : O →+* O') (hinj : Function.Injective f)
    (hmax : Ideal.comap f (maximalIdeal O') = maximalIdeal O) (x : K) :
    x ∈ O ↔ fracLift O O' f hinj x ∈ O' := by
  have hg := fracLift_apply O O' f hinj
  have hginj := fracLift_injective O O' f hinj
  constructor
  · intro hx
    have h2 : fracLift O O' f hinj x = (f ⟨x, hx⟩ : K') := hg ⟨x, hx⟩
    rw [h2]
    exact (f ⟨x, hx⟩).2
  · intro hx
    by_contra hxO
    have hxne : x ≠ 0 := by rintro rfl; exact hxO (O.zero_mem)
    have hnu : x⁻¹ ∈ O.nonunits :=
      (ValuationSubring.inv_mem_nonunits_iff (A := O)).mpr (Or.inr hxO)
    have hxinv : x⁻¹ ∈ O := ValuationSubring.nonunits_subset hnu
    have hmem : (⟨x⁻¹, hxinv⟩ : O) ∈ maximalIdeal O :=
      ValuationSubring.coe_mem_nonunits_iff.mp hnu
    have hmem' : f ⟨x⁻¹, hxinv⟩ ∈ maximalIdeal O' := by
      have h2 := hmem
      rw [← hmax] at h2
      exact Ideal.mem_comap.mp h2
    have hnn : (fracLift O O' f hinj x)⁻¹ ∈ O'.nonunits := by
      rw [← map_inv₀, hg ⟨x⁻¹, hxinv⟩]
      exact ValuationSubring.coe_mem_nonunits_iff.mpr hmem'
    have hmemO' : (fracLift O O' f hinj x)⁻¹ ∈ O' :=
      ValuationSubring.nonunits_subset hnn
    have hnonunit : ¬ IsUnit (⟨(fracLift O O' f hinj x)⁻¹, hmemO'⟩ : O') :=
      (mem_maximalIdeal_iff_not_isUnit _).mp (ValuationSubring.coe_mem_nonunits_iff.mp hnn)
    have hunit : IsUnit (⟨(fracLift O O' f hinj x)⁻¹, hmemO'⟩ : O') := by
      refine IsUnit.of_mul_eq_one (⟨fracLift O O' f hinj x, hx⟩ : O') ?_
      apply Subtype.ext
      show (fracLift O O' f hinj x)⁻¹ * fracLift O O' f hinj x = 1
      exact inv_mul_cancel₀ (fun h => hxne ((map_eq_zero_iff _ hginj).mp h))
    exact hnonunit hunit

/-- The fraction-field map preserves the relation `v x ≤ v y`. -/
lemma fracLift_val_le_iff (O : ValuationSubring K) (O' : ValuationSubring K')
    (f : O →+* O') (hinj : Function.Injective f)
    (hmax : Ideal.comap f (maximalIdeal O') = maximalIdeal O) (x y : K) :
    O.valuation x ≤ O.valuation y ↔
      O'.valuation (fracLift O O' f hinj x) ≤ O'.valuation (fracLift O O' f hinj y) := by
  have hginj := fracLift_injective O O' f hinj
  have hval := fracLift_mem_iff O O' f hinj hmax
  rw [ValuationSubring.valuation_le_iff, ValuationSubring.valuation_le_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨⟨fracLift O O' f hinj (a : K), (hval (a : K)).mp a.2⟩, by rw [← map_mul, ha]⟩
  · rintro ⟨a, ha⟩
    by_cases hy : y = 0
    · subst hy
      have hgx : fracLift O O' f hinj x = 0 := by rw [← ha, map_zero, mul_zero]
      have hx0 : x = 0 := (map_eq_zero_iff _ hginj).mp hgx
      subst hx0
      exact ⟨0, by simp⟩
    · have hgy : fracLift O O' f hinj y ≠ 0 := fun h => hy ((map_eq_zero_iff _ hginj).mp h)
      have hxa : fracLift O O' f hinj (x * y⁻¹) = (a : K') := by
        rw [map_mul, map_inv₀, ← ha]
        exact mul_inv_cancel_right₀ hgy (a : K')
      refine ⟨⟨x * y⁻¹, (hval _).mpr (by rw [hxa]; exact a.2)⟩, ?_⟩
      show x * y⁻¹ * y = x
      rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]

/-- **Remark 2.2.2** (Johnson, §2.2): a ring hom between valuation rings which is injective and
pulls the maximal ideal back to the maximal ideal is induced by an embedding of valued fields on
fraction fields, and that embedding preserves the relation `v x ≤ v y`. -/
theorem valuedEmbedding_of_localHom (O : ValuationSubring K) (O' : ValuationSubring K')
    (f : O →+* O') (hinj : Function.Injective f)
    (hmax : Ideal.comap f (maximalIdeal O') = maximalIdeal O) :
    ∃ g : K →+* K', Function.Injective g ∧ (∀ x : K, x ∈ O ↔ g x ∈ O') ∧
      ∀ x y : K, O.valuation x ≤ O.valuation y ↔ O'.valuation (g x) ≤ O'.valuation (g y) :=
  ⟨fracLift O O' f hinj, fracLift_injective O O' f hinj,
    fracLift_mem_iff O O' f hinj hmax, fracLift_val_le_iff O O' f hinj hmax⟩

end Remark222

/-! ### Valued embeddings and the amalgamation theorem -/

section Amalgamation

variable {K K' : Type*} [Field K] [Field K']

/-- An embedding of valued fields in Johnson's language `L_val`: an injective ring hom which
preserves the relation `v x ≤ v y`. -/
def IsValEmbedding {Γ Γ' : Type*} [LinearOrderedCommGroupWithZero Γ]
    [LinearOrderedCommGroupWithZero Γ'] (v : Valuation K Γ) (v' : Valuation K' Γ')
    (f : K →+* K') : Prop :=
  Function.Injective f ∧ ∀ x y : K, v x ≤ v y ↔ v' (f x) ≤ v' (f y)

/-- The hypotheses of Remark 2.2.2: an injective ring hom of valuation rings which pulls the
maximal ideal back to the maximal ideal. -/
def IsLocalValHom (O : ValuationSubring K) (O' : ValuationSubring K') (f : O →+* O') : Prop :=
  Function.Injective f ∧ Ideal.comap f (maximalIdeal O') = maximalIdeal O

lemma val_lt_one_iff_of_valEmbedding {Γ Γ' : Type*} [LinearOrderedCommGroupWithZero Γ]
    [LinearOrderedCommGroupWithZero Γ'] {v : Valuation K Γ} {v' : Valuation K' Γ'}
    {f : K →+* K'} (hf : IsValEmbedding v v' f) (x : K) : v x < 1 ↔ v' (f x) < 1 := by
  have h1 : v x < v 1 ↔ v' (f x) < v' (f 1) := by
    rw [lt_iff_not_ge, lt_iff_not_ge, hf.2 1 x]
  simpa using h1

/-- A valued embedding preserves membership in the valuation rings. -/
lemma IsValEmbedding.mem_iff (O : ValuationSubring K) (O' : ValuationSubring K')
    (i : K →+* K') (hi : IsValEmbedding O.valuation O'.valuation i) (x : K) :
    x ∈ O ↔ i x ∈ O' := by
  have h2 : ∀ y : K, O.valuation y ≤ 1 ↔ O'.valuation (i y) ≤ 1 := by
    intro y
    rw [show (1 : O.ValueGroup) = O.valuation 1 from (map_one _).symm,
      show (1 : O'.ValueGroup) = O'.valuation (i 1) from by rw [map_one, map_one]]
    exact hi.2 y 1
  rw [← ValuationSubring.valuation_le_one_iff O x,
    ← ValuationSubring.valuation_le_one_iff O' (i x)]
  exact h2 x

/-- The fraction-field map of Remark 2.2.2 is a valued embedding. -/
lemma fracLift_isValEmbedding (O : ValuationSubring K) (O' : ValuationSubring K')
    (f : O →+* O') (hinj : Function.Injective f)
    (hmax : Ideal.comap f (maximalIdeal O') = maximalIdeal O) :
    IsValEmbedding O.valuation O'.valuation (fracLift O O' f hinj) :=
  ⟨fracLift_injective O O' f hinj, fracLift_val_le_iff O O' f hinj hmax⟩

/-- Restricting a valued embedding to the valuation rings gives a local injective hom. -/
lemma isLocalValHom_restrict (O : ValuationSubring K) (O' : ValuationSubring K')
    (i : K →+* K') (hi : IsValEmbedding O.valuation O'.valuation i) :
    IsLocalValHom O O'
      (i.restrict O O' fun x hx => (IsValEmbedding.mem_iff O O' i hi x).mp hx) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have h := congrArg (fun z : O' => (z : K')) hxy
    simp only [RingHom.coe_restrict_apply] at h
    exact hi.1 h
  · ext x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff O' (i.restrict _ _ _ x),
      ValuationSubring.valuation_lt_one_iff O x]
    exact (val_lt_one_iff_of_valEmbedding hi (x : K)).symm


/-- Conversely, an injective ring hom which preserves the valuation rings is an `L_val`-embedding:
the quantifier-free type of the language `L_val` is exactly the theory of the valuation ring. -/
theorem isValEmbedding_of_mem_iff (O : ValuationSubring K) (O' : ValuationSubring K')
    (i : K →+* K') (hinj : Function.Injective i) (hmem : ∀ x : K, x ∈ O ↔ i x ∈ O') :
    IsValEmbedding O.valuation O'.valuation i := by
  refine ⟨hinj, ?_⟩
  intro x y
  rw [ValuationSubring.valuation_le_iff, ValuationSubring.valuation_le_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨⟨i (a : K), (hmem (a : K)).mp a.2⟩, by rw [← map_mul, ha]⟩
  · rintro ⟨a, ha⟩
    by_cases hy : y = 0
    · subst hy
      have hx : i x = 0 := by rw [← ha, map_zero, mul_zero]
      have hx0 : x = 0 := hinj (by simpa using hx)
      subst hx0
      exact ⟨0, by simp⟩
    · have hiy : i y ≠ 0 := fun h => hy (hinj (by simpa using h))
      have hxa : i (x * y⁻¹) = (a : K') := by
        rw [map_mul, map_inv₀, ← ha]
        exact mul_inv_cancel_right₀ hiy (a : K')
      refine ⟨⟨x * y⁻¹, (hmem _).mpr (by rw [hxa]; exact a.2)⟩, ?_⟩
      show x * y⁻¹ * y = x
      rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]

universe u

/-- **Amalgamation of valued fields** (Johnson, Lemma 2.2.7), reduced to the ring-theoretic
amalgamation statement `star` for valuation rings, which is where Johnson uses Chevalley's lemma
2.2.1(2) together with the tensor product `O₁ ⊗_{O₀} O₂` (Lemmas 2.2.4-2.2.6). -/
theorem amalgamation_of_ring_amalgamation
    (star : ∀ {A A₁ A₂ : Type u} [Field A] [Field A₁] [Field A₂]
      (B : ValuationSubring A) (B₁ : ValuationSubring A₁) (B₂ : ValuationSubring A₂)
      (f₁ : B →+* B₁) (f₂ : B →+* B₂),
      IsLocalValHom B B₁ f₁ → IsLocalValHom B B₂ f₂ →
      ∃ (C : Type u) (_ : Field C) (B₃ : ValuationSubring C) (g₁ : B₁ →+* B₃) (g₂ : B₂ →+* B₃),
        IsLocalValHom B₁ B₃ g₁ ∧ IsLocalValHom B₂ B₃ g₂ ∧ g₁.comp f₁ = g₂.comp f₂)
    {F F₁ F₂ : Type u} [Field F] [Field F₁] [Field F₂]
    (O : ValuationSubring F) (O₁ : ValuationSubring F₁) (O₂ : ValuationSubring F₂)
    (i₁ : F →+* F₁) (i₂ : F →+* F₂)
    (h₁ : IsValEmbedding O.valuation O₁.valuation i₁)
    (h₂ : IsValEmbedding O.valuation O₂.valuation i₂) :
    ∃ (N : Type u) (_ : Field N) (O₃ : ValuationSubring N) (j₁ : F₁ →+* N) (j₂ : F₂ →+* N),
      IsValEmbedding O₁.valuation O₃.valuation j₁ ∧ IsValEmbedding O₂.valuation O₃.valuation j₂ ∧
      j₁.comp i₁ = j₂.comp i₂ := by
  classical
  -- Step 1: restrict the valued embeddings to local injective homs of valuation rings.
  set f₁ : O →+* O₁ := i₁.restrict O O₁ fun x hx => (IsValEmbedding.mem_iff O O₁ i₁ h₁ x).mp hx
    with hf₁def
  have hf₁ : IsLocalValHom O O₁ f₁ := isLocalValHom_restrict O O₁ i₁ h₁
  set f₂ : O →+* O₂ := i₂.restrict O O₂ fun x hx => (IsValEmbedding.mem_iff O O₂ i₂ h₂ x).mp hx
    with hf₂def
  have hf₂ : IsLocalValHom O O₂ f₂ := isLocalValHom_restrict O O₂ i₂ h₂
  -- Step 2: the ring-theoretic amalgamation.
  obtain ⟨N, hN, O₃, g₁, g₂, hg₁, hg₂, hcomm⟩ := star O O₁ O₂ f₁ f₂ hf₁ hf₂
  letI : Field N := hN
  -- Step 3: pass back to fraction fields (Remark 2.2.2).
  refine ⟨N, hN, O₃, fracLift O₁ O₃ g₁ hg₁.1, fracLift O₂ O₃ g₂ hg₂.1,
    fracLift_isValEmbedding O₁ O₃ g₁ hg₁.1 hg₁.2,
    fracLift_isValEmbedding O₂ O₃ g₂ hg₂.1 hg₂.2, ?_⟩
  -- Step 4: the square commutes, checked on the valuation ring `O` and extended to `F`.
  refine IsFractionRing.ringHom_ext (A := O) fun x => ?_
  have hx₁ : i₁ ((x : O) : F) ∈ O₁ := (IsValEmbedding.mem_iff O O₁ i₁ h₁ _).mp x.2
  have hx₂ : i₂ ((x : O) : F) ∈ O₂ := (IsValEmbedding.mem_iff O O₂ i₂ h₂ _).mp x.2
  have e₁ : fracLift O₁ O₃ g₁ hg₁.1 (i₁ ((x : O) : F)) = (g₁ (f₁ x) : N) :=
    fracLift_apply O₁ O₃ g₁ hg₁.1 (⟨i₁ ((x : O) : F), hx₁⟩ : O₁)
  have e₂ : fracLift O₂ O₃ g₂ hg₂.1 (i₂ ((x : O) : F)) = (g₂ (f₂ x) : N) :=
    fracLift_apply O₂ O₃ g₂ hg₂.1 (⟨i₂ ((x : O) : F), hx₂⟩ : O₂)
  have e₃ : g₁ (f₁ x) = g₂ (f₂ x) := RingHom.congr_fun hcomm x
  show fracLift O₁ O₃ g₁ hg₁.1 (i₁ ((x : O) : F)) =
    fracLift O₂ O₃ g₂ hg₂.1 (i₂ ((x : O) : F))
  rw [e₁, e₃, ← e₂]

end Amalgamation


/-! ### Chevalley's lemma, hom form, and the extension of valuations -/

/-- **Chevalley's Lemma 2.2.1(2)** (hom form). Let `φ : R →+* K` be a ring hom into a field and
let `p` be a prime ideal of `R` containing `ker φ`. Then there is a valuation subring `O` of `K`
containing the image of `φ` such that for all `x : R`, `φ x` lies in the maximal ideal of `O`
iff `x ∈ p`. -/
theorem chevalley_hom {R : Type*} [CommRing R] {K : Type*} [Field K]
    (φ : R →+* K) (p : Ideal R) [p.IsPrime] (hker : RingHom.ker φ ≤ p) :
    ∃ O : ValuationSubring K, φ.range ≤ O.toSubring ∧ ∀ x : R, O.valuation (φ x) < 1 ↔ x ∈ p := by
  classical
  have hker' : RingHom.ker φ.rangeRestrict ≤ p := by
    intro x hx
    apply hker
    have hx' : φ.rangeRestrict x = 0 := hx
    have h2 : (φ.rangeRestrict x : K) = 0 := by rw [hx']; rfl
    rwa [RingHom.coe_rangeRestrict] at h2
  haveI hp' : (Ideal.map φ.rangeRestrict p).IsPrime :=
    Ideal.map_isPrime_of_surjective φ.rangeRestrict_surjective hker'
  obtain ⟨O, hOle, hO⟩ := chevalley_subring φ.range (Ideal.map φ.rangeRestrict p)
  have hcomap : Ideal.comap φ.rangeRestrict (Ideal.map φ.rangeRestrict p) = p := by
    rw [Ideal.comap_map_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker']
  refine ⟨O, hOle, fun x => ?_⟩
  rw [show φ x = ((φ.rangeRestrict x : φ.range) : K) from (RingHom.coe_rangeRestrict φ x).symm,
    hO (φ.rangeRestrict x), ← Ideal.mem_comap, hcomap]

/-- **Corollary 2.2.3** (Johnson, §2.2): a valuation on a field extends to any field extension.
This is the content of Chevalley's lemma 2.2.1(1) used by Johnson in §2.2. -/
theorem valExtension_of_fieldExtension {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Γ : Type u} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) :
    ∃ (Γ' : Type u) (_ : LinearOrderedCommGroupWithZero Γ') (w : Valuation L Γ'), v.HasExtension w := by
  classical
  set O_K := v.valuationSubring with hO_K
  set φ : O_K →+* L := (algebraMap K L).comp O_K.subtype with hφ
  have halg_inj : Function.Injective (algebraMap K L) := by
    intro a b hab
    by_contra hne
    have h1 : algebraMap K L (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h2 : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h3 : algebraMap K L 1 = 0 := by
      rw [← mul_inv_cancel₀ h2, map_mul, h1, zero_mul]
    rw [map_one] at h3
    exact one_ne_zero h3
  have hker : RingHom.ker φ ≤ maximalIdeal O_K := by
    intro y hy
    rw [RingHom.mem_ker] at hy
    have hy0 : ((y : O_K) : K) = 0 := halg_inj (by simpa [hφ] using hy)
    rw [show y = 0 from Subtype.ext hy0]
    exact (maximalIdeal O_K).zero_mem
  obtain ⟨O, hOle, hO⟩ := chevalley_hom φ (maximalIdeal O_K) hker
  have hle : ∀ y : O_K, (φ y : L) ∈ O := fun y => hOle (RingHom.mem_range_self φ y)
  refine ⟨O.ValueGroup, inferInstance, O.valuation, ?_⟩
  refine Valuation.HasExtension.ofComapInteger (vK := v) (vA := O.valuation) ?_
  rw [ValuationSubring.integer_valuation]
  show Subring.comap (algebraMap K L) O.toSubring = O_K.toSubring
  refine le_antisymm ?_ ?_
  · -- the harder inclusion: `O ∩ K ⊆ O_K`
    intro x hx
    by_contra hxO
    have hxne : x ≠ 0 := by rintro rfl; exact hxO (O_K.zero_mem)
    have hnu : x⁻¹ ∈ O_K.nonunits :=
      (ValuationSubring.inv_mem_nonunits_iff (A := O_K)).mpr (Or.inr hxO)
    have hxinv : x⁻¹ ∈ O_K := ValuationSubring.nonunits_subset hnu
    have hmO : (⟨φ ⟨x⁻¹, hxinv⟩, hle _⟩ : O) ∈ maximalIdeal O := by
      rw [ValuationSubring.valuation_lt_one_iff]
      exact (hO ⟨x⁻¹, hxinv⟩).mpr (ValuationSubring.coe_mem_nonunits_iff.mp hnu)
    have hunit : IsUnit (⟨φ ⟨x⁻¹, hxinv⟩, hle _⟩ : O) := by
      refine IsUnit.of_mul_eq_one (⟨algebraMap K L x, hx⟩ : O) ?_
      apply Subtype.ext
      show (φ ⟨x⁻¹, hxinv⟩ : L) * algebraMap K L x = 1
      have h1 : (φ ⟨x⁻¹, hxinv⟩ : L) = algebraMap K L x⁻¹ := rfl
      rw [h1, ← map_mul, inv_mul_cancel₀ hxne, map_one]
    exact (mem_maximalIdeal_iff_not_isUnit _).mp hmO hunit
  · intro x hx
    exact hle ⟨x, hx⟩


/-- **Chevalley's Lemma 2.2.1(2)** in the form in which Johnson applies it (to the tensor product
`O₁ ⊗_{O₀} O₂`): for a ring `R` and primes `q ⊆ p` there are a field `K`, a valuation subring
`O ⊆ K` and a ring hom `f : R →+* O` with `f⁻¹(0) = q` and `f⁻¹(m_O) = p`, the latter expressed
in the language `L_val` as `v_O (f x) < 1 ↔ x ∈ p`. -/
theorem chevalley_hom' {R : Type u} [CommRing R] (q p : Ideal R) [q.IsPrime] [p.IsPrime]
    (hqp : q ≤ p) :
    ∃ (K : Type u) (_ : Field K) (O : ValuationSubring K) (f : R →+* O),
      (∀ x : R, f x = 0 ↔ x ∈ q) ∧ ∀ x : R, O.valuation (f x : K) < 1 ↔ x ∈ p := by
  classical
  set K : Type u := FractionRing (R ⧸ q) with hK
  let φ : R →+* K := (algebraMap (R ⧸ q) K).comp (Ideal.Quotient.mk q)
  have hker : RingHom.ker φ = q := by
    ext x
    rw [RingHom.mem_ker]
    constructor
    · intro h
      have h' : (Ideal.Quotient.mk q x : R ⧸ q) = 0 :=
        IsFractionRing.injective (R ⧸ q) K (by simpa [φ] using h)
      exact (Ideal.Quotient.eq_zero_iff_mem).mp h'
    · intro h
      have h' : (Ideal.Quotient.mk q x : R ⧸ q) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr h
      simp [φ, h']
  have hker' : RingHom.ker φ ≤ p := by rw [hker]; exact hqp
  obtain ⟨O, hOle, hO⟩ := chevalley_hom φ p hker'
  set f : R →+* O := φ.codRestrict O.toSubring (fun x => hOle (RingHom.mem_range_self φ x)) with hf
  refine ⟨K, inferInstance, O, f, ?_, ?_⟩
  · intro x
    have h1 : ((f x : O) : K) = φ x := RingHom.codRestrict_apply _ _ _ x
    constructor
    · intro h
      have h3 : ((f x : O) : K) = 0 := by rw [h]; rfl
      rw [h1] at h3
      have h4 : x ∈ RingHom.ker φ := h3
      rwa [hker] at h4
    · intro h
      have h4 : x ∈ RingHom.ker φ := by rw [hker]; exact h
      have h3 : φ x = 0 := h4
      apply Subtype.ext
      rw [h1, h3]
      rfl
  · intro x
    rw [show ((f x : O) : K) = φ x from RingHom.codRestrict_apply _ _ _ x]
    exact hO x

end Johnson22

#print axioms Johnson22.chevalley_subring
#print axioms Johnson22.chevalley_hom
#print axioms Johnson22.chevalley_hom'
#print axioms Johnson22.valuedEmbedding_of_localHom
#print axioms Johnson22.isValEmbedding_of_mem_iff
#print axioms Johnson22.amalgamation_of_ring_amalgamation
#print axioms Johnson22.valExtension_of_fieldExtension
