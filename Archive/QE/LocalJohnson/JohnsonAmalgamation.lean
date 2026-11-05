import JohnsonGeometry

/-!
# Johnson's Chapter 2 proof: valued-field amalgamation

Extracted from the existing QE/Assembly_val.lean (sections 17–19).
The tensor-product statement `Johnson22.star` is proved here and supplies
amalgamation; no amalgamation theorem or QE theorem is assumed.
-/

open FirstOrder FirstOrder.Language FirstOrder.Ring
open scoped FirstOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-! ## 17. Johnson §2.2: amalgamation of valuation rings (`star`) -/

set_option maxHeartbeats 1000000


/-!
# Johnson, Chapter 2, §2.2: amalgamation of valued fields

This file formalizes the ring-theoretic core of §2.2 of Will Johnson's thesis
*Fun with Fields*, Chapter 2, "A direct proof of quantifier elimination and C-minimality in ACVF".
This section supplies
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
  `star` for valuation rings.
* `Johnson22.star` — **the amalgamation statement for valuation rings, proved** (Johnson's
  proof of 2.2.7 verbatim).  Write `S := B₁ ⊗_B B₂`.  `B₁, B₂` and the fraction fields `A₁, A₂`
  are torsion-free, hence flat, over the valuation ring `B` — this is NOT Johnson's Lemma 2.2.4
  but Mathlib's `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`, since a valuation ring is a
  Bezout domain (`flat_of_torsion_eq_bot`, `torsion_eq_bot_of_injective`).  Hence
  `B₁ ⊗_B B₂ ↪ A₁ ⊗_B A₂` (`TensorProduct.map_injective_of_flat_flat`), so a minimal prime of `S`
  lifts to a prime of `A₁ ⊗_B A₂`, which contracts to `0` in `A₁` and `A₂` — that is Lemma 2.2.6.
  For the prime `p`: the residue-field tensor `k₁ ⊗_{k₀} k₂` is nontrivial
  (`nontrivial_of_algebraMap_injective_of_isDomain`), and `p` is the pullback of one of its
  primes; `p` contracts to `m₁` and `m₂`.  Then a minimal prime `q ≤ p` contracts to `0`, and
  Chevalley in the two-prime form (`chevalley_hom'`, 2.2.1(2)) gives `S → O₃` with prescribed
  kernels.  The closing `example` typechecks `amalgamation_of_ring_amalgamation star`, i.e. the
  amalgamation property for valued fields, at universe `Type u`.
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
    have e1 : (1 : O.ValueGroup) = O.valuation 1 := (map_one _).symm
    have e2 : (1 : O'.ValueGroup) = O'.valuation (i 1) := by rw [map_one, map_one]
    rw [e1, e2]
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


/-! ### Johnson, Lemma 2.2.4: torsion-free modules over a valuation ring are flat -/

section TorsionFree

/-- A torsion-free module over a valuation ring is flat (Johnson, Lemma 2.2.4.2), using
Mathlib's `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout` and the fact that a valuation ring
is a Bezout domain. -/
theorem flat_of_torsion_eq_bot {R M : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    [AddCommGroup M] [Module R M] (h : Submodule.torsion R M = ⊥) : Module.Flat R M :=
  Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr h

/-- An algebra over a domain which is a domain and whose structure map is injective is
torsion-free. -/
theorem torsion_eq_bot_of_injective {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S] (h : Function.Injective (algebraMap R S)) :
    Submodule.torsion R S = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_torsion_iff] at hx
  obtain ⟨⟨r, hr⟩, hrx⟩ := hx
  have hr0 : r ≠ 0 := fun h0 => zero_notMem_nonZeroDivisors (h0 ▸ hr)
  have h2 : algebraMap R S r * x = 0 := by simpa [Algebra.smul_def] using hrx
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (h (by simpa using h3)) hr0
  · exact h3

end TorsionFree

/-! ### Lemma 2.2.6 and the two-prime Chevalley step: `star`

`star` is proved by Johnson's argument (Fun with Fields, §2.2, Lemmas 2.2.4-2.2.7):

* Step 1. `B₁`, `B₂`, `A₁`, `A₂` are flat over `B` (Lemma 2.2.4): they are torsion-free
  (`torsion_eq_bot_of_injective`) and a torsion-free module over a valuation ring is flat
  (`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`, using `ValuationRing → IsBezout`).
* Step 2. Hence `S = B₁ ⊗_B B₂ ↪ A₁ ⊗_B A₂` (Lemma 2.2.6's input), as a *ring* hom
  `Algebra.TensorProduct.map φ₁ φ₂`, whose injectivity follows from
  `TensorProduct.map_injective_of_flat_flat` on pure tensors.
* Step 3. Lemma 2.2.6: a minimal prime `q` of `S` contracts to `0` in `B₁` and `B₂`.  A prime of
  `A₁ ⊗_B A₂` restricts to `0` in the field `A₁`, and Lemma 2.2.5
  (`Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective`) lifts `q` to such a prime.
* Step 4. Lemma 2.2.7's prime `p`: `k₁ ⊗_{k₀} k₂` (residue fields) is nontrivial by
  `Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain`, so it has a maximal
  ideal `𝔪`; the pullback of `𝔪` along `B₁ ⊗_B B₂ → k₁ ⊗_{k₀} k₂` is a prime whose contractions to
  `B₁`, `B₂` are the maximal ideals (they contain them, and maximal ideals are maximal).
* Step 5. Take a minimal prime `q ≤ p`, apply Chevalley's Lemma 2.2.1(2) (`chevalley_hom'`) to get
  `m : S → O` with `m⁻¹(0) = q` and `m⁻¹(m_O) = p`; then `gᵢ = m ∘ (Bᵢ → S)` are local injective
  homs into `O`, with `g₁ ∘ f₁ = g₂ ∘ f₂`.

The only ingredient taken from Johnson without reproving it is Lemma 2.2.4.1 (finitely generated
torsion-free modules over a valuation ring are free); its consequence 2.2.4.2 is supplied by
Mathlib's Bezout-domain criterion.  Lemmas 2.2.5 and 2.2.1 (both parts) are also taken from
Mathlib resp. the earlier part of this file. -/

section Star

open scoped TensorProduct

/-- **Amalgamation for valuation rings** (`star`), Johnson, Lemma 2.2.7. -/
theorem star : ∀ {A A₁ A₂ : Type u} [Field A] [Field A₁] [Field A₂]
    (B : ValuationSubring A) (B₁ : ValuationSubring A₁) (B₂ : ValuationSubring A₂)
    (f₁ : B →+* B₁) (f₂ : B →+* B₂),
    IsLocalValHom B B₁ f₁ → IsLocalValHom B B₂ f₂ →
    ∃ (C : Type u) (_ : Field C) (B₃ : ValuationSubring C) (g₁ : B₁ →+* B₃) (g₂ : B₂ →+* B₃),
      IsLocalValHom B₁ B₃ g₁ ∧ IsLocalValHom B₂ B₃ g₂ ∧ g₁.comp f₁ = g₂.comp f₂ := by
  intro A A₁ A₂ _ _ _ B B₁ B₂ f₁ f₂ hf₁ hf₂
  classical
  -- ## Step 0: `B`-algebra structures and consequences of the hypotheses
  letI algBB₁ : Algebra B B₁ := f₁.toAlgebra
  letI algBB₂ : Algebra B B₂ := f₂.toAlgebra
  haveI hloc₁ : IsLocalHom (algebraMap B B₁) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact ((IsLocalRing.local_hom_TFAE f₁).out 4 0 rfl rfl).mp hf₁.2
  haveI hloc₂ : IsLocalHom (algebraMap B B₂) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact ((IsLocalRing.local_hom_TFAE f₂).out 4 0 rfl rfl).mp hf₂.2
  have hinj₁ : Function.Injective (algebraMap B B₁) := by
    rw [RingHom.algebraMap_toAlgebra]; exact hf₁.1
  have hinj₂ : Function.Injective (algebraMap B B₂) := by
    rw [RingHom.algebraMap_toAlgebra]; exact hf₂.1
  letI algBA₁ : Algebra B A₁ := ((algebraMap B₁ A₁).comp f₁).toAlgebra
  letI algBA₂ : Algebra B A₂ := ((algebraMap B₂ A₂).comp f₂).toAlgebra
  haveI htow₁ : IsScalarTower B B₁ A₁ := IsScalarTower.of_algebraMap_eq' rfl
  haveI htow₂ : IsScalarTower B B₂ A₂ := IsScalarTower.of_algebraMap_eq' rfl
  -- ## Step 1: flatness of `B₁`, `B₂`, `A₁`, `A₂` over `B` (Lemma 2.2.4)
  haveI hflat₁ : Module.Flat B B₁ := flat_of_torsion_eq_bot (torsion_eq_bot_of_injective hinj₁)
  haveI hflat₂ : Module.Flat B B₂ := flat_of_torsion_eq_bot (torsion_eq_bot_of_injective hinj₂)
  haveI hfrac₁ : Module.Flat B₁ A₁ := IsLocalization.flat A₁ (nonZeroDivisors B₁)
  haveI hfrac₂ : Module.Flat B₂ A₂ := IsLocalization.flat A₂ (nonZeroDivisors B₂)
  haveI hflatA₁ : Module.Flat B A₁ := Module.Flat.trans B B₁ A₁
  haveI hflatA₂ : Module.Flat B A₂ := Module.Flat.trans B B₂ A₂
  -- ## Step 2: the ring hom `S = B₁ ⊗_B B₂ → D = A₁ ⊗_B A₂` is injective
  set φ₁ : B₁ →ₐ[B] A₁ := IsScalarTower.toAlgHom B B₁ A₁ with hφ₁
  set φ₂ : B₂ →ₐ[B] A₂ := IsScalarTower.toAlgHom B B₂ A₂ with hφ₂
  set F₁ : B₁ →ₗ[B] A₁ := (Algebra.linearMap B₁ A₁).restrictScalars B with hF₁
  set F₂ : B₂ →ₗ[B] A₂ := (Algebra.linearMap B₂ A₂).restrictScalars B with hF₂
  have hF₁inj : Function.Injective F₁ := fun x y h => IsFractionRing.injective B₁ A₁ h
  have hF₂inj : Function.Injective F₂ := fun x y h => IsFractionRing.injective B₂ A₂ h
  have hinjT : Function.Injective
      (Algebra.TensorProduct.map φ₁ φ₂ : B₁ ⊗[B] B₂ →ₐ[B] A₁ ⊗[B] A₂) := by
    have hlin : Function.Injective (TensorProduct.map F₁ F₂ : B₁ ⊗[B] B₂ →ₗ[B] A₁ ⊗[B] A₂) :=
      TensorProduct.map_injective_of_flat_flat F₁ F₂ hF₁inj hF₂inj
    have hcoe : ∀ x : B₁ ⊗[B] B₂,
        (Algebra.TensorProduct.map φ₁ φ₂ : B₁ ⊗[B] B₂ →ₐ[B] A₁ ⊗[B] A₂) x =
          (TensorProduct.map F₁ F₂ : B₁ ⊗[B] B₂ →ₗ[B] A₁ ⊗[B] A₂) x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [hF₁, hF₂, hφ₁, hφ₂]
      | add x y hx hy => simp [hx, hy]
    rw [show ⇑(Algebra.TensorProduct.map φ₁ φ₂ : B₁ ⊗[B] B₂ →ₐ[B] A₁ ⊗[B] A₂) =
        ⇑(TensorProduct.map F₁ F₂ : B₁ ⊗[B] B₂ →ₗ[B] A₁ ⊗[B] A₂) from funext hcoe]
    exact hlin

  -- ## Step 3: minimal primes of `S = B₁ ⊗_B B₂` contract to `0` in `B₁` and `B₂` (Lemma 2.2.6)
  set ι : B₁ ⊗[B] B₂ →+* A₁ ⊗[B] A₂ :=
    (Algebra.TensorProduct.map φ₁ φ₂ : B₁ ⊗[B] B₂ →ₐ[B] A₁ ⊗[B] A₂).toRingHom with hι
  set incL : A₁ →+* A₁ ⊗[B] A₂ :=
    (Algebra.TensorProduct.includeLeft (R := B) (S := B) (A := A₁) (B := A₂)).toRingHom with hincL
  set incR : A₂ →+* A₁ ⊗[B] A₂ :=
    (Algebra.TensorProduct.includeRight (R := B) (A := A₁) (B := A₂)).toRingHom with hincR
  set i₁ : B₁ →+* B₁ ⊗[B] B₂ := Algebra.TensorProduct.includeLeftRingHom with hi₁
  set i₂ : B₂ →+* B₁ ⊗[B] B₂ :=
    (Algebra.TensorProduct.includeRight : B₂ →ₐ[B] B₁ ⊗[B] B₂).toRingHom with hi₂
  have hi₁inj : Function.Injective i₁ :=
    Algebra.TensorProduct.includeLeft_injective (R := B) (S := B) (A := B₁) (B := B₂) hinj₂
  have hi₂inj : Function.Injective i₂ :=
    Algebra.TensorProduct.includeRight_injective (R := B) (A := B₁) (B := B₂) hinj₁
  have hιi₁ : ι.comp i₁ = incL.comp (algebraMap B₁ A₁) := by
    ext a
    simp [hι, hi₁, hincL, hφ₁]
  have hιi₂ : ι.comp i₂ = incR.comp (algebraMap B₂ A₂) := by
    ext a
    simp [hι, hi₂, hincR, hφ₂, Algebra.TensorProduct.map_tmul]
  have h226₁ : ∀ q : Ideal (B₁ ⊗[B] B₂), q ∈ minimalPrimes (B₁ ⊗[B] B₂) →
      Ideal.comap i₁ q = ⊥ := by
    intro q hq
    obtain ⟨Q, hQprime, hQcomap⟩ :=
      Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective (f := ι) hinjT q hq
    haveI hQp : Q.IsPrime := hQprime
    have hQL : Ideal.comap incL Q = ⊥ := by
      rcases Ideal.eq_bot_or_top (Ideal.comap incL Q) with h | h
      · exact h
      · exfalso
        have h2 : (1 : A₁) ∈ Ideal.comap incL Q := h ▸ Submodule.mem_top
        rw [Ideal.mem_comap, map_one] at h2
        exact hQp.ne_top (Ideal.eq_top_iff_one Q |>.mpr h2)
    calc Ideal.comap i₁ q
        = Ideal.comap i₁ (Ideal.comap ι Q) := by rw [hQcomap]
      _ = Ideal.comap (ι.comp i₁) Q := Ideal.comap_comap _ _
      _ = Ideal.comap (incL.comp (algebraMap B₁ A₁)) Q := by rw [hιi₁]
      _ = Ideal.comap (algebraMap B₁ A₁) (Ideal.comap incL Q) := (Ideal.comap_comap _ _).symm
      _ = ⊥ := by rw [hQL]; exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective B₁ A₁)
  have h226₂ : ∀ q : Ideal (B₁ ⊗[B] B₂), q ∈ minimalPrimes (B₁ ⊗[B] B₂) →
      Ideal.comap i₂ q = ⊥ := by
    intro q hq
    obtain ⟨Q, hQprime, hQcomap⟩ :=
      Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective (f := ι) hinjT q hq
    haveI hQp : Q.IsPrime := hQprime
    have hQR : Ideal.comap incR Q = ⊥ := by
      rcases Ideal.eq_bot_or_top (Ideal.comap incR Q) with h | h
      · exact h
      · exfalso
        have h2 : (1 : A₂) ∈ Ideal.comap incR Q := h ▸ Submodule.mem_top
        rw [Ideal.mem_comap, map_one] at h2
        exact hQp.ne_top (Ideal.eq_top_iff_one Q |>.mpr h2)
    calc Ideal.comap i₂ q
        = Ideal.comap i₂ (Ideal.comap ι Q) := by rw [hQcomap]
      _ = Ideal.comap (ι.comp i₂) Q := Ideal.comap_comap _ _
      _ = Ideal.comap (incR.comp (algebraMap B₂ A₂)) Q := by rw [hιi₂]
      _ = Ideal.comap (algebraMap B₂ A₂) (Ideal.comap incR Q) := (Ideal.comap_comap _ _).symm
      _ = ⊥ := by rw [hQR]; exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective B₂ A₂)
  -- ## Step 4: a prime `p` of `S` whose contractions to `B₁`, `B₂` are the maximal ideals
  let k0 : Type u := IsLocalRing.ResidueField B
  let k1 : Type u := IsLocalRing.ResidueField B₁
  let k2 : Type u := IsLocalRing.ResidueField B₂
  let T : Type u := k1 ⊗[k0] k2
  haveI hTnontriv : Nontrivial T :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k0 k1 k2
      (RingHom.injective (algebraMap k0 k1)) (RingHom.injective (algebraMap k0 k2))
  let ψ₁ : B₁ →ₐ[B] T :=
    ((Algebra.TensorProduct.includeLeft (R := k0) (S := k0) (A := k1) (B := k2)).restrictScalars B).comp
      (IsScalarTower.toAlgHom B B₁ k1)
  let ψ₂ : B₂ →ₐ[B] T :=
    ((Algebra.TensorProduct.includeRight (R := k0) (A := k1) (B := k2)).restrictScalars B).comp
      (IsScalarTower.toAlgHom B B₂ k2)
  have hψ₁ : ∀ a : B₁, ψ₁ a = (IsLocalRing.residue B₁ a) ⊗ₜ[k0] (1 : k2) := by
    intro a
    show (algebraMap B₁ k1) a ⊗ₜ[k0] (1 : k2) = _
    rw [show (algebraMap B₁ k1 : B₁ →+* k1) = IsLocalRing.residue B₁ from
      IsLocalRing.ResidueField.algebraMap_eq B₁]
  have hψ₂ : ∀ a : B₂, ψ₂ a = (1 : k1) ⊗ₜ[k0] (IsLocalRing.residue B₂ a) := by
    intro a
    show (1 : k1) ⊗ₜ[k0] (algebraMap B₂ k2) a = _
    rw [show (algebraMap B₂ k2 : B₂ →+* k2) = IsLocalRing.residue B₂ from
      IsLocalRing.ResidueField.algebraMap_eq B₂]
  let φ : B₁ ⊗[B] B₂ →ₐ[B] T := Algebra.TensorProduct.lift ψ₁ ψ₂ (fun x y => Commute.all _ _)
  have hφ₁ : ∀ a : B₁, φ (a ⊗ₜ[B] (1 : B₂)) = ψ₁ a := by
    intro a; simp [φ, Algebra.TensorProduct.lift_tmul]
  have hφ₂ : ∀ a : B₂, φ ((1 : B₁) ⊗ₜ[B] a) = ψ₂ a := by
    intro a; simp [φ, Algebra.TensorProduct.lift_tmul]
  obtain ⟨𝔪, h𝔪max⟩ := Ideal.exists_maximal T
  haveI h𝔪prime : 𝔪.IsPrime := h𝔪max.isPrime
  haveI hpprime : (Ideal.comap φ.toRingHom 𝔪).IsPrime := Ideal.comap_isPrime _ _
  have hle₁ : IsLocalRing.maximalIdeal B₁ ≤ Ideal.comap i₁ (Ideal.comap φ.toRingHom 𝔪) := by
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have h0 : IsLocalRing.residue B₁ a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
    have h1 : i₁ a = a ⊗ₜ[B] (1 : B₂) := Algebra.TensorProduct.includeLeftRingHom_apply a
    rw [h1, show φ.toRingHom (a ⊗ₜ[B] (1 : B₂)) = ψ₁ a from hφ₁ a, hψ₁, h0,
      TensorProduct.zero_tmul]
    exact 𝔪.zero_mem
  have hpne₁ : Ideal.comap i₁ (Ideal.comap φ.toRingHom 𝔪) ≠ ⊤ := by
    intro h
    have h2 : (1 : B₁) ∈ Ideal.comap i₁ (Ideal.comap φ.toRingHom 𝔪) :=
      h ▸ Submodule.mem_top
    have h1 : (1 : B₁ ⊗[B] B₂) ∈ Ideal.comap φ.toRingHom 𝔪 := by simpa using h2
    exact hpprime.ne_top (Ideal.eq_top_iff_one _ |>.mpr h1)
  have hp₁ : Ideal.comap i₁ (Ideal.comap φ.toRingHom 𝔪) = IsLocalRing.maximalIdeal B₁ :=
    ((IsLocalRing.maximalIdeal.isMaximal B₁).eq_of_le hpne₁ hle₁).symm
  have hle₂ : IsLocalRing.maximalIdeal B₂ ≤ Ideal.comap i₂ (Ideal.comap φ.toRingHom 𝔪) := by
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have h0 : IsLocalRing.residue B₂ a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
    have h1 : i₂ a = (1 : B₁) ⊗ₜ[B] a := Algebra.TensorProduct.includeRight_apply a
    rw [h1, show φ.toRingHom ((1 : B₁) ⊗ₜ[B] a) = ψ₂ a from hφ₂ a, hψ₂, h0,
      TensorProduct.tmul_zero]
    exact 𝔪.zero_mem
  have hpne₂ : Ideal.comap i₂ (Ideal.comap φ.toRingHom 𝔪) ≠ ⊤ := by
    intro h
    have h2 : (1 : B₂) ∈ Ideal.comap i₂ (Ideal.comap φ.toRingHom 𝔪) :=
      h ▸ Submodule.mem_top
    have h1 : (1 : B₁ ⊗[B] B₂) ∈ Ideal.comap φ.toRingHom 𝔪 := by simpa using h2
    exact hpprime.ne_top (Ideal.eq_top_iff_one _ |>.mpr h1)
  have hp₂ : Ideal.comap i₂ (Ideal.comap φ.toRingHom 𝔪) = IsLocalRing.maximalIdeal B₂ :=
    ((IsLocalRing.maximalIdeal.isMaximal B₂).eq_of_le hpne₂ hle₂).symm
  -- ## Step 5: Chevalley's Lemma 2.2.1(2) and the amalgam
  obtain ⟨q, hqmin, hqle⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (B₁ ⊗[B] B₂)))
      (J := Ideal.comap φ.toRingHom 𝔪) bot_le
  have hq₁ : Ideal.comap i₁ q = ⊥ := h226₁ q hqmin
  have hq₂ : Ideal.comap i₂ q = ⊥ := h226₂ q hqmin
  haveI hqprime : q.IsPrime := hqmin.isPrime
  obtain ⟨K, hK, O, m, hm0, hmm⟩ := chevalley_hom' q (Ideal.comap φ.toRingHom 𝔪) hqle
  letI : Field K := hK
  have hker₁ : Function.Injective (m.comp i₁) := by
    intro x y hxy
    have h2 : i₁ (x - y) ∈ q := by
      rw [← hm0]
      show m (i₁ (x - y)) = 0
      simp only [map_sub]
      rw [show m (i₁ x) = m (i₁ y) from hxy, sub_self]
    rw [← Ideal.mem_comap, hq₁, Ideal.mem_bot] at h2
    exact sub_eq_zero.mp h2
  have hker₂ : Function.Injective (m.comp i₂) := by
    intro x y hxy
    have h2 : i₂ (x - y) ∈ q := by
      rw [← hm0]
      show m (i₂ (x - y)) = 0
      simp only [map_sub]
      rw [show m (i₂ x) = m (i₂ y) from hxy, sub_self]
    rw [← Ideal.mem_comap, hq₂, Ideal.mem_bot] at h2
    exact sub_eq_zero.mp h2
  have hmax₁ : Ideal.comap (m.comp i₁) (IsLocalRing.maximalIdeal O) = IsLocalRing.maximalIdeal B₁ := by
    ext x
    rw [Ideal.mem_comap]
    have h1 : (m.comp i₁) x ∈ IsLocalRing.maximalIdeal O ↔ O.valuation ((m.comp i₁) x) < 1 :=
      ValuationSubring.valuation_lt_one_iff O _
    have h2 : O.valuation ((m.comp i₁) x) < 1 ↔ i₁ x ∈ Ideal.comap φ.toRingHom 𝔪 := hmm (i₁ x)
    have h3 : i₁ x ∈ Ideal.comap φ.toRingHom 𝔪 ↔ x ∈ Ideal.comap i₁ (Ideal.comap φ.toRingHom 𝔪) :=
      Ideal.mem_comap
    have h4 : x ∈ Ideal.comap i₁ (Ideal.comap φ.toRingHom 𝔪) ↔ x ∈ IsLocalRing.maximalIdeal B₁ := by
      rw [hp₁]
    exact h1.trans (h2.trans (h3.trans h4))
  have hmax₂ : Ideal.comap (m.comp i₂) (IsLocalRing.maximalIdeal O) = IsLocalRing.maximalIdeal B₂ := by
    ext x
    rw [Ideal.mem_comap]
    have h1 : (m.comp i₂) x ∈ IsLocalRing.maximalIdeal O ↔ O.valuation ((m.comp i₂) x) < 1 :=
      ValuationSubring.valuation_lt_one_iff O _
    have h2 : O.valuation ((m.comp i₂) x) < 1 ↔ i₂ x ∈ Ideal.comap φ.toRingHom 𝔪 := hmm (i₂ x)
    have h3 : i₂ x ∈ Ideal.comap φ.toRingHom 𝔪 ↔ x ∈ Ideal.comap i₂ (Ideal.comap φ.toRingHom 𝔪) :=
      Ideal.mem_comap
    have h4 : x ∈ Ideal.comap i₂ (Ideal.comap φ.toRingHom 𝔪) ↔ x ∈ IsLocalRing.maximalIdeal B₂ := by
      rw [hp₂]
    exact h1.trans (h2.trans (h3.trans h4))
  refine ⟨K, hK, O, m.comp i₁, m.comp i₂, ⟨hker₁, hmax₁⟩, ⟨hker₂, hmax₂⟩, ?_⟩
  ext b
  have h2S : (algebraMap B (B₁ ⊗[B] B₂)) b = b • ((1:B₁) ⊗ₜ[B] (1:B₂)) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]
  have e1 : i₁ (f₁ b) = (algebraMap B (B₁ ⊗[B] B₂)) b := by
    have h1 : i₁ (f₁ b) = (b • (1:B₁)) ⊗ₜ[B] (1:B₂) := by
      rw [hi₁, Algebra.TensorProduct.includeLeftRingHom_apply, ← RingHom.algebraMap_toAlgebra f₁,
        Algebra.algebraMap_eq_smul_one (R := B) (A := B₁)]
    rw [h1, h2S, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  have e2 : i₂ (f₂ b) = (algebraMap B (B₁ ⊗[B] B₂)) b := by
    have h1 : i₂ (f₂ b) = (1:B₁) ⊗ₜ[B] (b • (1:B₂)) := by
      rw [hi₂, ← RingHom.algebraMap_toAlgebra f₂, Algebra.algebraMap_eq_smul_one (R := B) (A := B₂)]
      show (Algebra.TensorProduct.includeRight (R := B) (A := B₁) (B := B₂) (b • (1:B₂)))
        = (1:B₁) ⊗ₜ[B] (b • (1:B₂))
      rw [Algebra.TensorProduct.includeRight_apply]
    rw [h1, h2S, TensorProduct.tmul_smul]
  simp only [RingHom.comp_apply, e1, e2]

end Star

end Johnson22

#print axioms Johnson22.chevalley_subring
#print axioms Johnson22.chevalley_hom
#print axioms Johnson22.chevalley_hom'
#print axioms Johnson22.valuedEmbedding_of_localHom
#print axioms Johnson22.flat_of_torsion_eq_bot
#print axioms Johnson22.torsion_eq_bot_of_injective
#print axioms Johnson22.star
#check Johnson22.amalgamation_of_ring_amalgamation Johnson22.star
#check Johnson22.star

section EndToEnd
universe u

/-- End-to-end check: `star` has the exact shape that `amalgamation_of_ring_amalgamation` consumes,
and the amalgamation property for valued fields follows from it at universe `Type u`. -/
example {F F₁ F₂ : Type u} [Field F] [Field F₁] [Field F₂]
    (O : ValuationSubring F) (O₁ : ValuationSubring F₁) (O₂ : ValuationSubring F₂)
    (i₁ : F →+* F₁) (i₂ : F →+* F₂)
    (h₁ : Johnson22.IsValEmbedding O.valuation O₁.valuation i₁)
    (h₂ : Johnson22.IsValEmbedding O.valuation O₂.valuation i₂) :
    ∃ (N : Type u) (_ : Field N) (O₃ : ValuationSubring N) (j₁ : F₁ →+* N) (j₂ : F₂ →+* N),
      Johnson22.IsValEmbedding O₁.valuation O₃.valuation j₁ ∧
      Johnson22.IsValEmbedding O₂.valuation O₃.valuation j₂ ∧ j₁.comp i₁ = j₂.comp i₂ :=
  Johnson22.amalgamation_of_ring_amalgamation Johnson22.star O O₁ O₂ i₁ i₂ h₁ h₂

end EndToEnd

#print axioms Johnson22.isValEmbedding_of_mem_iff
#print axioms Johnson22.amalgamation_of_ring_amalgamation
#print axioms Johnson22.valExtension_of_fieldExtension

/-! ## 18. `HasAmalgamation valField` -/

namespace ValOneEC

section ValSubring

/-- The order of a valuation is the order of its valuation subring's canonical valuation.  This is
what lets Johnson's §2.2 amalgamation theorem, which is stated for `ValuationSubring`s, be applied
to the valuations `exists_valuation_of_isValPred` produces. -/
theorem le_iff_valuationSubring_valuation_le {K : Type} [Field K] {Γ : Type}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (x y : K) :
    v x ≤ v y ↔ v.valuationSubring.valuation x ≤ v.valuationSubring.valuation y := by
  rw [ValuationSubring.valuation_le_iff]
  constructor
  · intro h
    by_cases hy : y = 0
    · subst hy
      rw [map_zero] at h
      have hx : x = 0 := v.zero_iff.mp (le_antisymm h zero_le)
      subst hx
      exact ⟨0, by simp⟩
    · refine ⟨⟨x * y⁻¹, ?_⟩, by field_simp⟩
      rw [Valuation.mem_valuationSubring_iff, map_mul, map_inv₀]
      calc v x * (v y)⁻¹ ≤ v y * (v y)⁻¹ := by
            exact mul_le_mul_left h _
        _ = 1 := by rw [mul_inv_cancel₀ (v.ne_zero_iff.mpr hy)]
  · rintro ⟨a, ha⟩
    have hx : v x = v (a : K) * v y := by
      rw [← ha, map_mul]
    rw [hx]
    calc v (a : K) * v y ≤ 1 * v y := by
          exact mul_le_mul_left a.2 _
      _ = v y := one_mul _

/-- An `L_val`-embedding between `valStructure`s is a Johnson valued embedding of `ValuationSubring`s. -/
theorem isValEmbedding_of_valEmb {K : Type} [Field K] {K' : Type} [Field K'] {Γ : Type}
    [LinearOrderedCommGroupWithZero Γ] {Γ' : Type} [LinearOrderedCommGroupWithZero Γ']
    {v : Valuation K Γ} {w : Valuation K' Γ'}
    (F : @Embedding Language.val K K' (FirstOrder.valStructure v) (FirstOrder.valStructure w)) :
    Johnson22.IsValEmbedding v w (ringHomOfEmbedding v w F) := by
  letI := FirstOrder.valStructure v
  letI := FirstOrder.valStructure w
  refine ⟨fun x y h => F.inj' h, fun x y => ?_⟩
  have h := F.map_rel' ValRel.le ![x, y]
  have h' : (F.toFun ∘ ![x, y]) = ![F.toFun x, F.toFun y] := by
    funext i
    fin_cases i <;> rfl
  rw [h'] at h
  exact h.symm

end ValSubring

end ValOneEC

/-! ## 19. `HasAmalgamation valField` -/

namespace ValOneEC

section Amalgamation

open FirstOrder FirstOrder.Language FirstOrder.Ring

/-- Copy of `JohnsonCriterion.HasAmalgamation` (`QE/ACF_HasQE.lean`) specialised to `L_val`. -/
def HasAmalgamation (T : Language.val.Theory) : Prop :=
  ∀ (A B C : T.ModelType.{0, 0, 0}) (i : A ↪[Language.val] B) (j : A ↪[Language.val] C),
    ∃ (D : T.ModelType.{0, 0, 0}) (i' : B ↪[Language.val] D) (j' : C ↪[Language.val] D),
      i'.comp i = j'.comp j

/-- A Johnson valued embedding of valuations is one of their valuation subrings. -/
theorem isValEmbedding_subring {K : Type} [Field K] {K' : Type} [Field K'] {Γ : Type}
    [LinearOrderedCommGroupWithZero Γ] {Γ' : Type} [LinearOrderedCommGroupWithZero Γ']
    {v : Valuation K Γ} {w : Valuation K' Γ'} {f : K →+* K'}
    (h : Johnson22.IsValEmbedding v w f) :
    Johnson22.IsValEmbedding v.valuationSubring.valuation w.valuationSubring.valuation f := by
  refine ⟨h.1, fun x y => ?_⟩
  rw [← le_iff_valuationSubring_valuation_le v x y,
    ← le_iff_valuationSubring_valuation_le w (f x) (f y)]
  exact h.2 x y

/-- A model of `valField`, together with a valuation realising its predicate, has its own structure
equal to the `valStructure` of the valuation subring's canonical valuation. -/
theorem valStruct_eq_of_valuationSubring (M : ValPM.valField.ModelType.{0, 0, 0}) [Field M]
    [CompatibleRing M] [valRingHom.IsExpansionOn M] {Γ : Type}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation M Γ)
    (hv : ∀ x y, (ValPM.predM : M → M → Prop) x y ↔ v x ≤ v y) :
    M.struc = FirstOrder.valStructure v.valuationSubring.valuation :=
  (ValPM.valStruct_ext M).trans
    (ValPM.valStructOf_eq_valStructure (p := (ValPM.predM : M → M → Prop))
      (v := v.valuationSubring.valuation) (fun x y =>
        (hv x y).trans (le_iff_valuationSubring_valuation_le v x y)))

/-- **The amalgamation property for `valField`**, from Johnson's §2.2 theorem for valuation
rings.  Each model of `valField` is a Mathlib valued field, its own `L_val`-structure is the
`valStructure` of the valuation subring's canonical valuation, and
`amalgamation_of_ring_amalgamation` then produces the amalgam, which is packaged as a model of
`valField` again through `valStructure_model`. -/
theorem hasAmalgamation_valField : HasAmalgamation ValPM.valField := by
  intro A B C i j
  -- field structures on `A`
  letI : Language.ring.Structure A := ValPM.ringStructOfVal A
  haveI hexpA : valRingHom.IsExpansionOn A := ValPM.ringStructOfVal.expansion A
  have hfieldA : A ⊨ Theory.field := ValPM.model_field_of_valField A A.is_model
  letI : Field A := FirstOrder.Field.fieldOfModelField A
  letI : CompatibleRing A := FirstOrder.Field.compatibleRingOfModelField A
  have hpredA : ValPM.IsValPred (ValPM.predM : A → A → Prop) := ValPM.isValPred_of_model A.is_model
  letI : Language.ring.Structure B := ValPM.ringStructOfVal B
  haveI hexpB : valRingHom.IsExpansionOn B := ValPM.ringStructOfVal.expansion B
  have hfieldB : B ⊨ Theory.field := ValPM.model_field_of_valField B B.is_model
  letI : Field B := FirstOrder.Field.fieldOfModelField B
  letI : CompatibleRing B := FirstOrder.Field.compatibleRingOfModelField B
  have hpredB : ValPM.IsValPred (ValPM.predM : B → B → Prop) := ValPM.isValPred_of_model B.is_model
  letI : Language.ring.Structure C := ValPM.ringStructOfVal C
  haveI hexpC : valRingHom.IsExpansionOn C := ValPM.ringStructOfVal.expansion C
  have hfieldC : C ⊨ Theory.field := ValPM.model_field_of_valField C C.is_model
  letI : Field C := FirstOrder.Field.fieldOfModelField C
  letI : CompatibleRing C := FirstOrder.Field.compatibleRingOfModelField C
  have hpredC : ValPM.IsValPred (ValPM.predM : C → C → Prop) := ValPM.isValPred_of_model C.is_model
  -- valuations
  obtain ⟨ΓA, hΓA, vA, hvA⟩ := ValPM.exists_valuation_of_isValPred hpredA
  letI := hΓA
  obtain ⟨ΓB, hΓB, vB, hvB⟩ := ValPM.exists_valuation_of_isValPred hpredB
  letI := hΓB
  obtain ⟨ΓC, hΓC, vC, hvC⟩ := ValPM.exists_valuation_of_isValPred hpredC
  letI := hΓC
  -- the structures realised by the valuation subrings
  have hAs : A.struc = FirstOrder.valStructure vA.valuationSubring.valuation :=
    valStruct_eq_of_valuationSubring A vA hvA
  have hBs : B.struc = FirstOrder.valStructure vB.valuationSubring.valuation :=
    valStruct_eq_of_valuationSubring B vB hvB
  have hCs : C.struc = FirstOrder.valStructure vC.valuationSubring.valuation :=
    valStruct_eq_of_valuationSubring C vC hvC
  -- the two embeddings, transported
  let FAB : @Embedding Language.val A B (FirstOrder.valStructure vA) (FirstOrder.valStructure vB) :=
    embeddingCast ((ValPM.valStruct_ext A).trans
      (ValPM.valStructOf_eq_valStructure (p := (ValPM.predM : A → A → Prop)) (v := vA) hvA))
      ((ValPM.valStruct_ext B).trans
      (ValPM.valStructOf_eq_valStructure (p := (ValPM.predM : B → B → Prop)) (v := vB) hvB)) i
  let FAC : @Embedding Language.val A C (FirstOrder.valStructure vA) (FirstOrder.valStructure vC) :=
    embeddingCast ((ValPM.valStruct_ext A).trans
      (ValPM.valStructOf_eq_valStructure (p := (ValPM.predM : A → A → Prop)) (v := vA) hvA))
      ((ValPM.valStruct_ext C).trans
      (ValPM.valStructOf_eq_valStructure (p := (ValPM.predM : C → C → Prop)) (v := vC) hvC)) j
  -- the amalgam
  obtain ⟨N, hN, O₃, j₁, j₂, hj₁, hj₂, hcomm⟩ :=
    Johnson22.amalgamation_of_ring_amalgamation Johnson22.star
      vA.valuationSubring vB.valuationSubring vC.valuationSubring
      (ringHomOfEmbedding vA vB FAB) (ringHomOfEmbedding vA vC FAC)
      (isValEmbedding_subring (isValEmbedding_of_valEmb FAB))
      (isValEmbedding_subring (isValEmbedding_of_valEmb FAC))
  letI : Field N := hN
  letI : Language.val.Structure N := FirstOrder.valStructure O₃.valuation
  haveI : N ⊨ ValPM.valField := ValPM.valStructure_model O₃.valuation
  -- the amalgam as a model of `valField`, with its structure and the two embeddings
  let D : ValPM.valField.ModelType.{0, 0, 0} := Theory.ModelType.of (T := ValPM.valField) N
  have hDs : (D.struc : Language.val.Structure N) = FirstOrder.valStructure O₃.valuation := rfl
  let innerB : @Embedding Language.val B N (FirstOrder.valStructure vB.valuationSubring.valuation)
      (FirstOrder.valStructure O₃.valuation) :=
    embeddingOfIsValEmb vB.valuationSubring.valuation O₃.valuation j₁ hj₁.1 hj₁.2
  let innerC : @Embedding Language.val C N (FirstOrder.valStructure vC.valuationSubring.valuation)
      (FirstOrder.valStructure O₃.valuation) :=
    embeddingOfIsValEmb vC.valuationSubring.valuation O₃.valuation j₂ hj₂.1 hj₂.2
  refine ⟨D, ?_, ?_, ?_⟩
  · exact embeddingCast hBs.symm hDs.symm innerB
  · exact embeddingCast hCs.symm hDs.symm innerC
  · -- the square commutes, because all the casts preserve the underlying function
    refine FirstOrder.Language.Embedding.ext ?_
    intro a
    have h := RingHom.congr_fun hcomm a
    exact h

end Amalgamation

end ValOneEC

#print axioms ValOneEC.hasAmalgamation_valField
#print axioms ValOneEC.isValEmbedding_subring
#print axioms ValOneEC.valStruct_eq_of_valuationSubring
#check @ValOneEC.hasAmalgamation_valField
#check @ValOneEC.oneECIn_of_modelType
#check @ValPM.hasPrimeModels_ACVF_val

