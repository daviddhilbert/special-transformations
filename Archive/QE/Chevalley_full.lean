import Mathlib

/-!
# Chevalley's lemma and the extension of a valuation along a field extension

This file formalizes §2.2 of Will Johnson's thesis, Chapter 2 ("A direct proof of quantifier
elimination and C-minimality in ACVF").

* `Chevalley.exists_valuationSubring_comap_eq` — the local case of **Chevalley's lemma**
  (Lemma 2.2.1 (1)), which is the only case needed for the extension corollary: a valuation
  subring `O` of `K` sits inside a valuation subring `V` of an extension field `L` with
  `V ⊓ K = O`.
* `Chevalley.chevalley` — the general **Chevalley's lemma**, Lemma 2.2.1 (1): for a subring
  `R ⊆ L` and a prime ideal `p` of `R` there is a valuation subring `V` of `L` with
  `R ≤ V` and `R ⊓ m_V = p` (equivalently `R \ p = Vˣ ⊓ R`).
* `Chevalley.exists_hasExtension` — **Corollary 2.2.3**: any valuation on a field `K` extends
  to a valuation on any extension field `L` (as a `Valuation.HasExtension` instance, i.e. the
  pulled back valuation is *equivalent* to the given one, which is the right notion of
  "extends" when the value group is allowed to grow).
* `Chevalley.exists_hasExtension_domination` — Corollary 2.2.3 in the form §2.2 consumes: the
  extension is an embedding of valued fields (`v x ≤ v y` is preserved and reflected) and a
  local map of valuation rings (`v x < 1 ↔ V.valuation x < 1`).
* `Chevalley.exists_isEquiv_comap` — the same as `IsEquiv`, without existential universes.
* `Chevalley.exists_valuationSubring_algClosure`, `Chevalley.exists_algClosed_nontrivial` —
  every (non-trivially) valued field is a valued subfield of a model of `ACVF`.

All of it is derived from Mathlib's form of the heart of Chevalley's lemma,
`LocalSubring.exists_le_valuationSubring` ("every local subring of a field lies in a valuation
subring", `Mathlib/RingTheory/Valuation/LocalSubring.lean`), through its packaging
`IsLocalRing.exists_factor_valuationRing`.
-/

open IsLocalRing Valuation

namespace Chevalley

section LocalCase

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Chevalley's lemma, local case.** Let `O` be a valuation subring of a field `K` and let
`L/K` be a field extension. Then `O` is contained in a valuation subring `V` of `L` whose
intersection with `K` is exactly `O`.

In the notation of Lemma 2.2.1 (1) applied to the pair `(O, m_O)` inside the field `L`, this is
`O ⊆ V` together with `O \ m_O = Vˣ ∩ O` and `m_O = m_V ∩ O`, both of which are exactly the
statement `∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O`. -/
theorem exists_valuationSubring_comap_eq {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) :
    ∃ V : ValuationSubring L, V.comap (algebraMap K L) = v.valuationSubring := by
  classical
  -- `O` is local, so by Mathlib's form of Chevalley it sits in a valuation subring `V` of `L`
  -- in such a way that nonunits of `O` become nonunits of `V` ("domination").
  set O : ValuationSubring K := v.valuationSubring with hO
  set f : O →+* L := (algebraMap K L).comp (Subring.subtype O.toSubring) with hf
  obtain ⟨V, hF, hloc⟩ := IsLocalRing.exists_factor_valuationRing (K := L) f
  set g : O →+* V := f.codRestrict V.toSubring hF with hg
  have mem_iff : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O := by
    intro x
    refine ⟨?_, fun hx => hF ⟨x, hx⟩⟩
    intro hx
    by_cases hxO : x ∈ O
    · exact hxO
    · -- `x ∉ O`, so `x⁻¹ ∈ O` and `x⁻¹` is a nonunit of `O`, hence a nonunit of `V`;
      -- but `algebraMap x ∈ V` makes its inverse a unit of `V`.  Contradiction.
      exfalso
      have h : x⁻¹ ∈ O := (ValuationSubring.mem_or_inv_mem _ x).resolve_left hxO
      have hx0 : x ≠ 0 := fun e => hxO (e ▸ zero_mem _)
      -- `⟨x⁻¹, h⟩` is a nonunit of `O`
      have hnu : ¬ IsUnit (⟨x⁻¹, h⟩ : O) := by
        rw [isUnit_iff_exists_inv]
        rintro ⟨z, hz⟩
        have h1 : x⁻¹ * (z : K) = 1 := by simpa using congrArg (Subtype.val) hz
        have h2 : (z : K) = x := by
          have h3 := congrArg (fun t : K => x * t) h1
          simpa [← mul_assoc, mul_inv_cancel₀ hx0] using h3
        exact hxO (h2 ▸ z.2)
      -- but its image under the local map into `V` is a unit of `V`
      have hunit : IsUnit (g ⟨x⁻¹, h⟩) := by
        rw [isUnit_iff_exists_inv]
        refine ⟨⟨algebraMap K L x, hx⟩, ?_⟩
        refine Subtype.ext ?_
        show ((g ⟨x⁻¹, h⟩ : V) : L) * algebraMap K L x = 1
        rw [show ((g ⟨x⁻¹, h⟩ : V) : L) = algebraMap K L x⁻¹ from rfl]
        rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
      exact hnu (hloc.map_nonunit ⟨x⁻¹, h⟩ hunit)
  refine ⟨V, ?_⟩
  ext x
  exact mem_iff x

/-! ### Corollary 2.2.3: a valuation extends along a field extension -/

/-- **Corollary 2.2.3 of the chapter.**  A valuation `v` on `K` extends to a valuation on any
extension field `L`: there is a valuation subring `V` of `L` whose valuation pulls back to a
valuation of `K` equivalent to `v`.  (Equivalence is the correct notion of "extends" when the
value group is allowed to grow, and is exactly `Valuation.HasExtension`.)

Note that the extension `L/K` is arbitrary — no finiteness, separability or completeness
hypothesis is used. -/
theorem exists_hasExtension {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) : ∃ V : ValuationSubring L, v.HasExtension V.valuation := by
  obtain ⟨V, hV⟩ := exists_valuationSubring_comap_eq (L := L) v
  have key : ∀ x : K, x ∈ v.valuationSubring ↔ V.valuation (algebraMap K L x) ≤ 1 := by
    intro x
    rw [ValuationSubring.valuation_le_one_iff, ← hV, ValuationSubring.mem_comap]
  refine ⟨V, ⟨?_⟩⟩
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  exact (Valuation.mem_integer_iff v x).symm.trans (key x)

/-- **Corollary 2.2.3 of the chapter**, universe-free form: every valuation on `K` is
equivalent to the restriction of the valuation of some valuation subring of the extension
field `L`. -/
theorem exists_isEquiv_comap {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) :
    ∃ V : ValuationSubring L, v.IsEquiv (V.valuation.comap (algebraMap K L)) :=
  ⟨(exists_hasExtension (L := L) v).choose,
    (exists_hasExtension (L := L) v).choose_spec.val_isEquiv_comap⟩

/-- **Corollary 2.2.3, embedding/domination form.**  The extension `K → L` is an embedding of
valued fields: the order relation `v x ≤ v y` and the property of being a non-unit are both
reflected exactly.  This is the form in which §2.2 uses the corollary (cf. Remark 2.2.2: the
inclusion `O_v → V` is a *local* homomorphism of valuation rings). -/
theorem exists_hasExtension_domination {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) :
    ∃ V : ValuationSubring L, v.HasExtension V.valuation ∧
      (∀ x y : K, V.valuation (algebraMap K L x) ≤ V.valuation (algebraMap K L y) ↔ v x ≤ v y) ∧
      (∀ x : K, V.valuation (algebraMap K L x) < 1 ↔ v x < 1) := by
  obtain ⟨V, hV⟩ := exists_hasExtension (L := L) v
  refine ⟨V, hV, fun x y => ?_, fun x => ?_⟩
  · exact Valuation.HasExtension.val_map_le_iff v V.valuation x y
  · exact Valuation.HasExtension.val_map_lt_one_iff v V.valuation x

end LocalCase

/-! ### Chevalley's lemma -/

section Chevalley

variable {L : Type*} [Field L]

/-- **Chevalley's lemma (Lemma 2.2.1 (1) of the chapter).**  Let `R` be a subring of a field `L`
and `p` a prime ideal of `R`.  Then there is a valuation subring `V` of `L` such that
`R ⊆ V`, `R \ p = Vˣ ∩ R` and `p = m_V ∩ R`; both of the latter are exactly the single
statement `∀ r : R, (r : L) ∈ V.nonunits ↔ r ∈ p`. -/
theorem chevalley (R : Subring L) (p : Ideal R) [p.IsPrime] :
    ∃ V : ValuationSubring L, R ≤ V.toSubring ∧ ∀ r : R, (r : L) ∈ V.nonunits ↔ r ∈ p := by
  classical
  -- `R ↪ L` inverts `R \ p`, so it factors through the localization of `R` at `p`
  have hunit : ∀ y : ↥p.primeCompl, IsUnit ((Subring.subtype R : R →+* L) (y : R)) := by
    rintro ⟨y, hy⟩
    have hy' : (y : R) ∉ p := by simpa using hy
    rw [isUnit_iff_ne_zero]
    intro h
    refine hy' ?_
    have hy0 : (y : R) = 0 := Subtype.ext (by simpa using h)
    rw [hy0]
    exact p.zero_mem
  let ψ : Localization.AtPrime p →+* L := IsLocalization.lift (M := p.primeCompl) hunit
  have hψ : ∀ r : R, ψ (algebraMap R (Localization.AtPrime p) r) = (r : L) :=
    fun r => IsLocalization.lift_eq hunit r
  obtain ⟨V, hF, hloc⟩ := IsLocalRing.exists_factor_valuationRing (K := L) ψ
  set Ψ : Localization.AtPrime p →+* V := ψ.codRestrict V.toSubring hF with hΨ
  have hRV : R ≤ V.toSubring := by
    intro r hr
    have h1 := hF (algebraMap R (Localization.AtPrime p) ⟨r, hr⟩)
    rwa [hψ] at h1
  have hnonunits : ∀ r : R, ((r : L) ∈ V.nonunits ↔ ¬ IsUnit (⟨(r : L), hRV r.2⟩ : V)) := by
    intro r
    rw [ValuationSubring.mem_nonunits_iff,
      ValuationSubring.valuation_eq_one_iff (A := V) ⟨(r : L), hRV r.2⟩]
    exact ⟨fun h h1 => (ne_of_lt h) h1,
      fun h => lt_of_le_of_ne (V.valuation_le_one ⟨(r : L), hRV r.2⟩) h⟩
  refine ⟨V, hRV, fun r => ?_⟩
  rw [hnonunits r]
  constructor
  · -- `(r : L)` a nonunit forces `r ∈ p`
    intro hnu
    by_contra hrp
    have hu : IsUnit (algebraMap R (Localization.AtPrime p) r) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p]
      exact hrp
    have := IsUnit.map Ψ hu
    exact hnu (by
      rwa [show Ψ (algebraMap R (Localization.AtPrime p) r) = ⟨(r : L), hRV r.2⟩ from
        Subtype.ext (hψ r)] at this)
  · -- `r ∈ p` makes `(r : L)` a nonunit
    intro hrp
    have hmax : algebraMap R (Localization.AtPrime p) r ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p r).mpr hrp
    have hnu : ¬ IsUnit (algebraMap R (Localization.AtPrime p) r) := fun h =>
      ((mem_nonunits_iff).mp ((IsLocalRing.mem_maximalIdeal _).mp hmax)) h
    have hnu' : ¬ IsUnit (Ψ (algebraMap R (Localization.AtPrime p) r)) :=
      fun hu => hnu (hloc.map_nonunit _ hu)
    rwa [show Ψ (algebraMap R (Localization.AtPrime p) r) = ⟨(r : L), hRV r.2⟩ from
      Subtype.ext (hψ r)] at hnu'

end Chevalley

/-! ### Every valued field is a valued subfield of a model of `ACVF` -/

section AlgClosed

variable {K : Type*} [Field K]

/-- Every valued field embeds in an algebraically closed valued field: Theorem 2.0.1 (2)'s
"every valued field embeds into a model of ACVF", obtained by applying Corollary 2.2.3 to the
algebraic closure.  This is the hypothesis "(every model of `T₀` embeds in a model of `T`)"
that the model-completion half of Lemma 2.1.4 needs. -/
theorem exists_valuationSubring_algClosure {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) :
    ∃ V : ValuationSubring (AlgebraicClosure K), v.HasExtension V.valuation :=
  exists_hasExtension (L := AlgebraicClosure K) v

/-- The same, with non-triviality: a *non-trivially* valued field embeds in a
non-trivially valued algebraically closed field, i.e. in a model of `ACVF`. -/
theorem exists_algClosed_nontrivial {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hv : v.IsNontrivial) :
    ∃ V : ValuationSubring (AlgebraicClosure K),
      v.HasExtension V.valuation ∧ V.valuation.IsNontrivial := by
  obtain ⟨V, hV⟩ := exists_hasExtension (L := AlgebraicClosure K) v
  refine ⟨V, hV, ?_⟩
  have h1 : (V.valuation.comap (algebraMap K (AlgebraicClosure K))).IsNontrivial :=
    isNontrivial_of_isEquiv hV.val_isEquiv_comap hv
  obtain ⟨x, hx0, hx1⟩ := h1.exists_val_nontrivial
  exact ⟨algebraMap K (AlgebraicClosure K) x, by simpa using hx0, by simpa using hx1⟩

end AlgClosed

end Chevalley

/-! ### Non-vacuity

These instances show that the theorems above are not vacuous: the `p`-adic valuation on `ℚ`
extends to a genuinely non-trivial valuation on a model of `ACVF`. -/

theorem padicValuation_isNontrivial (p : ℕ) [Fact p.Prime] :
    (Rat.padicValuation p).IsNontrivial := by
  rw [Valuation.isNontrivial_iff_exists_lt_one]
  refine ⟨(p : ℚ), ?_, ?_⟩
  · exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  · rw [Rat.padicValuation_self]
    show WithZero.exp (-1 : ℤ) < 1
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)

example (p : ℕ) [Fact p.Prime] :
    ∃ V : ValuationSubring ℂ, (Rat.padicValuation p).HasExtension V.valuation :=
  Chevalley.exists_hasExtension (L := ℂ) _

example (p : ℕ) [Fact p.Prime] :
    ∃ V : ValuationSubring (AlgebraicClosure ℚ),
      (Rat.padicValuation p).HasExtension V.valuation ∧ V.valuation.IsNontrivial :=
  Chevalley.exists_algClosed_nontrivial (Rat.padicValuation p) (padicValuation_isNontrivial p)

/-! ### Axiom audit -/

#print axioms Chevalley.exists_valuationSubring_comap_eq
#print axioms Chevalley.exists_hasExtension
#print axioms Chevalley.exists_isEquiv_comap
#print axioms Chevalley.chevalley
#print axioms Chevalley.exists_valuationSubring_algClosure
#print axioms Chevalley.exists_hasExtension_domination
#print axioms Chevalley.exists_algClosed_nontrivial
