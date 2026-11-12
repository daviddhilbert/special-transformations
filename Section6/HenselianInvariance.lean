module

public import Section6.HenselianFactorization
public import Section6.IntegralConjugates
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.LocalSubring

@[expose] public section

/-! In residue characteristic zero, choose a natural-number translate
whose inverse is integral at every conjugate. If the original valuation
ring is not preserved, the minimal polynomial of that inverse has mixed
residue roots, contradicting henselian factor lifting. -/

noncomputable section
open Classical Polynomial IsLocalRing

namespace SpecialTransformations.Section6

variable {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
variable (w : Valuation L Γ)

theorem nat_sub_value_one [CharZero (ResidueField w.valuationSubring)]
    (n m : ℕ) (h : n ≠ m) : w ((n : L) - (m : L)) = 1 := by
  let a : w.valuationSubring := (n : w.valuationSubring) - (m : w.valuationSubring)
  have ha : (a : L) = (n : L) - (m : L) := by
    change w.valuationSubring.subtype a = _
    simp [a]
  have hle := (Valuation.mem_valuationSubring_iff w _).mp a.property
  have hn : ¬ w (a : L) < 1 := by
    intro hsmall
    have hzero := (residue_eq_zero_iff a).mpr
      ((Valuation.mem_maximalIdeal_iff L w).mpr hsmall)
    simp only [a, map_sub, map_natCast, sub_eq_zero] at hzero
    exact h (Nat.cast_injective hzero)
  rw [← ha]
  exact le_antisymm hle (le_of_not_gt hn)

private theorem value_nat_le_one (n : ℕ) : w (n : L) ≤ 1 := by
  have h := (Valuation.mem_valuationSubring_iff w _).mp
    ((n : w.valuationSubring).property)
  change w (w.valuationSubring.subtype (n : w.valuationSubring)) ≤ 1 at h
  simpa only [map_natCast] using h

private theorem translate_value_ge_one {F : Subfield L} [IsGalois F L] (x : L)
    (hsep : ∀ n m : ℕ, n ≠ m → w ((n : L) - (m : L)) = 1) :
    ∃ n : ℕ, ∀ σ : L ≃ₐ[F] L, 1 ≤ w (σ x + (n : L)) := by
  let bad (z : L) : ℕ := if h : ∃ n : ℕ, w (z + (n : L)) < 1 then h.choose else 0
  let s := conjugates F x
  let n := s.sup bad + 1
  refine ⟨n, fun σ => le_of_not_gt fun h => ?_⟩
  let z := σ x
  have hz : z ∈ s := (mem_conjugates F x _).mpr ⟨σ, rfl⟩
  have he : ∃ m : ℕ, w (z + (m : L)) < 1 := ⟨n, h⟩
  have hbad : bad z = he.choose := dif_pos he
  have hn : n = he.choose := by
    by_contra hne
    have hdiff : w ((n : L) - (he.choose : L)) < 1 := by
      rw [show (n : L) - (he.choose : L) = (z + n) - (z + he.choose) by ring]
      exact (w.map_sub _ _).trans_lt (max_lt h he.choose_spec)
    rw [hsep _ _ hne] at hdiff
    exact (lt_irrefl _ hdiff)
  have hn' : n ≤ s.sup bad := by
    rw [hn, ← hbad]
    exact Finset.le_sup hz
  exact Nat.not_succ_le_self _ hn'

private theorem residue_root_of_root {F : Subfield L}
    (v : Valuation F Γ) [v.HasExtension w] (Q : v.valuationSubring[X])
    (z : w.valuationSubring)
    (hroot : ((Q.map v.valuationSubring.subtype).map (algebraMap F L)).IsRoot (z : L)) :
    ((Q.map (residue v.valuationSubring)).map
      (algebraMap (ResidueField v.valuationSubring) (ResidueField w.valuationSubring))).IsRoot
        (residue w.valuationSubring z) := by
  let A := v.valuationSubring
  let B := w.valuationSubring
  let ι := algebraMap A B
  have hz : Q.eval₂ ι z = 0 := by
    apply (show Function.Injective B.subtype from Subtype.val_injective)
    rw [map_zero, Polynomial.eval₂_eq_eval_map, ← Polynomial.eval₂_at_apply, Polynomial.eval₂_map]
    have he : B.subtype.comp ι = (algebraMap F L).comp A.subtype := by ext x; rfl
    rw [he]
    change Q.eval₂ ((algebraMap F L).comp v.valuationSubring.subtype) (z : L) = 0
    simpa only [Polynomial.IsRoot, Polynomial.map_map, Polynomial.eval₂_eq_eval_map] using hroot
  let ρ := algebraMap (ResidueField A) (ResidueField B)
  have he : ρ.comp (residue A) = (residue B).comp ι := by
    ext x
    exact Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap v w x
  change ((Q.map (residue A)).map ρ).eval (residue B z) = 0
  rw [Polynomial.eval_map, Polynomial.eval₂_map, he, ← Polynomial.eval₂_map,
    Polynomial.eval₂_at_apply, ← Polynomial.eval₂_eq_eval_map, hz, map_zero]

private theorem automorphism_le_one {F : Subfield L} [IsGalois F L]
    [HenselianLocalRing (w.comap F.subtype).valuationSubring]
    (hsep : ∀ n m : ℕ, n ≠ m → w ((n : L) - (m : L)) = 1)
    (σ : L ≃ₐ[F] L) (x : L) (hx : w x ≤ 1) : w (σ x) ≤ 1 := by
  by_contra hσ
  have hσx := lt_of_not_ge hσ
  obtain ⟨n, hn⟩ := translate_value_ge_one (F := F) w x hsep
  let y := (x + (n : L))⁻¹
  have hyval (τ : L ≃ₐ[F] L) : w (τ y) = (w (τ x + (n : L)))⁻¹ := by
    simp only [y, map_inv₀, map_add, map_natCast]
  have hy : w y = 1 := by
    have hfirst : 1 ≤ w (x + (n : L)) := hn (AlgEquiv.refl : L ≃ₐ[F] L)
    have he : w (x + (n : L)) = 1 :=
      le_antisymm ((w.map_add _ _).trans (max_le hx (value_nat_le_one w n))) hfirst
    change w ((x + (n : L))⁻¹) = 1
    rw [map_inv₀, he, inv_one]
  have hyσ : w (σ y) < 1 := by
    rw [hyval, Valuation.map_add_eq_of_lt_left w ((value_nat_le_one w n).trans_lt hσx)]
    exact (inv_lt_one₀ (zero_lt_one.trans hσx)).mpr hσx
  have hIntegral := isIntegral_of_conjugates_le_one F w y fun τ => by
    rw [hyval]
    exact (inv_le_one₀ (zero_lt_one.trans_le (hn τ))).mpr (hn τ)
  let v := w.comap F.subtype
  let A := v.valuationSubring
  let Q := minpoly A y
  have hQ : Q.Monic := minpoly.monic hIntegral
  have hQmap : Q.map A.subtype = minpoly F y :=
    (minpoly.isIntegrallyClosed_eq_field_fractions' F hIntegral).symm
  have hQirr : Irreducible (Q.map A.subtype) := by
    rw [hQmap]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral y)
  have hroot (τ : L ≃ₐ[F] L) :
      ((Q.map A.subtype).map (algebraMap F L)).IsRoot (τ y) := by
    rw [hQmap, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  letI : v.HasExtension w := ⟨fun _ _ => Iff.rfl⟩
  let y₀ : w.valuationSubring := ⟨y, (Valuation.mem_valuationSubring_iff w _).mpr hy.le⟩
  let yσ : w.valuationSubring := ⟨σ y, (Valuation.mem_valuationSubring_iff w _).mpr hyσ.le⟩
  have hzero : residue w.valuationSubring yσ = 0 :=
    (residue_eq_zero_iff yσ).mpr ((Valuation.mem_maximalIdeal_iff L w).mpr hyσ)
  have hne : residue w.valuationSubring y₀ ≠ 0 := fun he => by
    have hh := (Valuation.mem_maximalIdeal_iff L w).mp ((residue_eq_zero_iff y₀).mp he)
    exact (ne_of_lt hh) hy
  let ρ := algebraMap (ResidueField A) (ResidueField w.valuationSubring)
  have hz := residue_root_of_root w v Q yσ (hroot σ)
  change ((Q.map (residue A)).map ρ).IsRoot (residue w.valuationSubring yσ) at hz
  have hzmap : ((Q.map (residue A)).map ρ).eval (ρ 0) = 0 := by
    simpa only [Polynomial.IsRoot, hzero, map_zero] using hz
  rw [Polynomial.eval_map_apply] at hzmap
  have hz' : (Q.map (residue A)).IsRoot 0 := by
    change (Q.map (residue A)).eval 0 = 0
    apply ρ.injective
    simpa only [map_zero] using hzmap
  exact false_of_mixed_residue_roots hQ hQirr hz' ρ hne
    (residue_root_of_root w v Q y₀ (hroot AlgEquiv.refl))

theorem henselian_automorphism_invariance {F : Subfield L} [IsGalois F L]
    [HenselianLocalRing (w.comap F.subtype).valuationSubring]
    (hsep : ∀ n m : ℕ, n ≠ m → w ((n : L) - (m : L)) = 1)
    (σ : L ≃ₐ[F] L) (x y : L) :
    w (σ x) ≤ w (σ y) ↔ w x ≤ w y := by
  have h (z : L) : w (σ z) ≤ 1 ↔ w z ≤ 1 := by
    refine ⟨fun hz => ?_, automorphism_le_one w hsep σ z⟩
    simpa only [AlgEquiv.symm_apply_apply] using automorphism_le_one w hsep σ.symm (σ z) hz
  have he : (w.comap σ.toRingHom).IsEquiv w := Valuation.isEquiv_of_val_le_one h
  exact he x y

end SpecialTransformations.Section6
