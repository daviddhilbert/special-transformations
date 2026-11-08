import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! An algebraic element is integral over the base valuation ring when its
entire Galois orbit lies in the ambient valuation ring. -/

noncomputable section
open Classical Polynomial
open scoped BigOperators

namespace SpecialTransformations.Section6

variable {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
variable (F : Subfield L) [IsGalois F L]

private theorem finite_orbit (x : L) : (Set.range (fun σ : L ≃ₐ[F] L => σ x)).Finite := by
  refine ((minpoly F x).rootSet_finite L).subset ?_
  rintro _ ⟨σ, rfl⟩
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  apply (Polynomial.mem_rootSet_of_ne (minpoly.ne_zero hx)).mpr
  rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]

def conjugates (x : L) : Finset L := (finite_orbit F x).toFinset

theorem mem_conjugates (x y : L) :
    y ∈ conjugates F x ↔ ∃ σ : L ≃ₐ[F] L, σ x = y := (finite_orbit F x).mem_toFinset

private theorem conjugates_map (x : L) (σ : L ≃ₐ[F] L) :
    (conjugates F x).map σ.toEquiv.toEmbedding = conjugates F x := by
  ext y
  simp only [Finset.mem_map, mem_conjugates]
  constructor
  · rintro ⟨_, ⟨τ, rfl⟩, rfl⟩
    exact ⟨τ.trans σ, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨σ.symm (τ x), ⟨τ.trans σ.symm, rfl⟩, σ.apply_symm_apply _⟩

theorem isIntegral_of_conjugates_le_one (w : Valuation L Γ) (x : L)
    (hx : ∀ σ : L ≃ₐ[F] L, w (σ x) ≤ 1) :
    IsIntegral (w.comap F.subtype).valuationSubring x := by
  let A := (w.comap F.subtype).valuationSubring
  let roots := conjugates F x
  let p : L[X] := ∏ z ∈ roots, (X - C z)
  have hpm : p.Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun z _ => monic_X_sub_C z)
  have hp (σ : L ≃ₐ[F] L) : p.map σ.toRingHom = p := by
    change Polynomial.mapRingHom σ.toRingHom (∏ z ∈ roots, (X - C z)) = _
    rw [map_prod]
    have hmap (q : L[X]) : Polynomial.mapRingHom σ.toRingHom q = q.map σ.toRingHom := rfl
    simp only [hmap, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    change (∏ z ∈ roots, (X - C (σ z))) = (∏ z ∈ roots, (X - C z))
    have hperm : roots.map σ.toEquiv.toEmbedding = roots := conjugates_map F x σ
    conv_rhs => rw [← hperm, Finset.prod_map]
    rfl
  let pO : w.valuationSubring[X] :=
    ∏ z ∈ roots.attach, (X - C (⟨z.val, by
      obtain ⟨σ, hσ⟩ := (mem_conjugates F x z.val).mp z.property
      exact hσ ▸ hx σ⟩ : w.valuationSubring))
  have hO : pO.map w.valuationSubring.subtype = p := by
    change Polynomial.mapRingHom w.valuationSubring.subtype (∏ z ∈ roots.attach, _) = _
    rw [map_prod]
    have hmap (q : w.valuationSubring[X]) :
        Polynomial.mapRingHom w.valuationSubring.subtype q = q.map w.valuationSubring.subtype := rfl
    simp only [hmap, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact Finset.prod_attach roots (fun z => X - C z)
  have hcoeff (i : ℕ) : ∃ a : A, algebraMap A L a = p.coeff i := by
    have hfixed (σ : L ≃ₐ[F] L) : σ (p.coeff i) = p.coeff i := by
      change σ.toRingHom (p.coeff i) = p.coeff i
      rw [← Polynomial.coeff_map, hp]
    obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (p.coeff i)).mpr hfixed
    refine ⟨⟨a, ?_⟩, ha⟩
    change w (a : L) ≤ 1
    rw [show (a : L) = p.coeff i from ha, ← hO, Polynomial.coeff_map]
    exact (pO.coeff i).property
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts p).mp ((Polynomial.lifts_iff_coeff_lifts p).mpr hcoeff)
  have hinj : Function.Injective (algebraMap A L) :=
    (algebraMap F L).injective.comp A.subtype_injective
  have hqm : q.Monic := Polynomial.monic_of_injective hinj (hq.symm ▸ hpm)
  refine ⟨q, hqm, ?_⟩
  change q.eval₂ (algebraMap A L) x = 0
  rw [Polynomial.eval₂_eq_eval_map, hq]
  change Polynomial.evalRingHom x (∏ z ∈ roots, (X - C z)) = 0
  rw [map_prod]
  apply Finset.prod_eq_zero (show x ∈ roots from (mem_conjugates F x x).mpr ⟨AlgEquiv.refl, rfl⟩)
  simp

end SpecialTransformations.Section6
