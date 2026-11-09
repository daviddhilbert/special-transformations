import Section9.GaussDerivative
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! A tuple of integral elements with algebraically independent residues
gives Gauss evaluation over a valued subfield. No rank condition enters
the normalization or the reduction. -/

open MvPolynomial IsLocalRing

namespace SpecialTransformations.Section9

variable {K G ι : Type*} [Field K] [LinearOrderedCommGroupWithZero G]

private theorem residue_nonzero_iff (v : Valuation K G) (a : v.valuationSubring) :
    residue v.valuationSubring a ≠ 0 ↔ v (a : K) = 1 := by
  have ha : v (a : K) ≤ 1 := (Valuation.mem_valuationSubring_iff v _).mp a.property
  rw [ne_eq, residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff, not_lt]
  exact ⟨fun h => le_antisymm ha h, fun h => h.ge⟩

def valuationRingInclusion (v : Valuation K G) (E : Subfield K) :
    (v.comap E.subtype).valuationSubring →+* v.valuationSubring where
  toFun c := ⟨(c.val : K), c.property⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

instance valuationRingInclusion_isLocalHom (v : Valuation K G) (E : Subfield K) :
    IsLocalHom (valuationRingInclusion v E) where
  map_nonunit c hc := by
    apply (residue_ne_zero_iff_isUnit _).mp
    apply (residue_nonzero_iff (v.comap E.subtype) c).mpr
    exact (residue_nonzero_iff v _).mp
      ((residue_ne_zero_iff_isUnit _).mpr hc)

noncomputable def residueFieldInclusion (v : Valuation K G) (E : Subfield K) :
    ResidueField (v.comap E.subtype).valuationSubring →+* ResidueField v.valuationSubring :=
  ResidueField.map (valuationRingInclusion v E)

private theorem exists_integralPolynomial {F : Type*} [Field F]
    (w : Valuation F G) (P : MvPolynomial ι F) (hP : ∀ i ∈ P.support, w (P.coeff i) ≤ 1) :
    ∃ Q : MvPolynomial ι w.valuationSubring, Q.map w.valuationSubring.subtype = P := by
  classical
  let c (i : P.support) : w.valuationSubring :=
    ⟨P.coeff i, (Valuation.mem_valuationSubring_iff w _).mpr (hP i i.property)⟩
  refine ⟨∑ i : P.support, monomial i.val (c i), ?_⟩
  calc
    _ = ∑ i : P.support, monomial i.val (P.coeff i) := by
      simp only [map_sum, map_monomial]
      rfl
    _ = P := (Finset.sum_coe_sort P.support _).trans P.support_sum_monomial_coeff

/-- Algebraically independent residues give the coefficient bound on
evaluation. The independence can be expressed using the residue field
of the actual valued subfield. -/
theorem isGaussEvaluation_of_independent_residues
    (v : Valuation K G) (E : Subfield K) (x : ι → v.valuationSubring)
    (hi : Function.Injective (eval₂Hom (residueFieldInclusion v E)
      (fun i => residue v.valuationSubring (x i)))) :
    IsGaussEvaluation (E := E) v (fun i => (x i).val) := by
  classical
  let w := v.comap E.subtype
  intro P d hd
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image P.support
    (fun i => w (P.coeff i)) ⟨d, hd⟩
  let c := P.coeff s
  have hc : c ≠ 0 := mem_support_iff.mp hs
  have hv : w c ≠ 0 := w.ne_zero_iff.mpr hc
  let N := C c⁻¹ * P
  have hcoeff (i : ι →₀ ℕ) : w (N.coeff i) ≤ 1 := by
    dsimp only [N]
    rw [coeff_C_mul, map_mul, map_inv₀]
    by_cases hi : i ∈ P.support
    · exact (mul_le_mul_of_nonneg_left (hmax i hi) zero_le).trans_eq (inv_mul_cancel₀ hv)
    · rw [notMem_support_iff.mp hi, map_zero, mul_zero]
      exact zero_le_one
  obtain ⟨Q, hQ⟩ := exists_integralPolynomial w N (fun i _ => hcoeff i)
  let A := w.valuationSubring
  let B := v.valuationSubring
  let incl : A →+* B := valuationRingInclusion v E
  let q := Q.eval₂ incl x
  have hco : (Q.coeff s).val = 1 := by
    have he := congrArg (fun p : MvPolynomial ι E => p.coeff s) hQ
    change (Q.map A.subtype).coeff s = N.coeff s at he
    dsimp only [N] at he
    rw [coeff_map, coeff_C_mul, show P.coeff s = c from rfl, inv_mul_cancel₀ hc] at he
    exact he
  have hred : Q.map (residue A) ≠ 0 := by
    intro h
    have he := congrArg (fun p : MvPolynomial ι (ResidueField A) => p.coeff s) h
    rw [coeff_map] at he
    change residue A (Q.coeff s) = 0 at he
    exact ((residue_nonzero_iff w _).mpr (by rw [hco, map_one])) he
  have hq : residue B q ≠ 0 := by
    intro hz
    apply hred (hi ?_)
    change eval₂ (residueFieldInclusion v E) (fun i => residue B (x i))
      (Q.map (residue A)) = eval₂ (residueFieldInclusion v E)
        (fun i => residue B (x i)) (0 : MvPolynomial ι (ResidueField A))
    rw [eval₂_map, eval₂_zero]
    have he : (residueFieldInclusion v E).comp (residue A) = (residue B).comp incl :=
      ResidueField.map_comp_residue incl
    rw [he, ← hom_eval₂]
    exact hz
  have hval := (residue_nonzero_iff v q).mp hq
  have hqval : (q.val : K) = aeval (fun i => (x i).val) N := by
    rw [← hQ, aeval_def, eval₂_map]
    have he : (algebraMap E K).comp A.subtype = B.subtype.comp incl := rfl
    rw [he]
    change B.subtype (Q.eval₂ incl x) = Q.eval₂ (B.subtype.comp incl) (fun i => B.subtype (x i))
    exact hom_eval₂ Q incl B.subtype x
  have hN : v (aeval (fun i => (x i).val) N) = 1 := hqval ▸ hval
  dsimp only [N] at hN
  rw [map_mul, aeval_C, map_inv₀, map_mul, map_inv₀] at hN
  have hPval : v (aeval (fun i => (x i).val) P) = w c := by
    calc
      _ = w c * ((w c)⁻¹ * v (aeval (fun i => (x i).val) P)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hv, one_mul]
      _ = _ := by rw [show (w c)⁻¹ * v (aeval (fun i => (x i).val) P) = 1 from hN, mul_one]
  rw [hPval]
  exact hmax d hd

end SpecialTransformations.Section9
