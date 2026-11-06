import Section4.ResidueRVSet
import Section4.RVParameterInvariance
import Section4.SmallGeneratedBase
import Mathlib.Algebra.MvPolynomial.Eval

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem residueParameterField_mono {B C : LRV.Substructure M} (hBC : B ≤ C) :
    residueParameterField B ≤ residueParameterField C := fun _ hx => hBC hx

/-- A full-dimensional residue set is Zariski dense over the entire
ambient residue field. Its finitely many polynomial coefficients are
named explicitly in a small generated LRV substructure. -/
theorem residue_polynomial_eq_zero_of_full_dimension
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hh : StronglyHomogeneous M κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    {n : ℕ} (D : Set (Fin n → ModelResidue M)) (hD : Relative.Def (residueParameterField B) D)
    (hne : D.Nonempty)
    (hdim : rvDim (residueRVSet hcan (residueParameterField B) (B : Set M)
      (residueParameterField_le_definableField B) D hD) = n)
    (p : MvPolynomial (Fin n) (ModelResidue M))
    (hp : ∀ a ∈ D, p.eval a = 0) : p = 0 := by
  let C : Set M := residueRaw '' (p.coeffs : Set (ModelResidue M))
  have hC : C.Finite := p.coeffs.finite_toSet.image residueRaw
  let B' := Substructure.closure LRV ((B : Set M) ∪ C)
  have hBB' : B ≤ B' := fun _ hx => Substructure.subset_closure (Or.inl hx)
  have hB' : Cardinal.mk B' < κ := small_generated_finite_extension hκ B hB C hC
  let E := residueParameterField B'
  have hDE : Relative.Def E D := hD.mono (residueParameterField_mono hBB')
  let A := residueRVSet hcan (residueParameterField B) (B : Set M)
    (residueParameterField_le_definableField B) D hD
  let A' := residueRVSet hcan E (B' : Set M)
    (residueParameterField_le_definableField B') D hDE
  have hd' : rvDim A' = n := by
    change rvDim (A.extend hBB') = n
    exact (rvDim_parameter_invariant hcan hex hκ.le hs hh hBB' hB hB' A).trans hdim
  have hcoeff : (p.coeffs : Set (ModelResidue M)) ⊆ Set.range E.subtype := by
    intro c hc
    have hc' : c ∈ E := Substructure.subset_closure (Or.inr ⟨c, hc, rfl⟩)
    exact ⟨⟨c, hc'⟩, rfl⟩
  obtain ⟨q, hq⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.mpr hcoeff
  obtain ⟨a, ha, hrank⟩ := exists_residue_point_of_maximum_rank hcan hex hs B' hB' D hDE hne
  have hind : AlgebraicIndependent E a := (tupleField_trdeg_eq_arity_iff E a).mp
    (hrank.trans (congrArg (fun k : ℕ => (k : Cardinal)) hd'))
  have hqa : q.eval₂ E.subtype a = 0 := by
    have h := hp a ha
    rw [← hq, MvPolynomial.eval_map] at h
    exact h
  have hq0 := hind.eq_zero_of_aeval_eq_zero q hqa
  rw [← hq, hq0, map_zero]

end SpecialTransformations.Section4.ResiduePurity

end
