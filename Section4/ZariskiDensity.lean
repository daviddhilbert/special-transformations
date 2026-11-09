import Section4.ModelGeometry
import Section4.ZariskiPrimeBound
import Section3.SmallFiniteParameters

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry
open scoped BigOperators

noncomputable section

namespace SpecialTransformations.Section4

theorem polynomial_over_subfield {K : Type} [Field K] (E : Subfield K)
    {n : ℕ} (p : MvPolynomial (Fin n) K) (hcoeff : ∀ m, p.coeff m ∈ E) :
    ∃ q : MvPolynomial (Fin n) E, q.map E.subtype = p := by
  apply (MvPolynomial.mem_range_map_iff_coeffs_subset (f := E.subtype) (x := p)).mpr
  intro c hc
  obtain ⟨m, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
  exact ⟨⟨p.coeff m, hcoeff m⟩, rfl⟩

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A full-dimensional definable mixed set is Zariski dense in its VF
coordinates over the entire ambient field. Finite coefficient names are
adjoined explicitly and parameter invariance supplies a new generic point. -/
theorem polynomial_eq_zero_of_full_dimension
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hne : A.carrier.Nonempty) (hdim : vfDim Δ A = n)
    (p : MvPolynomial (Fin n) (VFType (M := M)))
    (hp : ∀ a : A, p.eval a.val.1 = 0) : p = 0 := by
  let C : Set M := (fun m => (p.coeff m).val) '' (p.support : Set _)
  have hC : C.Finite := p.support.finite_toSet.image _
  let T := S ∪ C
  have hST : S ⊆ T := Set.subset_union_left
  have hT : Cardinal.mk T < κ := small_union_finite hκ S hsmall C hC
  let E := vfParameterField (M := M) T
  have hcoeff (m : Fin n →₀ ℕ) : p.coeff m ∈ E := by
    by_cases hm : m ∈ p.support
    · exact Subfield.subset_closure (Or.inr ⟨m, hm, rfl⟩)
    · rw [MvPolynomial.notMem_support_iff.mp hm]
      exact E.zero_mem
  obtain ⟨q, hq⟩ := polynomial_over_subfield E p hcoeff
  have hdT : vfDim Δ (A.extend hST) = n :=
    (vfDim_parameter_invariant_model hcan hs hsmall hT hST Δ hΔ A).trans hdim
  obtain ⟨a, ha⟩ := exists_independent_of_full_dimension hcan hs hT Δ hΔ
    (A.extend hST) hne hdT
  have hzero : q.eval₂ E.subtype a.val.1 = 0 := by
    have h := hp ⟨a.val, a.property⟩
    rw [← hq, MvPolynomial.eval_map] at h
    exact h
  have hq0 := ha.eq_zero_of_aeval_eq_zero q hzero
  rw [← hq, hq0, map_zero]

theorem vfVanishingIdeal_eq_bot_of_full_dimension
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hne : A.carrier.Nonempty) (hdim : vfDim Δ A = n) : vfVanishingIdeal A = ⊥ := by
  apply bot_unique
  intro p hp
  exact polynomial_eq_zero_of_full_dimension hcan hκ hs hsmall Δ hΔ A hne hdim p
    ((mem_vfVanishingIdeal_iff A p).mp hp)

end SpecialTransformations.Section4

end
