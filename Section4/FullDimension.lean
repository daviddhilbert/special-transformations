import Section4.VFDimensionRank
import Section4.TupleIndependence
import Section4.GenericPoints
import Section4.PolydiscLocal
import Section4.VFRealFibres
import ValuedFieldExtension

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_independent_of_full_dimension
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded) {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hne : A.carrier.Nonempty)
    (hdim : vfDim Δ A = n) : ∃ a : A, AlgebraicIndependent (vfParameterField S) a.val.1 := by
  have hmax : vfTrdeg A = n := (lemma_4_4 hcan hs hsmall Δ hΔ A).symm.trans hdim
  obtain ⟨a₀, ha₀⟩ := hne
  have hrange : (Set.range (fun a : A => (vfTupleTrdeg S a.val.1).toNat)).Nonempty :=
    ⟨_, ⟨a₀, ha₀⟩, rfl⟩
  obtain ⟨a, ha⟩ := Nat.sSup_mem hrange (vfTrdeg_bounded A)
  change (vfTupleTrdeg S a.val.1).toNat = vfTrdeg A at ha
  rw [hmax] at ha
  have hfin := (vfTupleTrdeg_le_arity S a.val.1).trans_lt Cardinal.natCast_lt_aleph0
  have hcard : vfTupleTrdeg S a.val.1 = (n : Cardinal) := by
    rw [← Cardinal.cast_toNat_of_lt_aleph0 hfin, ha]
  exact ⟨a, (tupleField_trdeg_eq_arity_iff (vfParameterField S) a.val.1).mp hcard⟩

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem model_valuation_nontrivial
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    ∃ ε : VFType (M := M), ε ≠ 0 ∧ Valued.v ε < 1 := by
  obtain ⟨ε, hε0, hε⟩ := ValuedFieldExtension.exists_nontrivial_predV (M := M)
  refine ⟨ε, hε0, lt_of_not_ge ?_⟩
  intro h
  apply hε
  apply (hv 1 ε).mpr
  simpa only [map_one] using h

theorem vfDim_eq_arity_of_contains_polydisc
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S)
    (t : Fin r → CanonicalRV.RVSort M)
    (D : ValuedPolydisc (Valued.v : Valuation (VFType (M := M)) Γ) n)
    (hD : ∀ x ∈ D.carrier, (x, t) ∈ A.carrier) : vfDim Δ A = n := by
  obtain ⟨a, ha⟩ := exists_independent_of_contains_box hs hsmall A D.side
    (D.side_infinite (model_valuation_nontrivial hv)) t
    (fun x hx => hD x ((D.mem_carrier_iff x).mpr hx))
  have hrank : vfTupleTrdeg S a.val.1 = (n : Cardinal) :=
    (tupleField_trdeg_eq_arity_iff (vfParameterField S) a.val.1).mpr ha
  have hle := vfTupleTrdeg_le_vfDim hcan Δ hΔ A a
  rw [hrank] at hle
  have hn : n ≤ vfDim Δ A := by exact_mod_cast hle
  exact (vfDim_le_arity Δ A).antisymm hn

/-- Lemma 4.6 with explicit nonemptiness, required by dimension(empty)=0
when the VF arity is zero. All radii are actual nonzero realized radii. -/
theorem lemma_4_6 (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S) (hne : A.carrier.Nonempty) :
    vfDim Δ A = n ↔ ∃ t : Fin r → CanonicalRV.RVSort M,
      ∃ D : ValuedPolydisc (Valued.v : Valuation (VFType (M := M)) Γ) n,
        ∀ x ∈ D.carrier, (x, t) ∈ A.carrier := by
  constructor
  · intro hd
    obtain ⟨a, ha⟩ := exists_independent_of_full_dimension hcan hs hsmall Δ hΔ A hne hd
    let t := a.val.2
    let B := S ∪ Set.range (rvValues t)
    have haB : AlgebraicIndependent (vfParameterField B) a.val.1 := by
      change AlgebraicIndependent (vfParameterField (S ∪ Set.range (rvValues t))) a.val.1
      rw [vfParameterField_union_rv S _ (by rintro x ⟨i, rfl⟩; exact (t i).property)]
      exact ha
    obtain ⟨D, hcentre, hD⟩ := independent_definable_contains_polydisc hv B
      (rawFixedRVFibre A t) (rawFixedRVFibre_sorted hcan A t) a.val.1 haB
      ((mem_rawFixedRVFibre A t a.val.1).mpr a.property)
    exact ⟨t, D, fun x hx => (mem_rawFixedRVFibre A t x).mp (hD x hx)⟩
  · rintro ⟨t, D, hD⟩
    exact vfDim_eq_arity_of_contains_polydisc hcan hs hsmall Δ hΔ hv A t D hD

end SpecialTransformations.Section4

end
