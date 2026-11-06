import Section4.PolynomialZero
import Section4.FiniteCover
import Section4.VFDimensionRank

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry
open scoped BigOperators

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- If a fixed coordinate selection is dependent at every point of a
definable set, one nonzero polynomial over its original VF parameter field
vanishes on the whole selected image. Saturation supplies the finite cover;
the product combines its equations. -/
theorem exists_polynomial_vanishing_on_selection
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    {n r d : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S) (v : Fin d → Fin n)
    (hdep : ∀ a : A, ¬ AlgebraicIndependent (vfParameterField S) (a.val.1 ∘ v)) :
    ∃ p : MvPolynomial (Fin d) (vfParameterField S), p ≠ 0 ∧
      ∀ a : A, p.eval₂ (vfParameterField S).subtype (a.val.1 ∘ v) = 0 := by
  let E := vfParameterField (M := M) S
  let P := rawMixedSpace (M := M) n r
  let Poly := {p : MvPolynomial (Fin d) E // p ≠ 0}
  let Z (p : Poly) : Set (P.Index → M) := P.domain ∩
    (fun z => fun i => z (.inl (v i))) ⁻¹' PolynomialZero.zeroSet E p.val
  have hZ (p : Poly) : S.Definable LRV (Z p) :=
    (P.definable_domain S).inter
      ((PolynomialZero.zeroSet_parameterField_definable S p.val).raw_definable.preimage_comp
        (fun i => Sum.inl (v i)))
  have hcover : ∀ z ∈ P.preimage A.carrier, ∃ c ∈ Set.range Z, z ∈ c := by
    rintro z ⟨hz, ha⟩
    let a : A := ⟨P.decode ⟨z, hz⟩, ha⟩
    have hex : ∃ p : MvPolynomial (Fin d) E,
        p ≠ 0 ∧ p.eval₂ E.subtype (a.val.1 ∘ v) = 0 := by
      by_contra h
      apply hdep a
      apply algebraicIndependent_iff.mpr
      intro p hp
      by_contra hp0
      exact h ⟨p, hp0, hp⟩
    obtain ⟨p, hp0, hpa⟩ := hex
    let p' : Poly := ⟨p, hp0⟩
    refine ⟨Z p', Set.mem_range_self p', hz, ?_⟩
    have hc : vfValues (a.val.1 ∘ v) = fun i => z (.inl (v i)) := by
      funext i
      exact congrFun (mixedValues_decode ⟨z, hz⟩) (.inl (v i))
    change (fun i => z (.inl (v i))) ∈ PolynomialZero.zeroSet E p
    rw [← hc]
    exact ⟨fun i => (a.val.1 (v i)).property, hpa⟩
  obtain ⟨C, hC, hsub, hcov⟩ := definable_finite_subcover_index hs S hsmall
    (P.preimage A.carrier) A.definable (Set.range Z)
    (by rintro _ ⟨p, rfl⟩; exact hZ p) hcover
  letI : Fintype C := hC.fintype
  have hchoice (c : C) : ∃ p : Poly, Z p = c.val := hsub c.property
  let p (c : C) : Poly := Classical.choose (hchoice c)
  have hpc (c : C) : Z (p c) = c.val := Classical.choose_spec (hchoice c)
  refine ⟨∏ c : C, (p c).val, Finset.prod_ne_zero_iff.mpr (fun c _ => (p c).property), ?_⟩
  intro a
  have ha : mixedValues a.val ∈ P.preimage A.carrier :=
    ⟨mixedValues_mem_domain a.val, by simpa only [P, decode_mixedValues] using a.property⟩
  obtain ⟨c, hc, hac⟩ := hcov _ ha
  let c' : C := ⟨c, hc⟩
  have hz := (Set.ext_iff.mp (hpc c') (mixedValues a.val)).mpr hac
  have hz' : vfValues (a.val.1 ∘ v) ∈ PolynomialZero.zeroSet E (p c').val := hz.2
  obtain ⟨hVF, hzero⟩ := hz'
  have he : (fun i => (⟨(a.val.1 (v i)).val, hVF i⟩ : VFType (M := M))) =
      a.val.1 ∘ v := by
    funext i
    exact Subtype.ext rfl
  change (p c').val.eval₂ E.subtype
    (fun i => ⟨(a.val.1 (v i)).val, hVF i⟩) = 0 at hzero
  rw [he] at hzero
  rw [MvPolynomial.eval₂_prod]
  exact Finset.prod_eq_zero_iff.mpr ⟨c', Finset.mem_univ _, hzero⟩

theorem vfTupleTrdeg_select_le (S : Set M) {n d : ℕ}
    (a : Fin n → VFType (M := M)) (v : Fin d → Fin n) :
    vfTupleTrdeg S (a ∘ v) ≤ vfTupleTrdeg S a := by
  apply relativeTrdeg_mono
  apply sup_le le_sup_left
  apply (Subfield.closure_mono (show Set.range (a ∘ v) ⊆ Set.range a from
    by rintro x ⟨i, rfl⟩; exact Set.mem_range_self (v i))).trans le_sup_right

end SpecialTransformations.Section4

end
