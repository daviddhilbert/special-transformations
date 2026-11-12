module

public import Section4.PolynomialZero
public import Section4.FiniteCover
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry
open scoped BigOperators

noncomputable section

namespace SpecialTransformations.Section4

theorem exists_avoid_polynomials_on_box {K : Type} [Field K] {n : ℕ}
    {ι : Type} [Fintype ι] (B : Fin n → Set K) (hB : ∀ i, (B i).Infinite)
    (p : ι → MvPolynomial (Fin n) K) (hp : ∀ i, p i ≠ 0) :
    ∃ x ∈ Set.pi Set.univ B, ∀ i, (p i).eval x ≠ 0 := by
  let q := ∏ i, p i
  have hq : q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hex : ∃ x ∈ Set.pi Set.univ B, q.eval x ≠ 0 := by
    by_contra h
    apply hq
    apply MvPolynomial.funext_set B hB
    intro x hx
    by_contra hz
    exact h ⟨x, hx, hz⟩
  obtain ⟨x, hx, hqx⟩ := hex
  have hprod : (∏ i, (p i).eval x) ≠ 0 := by
    simpa only [q, MvPolynomial.eval_prod] using hqx
  exact ⟨x, hx, fun i => Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)⟩

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A definable set containing an infinite-sided VF box in a fixed RV
fibre has a VF tuple algebraically independent over its original base.
The box need not itself be definable. Genuine saturation is applied only
to the original-base polynomial zero-set cover of the definable source. -/
theorem exists_independent_of_contains_box {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ) {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (B : Fin n → Set (VFType (M := M))) (hB : ∀ i, (B i).Infinite)
    (t : Fin r → CanonicalRV.RVSort M)
    (hbox : ∀ x ∈ Set.pi Set.univ B, (x, t) ∈ A.carrier) :
    ∃ a : A, AlgebraicIndependent (vfParameterField S) a.val.1 := by
  by_contra hnone
  let E := vfParameterField (M := M) S
  let P := rawMixedSpace (M := M) n r
  let Poly := {p : MvPolynomial (Fin n) E // p ≠ 0}
  let Z (p : Poly) : Set (P.Index → M) := P.domain ∩
    (fun z => z ∘ Sum.inl) ⁻¹' PolynomialZero.zeroSet E p.val
  have hZ (p : Poly) : S.Definable LRV (Z p) :=
    (P.definable_domain S).inter
      ((PolynomialZero.zeroSet_parameterField_definable S p.val).raw_definable.preimage_comp Sum.inl)
  have hcover : ∀ z ∈ P.preimage A.carrier, ∃ c ∈ Set.range Z, z ∈ c := by
    rintro z ⟨hz, ha⟩
    let a : A := ⟨P.decode ⟨z, hz⟩, ha⟩
    have hex : ∃ p : MvPolynomial (Fin n) E, p ≠ 0 ∧ p.eval₂ E.subtype a.val.1 = 0 := by
      by_contra h
      apply hnone
      refine ⟨a, algebraicIndependent_iff.mpr ?_⟩
      intro p hp
      by_contra hp0
      exact h ⟨p, hp0, hp⟩
    obtain ⟨p, hp0, hpa⟩ := hex
    let p' : Poly := ⟨p, hp0⟩
    refine ⟨Z p', Set.mem_range_self p', hz, ?_⟩
    have hc : vfValues a.val.1 = z ∘ Sum.inl := by
      funext i
      exact congrFun (mixedValues_decode ⟨z, hz⟩) (.inl i)
    change z ∘ Sum.inl ∈ PolynomialZero.zeroSet E p
    rw [← hc]
    exact ⟨fun i => (a.val.1 i).property, hpa⟩
  obtain ⟨C, hC, hsub, hcov⟩ := definable_finite_subcover_index hs S hsmall
    (P.preimage A.carrier) A.definable (Set.range Z)
    (by rintro _ ⟨p, rfl⟩; exact hZ p) hcover
  letI : Fintype C := hC.fintype
  have hchoice (c : C) : ∃ p : Poly, Z p = c.val := hsub c.property
  let p (c : C) : Poly := Classical.choose (hchoice c)
  have hpc (c : C) : Z (p c) = c.val := Classical.choose_spec (hchoice c)
  have hmap : Function.Injective (MvPolynomial.map (σ := Fin n) E.subtype) :=
    MvPolynomial.map_injective E.subtype Subtype.val_injective
  obtain ⟨x, hx, havoid⟩ := exists_avoid_polynomials_on_box B hB
    (fun c : C => (p c).val.map E.subtype) (by
      intro c hz
      exact (p c).property (hmap (by simpa only [map_zero] using hz)))
  have ha : mixedValues (x, t) ∈ P.preimage A.carrier :=
    ⟨mixedValues_mem_domain (x, t), by
      simpa only [P, decode_mixedValues] using hbox x hx⟩
  obtain ⟨c, hc, hxc⟩ := hcov _ ha
  let c' : C := ⟨c, hc⟩
  have hxZ := (Set.ext_iff.mp (hpc c') (mixedValues (x, t))).mpr hxc
  have hz : vfValues x ∈ PolynomialZero.zeroSet E (p c').val := hxZ.2
  obtain ⟨hVF, hzero⟩ := hz
  have he : (fun i => (⟨(x i).val, hVF i⟩ : VFType (M := M))) = x := by
    funext i
    exact Subtype.ext rfl
  change (p c').val.eval₂ E.subtype (fun i => ⟨(x i).val, hVF i⟩) = 0 at hzero
  rw [he] at hzero
  apply havoid c'
  simpa only [MvPolynomial.eval_map] using hzero

end SpecialTransformations.Section4

end
