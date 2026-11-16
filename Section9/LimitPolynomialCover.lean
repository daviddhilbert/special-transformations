module

public import Section4.PolynomialCover
public import Section8.VFDefinableTopology

@[expose] public section

/-! The polynomial cover for the unary-output case of Lemma 9.5.
A finite VF fibre cannot contain the side of an open polydisc.
Consequently every graph point is algebraically dependent, and the
published polynomial-cover theorem supplies one equation over the
original VF parameter field. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

local notation "VF" => VFType (M := M)

/-- A definable relation on two VF coordinates with finite second
fibres lies on a nonzero polynomial over the original parameter field. -/
theorem exists_polynomial_of_finite_vf_fibres
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ) {G : Set (Fin 2 → M)}
    (hG : S.Definable LRV G) (hsort : ∀ z ∈ G, ∀ i, iVF (z i))
    (hfin : ∀ x : VF, {y : VF | vfValues ![x, y] ∈ G}.Finite) :
    ∃ P : MvPolynomial (Fin 2) (vfParameterField S), P ≠ 0 ∧
      ∀ z : Fin 2 → VF, vfValues z ∈ G → P.eval₂ (vfParameterField S).subtype z = 0 := by
  let A := vfObjectOfRaw hG
  have hdef := raw_definableOver_sorted hc S (fun _ : Fin 2 => .vf) G hG hsort
  let v := Values.presentationValuation (M := M)
  letI : Valued VF (Values.presentationType (M := M)) := Valued.mk' v
  have hv (x y : VF) : VFValued.predV x y ↔ v x ≤ v y := Values.presentation_compatible x y
  have hdep (p : A) : ¬ AlgebraicIndependent (vfParameterField S) (p.val.1 ∘ id) := by
    intro hind
    let a := p.val.1
    have ha : AlgebraicIndependent (vfParameterField S) a := hind
    obtain ⟨D, hcentre, hD⟩ := independent_definable_contains_polydisc hv S G hdef a ha p.property
    have hinf := D.side_infinite (model_valuation_nontrivial hv) (1 : Fin 2)
    apply hinf ((hfin (a 0)).subset ?_)
    intro y hy
    let z : Fin 2 → VF := ![a 0, y]
    have hz : z ∈ D.carrier := by
      intro i
      fin_cases i
      · have hr : 0 < v (D.step 0) := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr (D.step_ne_zero 0))
        change v (a 0 - D.centre 0) < v (D.step 0)
        simpa only [hcentre, sub_self, map_zero] using hr
      · exact hy
    exact hD z hz
  obtain ⟨P, hP, hzero⟩ := exists_polynomial_vanishing_on_selection hs hsmall A id hdep
  refine ⟨P, hP, fun z hz => ?_⟩
  let p : A := ⟨(z, Fin.elim0), hz⟩
  exact hzero p

end SpecialTransformations.Section9
