import Section10.WeightedZero
import Section5.Surjectivity

/-! Transport the actual supplied form through the ordinary finite lift
presentation. The zero label projection has a definable inverse, so this
works equally for RV and Gamma forms without choosing Gamma representatives. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8

noncomputable section

namespace SpecialTransformations.Section10

variable {M G : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable [CommMonoidWithZero G]

/-- Transport the checked normalized Section 5 theorem to a canonical model.
The auxiliary space is arbitrary RV-coded, as in the imported theorem. -/
theorem ordinary_zero_representation
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : Set M} (hsmall : Cardinal.mk S < κ) (Δ : Space LRV M) (hΔ : Δ.RVCoded)
    (A : VFFiniteObject Δ S 0) :
    ∃ U : RVFiniteObject (M := M) S 0, Nonempty (A ≅ rvLiftFiniteObject Δ U) := by
  have transport (T : LRV.Structure M) (e : @CanonicalStructure.normalize M sM = T) :
      ∀ (hT : @Theory.Model LRV M T Axioms.ACVF)
        (Δ : @Space LRV M T), @Space.RVCoded M T Δ →
        ∀ A : @VFFiniteObject M T Δ S 0,
          ∃ U : @RVFiniteObject M T S 0,
            Nonempty (A ≅ @rvLiftFiniteObject M T hT S 0 Δ U) := by
    cases e
    intro hT Δ hΔ A
    exact @Section5.corollary_5_7_finite_of_rvCoded M sM hM κ hκ hs h00 S hsmall Δ hΔ 0 A
  exact transport sM (normalize_eq_of_isCanonical hc) hM Δ hΔ A

theorem volumeGammaSpace_rvCoded (hc : CanonicalStructure.IsCanonical (M := M)) :
    (volumeGammaSpace hc).RVCoded := by
  have transport {T U : LRV.Structure M} (e : T = U) (P : @Space LRV M T) :
      @Space.RVCoded M T P → @Space.RVCoded M U (e ▸ P) := by
    cases e
    exact id
  exact transport (normalize_eq_of_isCanonical hc) (@gammaSpace M sM hM) gammaSpace_rvCoded

/-- The actual form, not only its valuation, descends through the zero lift. -/
theorem weighted_zero_of_ordinary_representation
    {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {d : VolumeScale M G}
    (A : MeasuredVFZero hc S d) (U : RVFiniteObject (M := M) S 0)
    (e : A.underlying ≅ rvLiftFiniteObject (volumeGammaSpace hc) U) :
    ∃ V : MeasuredRVZero S d, V.underlying = U ∧ Nonempty (A ≅ V.lift hc) := by
  let E := (vfDimensionProperty (volumeGammaSpace hc) S 0).ι.mapIso
    ((vfBoundedFiniteProperty (volumeGammaSpace hc) S 0).ι.mapIso e)
  let f : Map A.domain (rvLift U.obj) := E.hom
  have hf : Function.Bijective f := DefinableSetCat.bijective_of_iso E
  let labels := Section9.liftLabelMap U.obj
  have hl := liftLabelMap_zero_bijective U
  let g := (f.inverse hf).comp (labels.inverse hl)
  let V : MeasuredRVZero S d := ⟨U, A.form.pullback g⟩
  refine ⟨V, rfl, ⟨WeightedZero.isoOfExactMap ⟨f, hf, ?_⟩⟩⟩
  intro a
  change A.weight a = A.weight (f.inverse hf (labels.inverse hl (labels (f a))))
  rw [Map.inverse_apply, Map.inverse_apply]

/-- Theorem 10.4 at zero, uniformly for the existing RV and Gamma scales.
The ordinary VF object may have arbitrary mixed presentation arity. -/
theorem theorem_10_4_weighted_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : Set M} (hsmall : Cardinal.mk S < κ) {d : VolumeScale M G}
    (A : MeasuredVFZero hc S d) :
    ∃ U : MeasuredRVZero S d, Nonempty (A ≅ U.lift hc) := by
  obtain ⟨U, ⟨e⟩⟩ := ordinary_zero_representation hc hκ hs h00 hsmall
    (volumeGammaSpace hc) (volumeGammaSpace_rvCoded hc) A.underlying
  obtain ⟨V, _, hV⟩ := weighted_zero_of_ordinary_representation A U e
  exact ⟨V, hV⟩

end SpecialTransformations.Section10
