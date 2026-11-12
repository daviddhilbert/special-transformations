module

public import Section7.PositiveSurjectivity

@[expose] public section

/-! In degree zero Definitions 10.1 and 10.3 use the unmeasured
categories. The fixed-degree lift and its properties specialize directly. -/

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace SpecialTransformations.Section10

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
local notation "Δ" => (@Section5.liftGammaSpace M sM hM)

theorem theorem_10_4_zero {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (A : Section5.normalizedVFFiniteObject Δ S 0) :
    ∃ U : @RVFiniteObject M N S 0, Nonempty (A ≅ Section5.normalizedLiftFiniteObject Δ U) :=
  Section5.Paper.corollary_5_7_finite hκ hs h00 hsmall 0 A

set_option linter.style.haveILetI false in
theorem theorem_10_5_zero {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : @Base M N hN) (hsmall : Cardinal.mk (@Base.real M N hN B) < κ)
    (hB : @VFGammaGeneratedBase M N hN B) :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    ∀ {U V : RVFiniteObject (M := M) B.real 0}, (U ≅ V) →
      Nonempty (rvLiftFiniteObject Δ U ≅ rvLiftFiniteObject Δ V) := by
  let hsN : @Saturated M N κ := hs.normalize
  let hcan := @CanonicalStructure.normalize_isCanonical M sM
  let h00N : @Theory.Model LRV M N Axioms.ACVF00 := normalized_model00 h00
  letI : LRV.Structure M := N
  letI : M ⊨ Axioms.ACVF := hN
  intro U V e
  obtain ⟨f⟩ := Section7.rvLiftObject_iso_of_rvIso hcan hκ hsN h00N B hsmall hB
    (Values.presentationValuation (M := M)) (Values.presentation_compatible (M := M)) Δ
    ((finiteVolumeProperty B.real 0).ι.mapIso e)
  exact ⟨vfFiniteBoundedIsoOfAmbient Δ f⟩

theorem corollary_10_6_zero {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : @Base M N hN) (hsmall : Cardinal.mk (@Base.real M N hN B) < κ)
    (hB : @VFGammaGeneratedBase M N hN B) :
    let hΔ := @gammaSpace_rvCoded M sM hM
    let hsN : @Saturated M N κ := hs.normalize
    let hcan := @CanonicalStructure.normalize_isCanonical M sM
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    ∃ L : RVFiniteKPlus (M := M) B.real 0 →+ VFFiniteBoundedKPlus hcan hsN hsmall Δ hΔ 0,
      Function.Surjective L ∧
      ∀ U : RVFiniteObject (M := M) B.real 0,
        L (rvFiniteClass U) = vfFiniteBoundedClass hcan hsN hsmall Δ hΔ (rvLiftFiniteObject Δ U) :=
  Section7.corollary_7_7_finite hκ hs h00 B hsmall hB 0

end SpecialTransformations.Section10
