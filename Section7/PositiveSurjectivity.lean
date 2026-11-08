import Section7.PositiveLift
import Section5.Surjectivity

/-!
# Corollary 7.7 on the fixed-degree positive quotients

The representation of each VF object as an actual lift is supplied by
Section 5. Both quotients use the actual Gamma presentation for dimension.
-/

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
local notation "realN" => (@Base.real M N hN)

theorem corollary_7_7 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : @Base M N hN) (hsmall : Cardinal.mk (realN B) < κ)
    (hB : @VFGammaGeneratedBase M N hN B)
    (k : ℕ) :
    let Δ := @Section5.liftGammaSpace M sM hM
    let hΔ := @gammaSpace_rvCoded M sM hM
    let hsN : @Saturated M N κ := hs.normalize
    let hcan := @CanonicalStructure.normalize_isCanonical M sM
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    ∃ L : RVKPlus (M := M) (realN B) k →+ VFBoundedKPlus hcan hsN hsmall Δ hΔ k,
      Function.Surjective L ∧
      ∀ U : RVObject (M := M) (realN B) k,
        L (rvClass U) = vfBoundedClass hcan hsN hsmall Δ hΔ (rvLiftObject Δ U) := by
  let Δ := @Section5.liftGammaSpace M sM hM
  let hΔ := @gammaSpace_rvCoded M sM hM
  have hrep (A : Section5.normalizedVFObject Δ (realN B) k) :=
    Section5.Paper.corollary_5_7 hs h00 hsmall k A
  have h00N : @Theory.Model LRV M N Axioms.ACVF00 := normalized_model00 h00
  let hsN : @Saturated M N κ := hs.normalize
  let hcan := @CanonicalStructure.normalize_isCanonical M sM
  letI : LRV.Structure M := N
  letI : M ⊨ Axioms.ACVF := hN
  let w := Values.presentationValuation (M := M)
  have hw := Values.presentation_compatible (M := M)
  exact ⟨positiveLift hcan hκ hsN h00N B hsmall hB w hw Δ hΔ k,
    positiveLift_surjective_of_representation hcan hκ hsN h00N B hsmall hB w hw Δ hΔ k hrep,
    positiveLift_class hcan hκ hsN h00N B hsmall hB w hw Δ hΔ k⟩

theorem corollary_7_7_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : @Base M N hN) (hsmall : Cardinal.mk (realN B) < κ)
    (hB : @VFGammaGeneratedBase M N hN B)
    (k : ℕ) :
    let Δ := @Section5.liftGammaSpace M sM hM
    let hΔ := @gammaSpace_rvCoded M sM hM
    let hsN : @Saturated M N κ := hs.normalize
    let hcan := @CanonicalStructure.normalize_isCanonical M sM
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    ∃ Lfin : RVFiniteKPlus (M := M) (realN B) k →+ VFFiniteBoundedKPlus hcan hsN hsmall Δ hΔ k,
      Function.Surjective Lfin ∧
      ∀ U : RVFiniteObject (M := M) (realN B) k,
        Lfin (rvFiniteClass U) = vfFiniteBoundedClass hcan hsN hsmall Δ hΔ (rvLiftFiniteObject Δ U) := by
  let Δ := @Section5.liftGammaSpace M sM hM
  let hΔ := @gammaSpace_rvCoded M sM hM
  have hrepFin (A : Section5.normalizedVFFiniteObject Δ (realN B) k) :=
    Section5.Paper.corollary_5_7_finite hκ hs h00 hsmall k A
  have h00N : @Theory.Model LRV M N Axioms.ACVF00 := normalized_model00 h00
  let hsN : @Saturated M N κ := hs.normalize
  let hcan := @CanonicalStructure.normalize_isCanonical M sM
  letI : LRV.Structure M := N
  letI : M ⊨ Axioms.ACVF := hN
  let w := Values.presentationValuation (M := M)
  have hw := Values.presentation_compatible (M := M)
  exact ⟨positiveFiniteLift hcan hκ hsN h00N B hsmall hB w hw Δ hΔ k,
    positiveFiniteLift_surjective_of_representation hcan hκ hsN h00N B hsmall hB w hw Δ hΔ k hrepFin,
    positiveFiniteLift_class hcan hκ hsN h00N B hsmall hB w hw Δ hΔ k⟩

end SpecialTransformations.Section7
