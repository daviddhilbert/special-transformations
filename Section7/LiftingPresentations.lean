module

public import Section5.Surjectivity

@[expose] public section

/-! Compatibility exports for the presentation lemmas now supplied by Section 5. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem finite_fibres_of_section5_presentation {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : Section5.PresentedSpace (M := M)) (hΔ : @Space.RVCoded M N Δ) (k : ℕ)
    (A : Section5.normalizedVFFiniteObject Δ S k) {m : ℕ}
    (D : Section5.DefSet (M := M) S k m)
    (f : Section5.Map (Section5.normalizedVFData Δ S k
      (Section5.normalizedFiniteParent Δ S k A)).2 D)
    (hf : Function.Bijective f) (x : Fin k → Section5.VF (M := M)) :
    {t : Fin m → Section5.RV (M := M) | (x, t) ∈ Section5.carrier D}.Finite :=
  Section5.finite_fibres_of_presentation hκ hs hsmall Δ hΔ k A D f hf x

theorem section5_finite_dimensional_presentation {κ : Cardinal} (_hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) {S : Set M}
    (hsmall : Cardinal.mk S < κ)
    (Δ : Section5.PresentedSpace (M := M)) (hΔ : @Space.RVCoded M N Δ) (k : ℕ)
    (A : Section5.normalizedVFFiniteObject Δ S k) :
    ∃ m : ℕ, ∃ D : Section5.DefSet (M := M) S k m,
      ∃ f : Section5.Map (Section5.normalizedVFData Δ S k
        (Section5.normalizedFiniteParent Δ S k A)).2 D, Function.Bijective f :=
  Section5.dimensional_presentation hs h00 hsmall Δ hΔ k
    (Section5.normalizedFiniteParent Δ S k A)

end SpecialTransformations.Section7
