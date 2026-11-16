module

public import Section5.CategoryPresentations
public import Section5.VerticalObstacles
public import Section5.PolynomialPreparation
public import Section4.VFFiniteMaps
public import Section3.GammaPresentation

@[expose] public section

/-! Surjectivity of the canonical RV lift on the isomorphism classes of
both VF categories. Saturation and smallness are the paper's standing
conditions. The compatible valuation is constructed in the released model. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

abbrev liftGammaSpace : PresentedSpace (M := M) := @Section4.gammaSpace M sM hM

theorem finite_fibres_of_presentation {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : Section5.PresentedSpace (M := M)) (hΔ : @Space.RVCoded M N Δ) (k : ℕ)
    (A : Section5.normalizedVFFiniteObject Δ S k) {m : ℕ}
    (D : Section5.DefSet (M := M) S k m)
    (f : Section5.Map (Section5.normalizedVFData Δ S k
      (Section5.normalizedFiniteParent Δ S k A)).2 D)
    (hf : Function.Bijective f) (x : Fin k → Section5.VF (M := M)) :
    {t : Fin m → Section5.RV (M := M) | (x, t) ∈ Section5.carrier D}.Finite := by
  let g := Section5.rawPointMap D
  let hsN : @Saturated M N κ := hs.normalize
  let hcan := @CanonicalStructure.normalize_isCanonical M sM
  letI : LRV.Structure M := N
  letI : M ⊨ Axioms.ACVF := hN
  let A' : VFFiniteObject Δ (M := M) S k := A
  let g' := DefinableGeometry.Map.toImage g
  have hg : Function.Bijective g' := by
    constructor
    · intro a b he
      apply Subtype.ext
      exact congrArg (fun z : DefinableGeometry.Map.image g => z.val) he
    · rintro ⟨b, ⟨a, rfl⟩⟩
      exact ⟨a, rfl⟩
  let e := DefinableGeometry.Map.comp g' f
  have he : Function.Bijective e := hg.comp hf
  obtain ⟨p, hp⟩ := finite_map_to_vf_of_dimension_and_finite_rv_fibres hcan hκ hsN
    hsmall Δ hΔ A'.obj.obj.set A'.obj.property A'.property
  let q := DefinableGeometry.Map.comp p (DefinableGeometry.Map.inverse e he)
  have hinv : Function.Injective (DefinableGeometry.Map.inverse e he) :=
    (Equiv.ofBijective e he).symm.injective
  have hq : q.FiniteFibres := hp.comp (DefinableGeometry.Map.finiteFibres_of_injective hinv)
  have hfin := (dimension_and_finite_rv_fibres_of_finite_map_to_vf
    hcan hκ hsN hsmall Δ q hq).2 x
  apply hfin.subset
  intro t ht
  exact ⟨⟨(x, t), ht⟩, rfl⟩

theorem corollary_5_7_of_rvCoded {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : PresentedSpace (M := M)) (hΔ : @Space.RVCoded M N Δ) (k : ℕ)
    (A : normalizedVFObject Δ S k) :
    ∃ U : @Section4.RVObject M N S k, Nonempty (A ≅ normalizedLiftObject Δ U) := by
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  obtain ⟨U, f, hf⟩ := lift_representation_of_reduction h00 v hv
    (uniformVerticalObstacles hs hsmall v hv) (normalizedVFData Δ S k A).2
    (dimensional_presentation hs h00 hsmall Δ hΔ k A)
  refine ⟨U, ⟨?_⟩⟩
  apply ObjectProperty.isoMk
  exact @DefinableSetCat.isoOfBijective LRV M N _ _ S _ _ f hf

theorem corollary_5_7_finite_of_rvCoded {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : PresentedSpace (M := M)) (hΔ : @Space.RVCoded M N Δ) (k : ℕ)
    (A : normalizedVFFiniteObject Δ S k) :
    ∃ U : @Section4.RVFiniteObject M N S k,
      Nonempty (A ≅ normalizedLiftFiniteObject Δ U) := by
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  let A₀ := normalizedFiniteParent Δ S k A
  obtain ⟨U, f, hf⟩ := finite_lift_representation_of_reduction h00 v hv
    (uniformVerticalObstacles hs hsmall v hv) (normalizedVFData Δ S k A₀).2
    (dimensional_presentation hs h00 hsmall Δ hΔ k A₀)
    (finite_fibres_of_presentation hκ hs hsmall Δ hΔ k A)
  refine ⟨U, ⟨?_⟩⟩
  apply ObjectProperty.isoMk
  apply ObjectProperty.isoMk
  exact @DefinableSetCat.isoOfBijective LRV M N _ _ S _ _ f hf

namespace Paper

theorem theorem_5_4 {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : Set M} (hsmall : Cardinal.mk S < κ) {n m : ℕ}
    {A₀ : DefSet (M := M) S n 0} {A : DefSet (M := M) S n m}
    (u : Fin n → RV (M := M))
    (hFibre : carrier A₀ = {p | ∀ i, rv (vfAt p i) = u i})
    (τ : SpecialBijection A₀ A) (p : MvPolynomial (Fin n) (VF (M := M)))
    (hc : ∀ d, (p.coeff d).val ∈ S) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S n r, ∃ T : SpecialBijection A B,
      (τ.chain.append T.chain).Alternating none ∧
        ∀ b c : B, SameRV b.val c.val →
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (T.inverseMap b)).val) p) =
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (T.inverseMap c)).val) p) :=
  Section5.theorem_5_4 h00 Values.presentationValuation Values.presentation_compatible
    (uniformVerticalObstacles hs hsmall Values.presentationValuation Values.presentation_compatible)
    u hFibre τ p hc

theorem theorem_5_5 {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : Set M} (hsmall : Cardinal.mk S < κ) {n m : ℕ}
    {A₀ : DefSet (M := M) S n 0} {A : DefSet (M := M) S n m}
    (τ : SpecialBijection A₀ A) (p : MvPolynomial (Fin n) (VF (M := M)))
    (hc : ∀ d, (p.coeff d).val ∈ S) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S n r, ∃ T : SpecialBijection A B,
      (τ.chain.append T.chain).Alternating none ∧ IsRVPullback (carrier B) ∧
        ∀ b c : B, SameRV b.val c.val →
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (T.inverseMap b)).val) p) =
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (T.inverseMap c)).val) p) :=
  Section5.theorem_5_5 h00 Values.presentationValuation Values.presentation_compatible
    (uniformVerticalObstacles hs hsmall Values.presentationValuation Values.presentation_compatible)
    τ p hc

theorem corollary_5_6 {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : Set M} (hsmall : Cardinal.mk S < κ) {n m : ℕ}
    (A : DefSet (M := M) S n m) : IsDeformedRVPullback A :=
  Section5.corollary_5_6 h00 Values.presentationValuation Values.presentation_compatible
    (uniformVerticalObstacles hs hsmall Values.presentationValuation Values.presentation_compatible) A

theorem corollary_5_7 {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : Set M} (hsmall : Cardinal.mk S < κ) (k : ℕ)
    (A : normalizedVFObject (liftGammaSpace (M := M)) S k) :
    ∃ U : @Section4.RVObject M N S k,
      Nonempty (A ≅ normalizedLiftObject (liftGammaSpace (M := M)) U) :=
  corollary_5_7_of_rvCoded hs h00 hsmall liftGammaSpace gammaSpace_rvCoded k A

theorem corollary_5_7_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : Set M} (hsmall : Cardinal.mk S < κ) (k : ℕ)
    (A : normalizedVFFiniteObject (liftGammaSpace (M := M)) S k) :
    ∃ U : @Section4.RVFiniteObject M N S k,
      Nonempty (A ≅ normalizedLiftFiniteObject (liftGammaSpace (M := M)) U) :=
  corollary_5_7_finite_of_rvCoded hκ hs h00 hsmall liftGammaSpace gammaSpace_rvCoded k A

end Paper

end SpecialTransformations.Section5
