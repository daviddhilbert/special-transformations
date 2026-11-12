module

public import Section9.ResidueChartSelector
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-! A selector on the finite étale generic fibre has a numerator in
the original algebra. Its vanishing detects the same formula at every
field-valued point that is injective on the base. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open scoped TensorProduct nonZeroDivisors

namespace SpecialTransformations.Section9

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem exists_genericChart_selector
    {R A α : Type} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Algebra.FormallyUnramified R A] [Algebra.EssFiniteType R A] {n : ℕ}
    (a : α → A) (x : Fin n → A) (φ : Language.ring.BoundedFormula α n) (hφ : φ.IsQF) :
    ∃ b : A, ∀ (K : Type) [Field K] (f : A →+* K),
      Function.Injective (f.comp (algebraMap R A)) →
      (φ.Realize (f ∘ a) (f ∘ x) ↔ f b ≠ 0) := by
  classical
  let F := FractionRing R
  let B := F ⊗[R] A
  let i : A →+* B := algebraMap A B
  let T := Algebra.algebraMapSubmonoid A R⁰
  letI : IsLocalization T B := inferInstance
  haveI : Module.Finite F B := Algebra.FormallyUnramified.finite_of_free F B
  haveI : IsArtinianRing B := IsArtinianRing.of_finite F B
  haveI : IsReduced B := Algebra.FormallyUnramified.isReduced_of_field F B
  obtain ⟨p, hp⟩ := exists_algebraicTest_of_isQF (i ∘ a) (i ∘ x) φ hφ
  obtain ⟨c, hc⟩ := p.exists_selector
  obtain ⟨⟨b, d⟩, hd⟩ := IsLocalization.surj T c
  refine ⟨b, fun K _ f hf => ?_⟩
  have hunit (s : T) : IsUnit (f s.val) := by
    obtain ⟨r, hr, he⟩ := s.property
    rw [← he, isUnit_iff_ne_zero]
    intro hz
    apply nonZeroDivisors.ne_zero hr
    apply hf
    change f (algebraMap R A r) = (f.comp (algebraMap R A)) 0
    rw [map_zero, hz]
  let g : B →+* K := IsLocalization.lift hunit
  have hg (y : A) : g (i y) = f y := IsLocalization.lift_eq hunit y
  have he (y : α → A) : g ∘ (i ∘ y) = f ∘ y := funext fun j => hg (y j)
  have h₁ := hp K g
  rw [he, (show g ∘ (i ∘ x) = f ∘ x from funext fun j => hg (x j))] at h₁
  have h₂ : f b = g c * f d.val := by
    have h := congrArg g hd
    change g (c * i d.val) = g (i b) at h
    simpa only [map_mul, hg] using h.symm
  rw [h₁, h₂, hc K g, mul_ne_zero_iff]
  by_cases h : p.holds g <;> simp [h, isUnit_iff_ne_zero.mp (hunit d)]

end SpecialTransformations.Section9
