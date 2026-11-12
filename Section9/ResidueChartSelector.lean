module

public import Mathlib.RingTheory.Etale.Field
public import Section7.GuardedBaseMonomials

@[expose] public section

/-! In a reduced finite algebra, a Boolean combination of polynomial
zero tests is selected by one element that takes only values zero and
one under field-valued points. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open scoped Classical

namespace SpecialTransformations.Section9

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal

inductive AlgebraicTest (A : Type)
  | zero (a : A)
  | and (p q : AlgebraicTest A)
  | not (p : AlgebraicTest A)

def AlgebraicTest.holds {A K : Type} [CommRing A] [Field K] (f : A →+* K) : AlgebraicTest A → Prop
  | .zero a => f a = 0
  | .and p q => p.holds f ∧ q.holds f
  | .not p => ¬ p.holds f

theorem exists_algebraicTest_of_isQF
    {A α : Type} [CommRing A] {n : ℕ}
    (a : α → A) (x : Fin n → A) (φ : Language.ring.BoundedFormula α n) (hφ : φ.IsQF) :
    ∃ p : AlgebraicTest A, ∀ (K : Type) [Field K] (f : A →+* K),
      φ.Realize (f ∘ a) (f ∘ x) ↔ p.holds f := by
  induction hφ with
  | falsum =>
    refine ⟨.not (.zero 0), fun K _ f => ?_⟩
    change False ↔ ¬f 0 = 0
    simp
  | of_isAtomic h =>
    cases h with
    | equal t u =>
      let v := Sum.elim a x
      refine ⟨.zero (t.realize v - u.realize v), fun K _ f => ?_⟩
      change t.realize (Sum.elim (f ∘ a) (f ∘ x)) = u.realize (Sum.elim (f ∘ a) (f ∘ x)) ↔
        f (t.realize v - u.realize v) = 0
      have hv : (fun i => f (v i)) = Sum.elim (f ∘ a) (f ∘ x) := by
        funext i
        cases i <;> rfl
      rw [map_sub, Section7.ringTerm_realize_map, Section7.ringTerm_realize_map, hv, sub_eq_zero]
    | rel r ts => cases r
  | imp _ _ hp hq =>
    obtain ⟨p, hp⟩ := hp
    obtain ⟨q, hq⟩ := hq
    refine ⟨.not (.and p (.not q)), fun K _ f => ?_⟩
    simp only [BoundedFormula.realize_imp, hp, hq, AlgebraicTest.holds]
    tauto

private theorem exists_partial_inverse {A : Type} [CommRing A] [IsArtinianRing A] [IsReduced A] (a : A) :
    ∃ b : A, a * (a * b) = a := by
  classical
  let e := IsArtinianRing.equivPi A
  refine ⟨e.symm (fun i => (e a i)⁻¹), e.injective ?_⟩
  rw [map_mul, map_mul, e.apply_symm_apply]
  funext i
  change e a i * (e a i * (e a i)⁻¹) = e a i
  by_cases h : e a i = 0
  · simp [h]
  · rw [mul_inv_cancel₀ h, mul_one]

theorem AlgebraicTest.exists_selector {A : Type} [CommRing A] [IsArtinianRing A] [IsReduced A]
    (p : AlgebraicTest A) :
    ∃ a : A, ∀ (K : Type) [Field K] (f : A →+* K),
      f a = if p.holds f then 1 else 0 := by
  classical
  induction p with
  | zero a =>
    obtain ⟨b, h⟩ := exists_partial_inverse a
    refine ⟨1 - a * b, fun K _ f => ?_⟩
    change f (1 - a * b) = if f a = 0 then 1 else 0
    rw [map_sub, map_mul, map_one]
    by_cases ha : f a = 0
    · simp [ha]
    · have he : f a * (f a * f b) = f a := by simpa only [map_mul] using congrArg f h
      have he' : f a * (f a * f b) = f a * 1 :=
        he.trans (mul_one _).symm
      rw [if_neg ha, mul_left_cancel₀ ha he', sub_self]
  | and p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a * b, fun K _ f => ?_⟩
    rw [map_mul, ha K f, hb K f]
    by_cases h₁ : p.holds f <;> by_cases h₂ : q.holds f <;> simp [AlgebraicTest.holds, h₁, h₂]
  | not p hp =>
    obtain ⟨a, ha⟩ := hp
    refine ⟨1 - a, fun K _ f => ?_⟩
    rw [map_sub, map_one, ha K f]
    by_cases h : p.holds f <;> simp [AlgebraicTest.holds, h]

end SpecialTransformations.Section9
