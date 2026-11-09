import Section9.DerivationExtension
import Mathlib.Algebra.Ring.Subring.Basic

/-! A derivation preserving a subring also preserves the image of its
étale neighbourhoods in an intermediate subring. This is the
derivation calculation for the henselization proof. -/

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section9

variable {K : Type} [CommRing K]

/-- The elementwise consequence of an ind-étale presentation.
For valuation-ring henselizations the presentation comes from
Stacks Project, Lemma 10.155.1. -/
def EtaleCovered (A B : Subring K) (hAB : A ≤ B) : Prop :=
  letI : Algebra A B := (Subring.inclusion hAB).toAlgebra
  ∀ b : B, ∃ (T : Type) (rT : CommRing T),
    letI := rT
    ∃ aT : Algebra A T, letI := aT
      Algebra.FormallyEtale A T ∧ ∃ (f : T →ₐ[A] B) (t : T), f t = b

/-- Extending a derivation across étale neighbourhoods keeps its values
in the target ring. This conclusion is independent of the choice of
neighbourhood, by uniqueness of extending the derivation. -/
theorem derivation_maps_subring_of_etaleCovered
    (A B : Subring K) (hAB : A ≤ B) (hcover : EtaleCovered A B hAB)
    (D : Derivation ℤ K K) (hA : ∀ a : A, D (a : K) ∈ A) :
    ∀ b : B, D (b : K) ∈ B := by
  intro b
  letI : Algebra A B := (Subring.inclusion hAB).toAlgebra
  obtain ⟨T, rT, aT, hT, f, t, ht⟩ := hcover b
  letI := rT
  letI := aT
  letI := hT
  letI : Algebra A K := A.subtype.toAlgebra
  letI : Algebra B K := B.subtype.toAlgebra
  letI : Algebra T B := f.toRingHom.toAlgebra
  letI : Algebra T K := (B.subtype.comp f.toRingHom).toAlgebra
  letI : IsScalarTower A T B := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  letI : IsScalarTower A T K := IsScalarTower.of_algebraMap_eq fun a =>
    congrArg Subtype.val (f.commutes a).symm
  letI : IsScalarTower T B K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let i : B →ₗ[T] K :=
    { toFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let dA : Derivation ℤ A B :=
    { toFun := fun a => ⟨D (a : K), hAB (hA a)⟩
      map_add' := fun a c => Subtype.ext (D.map_add (a : K) (c : K))
      map_smul' := fun a c => Subtype.ext (D.map_smul a (c : K))
      map_one_eq_zero' := Subtype.ext D.map_one_eq_zero
      leibniz' := fun a c => Subtype.ext (D.leibniz (a : K) (c : K)) }
  let dT := D.compAlgebraMap T
  have h (a : A) : dT (algebraMap A T a) = i (dA a) := by
    change D ((f (algebraMap A T a) : B) : K) = D (a : K)
    exact congrArg (fun z : B => D (z : K)) (f.commutes a)
  obtain ⟨d, hd⟩ := derivation_factors_of_formallyEtale i dA dT h
  have he := hd t
  change D ((f t : B) : K) = (d t : K) at he
  rw [← ht, he]
  exact (d t).property

end SpecialTransformations.Section9
