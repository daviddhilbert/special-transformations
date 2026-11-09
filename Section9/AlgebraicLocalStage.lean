import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.Localization.Integral
import Mathlib.FieldTheory.Minpoly.Field

/-! The fraction field of a domain that is an essentially finite
unramified algebra is finite over the base fraction field. Any map
out of the domain which is injective on the base is then injective. -/

namespace SpecialTransformations.Section9

open Polynomial

theorem finite_fractionRing_of_local_stage
    (A C : Type) [CommRing A] [IsDomain A] [CommRing C] [IsDomain C]
    [Algebra A C] [Algebra.FormallyUnramified A C] [Algebra.EssFiniteType A C] [FaithfulSMul A C] :
    letI : Algebra (FractionRing A) (FractionRing C) := FractionRing.liftAlgebra A (FractionRing C)
    Module.Finite (FractionRing A) (FractionRing C) := by
  letI : Algebra (FractionRing A) (FractionRing C) := FractionRing.liftAlgebra A (FractionRing C)
  letI : Algebra.FormallyUnramified (FractionRing A) (FractionRing C) :=
    Algebra.FormallyUnramified.of_restrictScalars A (FractionRing A) (FractionRing C)
  letI : Algebra.EssFiniteType (FractionRing A) (FractionRing C) :=
    Algebra.EssFiniteType.of_comp A (FractionRing A) (FractionRing C)
  exact Algebra.FormallyUnramified.finite_of_free (FractionRing A) (FractionRing C)

theorem local_stage_map_injective {A C S : Type} [CommRing A] [IsDomain A]
    [CommRing C] [IsDomain C] [Algebra A C] [Algebra.FormallyUnramified A C]
    [Algebra.EssFiniteType A C] [FaithfulSMul A C] [CommRing S]
    (f : C →+* S) (hf : Function.Injective (f.comp (algebraMap A C))) : Function.Injective f := by
  let K := FractionRing A
  let L := FractionRing C
  letI : Algebra K L := FractionRing.liftAlgebra A L
  letI : Module.Finite K L := finite_fractionRing_of_local_stage A C
  have hz (z : C) (hzero : f z = 0) : z = 0 := by
    by_contra hne
    let zL := algebraMap C L z
    have hneL : zL ≠ 0 := fun h => hne ((IsFractionRing.injective C L) (h.trans (map_zero _).symm))
    let P := minpoly K zL
    let Q := IsLocalization.integerNormalization (nonZeroDivisors A) P
    have hP : P.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero (IsIntegral.of_finite K zL) hneL
    obtain ⟨a, ha, he⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) P
    have hQ : Q.coeff 0 ≠ 0 := by
      intro h
      have he' := congrArg (fun p : K[X] => p.coeff 0) he
      change (Q.map (algebraMap A K)).coeff 0 = _ at he'
      rw [coeff_map, h, map_zero, coeff_smul, Algebra.smul_def] at he'
      have ha₀ : algebraMap A K a ≠ 0 := fun hh =>
        nonZeroDivisors.ne_zero ha (IsFractionRing.injective A K (hh.trans (map_zero _).symm))
      exact (mul_ne_zero ha₀ hP) he'.symm
    have hqL : aeval zL Q = 0 :=
      IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors A) P (minpoly.aeval K zL)
    have hq : aeval z Q = 0 := by
      apply IsFractionRing.injective C L
      change (IsScalarTower.toAlgHom A C L) (aeval z Q) = algebraMap C L (0 : C)
      rw [map_zero, ← aeval_algHom_apply (IsScalarTower.toAlgHom A C L)]
      exact hqL
    have hfQ : (f.comp (algebraMap A C)) (Q.coeff 0) = 0 := by
      have heval := congrArg f hq
      rw [map_zero, aeval_def, Polynomial.hom_eval₂, hzero, Polynomial.eval₂_at_zero] at heval
      exact heval
    exact hQ (hf (hfQ.trans (map_zero _).symm))
  intro a b he
  apply sub_eq_zero.mp
  exact hz _ (by rw [map_sub, he, sub_self])

theorem algebraic_local_stage (A C : Type) [CommRing A] [IsDomain A]
    [CommRing C] [IsDomain C] [Algebra A C] [Algebra.FormallyUnramified A C]
    [Algebra.EssFiniteType A C] [FaithfulSMul A C] : Algebra.IsAlgebraic A C := by
  let K := FractionRing A
  let L := FractionRing C
  letI : Algebra K L := FractionRing.liftAlgebra A L
  letI : Module.Finite K L := finite_fractionRing_of_local_stage A C
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : Algebra.IsAlgebraic A L := (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K)).mpr inferInstance
  exact Algebra.IsAlgebraic.tower_bot_of_injective (A := L) (IsFractionRing.injective C L)


end SpecialTransformations.Section9
