import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler

/-! Derivation extension across a formally étale map, by base change
of the module of Kähler differentials. -/

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section9

/-- Extending the functional on Kähler differentials extends the
derivation across a formally étale algebra, with values in any module
over the larger algebra. -/
theorem exists_derivation_formallyEtale_with_values
    {R S T N : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [AddCommGroup N] [Module R N] [Module S N] [Module T N]
    [IsScalarTower R S N] [IsScalarTower R T N] [IsScalarTower S T N]
    [Algebra.FormallyEtale S T] (D : Derivation R S N) :
    ∃ d : Derivation R T N, ∀ a : S, d (algebraMap S T a) = D a := by
  let L := (D.liftKaehlerDifferential.liftBaseChange T).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap
  refine ⟨KaehlerDifferential.linearMapEquivDerivation R T L, fun a => ?_⟩
  simp only [KaehlerDifferential.linearMapEquivDerivation_apply_apply, L, LinearMap.comp_apply,
    LinearEquiv.coe_coe, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]

theorem exists_derivation_formallyEtale
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyEtale S T] (D : Derivation R S T) :
    ∃ d : Derivation R T T, ∀ a : S, d (algebraMap S T a) = D a :=
  exists_derivation_formallyEtale_with_values D

/-- Two derivations over the smaller base agree on a formally étale
algebra once their restrictions to the intermediate algebra agree. -/
theorem derivation_eq_of_formallyEtale
    {R S T N : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [AddCommGroup N] [Module R N] [Module S N] [Module T N]
    [IsScalarTower R T N] [IsScalarTower S T N]
    [Algebra.FormallyEtale S T] (D E : Derivation R T N)
    (h : ∀ a : S, D (algebraMap S T a) = E (algebraMap S T a)) : D = E := by
  let Q := D - E
  have hQ (a : S) : Q (algebraMap S T a) = 0 := by
    change D (algebraMap S T a) - E (algebraMap S T a) = 0
    rw [h, sub_self]
  let d : Derivation S T N :=
    { toFun := Q
      map_add' := Q.map_add
      map_smul' := by
        intro a b
        change Q (a • b) = a • Q b
        rw [Algebra.smul_def, Q.leibniz, hQ, smul_zero, add_zero, algebraMap_smul]
      map_one_eq_zero' := Q.map_one_eq_zero
      leibniz' := Q.leibniz }
  apply Derivation.ext
  intro x
  apply sub_eq_zero.mp
  change d x = 0
  have hd : d.liftKaehlerDifferential (KaehlerDifferential.D S T x) = d x :=
    Derivation.liftKaehlerDifferential_comp_D _ _
  rw [← hd, Subsingleton.elim (KaehlerDifferential.D S T x) 0, map_zero]

/-- If the restriction of a derivation takes values in a smaller module,
the same is true throughout a formally étale algebra. -/
theorem derivation_factors_of_formallyEtale
    {R S T N P : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [AddCommGroup N] [Module R N] [Module S N] [Module T N]
    [IsScalarTower R S N] [IsScalarTower R T N] [IsScalarTower S T N]
    [AddCommGroup P] [Module R P] [Module S P] [Module T P]
    [IsScalarTower R T P] [IsScalarTower S T P]
    [Algebra.FormallyEtale S T] (i : N →ₗ[T] P)
    (dS : Derivation R S N) (dT : Derivation R T P)
    (h : ∀ a : S, dT (algebraMap S T a) = i (dS a)) :
    ∃ D : Derivation R T N, ∀ t, dT t = i (D t) := by
  obtain ⟨D, hD⟩ := exists_derivation_formallyEtale_with_values (T := T) dS
  have he : dT = i.compDer D := derivation_eq_of_formallyEtale dT (i.compDer D) (fun a => by
    change dT (algebraMap S T a) = i (D (algebraMap S T a))
    rw [hD, h])
  exact ⟨D, fun t => congrArg (fun d : Derivation R T P => d t) he⟩

/-- A derivation with values in the larger field extends across a
separable field extension. -/
theorem exists_derivation_extension
    {E F K : Type*} [Field E] [Field F] [Field K]
    [Algebra E F] [Algebra E K] [Algebra F K] [IsScalarTower E F K]
    [Algebra.IsSeparable F K] (D : Derivation E F K) :
    ∃ d : Derivation E K K, ∀ a : F, d (algebraMap F K a) = D a := by
  letI : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  exact exists_derivation_formallyEtale D

end SpecialTransformations.Section9
