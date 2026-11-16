module

public import Section7.JacobianNormalization
public import Section7.Imported.JacobianEtale

@[expose] public section

/-! The actual etale algebra of a square polynomial system: quotient by the
equations and invert its Jacobian. No etaleness or root-lifting conclusion
is assumed as a presentation field. -/

open MvPolynomial Algebra

namespace SpecialTransformations.Section7

variable {R : Type*} [CommRing R] {n : ℕ}

abbrev PolynomialSystemRing (F : Fin n → MvPolynomial (Fin n) R) :=
  MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range F)

noncomputable def polynomialSystemPresentation (F : Fin n → MvPolynomial (Fin n) R) :
    PreSubmersivePresentation R (PolynomialSystemRing F) (Fin n) (Fin n) :=
  PreSubmersivePresentation.naive (v := F) id Function.injective_id

theorem polynomialSystemPresentation_jacobian (F : Fin n → MvPolynomial (Fin n) R) :
    (polynomialSystemPresentation F).jacobian =
      Ideal.Quotient.mk (Ideal.span (Set.range F)) (jacobianPolynomial F) := by
  classical
  have hm : (polynomialSystemPresentation F).jacobiMatrix =
      (Matrix.of fun i j => pderiv j (F i)).transpose := by
    ext i j : 1
    rw [PreSubmersivePresentation.jacobiMatrix_apply]
    rfl
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hm, Matrix.det_transpose]
  rfl

@[simp] theorem polynomialSystemPresentation_dimension
    (F : Fin n → MvPolynomial (Fin n) R) : (polynomialSystemPresentation F).dimension = 0 := by
  simp [Presentation.dimension]

noncomputable abbrev PolynomialSystemEtaleRing (F : Fin n → MvPolynomial (Fin n) R) :=
  Localization.Away (polynomialSystemPresentation F).jacobian

instance polynomialSystemEtaleRing_etale (F : Fin n → MvPolynomial (Fin n) R) :
    Algebra.Etale R (PolynomialSystemEtaleRing F) := by
  have hs := Imported.JacobianEtale.localizationAway_standardSmooth
    (polynomialSystemPresentation F) (PolynomialSystemEtaleRing F)
  haveI : IsStandardSmoothOfRelativeDimension 0 R (PolynomialSystemEtaleRing F) := by
    simpa only [polynomialSystemPresentation_dimension] using hs
  infer_instance

noncomputable def polynomialSystemPoint {S : Type*} [CommRing S] [Algebra R S]
    (F : Fin n → MvPolynomial (Fin n) R) (a : Fin n → S)
    (hF : ∀ i, aeval a (F i) = 0) : PolynomialSystemRing F →ₐ[R] S :=
  Ideal.Quotient.liftₐ (Ideal.span (Set.range F)) (aeval a) (by
    change Ideal.span (Set.range F) ≤ RingHom.ker (aeval a).toRingHom
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hF i)

@[simp] theorem polynomialSystemPoint_mk {S : Type*} [CommRing S] [Algebra R S]
    (F : Fin n → MvPolynomial (Fin n) R) (a : Fin n → S)
    (hF : ∀ i, aeval a (F i) = 0) (p : MvPolynomial (Fin n) R) :
    polynomialSystemPoint F a hF (Ideal.Quotient.mk _ p) = aeval a p := rfl

theorem polynomialSystemPoint_jacobian {S : Type*} [CommRing S] [Algebra R S]
    (F : Fin n → MvPolynomial (Fin n) R) (a : Fin n → S)
    (hF : ∀ i, aeval a (F i) = 0) :
    polynomialSystemPoint F a hF (polynomialSystemPresentation F).jacobian =
      aeval a (jacobianPolynomial F) := by
  rw [polynomialSystemPresentation_jacobian, polynomialSystemPoint_mk]

noncomputable def polynomialSystemVariable (F : Fin n → MvPolynomial (Fin n) R) (i : Fin n) :
    PolynomialSystemEtaleRing F :=
  algebraMap (PolynomialSystemRing F) (PolynomialSystemEtaleRing F)
    (Ideal.Quotient.mk (Ideal.span (Set.range F)) (X i))

theorem polynomialSystemVariable_aeval (F : Fin n → MvPolynomial (Fin n) R)
    (p : MvPolynomial (Fin n) R) :
    aeval (polynomialSystemVariable F) p =
      algebraMap (PolynomialSystemRing F) (PolynomialSystemEtaleRing F) (Ideal.Quotient.mk _ p) := by
  have hh : aeval (polynomialSystemVariable F) =
      (IsScalarTower.toAlgHom R (PolynomialSystemRing F) (PolynomialSystemEtaleRing F)).comp
        (Ideal.Quotient.mkₐ R (Ideal.span (Set.range F))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [polynomialSystemVariable]
  exact AlgHom.congr_fun hh p

theorem polynomialSystemVariable_relation (F : Fin n → MvPolynomial (Fin n) R) (i : Fin n) :
    aeval (polynomialSystemVariable F) (F i) = 0 := by
  rw [polynomialSystemVariable_aeval]
  have hz : Ideal.Quotient.mk (Ideal.span (Set.range F)) (F i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  rw [hz, map_zero]

noncomputable def polynomialSystemEtalePoint {S : Type*} [CommRing S] [Algebra R S]
    (F : Fin n → MvPolynomial (Fin n) R) (a : Fin n → S)
    (hF : ∀ i, aeval a (F i) = 0) (hJ : IsUnit (aeval a (jacobianPolynomial F))) :
    PolynomialSystemEtaleRing F →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (polynomialSystemPresentation F).jacobian
    (f := polynomialSystemPoint F a hF) (by rwa [polynomialSystemPoint_jacobian])

@[simp] theorem polynomialSystemEtalePoint_variable {S : Type*} [CommRing S] [Algebra R S]
    (F : Fin n → MvPolynomial (Fin n) R) (a : Fin n → S)
    (hF : ∀ i, aeval a (F i) = 0) (hJ : IsUnit (aeval a (jacobianPolynomial F))) (i : Fin n) :
    polynomialSystemEtalePoint F a hF hJ (polynomialSystemVariable F i) = a i := by
  simp [polynomialSystemEtalePoint, polynomialSystemVariable, IsLocalization.Away.lift_eq]

theorem polynomialSystemHom_ext {S : Type*} [CommRing S] [Algebra R S]
    (F : Fin n → MvPolynomial (Fin n) R)
    {f g : PolynomialSystemEtaleRing F →ₐ[R] S}
    (h : ∀ i, f (polynomialSystemVariable F i) = g (polynomialSystemVariable F i)) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (polynomialSystemPresentation F).jacobian)
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  exact h i

end SpecialTransformations.Section7
