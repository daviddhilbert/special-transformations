/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in TauCeti-LICENSE.
Authors: The Tau Ceti contributors
-/
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Smoothness after inverting a presentation's Jacobian

Attributed excerpt of TauCeti/RingTheory/Smooth/Jacobian.lean at
e8758b7b2f82b9b1c3f33b992ab8f499b510240f, Git blob
d93a555d3d7e595becbd8c8a5203197179270aca. Only the localization theorem
is retained, with namespace/imports adapted to pinned Mathlib. The unrelated
cotangent-basis criterion and its dependencies are excluded.
-/

namespace SpecialTransformations.Section7.Imported.JacobianEtale

open Algebra

theorem localizationAway_standardSmooth
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Finite ι] [Finite σ] (P : PreSubmersivePresentation R S ι σ)
    (T : Type*) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalization.Away P.jacobian T] :
    IsStandardSmoothOfRelativeDimension P.dimension R T := by
  let Q := PreSubmersivePresentation.localizationAway T P.jacobian
  let QP : SubmersivePresentation R T (Unit ⊕ ι) (Unit ⊕ σ) :=
    { Q.comp P with
      jacobian_isUnit := by
        rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def, PreSubmersivePresentation.localizationAway_jacobian]
        exact (IsLocalization.Away.algebraMap_isUnit P.jacobian).mul
          (IsLocalization.Away.algebraMap_isUnit P.jacobian) }
  apply QP.isStandardSmoothOfRelativeDimension
  exact (Q.dimension_comp_eq_dimension_add_dimension P).trans (by
    simp [Presentation.dimension])

end SpecialTransformations.Section7.Imported.JacobianEtale
