/-
Attributed excerpt of Nyll/SchemeTheory/NoetherNormalization/Trdeg.lean.
Upstream n-yamaguchi-0729/NYLL, revision 2e9f92dc5fbeacd17189dcf0cdb499f528dfd77c.
The three initial theorems are retained with their original namespace and proofs.
The unused generator-refinement import is omitted. See NYLL-LICENSE and NYLL-NOTICE.
-/
/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.NoetherNormalization

/-!
# Field Arithmetic, Proposition 6.2.1: Noether normalization

This file connects mathlib's Noether normalization theorem with the
transcendence degree of the quotient field.  This is the first source-producing
step toward the full generator-sensitive statement in Fried--Jarden.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06

open Algebra Function

universe u

variable (K A : Type u)
variable [Field K] [CommRing A] [IsDomain A] [Algebra K A]

/-- Passing from a domain to its fraction field does not change transcendence degree. -/
theorem trdeg_fractionRing :
    trdeg K (FractionRing A) = trdeg K A := by
  let : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic (FractionRing A) (nonZeroDivisors A)
  have hzero : trdeg A (FractionRing A) = 0 := trdeg_eq_zero
  have h : trdeg K A + trdeg A (FractionRing A) = trdeg K (FractionRing A) :=
    trdeg_add_eq K A (A := FractionRing A)
  rw [hzero, add_zero] at h
  exact h.symm

/--
An injective integral map from a polynomial ring has as many variables as the
transcendence degree of its target.
-/
theorem trdeg_eq_of_injective_isIntegral {r : ℕ}
    (g : MvPolynomial (Fin r) K →ₐ[K] A) (hg : Injective g) (hint : g.IsIntegral) :
    trdeg K A = r := by
  algebraize [g.toRingHom]
  let : FaithfulSMul (MvPolynomial (Fin r) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  let : Algebra.IsIntegral (MvPolynomial (Fin r) K) A := ⟨hint⟩
  have hzero : trdeg (MvPolynomial (Fin r) K) A = 0 := trdeg_eq_zero
  have h : trdeg K (MvPolynomial (Fin r) K) +
      trdeg (MvPolynomial (Fin r) K) A = trdeg K A :=
    trdeg_add_eq K (MvPolynomial (Fin r) K) (A := A)
  rw [hzero, add_zero] at h
  simpa using h.symm

/--
A Noether normalization whose number of variables is the transcendence degree
of the quotient field.

The remaining part of Fried--Jarden Proposition 6.2.1 is the refinement relative
to a prescribed finite generating family, including the linear choice over an
infinite field.
-/
theorem exists_normalization_with_trdeg [Algebra.FiniteType K A] :
    Exists fun r : ℕ =>
      Exists fun g : MvPolynomial (Fin r) K →ₐ[K] A =>
        Injective g ∧ g.IsIntegral ∧ trdeg K (FractionRing A) = r := by
  obtain ⟨r, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg K A
  refine ⟨r, g, hg, hint, ?_⟩
  rw [trdeg_fractionRing K A]
  exact trdeg_eq_of_injective_isIntegral K A g hg hint

end Chapter06
end FieldArithmetic
