module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in TauCeti-LICENSE.
Authors: The Tau Ceti contributors
-/
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Unramified.LocalStructure

@[expose] public section

/-!
# Existence of lifts of residue points of etale algebras

Attributed excerpt of TauCeti/RingTheory/Henselian/Etale.lean at
e8758b7b2f82b9b1c3f33b992ab8f499b510240f (git blob
79fbca52ee56d6c9984bb8d04e0c46f85da7fb10).

Only the standard-etale existence proof and the surjectivity half of the
general theorem are retained. The uniqueness half and all other Tau Ceti
dependencies are excluded. Imports and namespace are adapted to this
project's pinned Mathlib; no external library version is assumed.

This is a generic theorem about genuine Mathlib henselian local rings,
not an RV lifting or generalized-Hensel hypothesis.
-/

open IsLocalRing Polynomial

namespace SpecialTransformations.Section7.Imported.EtaleLifting

variable {R S : Type*} [CommRing R] [HenselianLocalRing R] [CommRing S] [Algebra R S]

private theorem comp_surjective_of_isStandardEtale [Algebra.IsStandardEtale R S] :
    Function.Surjective
      ((Algebra.ofId R (ResidueField R)).comp : (S →ₐ[R] R) → S →ₐ[R] ResidueField R) := by
  intro ψ
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := R) (S := S)
  have hres (a : R) (p : R[X]) : residue R (aeval a p) = aeval (residue R a) p := by
    rw [← ResidueField.algebraMap_eq, aeval_algebraMap_apply]
  have hy := P.hasMap.map ψ
  obtain ⟨a₀, ha₀⟩ := residue_surjective (ψ P.x)
  obtain ⟨a, ha, haa₀⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a₀
    (by rw [← residue_eq_zero_iff, ← coe_aeval_eq_eval, hres, ha₀]; exact hy.1)
    (by
      rw [← residue_ne_zero_iff_isUnit, ← coe_aeval_eq_eval, hres, ha₀]
      exact hy.isUnit_derivative_f.ne_zero)
  have hra : residue R a = ψ P.x := by
    rw [← ha₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact haa₀
  have hP : P.HasMap a := by
    refine ⟨ha, ?_⟩
    rw [← residue_ne_zero_iff_isUnit, hres, hra]
    exact hy.2.ne_zero
  refine ⟨(P.lift a hP).comp P.equivRing.toAlgHom, P.hom_ext ?_⟩
  simp [hra]

/-- Every residue-field point of an etale algebra over a henselian local ring
lifts to a point over the ring itself. No uniqueness conclusion is assumed. -/
theorem residuePoint_lifts [Algebra.Etale R S] :
    Function.Surjective
      ((Algebra.ofId R (ResidueField R)).comp : (S →ₐ[R] R) → S →ₐ[R] ResidueField R) := by
  intro ψ
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨g, hg, _⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) (RingHom.ker ψ)
  have hg : IsUnit (ψ g) := isUnit_iff_ne_zero.mpr fun h => hg (RingHom.mem_ker.mpr h)
  let ψ' : Localization.Away g →ₐ[R] ResidueField R :=
    IsLocalization.liftAlgHom (M := .powers g) (f := ψ) fun ⟨_, n, hn⟩ => hn ▸ by
      simpa using hg.pow n
  obtain ⟨φ, hφ⟩ := comp_surjective_of_isStandardEtale ψ'
  refine ⟨φ.comp (IsScalarTower.toAlgHom R S _), AlgHom.ext fun s => ?_⟩
  simpa [ψ'] using AlgHom.congr_fun hφ (algebraMap S _ s)

end SpecialTransformations.Section7.Imported.EtaleLifting
