/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in TauCeti-LICENSE.
Authors: The Tau Ceti contributors
-/
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Unramified.Finite

/-!
# Uniqueness of unramified sections modulo a Jacobson-radical ideal

Attributed excerpt of TauCeti/RingTheory/Unramified/Diagonal.lean at
e8758b7b2f82b9b1c3f33b992ab8f499b510240f, Git blob
19673df2b1f9907b76e83839e40345295bb3e214. Three diagonal arguments are
retained and adapted to pinned Mathlib. The tensor-product quotient helper
is proved here by tensor induction; no further Tau Ceti dependency is used.
No nilpotence, completeness or adic-separatedness assumption is introduced.
-/

open scoped TensorProduct

namespace SpecialTransformations.Section7.Imported.UnramifiedUniqueness

private theorem productMap_mem_of_comp_eq
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    {e : S ⊗[R] S} (he : Algebra.TensorProduct.lmul' R e = 0)
    (J : Ideal T) {f g : S →ₐ[R] T}
    (hfg : (Ideal.Quotient.mkₐ R J).comp f = (Ideal.Quotient.mkₐ R J).comp g) :
    Algebra.TensorProduct.productMap f g e ∈ J := by
  let q := Ideal.Quotient.mkₐ R J
  have hpoint (b : S) : q (f b) = q (g b) := AlgHom.congr_fun hfg b
  have h (x : S ⊗[R] S) : q (Algebra.TensorProduct.productMap f g x) =
      q (f (Algebra.TensorProduct.lmul' R x)) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [Algebra.TensorProduct.productMap_apply_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
      rw [← hpoint b]
    | add a b ha hb => simp only [map_add, ha, hb]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (Algebra.TensorProduct.productMap f g e) = 0
  rw [h, he, map_zero, map_zero]

theorem exists_idempotent_diagonal (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    ∃ e : S ⊗[R] S, IsIdempotentElem e ∧
      RingHom.ker (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toRingHom =
        Ideal.span {e} :=
  (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R S)).mp <|
    (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton Ω[S⁄R]

theorem comp_eq_comp_of_isUnit {R S T U : Type*}
    [CommSemiring R] [CommRing S] [CommRing T] [Ring U]
    [Algebra R S] [Algebra R T] [Algebra R U] {e : S ⊗[R] S} (he : IsIdempotentElem e)
    (hker : RingHom.ker (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toRingHom ≤
      Ideal.span {e}) (f g : S →ₐ[R] T) (h : T →ₐ[R] U)
    (hu : IsUnit (h (1 - Algebra.TensorProduct.productMap f g e))) :
    h.comp f = h.comp g := by
  ext b
  rw [AlgHom.comp_apply, AlgHom.comp_apply, ← sub_eq_zero, ← map_sub]
  have hdiff : f b - g b = Algebra.TensorProduct.productMap f g (b ⊗ₜ[R] 1 - 1 ⊗ₜ[R] b) := by
    simp
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp
    (hker (by simp : b ⊗ₜ[R] 1 - 1 ⊗ₜ[R] b ∈ RingHom.ker _))
  rw [hdiff, ← ha, map_mul, map_mul]
  suffices h (Algebra.TensorProduct.productMap f g e) = 0 by rw [this, mul_zero]
  have hidem : IsIdempotentElem (h (Algebra.TensorProduct.productMap f g e)) := (he.map _).map h
  exact hu.mul_left_eq_zero.mp (by simpa only [map_sub, map_one] using hidem.mul_one_sub_self)

theorem ext_of_quotient_eq (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    {T : Type*} [CommRing T] [Algebra R T] (J : Ideal T) (hJ : J ≤ Ideal.jacobson ⊥)
    {f g : S →ₐ[R] T}
    (hfg : (Ideal.Quotient.mkₐ R J).comp f = (Ideal.Quotient.mkₐ R J).comp g) : f = g := by
  obtain ⟨e, he, hker⟩ := exists_idempotent_diagonal R S
  have hpe := productMap_mem_of_comp_eq
    (RingHom.mem_ker.mp (hker ▸ Ideal.mem_span_singleton_self e)) J hfg
  have hu : IsUnit (1 - Algebra.TensorProduct.productMap f g e) := by
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    simpa only [sub_sub_cancel_left, Ideal.jacobson_bot] using hJ (J.neg_mem hpe)
  simpa only [AlgHom.id_comp] using comp_eq_comp_of_isUnit he hker.le f g (AlgHom.id R T) hu

end SpecialTransformations.Section7.Imported.UnramifiedUniqueness
