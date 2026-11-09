import Section9.SimpleRootEquations
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.Radical

/-! Squarefree equations for finite correspondences over independent inputs. -/

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section9

open MvPolynomial UniqueFactorizationMonoid

/-- A polynomial equation for a finite correspondence can be replaced by
one that retains all its zeros and is simple over independent input
coordinates. Remove repeated factors over the fraction field of the
input polynomial ring, then clear denominators. -/
theorem exists_global_simpleRoot_equation
    {E K ι : Type*} [Field E] [Field K] [Algebra E K] [CharZero E]
    (P : Polynomial (MvPolynomial ι E)) (hP : P ≠ 0) :
    ∃ Q : Polynomial (MvPolynomial ι E),
      (∀ (x : ι → K) (y : K), (P.map (aeval x).toRingHom).eval y = 0 →
        (Q.map (aeval x).toRingHom).eval y = 0) ∧
      (∀ (x : ι → K) (y : K), AlgebraicIndependent E x →
        (P.map (aeval x).toRingHom).eval y = 0 →
        (Q.map (aeval x).toRingHom).derivative.eval y ≠ 0) := by
  classical
  let A := MvPolynomial ι E
  let F := FractionRing A
  let i : A →+* F := algebraMap A F
  have hi : Function.Injective i := IsFractionRing.injective A F
  have hcoeff (c : F) : ∃ a b : A, i b ≠ 0 ∧ i a = (RingHom.id F) c * i b := by
    obtain ⟨a, b, hb, he⟩ := IsFractionRing.div_surjective (A := A) c
    have hb' : i b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    exact ⟨a, b, hb', (div_eq_iff hb').mp he⟩
  let P' := P.map i
  have hp' : P' ≠ 0 := fun h => hP ((Polynomial.map_injective i hi)
    (h.trans (Polynomial.map_zero i).symm))
  let R := radical P'
  have hsep : R.Separable := PerfectField.separable_iff_squarefree.mpr squarefree_radical
  obtain ⟨Q, b, hb, hQ⟩ :=
    exists_polynomial_clearDenominators i (RingHom.id F) hcoeff R
  have hQ' : Q.map i = Polynomial.C (i b) * R := by
    simpa only [Polynomial.map_id] using hQ
  obtain ⟨N, hN⟩ := exists_dvd_radical_self_pow hp'
  have hdiv : P' ∣ (Q.map i) ^ N := by
    rw [hQ', mul_pow]
    exact dvd_mul_of_dvd_right hN _
  obtain ⟨W, hW⟩ := hdiv
  obtain ⟨S, d, hd, hS⟩ :=
    exists_polynomial_clearDenominators i (RingHom.id F) hcoeff W
  have hS' : S.map i = Polynomial.C (i d) * W := by
    simpa only [Polynomial.map_id] using hS
  have hIdentity : Polynomial.C d * Q ^ N = P * S := by
    apply Polynomial.map_injective i hi
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, hS']
    rw [show P.map i = P' from rfl, hW]
    ac_rfl
  have hconst (x : ι → K) (y : K) :
      ((Polynomial.C d).map (aeval x).toRingHom).eval y = aeval x d := by
    rw [Polynomial.eval_map, Polynomial.eval₂_C]
    rfl
  have hz (x : ι → K) (y : K) (hroot : (P.map (aeval x).toRingHom).eval y = 0) :
      aeval x d = 0 ∨ (Q.map (aeval x).toRingHom).eval y = 0 := by
    have h := congrArg (fun p : Polynomial A => (p.map (aeval x).toRingHom).eval y) hIdentity
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.eval_mul,
      hconst, Polynomial.eval_pow, hroot, zero_mul] at h
    exact (mul_eq_zero.mp h).imp id (fun h => eq_zero_of_pow_eq_zero h)
  refine ⟨Polynomial.C d * Q, fun x y hroot => ?_, fun x y hx hroot => ?_⟩
  · simp only [Polynomial.map_mul, Polynomial.eval_mul, hconst]
    exact mul_eq_zero.mpr (hz x y hroot)
  · have hxinj : Function.Injective (aeval (R := E) x).toRingHom := hx
    let f : F →+* K := IsFractionRing.lift (K := F) hxinj
    have hf (a : A) : f (i a) = aeval x a := IsFractionRing.lift_algebraMap hxinj a
    have hcomp : f.comp i = (aeval x).toRingHom := RingHom.ext hf
    have hQx : Q.map (aeval x).toRingHom = Polynomial.C (aeval x b) * R.map f := by
      have h := congrArg (Polynomial.map f) hQ'
      simpa only [Polynomial.map_map, hcomp, Polynomial.map_mul, Polynomial.map_C, hf] using h
    have hd' : aeval x d ≠ 0 := fun h => hd (by rw [hxinj (h.trans (map_zero (aeval x)).symm), map_zero])
    have hb' : aeval x b ≠ 0 := fun h => hb (by rw [hxinj (h.trans (map_zero (aeval x)).symm), map_zero])
    have hrootQ := (hz x y hroot).resolve_left hd'
    rw [hQx, Polynomial.eval_mul, Polynomial.eval_C] at hrootQ
    have hrootR : (R.map f).eval y = 0 := (mul_eq_zero.mp hrootQ).resolve_left hb'
    rw [Polynomial.map_mul, Polynomial.map_C, hQx, Polynomial.derivative_C_mul,
      Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_C]
    have hsR : (R.map f).Separable := hsep.map
    have haeval (p : Polynomial K) : Polynomial.aeval y p = p.eval y := by
      rw [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
    have hderiv := hsR.aeval_derivative_ne_zero (show Polynomial.aeval y (R.map f) = 0 by
      rw [haeval]; exact hrootR)
    rw [haeval] at hderiv
    exact mul_ne_zero hd' (mul_ne_zero hb' hderiv)

section OutputVariable

variable {E K ι : Type*} [Field E] [Field K] [Algebra E K]

private theorem putOutputVariable_surjective :
    Function.Surjective (putOutputVariable (E := E) (ι := ι)) := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C a =>
    exact ⟨Polynomial.C (C a), by simp [putOutputVariable]⟩
  | add P Q hP hQ =>
    obtain ⟨p, hp⟩ := hP
    obtain ⟨q, hq⟩ := hQ
    exact ⟨p + q, by simpa only [putOutputVariable, Polynomial.eval₂_add] using congrArg₂ (· + ·) hp hq⟩
  | mul_X P j hP =>
    obtain ⟨p, hp⟩ := hP
    rcases j with j | ⟨⟩
    · exact ⟨p * Polynomial.C (X j), by
        rw [putOutputVariable, Polynomial.eval₂_mul, Polynomial.eval₂_C]
        change putOutputVariable p * rename Sum.inl (X j) = _
        rw [hp, rename_X]⟩
    · exact ⟨p * Polynomial.X, by
        simpa only [putOutputVariable, Polynomial.eval₂_mul, Polynomial.eval₂_X] using
          congrArg (fun q => q * X (.inr ())) hp⟩

/-- Multivariate form of the global equation with simple output roots.
It applies to the single nonzero polynomial supplied by the residue
polynomial cover. -/
theorem exists_global_simpleRoot_mvPolynomial [CharZero E]
    (P : MvPolynomial (ι ⊕ Unit) E) (hP : P ≠ 0) :
    ∃ Q : MvPolynomial (ι ⊕ Unit) E,
      (∀ (x : ι → K) (y : K), aeval (Sum.elim x (fun _ => y)) P = 0 →
        aeval (Sum.elim x (fun _ => y)) Q = 0) ∧
      (∀ (x : ι → K) (y : K), AlgebraicIndependent E x →
        aeval (Sum.elim x (fun _ => y)) P = 0 →
        aeval (Sum.elim x (fun _ => y)) (pderiv (Sum.inr ()) Q) ≠ 0) := by
  obtain ⟨p, rfl⟩ := putOutputVariable_surjective P
  have hp : p ≠ 0 := fun h => hP (by rw [h]; simp [putOutputVariable])
  obtain ⟨q, hq, hq'⟩ := exists_global_simpleRoot_equation (K := K) p hp
  refine ⟨putOutputVariable q, fun x y h => ?_, fun x y hx h => ?_⟩
  · rw [aeval_putOutputVariable] at h ⊢
    exact hq x y h
  · rw [aeval_putOutputVariable] at h
    rw [aeval_pderiv_putOutputVariable]
    exact hq' x y hx h

end OutputVariable

end SpecialTransformations.Section9
