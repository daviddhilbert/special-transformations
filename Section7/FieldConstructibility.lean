import ProvedACFExtension
import Mathlib.ModelTheory.Definability
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet

/-!
# Constructible sets over the original coefficient field

The released pure-ACF QE is reused, not reproved. Quantifier-free ring terms
are evaluated in the polynomial ring over the parameter subfield; Boolean
operations then produce an actual constructible subset of its prime spectrum.
Field tuples are compared with this subset through their evaluation kernels.
The bounded-formula parameter conversion follows the local MIT
Section4/PureFieldAlgebraicity.lean, preserving the original parameter set.
-/

open FirstOrder FirstOrder.Language Topology

namespace SpecialTransformations.Section7

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

variable {K : Type} [Field K] (E : Subfield K) {n : ℕ}

noncomputable def ringTermPolynomial (t : Language.ring.Term (E ⊕ Fin n)) :
    MvPolynomial (Fin n) E := t.realize (Sum.elim MvPolynomial.C MvPolynomial.X)

theorem eval_ringTermPolynomial (t : Language.ring.Term (E ⊕ Fin n)) (a : Fin n → K) :
    MvPolynomial.eval₂ E.subtype a (ringTermPolynomial E t) =
      t.realize (Sum.elim E.subtype a) := by
  induction t with
  | var j => cases j <;> simp [ringTermPolynomial]
  | func f ts ih => cases f <;> simp_all [ringTermPolynomial, Term.realize]

noncomputable def fieldTuplePrime (a : Fin n → K) : PrimeSpectrum (MvPolynomial (Fin n) E) :=
  ⟨RingHom.ker (MvPolynomial.eval₂Hom E.subtype a), RingHom.ker_isPrime _⟩

theorem fieldTuplePrime_mem_zeroLocus (a : Fin n → K) (p : MvPolynomial (Fin n) E) :
    fieldTuplePrime E a ∈ PrimeSpectrum.zeroLocus {p} ↔ MvPolynomial.eval₂ E.subtype a p = 0 := by
  simp [PrimeSpectrum.mem_zeroLocus, fieldTuplePrime, RingHom.mem_ker]

theorem isConstructible_polynomial_zeroLocus (p : MvPolynomial (Fin n) E) :
    IsConstructible (PrimeSpectrum.zeroLocus {p}) := by
  rw [← isConstructible_compl]
  exact (PrimeSpectrum.isRetrocompact_zeroLocus_compl (Set.finite_singleton p)).isConstructible
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

theorem qf_ring_constructible (φ : Language.ring.BoundedFormula E n) (hq : φ.IsQF) :
    ∃ C : Set (PrimeSpectrum (MvPolynomial (Fin n) E)), IsConstructible C ∧
      ∀ a : Fin n → K, φ.Realize E.subtype a ↔ fieldTuplePrime E a ∈ C := by
  induction hq with
  | falsum => exact ⟨∅, IsConstructible.empty, fun _ => Iff.rfl⟩
  | of_isAtomic ha =>
    cases ha with
    | equal t u =>
      refine ⟨PrimeSpectrum.zeroLocus {ringTermPolynomial E t - ringTermPolynomial E u},
        isConstructible_polynomial_zeroLocus E _, ?_⟩
      intro a
      change t.realize (Sum.elim E.subtype a) = u.realize (Sum.elim E.subtype a) ↔ _
      rw [fieldTuplePrime_mem_zeroLocus, MvPolynomial.eval₂_sub, eval_ringTermPolynomial,
        eval_ringTermPolynomial, sub_eq_zero]
    | rel r ts => cases r
  | @imp φ ψ hφ hψ ihφ ihψ =>
    obtain ⟨C, hC, heC⟩ := ihφ
    obtain ⟨D, hD, heD⟩ := ihψ
    refine ⟨Cᶜ ∪ D, hC.compl.union hD, ?_⟩
    intro a
    simp only [BoundedFormula.realize_imp, heC, heD, Set.mem_union, Set.mem_compl_iff,
      imp_iff_not_or]

private theorem bounded_formula_of_definable {L : Language} {T : Type} [L.Structure T]
    {S : Set T} {n : ℕ} {A : Set (Fin n → T)} (hA : S.Definable L A) :
    ∃ φ : L.BoundedFormula S n, ∀ x, φ.Realize Subtype.val x ↔ x ∈ A := by
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hA
  refine ⟨BoundedFormula.relabel id φ, ?_⟩
  intro x
  rw [BoundedFormula.realize_relabel]
  have hv : Sum.elim (Subtype.val : S → T) (x ∘ Fin.castAdd 0) ∘ id =
      Sum.elim (Subtype.val : S → T) x := by
    funext u
    cases u <;> rfl
  have hx : (x ∘ Fin.natAdd n : Fin 0 → T) = default := Subsingleton.elim _ _
  rw [hv, hx]
  change φ.Realize (Sum.elim Subtype.val x) ↔ x ∈ A
  exact (Iff.of_eq (congrArg (fun U => x ∈ U) hφ)).symm

theorem field_definable_constructible [IsAlgClosed K] (D : Set (Fin n → K))
    (hD : (E : Set K).Definable Language.ring D) :
    ∃ C : Set (PrimeSpectrum (MvPolynomial (Fin n) E)), IsConstructible C ∧
      ∀ a : Fin n → K, a ∈ D ↔ fieldTuplePrime E a ∈ C := by
  obtain ⟨φ, hφ⟩ := bounded_formula_of_definable hD
  obtain ⟨ψ, hq, heq⟩ := ProvedACFExtension.fullQE E n φ
  obtain ⟨C, hC, hreal⟩ := qf_ring_constructible E ψ hq
  refine ⟨C, hC, ?_⟩
  intro a
  exact (hφ a).symm.trans ((heq K inferInstance E.subtype a).trans (hreal a))

end SpecialTransformations.Section7
