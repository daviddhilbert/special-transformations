import Section9.RVJacobian
import Section9.RVJacobianDerivations
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Section4.ResidueMultivariateFunctions
import ProvedACFExtension

/-! Descend the equations used to test a residue tangent to a coefficient
field. Over an elementary coefficient field the definable set's points
in that field test every equation with coefficients there. Expanding an
arbitrary residue polynomial along a vector-space basis reduces its
tangent test to those equations. -/

set_option backward.isDefEq.respectTransparency false

open MvPolynomial FirstOrder FirstOrder.Language
open SpecialTransformations.Section4.ResiduePurity
open scoped BigOperators

namespace SpecialTransformations.Section9

section Algebraic

variable {E K : Type*} [Field E] [Field K] [Algebra E K] {d : ℕ}

theorem isPolynomialTangent_of_base_equations
    (C : Set (Fin d → K)) (p h : Fin d → K)
    (hbase : ∀ Q : MvPolynomial (Fin d) E,
      (∀ x : Fin d → E, (algebraMap E K ∘ x) ∈ C → Q.eval x = 0) →
      ∀ x ∈ C, aeval x Q = 0)
    (hrel : ∀ Q : MvPolynomial (Fin d) E, (∀ x ∈ C, aeval x Q = 0) →
      ∑ i, aeval p (pderiv i Q) * h i = 0) :
    IsPolynomialTangent C p h := by
  classical
  intro P hP
  let I := Module.Free.ChooseBasisIndex E K
  let b : Module.Basis I E K := Module.Free.chooseBasis E K
  let J := P.support.biUnion (fun m => (b.repr (P.coeff m)).support)
  let Q (j : I) : MvPolynomial (Fin d) E :=
    ∑ m ∈ P.support, monomial m (b.repr (P.coeff m) j)
  have hQ (j : I) (m : Fin d →₀ ℕ) : (Q j).coeff m = b.repr (P.coeff m) j := by
    change (∑ l ∈ P.support, monomial l (b.repr (P.coeff l) j)).coeff m = _
    rw [coeff_sum]
    by_cases hm : m ∈ P.support
    · rw [Finset.sum_eq_single_of_mem m hm]
      · simp
      · intro l _ hne
        simp [coeff_monomial, hne]
    · rw [notMem_support_iff.mp hm, map_zero, Finsupp.zero_apply]
      apply Finset.sum_eq_zero
      intro l hl
      have hlm : l ≠ m := fun he => hm (he ▸ hl)
      simp only [coeff_monomial, if_neg hlm]
  have hsplit : P = ∑ j ∈ J, MvPolynomial.C (b j) * (Q j).map (algebraMap E K) := by
    apply MvPolynomial.ext
    intro m
    simp only [coeff_sum, coeff_C_mul, coeff_map, hQ]
    by_cases hm : m ∈ P.support
    · let r := b.repr (P.coeff m)
      have hr : r.support ⊆ J :=
        Finset.subset_biUnion_of_mem (fun m => (b.repr (P.coeff m)).support) hm
      have hsum : ∑ j ∈ J, r j • b j = P.coeff m := by
        rw [← Finset.sum_subset hr (fun j _ hj => by
          rw [Finsupp.notMem_support_iff.mp hj, zero_smul])]
        simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
          b.linearCombination_repr (P.coeff m)
      simpa only [r, Algebra.smul_def, mul_comm] using hsum.symm
    · rw [notMem_support_iff.mp hm]
      simp
  have hzero (j : I) (hj : j ∈ J) : ∀ x ∈ C, aeval x (Q j) = 0 := by
    apply hbase
    intro x hx
    have hv (j : I) : ((Q j).map (algebraMap E K)).eval (algebraMap E K ∘ x) =
        algebraMap E K ((Q j).eval x) := by
      rw [eval_map]
      exact (eval₂_comp (algebraMap E K) x (Q j)).symm
    have h := hP _ hx
    rw [hsplit, map_sum] at h
    simp only [map_mul, eval_C, hv] at h
    have hsum : (∑ j ∈ J, (Q j).eval x • b j) = 0 := by
      simpa only [Algebra.smul_def, mul_comm] using h
    have he := linearIndependent_iff'ₛ.mp b.linearIndependent J
      (fun j => (Q j).eval x) (fun _ => 0) (by simpa only [zero_smul, Finset.sum_const_zero] using hsum)
      j hj
    exact he
  rw [hsplit]
  simp only [map_sum, Finset.sum_mul, pderiv_mul, pderiv_C, zero_mul, zero_add,
    map_mul, eval_C, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  rw [← Finset.mul_sum]
  simp only [pderiv_map, eval_map, ← aeval_def, hrel (Q j) (hzero j hj), mul_zero]

end Algebraic

variable {K : Type} [Field K] {d : ℕ}

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- Quantifier elimination puts a point of any nonempty definable set
over an algebraically closed coefficient field back in that field. -/
private theorem exists_point_over_algClosed_subfield [IsAlgClosed K]
    (E : Subfield K) [IsAlgClosed E]
    (D : Set (Fin d → K)) (hD : Relative.Def E D) (hne : D.Nonempty) :
    ∃ x : Fin d → E, (E.subtype ∘ x) ∈ D := by
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hD
  let θ : Language.ring.BoundedFormula E d := BoundedFormula.relabel id φ
  have hθ (x : Fin d → K) : θ.Realize E.subtype x ↔ x ∈ D := by
    change (BoundedFormula.relabel id φ).Realize E.subtype x ↔ _
    rw [BoundedFormula.realize_relabel]
    have he : Sum.elim (E.subtype : E → K) (x ∘ Fin.castAdd 0) ∘ id =
        Sum.elim (E.subtype : E → K) x := by
      funext u
      cases u <;> rfl
    rw [he, show x ∘ Fin.natAdd d = (default : Fin 0 → K) from Subsingleton.elim _ _]
    exact (Iff.of_eq (congrArg (fun A => x ∈ A) hφ)).symm
  obtain ⟨ψ, hψ, hqe⟩ := ProvedACFExtension.fullQE E 0 θ.exs
  let e : E ↪[Language.ring] K :=
    ACFValidation.embeddingOfInjectiveRingHom E.subtype Subtype.val_injective
  have hQ : ψ.Realize E.subtype default ↔ ψ.Realize (id : E → E) default := by
    have h := QESaturatedExtension.embedding_realize_isQF e hψ (id : E → E)
      (default : Fin 0 → E)
    change ψ.Realize (E.subtype ∘ id) (E.subtype ∘ (default : Fin 0 → E)) ↔ _ at h
    rw [Function.comp_id, Subsingleton.elim (E.subtype ∘ (default : Fin 0 → E)) default] at h
    exact h
  have hK : θ.exs.Realize E.subtype := BoundedFormula.realize_exs.mpr
    ⟨hne.choose, (hθ _).mpr hne.choose_spec⟩
  have hE : θ.exs.Realize (id : E → E) :=
    (hqe E inferInstance id default).mpr (hQ.mp ((hqe K inferInstance E.subtype default).mp hK))
  obtain ⟨x, hx⟩ := BoundedFormula.realize_exs.mp hE
  have hcast : θ.Realize E.subtype (E.subtype ∘ x) := by
    obtain ⟨ψ, hψ, hqe⟩ := ProvedACFExtension.fullQE E d θ
    apply (hqe K inferInstance E.subtype (E.subtype ∘ x)).mpr
    exact (QESaturatedExtension.embedding_realize_isQF e hψ id x).mpr
      ((hqe E inferInstance id x).mp hx)
  exact ⟨x, (hθ _).mp hcast⟩

theorem isPolynomialTangent_of_definable_base_equations [IsAlgClosed K]
    (E : Subfield K) [IsAlgClosed E]
    (C : Set (Fin d → K)) (hC : Relative.Def E C) (p h : Fin d → K)
    (hrel : ∀ Q : MvPolynomial (Fin d) E, (∀ x ∈ C, aeval x Q = 0) →
      ∑ i, aeval p (pderiv i Q) * h i = 0) :
    IsPolynomialTangent C p h := by
  apply isPolynomialTangent_of_base_equations C p h _ hrel
  intro Q hQ x hx
  by_contra hn
  let D := C ∩ {z | Q.eval₂ E.subtype z = 0}ᶜ
  have hD : Relative.Def E D := hC.inter (mvPolynomial_zeroSet_definable E Q).compl
  have hxD : x ∈ D := ⟨hx, hn⟩
  obtain ⟨z, hz⟩ := exists_point_over_algClosed_subfield E D hD ⟨x, hxD⟩
  have hzero := hQ z hz.1
  exact hz.2 (by
    change Q.eval₂ E.subtype (E.subtype ∘ z) = 0
    rw [← eval₂_comp, hzero, map_zero])

/-- The derivative of the coordinates over the coefficient field is
tangent to a definable residue correspondence. The derivation may
take values in the field of the point. -/
theorem isPolynomialTangent_of_residue_derivation [IsAlgClosed K]
    (E : Subfield K) [IsAlgClosed E]
    {F : Type*} [Field F] [Algebra E F] (f : F →ₐ[E] K)
    (C : Set (Fin d → K)) (hC : Relative.Def E C)
    (p : Fin d → F) (hp : f ∘ p ∈ C) (D : Derivation E F F) :
    IsPolynomialTangent C (f ∘ p) (f ∘ D ∘ p) := by
  apply isPolynomialTangent_of_definable_base_equations E C hC
  intro Q hQ
  have he (P : MvPolynomial (Fin d) E) : f (aeval p P) = aeval (f ∘ p) P :=
    comp_aeval_apply p f P
  have hzero : aeval p Q = 0 := f.injective
    ((he Q).trans ((hQ _ hp).trans (map_zero f).symm))
  have h := derivation_aeval_eq_sum D p Q
  rw [hzero, map_zero] at h
  simpa only [map_sum, map_mul, he, map_zero, Function.comp_apply] using congrArg f h.symm

end SpecialTransformations.Section9
