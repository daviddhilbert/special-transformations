module

public import Section4.ResidueMultivariateFunctions
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-! Evaluation and partial differentiation for a fixed finite list of
monomials, with the coefficients supplied as residue-field variables.
These are the uniform formulas used in polynomial chart certificates. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Section4.ResiduePurity

namespace SpecialTransformations.Section9

variable {K : Type} [Field K] {a d : ℕ}
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

noncomputable def polynomialOfCoefficients (e : Fin a → Fin d →₀ ℕ) (c : Fin a → K) :
    MvPolynomial (Fin d) K := ∑ i, monomial (e i) (c i)

theorem exists_common_polynomial_support {m : ℕ} (P : Fin m → MvPolynomial (Fin d) K) :
    ∃ a : ℕ, ∃ e : Fin a → Fin d →₀ ℕ, ∃ c : Fin m → Fin a → K,
      ∀ j, polynomialOfCoefficients e (c j) = P j := by
  classical
  let U := Finset.univ.biUnion fun j => (P j).support
  let e := (Fintype.equivFin U).symm
  refine ⟨Fintype.card U, fun i => (e i).val, fun j i => (P j).coeff (e i).val, fun j => ?_⟩
  change (∑ i, monomial (e i).val ((P j).coeff (e i).val)) = P j
  rw [e.sum_comp (fun a => monomial a.val ((P j).coeff a.val))]
  calc
    _ = ∑ a ∈ U, monomial a ((P j).coeff a) :=
      Finset.sum_coe_sort U (fun a => monomial a ((P j).coeff a))
    _ = ∑ a ∈ (P j).support, monomial a ((P j).coeff a) :=
      (Finset.sum_subset
        (fun a ha => Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, ha⟩)
        (fun a _ ha => by rw [notMem_support_iff.mp ha, monomial_zero])).symm
    _ = _ := (P j).support_sum_monomial_coeff

theorem exists_polynomial_support (P : MvPolynomial (Fin d) K) :
    ∃ a : ℕ, ∃ e : Fin a → Fin d →₀ ℕ, ∃ c : Fin a → K,
      polynomialOfCoefficients e c = P := by
  obtain ⟨a, e, c, h⟩ := exists_common_polynomial_support (fun _ : Fin 1 => P)
  exact ⟨a, e, c 0, h 0⟩

private theorem relative_sum {I ι : Type} (E : Subfield K) (s : Finset I) (f : I → (ι → K) → K)
    (hf : ∀ i ∈ s, Relative.Fun E (f i)) : Relative.Fun E (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Relative.constant (ι := ι) 0 E.zero_mem
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem relative_prod {I ι : Type} (E : Subfield K) (s : Finset I) (f : I → (ι → K) → K)
    (hf : ∀ i ∈ s, Relative.Fun E (f i)) : Relative.Fun E (fun z => ∏ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using Relative.constant (ι := ι) 1 E.one_mem
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem relative_pow {ι : Type} {E : Subfield K} {f : (ι → K) → K}
    (hf : Relative.Fun E f) (n : ℕ) : Relative.Fun E (fun z => f z ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using Relative.constant (ι := ι) 1 E.one_mem
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem relative_eval_polynomialOfCoefficients (E : Subfield K) (e : Fin a → Fin d →₀ ℕ) :
    Relative.Fun E (fun z : Fin a ⊕ Fin d → K =>
      (polynomialOfCoefficients e (z ∘ Sum.inl)).eval (z ∘ Sum.inr)) := by
  simp only [polynomialOfCoefficients, map_sum, eval_monomial, Finsupp.prod, Function.comp_apply]
  apply relative_sum
  intro i _
  apply (Relative.projection (E := E) (Sum.inl i)).mul
  apply relative_prod
  intro j _
  exact relative_pow (Relative.projection (E := E) (Sum.inr j)) (e i j)

theorem relative_eval_pderiv_polynomialOfCoefficients (E : Subfield K)
    (e : Fin a → Fin d →₀ ℕ) (j : Fin d) :
    Relative.Fun E (fun z : Fin a ⊕ Fin d → K =>
      (pderiv j (polynomialOfCoefficients e (z ∘ Sum.inl))).eval (z ∘ Sum.inr)) := by
  simp only [polynomialOfCoefficients, map_sum, pderiv_monomial, eval_monomial, Finsupp.prod, Function.comp_apply]
  apply relative_sum
  intro i _
  have hc : (e i j : K) ∈ E := by
    have h : E.subtype (e i j : E) ∈ E := (e i j : E).property
    simpa only [map_natCast] using h
  apply ((Relative.projection (E := E) (Sum.inl i)).mul
    (Relative.constant (ι := Fin a ⊕ Fin d) (e i j : K) hc)).mul
  apply relative_prod
  intro l _
  exact relative_pow (Relative.projection (E := E) (Sum.inr (l : Fin d)))
    ((e i - Finsupp.single j 1 : Fin d →₀ ℕ) l)

theorem relative_det_of_entries {ι : Type} {n : ℕ} (E : Subfield K)
    (A : (ι → K) → Matrix (Fin n) (Fin n) K)
    (hA : ∀ i j, Relative.Fun E (fun z => A z i j)) :
    Relative.Fun E (fun z => (A z).det) := by
  classical
  simp only [Matrix.det_apply']
  apply relative_sum
  intro e _
  have he : (Equiv.Perm.sign e : K) ∈ E := by
    have h : E.subtype (Equiv.Perm.sign e : E) ∈ E := (Equiv.Perm.sign e : E).property
    simpa only [map_intCast] using h
  exact (Relative.constant (ι := ι) _ he).mul
    (relative_prod E Finset.univ (fun i z => A z (e i) i) (fun i _ => hA (e i) i))

theorem relative_eval_polynomialOfIndices {ι : Type} (E : Subfield K)
    (e : Fin a → Fin d →₀ ℕ) (c : Fin a → ι) (x : Fin d → ι) :
    Relative.Fun E (fun z : ι → K => (polynomialOfCoefficients e (z ∘ c)).eval (z ∘ x)) :=
  (relative_eval_polynomialOfCoefficients E e).comp
    (show (E : Set K).DefinableMap Language.ring (fun z : ι → K => z ∘ Sum.elim c x) from
      fun j => Relative.projection (E := E) (Sum.elim c x j))

theorem relative_eval_pderiv_polynomialOfIndices {ι : Type} (E : Subfield K)
    (e : Fin a → Fin d →₀ ℕ) (c : Fin a → ι) (x : Fin d → ι) (j : Fin d) :
    Relative.Fun E (fun z : ι → K => (pderiv j (polynomialOfCoefficients e (z ∘ c))).eval (z ∘ x)) :=
  (relative_eval_pderiv_polynomialOfCoefficients E e j).comp
    (show (E : Set K).DefinableMap Language.ring (fun z : ι → K => z ∘ Sum.elim c x) from
      fun j => Relative.projection (E := E) (Sum.elim c x j))

end SpecialTransformations.Section9
