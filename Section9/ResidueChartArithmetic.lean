import Section9.UniformResiduePolynomials
import Section7.TupleCoordinates

/-! Each fixed choice of monomial supports has first-order tests for
the square equations, the open factor, the input cut, and the
residue determinant. Coefficients are variables in all four tests. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {K : Type} [Field K] {n a b d : ℕ}
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

abbrev ChartCoefficientIndex (n a b d : ℕ) := ((Fin n × Fin a) ⊕ Fin b) ⊕ Fin d
abbrev ChartPointIndex (n a b d : ℕ) := ChartCoefficientIndex n a b d ⊕ Fin (n + n)

noncomputable def chartEquation
    (e : Fin a → Fin (n + n) →₀ ℕ) (c : ChartCoefficientIndex n a b d → K) (i : Fin n) :
    MvPolynomial (Fin (n + n)) K :=
  polynomialOfCoefficients e (fun j => c (.inl (.inl (i, j))))

noncomputable def chartExtraOpen
    (e : Fin b → Fin (n + n) →₀ ℕ) (c : ChartCoefficientIndex n a b d → K) :
    MvPolynomial (Fin (n + n)) K :=
  polynomialOfCoefficients e (fun j => c (.inl (.inr j)))

noncomputable def chartInputCut
    (e : Fin d → Fin n →₀ ℕ) (c : ChartCoefficientIndex n a b d → K) :
    MvPolynomial (Fin n) K :=
  polynomialOfCoefficients e (c ∘ Sum.inr)

noncomputable def chartDerivativeBlock
    (e : Fin a → Fin (n+n) →₀ ℕ) (s : Fin n → Fin (n+n))
    (z : ChartPointIndex n a b d → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => (pderiv (s j) (chartEquation e (z ∘ Sum.inl) i)).eval (z ∘ Sum.inr)

theorem relative_chart_arithmetic (E : Subfield K)
    (e : Fin a → Fin (n+n) →₀ ℕ) (o : Fin b → Fin (n+n) →₀ ℕ) (q : Fin d → Fin n →₀ ℕ) :
    let I := ChartPointIndex n a b d
    let A (z : I → K) := chartDerivativeBlock e (productRight n n) z
    let B (z : I → K) := chartDerivativeBlock e (productLeft n n) z
    Relative.Def E {z : I → K | ∀ i, (chartEquation e (z ∘ Sum.inl) i).eval (z ∘ Sum.inr) = 0} ∧
    Relative.Fun E (fun z : I → K => (A z).det * (chartExtraOpen o (z ∘ Sum.inl)).eval (z ∘ Sum.inr)) ∧
    Relative.Fun E (fun z : I → K => (chartInputCut q (z ∘ Sum.inl)).eval (z ∘ Sum.inr ∘ productLeft n n)) ∧
    Relative.Fun E (fun z : I → K => (B z).det) ∧
    Relative.Fun E (fun z : I → K => (-1 : K)^n * ((B z).det * ((A z).det)⁻¹)) := by
  let I := ChartPointIndex n a b d
  let A (z : I → K) := chartDerivativeBlock e (productRight n n) z
  let B (z : I → K) := chartDerivativeBlock e (productLeft n n) z
  have hdet (s : Fin n → Fin (n+n)) :
      Relative.Fun E (fun z : I → K => (chartDerivativeBlock e s z).det) := by
    apply relative_det_of_entries
    intro i j
    exact relative_eval_pderiv_polynomialOfIndices (ι := I) E e
      (fun l => .inl (.inl (.inl (i,l)))) Sum.inr (s j)
  have hQ : Relative.Fun E (fun z : I → K => (chartExtraOpen o (z ∘ Sum.inl)).eval (z ∘ Sum.inr)) :=
    relative_eval_polynomialOfIndices (ι := I) E o (fun i => .inl (.inl (.inr i))) Sum.inr
  have hcut : Relative.Fun E (fun z : I → K => (chartInputCut q (z ∘ Sum.inl)).eval
      (z ∘ Sum.inr ∘ productLeft n n)) :=
    relative_eval_polynomialOfIndices (ι := I) E q (fun i => .inl (.inr i)) (Sum.inr ∘ productLeft n n)
  have hs : (-1 : K) ^ n ∈ E := E.pow_mem (E.neg_mem E.one_mem) _
  refine ⟨?_, (hdet (productRight n n)).mul hQ, hcut, hdet (productLeft n n), ?_⟩
  · rw [Set.ofPred_forall]
    apply Set.definable_iInter_of_finite
    intro i
    exact (relative_eval_polynomialOfIndices (ι := I) E e
      (fun l => .inl (.inl (.inl (i,l)))) Sum.inr).eq_const 0 E.zero_mem
  · exact (Relative.constant (ι := I) _ hs).mul ((hdet (productLeft n n)).mul (hdet (productRight n n)).inv)

end SpecialTransformations.Section9
