module

public import Section3.RingSyntax
public import Mathlib.Algebra.MvPolynomial.Basic

@[expose] public section

/-! The finite expression and proof below are reused from the expression
block of `Section4/PolynomialZero.lean`. This isolated import boundary avoids
pulling the unrelated zero-set/definable-closure development into Section 5.
The existing source credit and repository license continue to apply. -/

open FirstOrder FirstOrder.Language
open scoped BigOperators

noncomputable section

namespace SpecialTransformations.Section5.PolynomialExpression

variable {R : Type} [CommRing R] {n : ℕ} (p : MvPolynomial (Fin n) R)

def enumeration : Fin p.support.card ≃ p.support := (Finset.equivFin p.support).symm

def expression : FreeCommRing (Fin p.support.card ⊕ Fin n) :=
  ∑ j : Fin p.support.card, FreeCommRing.of (Sum.inl j) *
    ∏ i : Fin n, FreeCommRing.of (Sum.inr i) ^ ((enumeration p j).val i)

theorem expression_eval {T : Type} [CommRing T] (h : R →+* T) (x : Fin n → T) :
    FreeCommRing.lift
      (Sum.elim (fun j => h (p.coeff ((enumeration p j).val))) x) (expression p) =
      p.eval₂ h x := by
  simp only [expression, map_sum, map_mul, map_prod, map_pow, FreeCommRing.lift_of,
    Sum.elim_inl, Sum.elim_inr]
  rw [MvPolynomial.eval₂_eq']
  calc
    _ = ∑ d : p.support, h (p.coeff d.val) * ∏ i : Fin n, x i ^ (d.val i) :=
      Fintype.sum_equiv (enumeration p) _ _ (fun _ => rfl)
    _ = _ := Finset.sum_coe_sort p.support
      (fun d : Fin n →₀ ℕ => h (p.coeff d) * ∏ i : Fin n, x i ^ (d i))

end SpecialTransformations.Section5.PolynomialExpression
