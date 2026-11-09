import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The coordinate-axis computation for the counterexample to the
pointwise partial Jacobian chain rule in Lemma 9.12. Each displayed axis
restriction is exactly linear. In the valued-field model its slopes are
therefore the partial derivatives. -/

namespace SpecialTransformations.Section9

variable {K : Type*} [Field K]

def shear (p : K × K) : K × K := (p.1, p.1 + p.2)

noncomputable def scaleDiagonal (c : K) (p : K × K) : K × K := by
  classical
  exact if p.1 = p.2 then (c * p.1, c * p.2) else p

theorem shear_bijective : Function.Bijective (shear (K := K)) := by
  let inv (p : K × K) : K × K := (p.1, p.2 - p.1)
  have hleft : Function.LeftInverse inv shear := by
    rintro ⟨x, y⟩
    simp [inv, shear]
  have hright : Function.RightInverse inv shear := by
    rintro ⟨x, y⟩
    simp [inv, shear]
  exact ⟨hleft.injective, hright.surjective⟩

private theorem scaleDiagonal_inverse (c : K) (hc : c ≠ 0) (p : K × K) :
    scaleDiagonal c⁻¹ (scaleDiagonal c p) = p := by
  by_cases h : p.1 = p.2
  · rcases p with ⟨x, y⟩
    change x = y at h
    subst y
    simp [scaleDiagonal, hc]
  · have hi : scaleDiagonal c p = p := by simp [scaleDiagonal, h]
    rw [hi]
    simp [scaleDiagonal, h]

theorem scaleDiagonal_bijective (c : K) (hc : c ≠ 0) :
    Function.Bijective (scaleDiagonal c) := by
  refine ⟨(show Function.LeftInverse (scaleDiagonal c⁻¹) (scaleDiagonal c) from
    scaleDiagonal_inverse c hc).injective, ?_⟩
  intro p
  exact ⟨scaleDiagonal c⁻¹ p, by
    simpa only [inv_inv] using scaleDiagonal_inverse c⁻¹ (inv_ne_zero hc) p⟩

def coordinateAxis (i : Fin 2) (x : K) : K × K :=
  if i = 0 then (x, 0) else (0, x)

/-- Each column records the exact linear restriction along an input axis. -/
def HasAxisMatrix (f : K × K → K × K) (A : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∀ i : Fin 2, ∀ x : K, f (coordinateAxis i x) = (x * A 0 i, x * A 1 i)

theorem shear_axisMatrix : HasAxisMatrix (shear (K := K)) !![1, 0; 1, 1] := by
  intro i x
  fin_cases i <;> simp [shear, coordinateAxis]

theorem doubleDiagonal_axisMatrix : HasAxisMatrix (scaleDiagonal (2 : K)) !![1, 0; 0, 1] := by
  intro i x
  fin_cases i <;> by_cases hx : x = 0 <;>
    simp [coordinateAxis, scaleDiagonal, hx, eq_comm (a := (0 : K))]

theorem doubleDiagonal_shear_axisMatrix :
    HasAxisMatrix (scaleDiagonal (2 : K) ∘ shear) !![2, 0; 2, 1] := by
  intro i x
  fin_cases i <;> by_cases hx : x = 0 <;>
    simp [coordinateAxis, scaleDiagonal, shear, hx, eq_comm (a := (0 : K)), mul_comm]

theorem axisJacobian_chain_failure [CharZero K] :
    (Matrix.det !![(2 : K), 0; 2, 1]) ≠
      (Matrix.det !![(1 : K), 0; 0, 1]) * Matrix.det !![(1 : K), 0; 1, 1] := by
  norm_num [Matrix.det_fin_two_of]

end SpecialTransformations.Section9
