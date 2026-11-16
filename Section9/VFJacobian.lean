module

public import Section9.Differentiation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-! The VF part of Definition 9.10 and the pointwise chain rule under
full differentiability. For a function with RV labels, the VF function
in these statements is the local function with the labels fixed. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section8

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

local notation "VF" => VFType (M := M)
local notation "v" => Values.vfValueHom (M := M)

def HasVFPartialAt (f : (Fin n → VF) → Fin m → VF) (a : Fin n → VF)
    (j : Fin n) (i : Fin m) (d : VF) : Prop :=
  ∀ ε : Values.Gamma (M := M), ∃ δ : Values.Gamma (M := M),
    ∀ t : VF, t ≠ 0 → δ.val < v t →
      ε.val * v t < v (f (a + Pi.single j t) i - f a i - d * t)

/-- The determinant formed from the individual partial derivatives. -/
def HasVFJacobianAt (f : (Fin n → VF) → Fin n → VF) (a : Fin n → VF) (J : VF) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) VF, (∀ i j, HasVFPartialAt f a j i (A i j)) ∧ A.det = J

/-- In arity zero the partial Jacobian is the empty determinant. -/
theorem hasVFJacobianAt_zero_arity (f : (Fin 0 → VF) → Fin 0 → VF) (a : Fin 0 → VF) :
    HasVFJacobianAt f a 1 :=
  ⟨1, fun i => Fin.elim0 i, Matrix.det_one⟩

theorem HasVFPartialAt.unique {f : (Fin n → VF) → Fin m → VF} {a : Fin n → VF}
    {j : Fin n} {i : Fin m} {d e : VF}
    (hd : HasVFPartialAt f a j i d) (he : HasVFPartialAt f a j i e) : d = e := by
  by_contra hne
  have hde : d - e ≠ 0 := sub_ne_zero.mpr hne
  let ε := Values.gammaOf (CanonicalRV.encodedRv (d - e))
    (fun h => hde ((CanonicalRV.encodedRv_zero_iff (d - e)).mp h))
  obtain ⟨δd, hδd⟩ := hd ε
  obtain ⟨δe, hδe⟩ := he ε
  obtain ⟨γ, hγ⟩ := exists_gt (max δd δe)
  obtain ⟨t, ht, hval⟩ := gamma_has_vf_representative γ
  have htd : δd.val < v t := by
    rw [hval]
    exact (le_max_left δd δe).trans_lt hγ
  have hte : δe.val < v t := by
    rw [hval]
    exact (le_max_right δd δe).trans_lt hγ
  let r := f (a + Pi.single j t) i - f a i - d * t
  let s := f (a + Pi.single j t) i - f a i - e * t
  have hs : ε.val * v t < v (s - r) :=
    (lt_min (hδe t ht hte) (hδd t ht htd)).trans_le (vfValue_min_le_sub s r)
  rw [show s - r = (d - e) * t by dsimp [r, s]; ring, map_mul] at hs
  exact (lt_irrefl _) hs

theorem HasVFPartialAt.congr_on_vfBall {f g : (Fin n → VF) → Fin m → VF} {a : Fin n → VF}
    {j : Fin n} {i : Fin m} {d : VF} {ρ : Values.Gamma (M := M)}
    (hf : HasVFPartialAt f a j i d) (he : Set.EqOn f g (vfBall a ρ)) :
    HasVFPartialAt g a j i d := by
  intro ε
  obtain ⟨δ, hδ⟩ := hf ε
  refine ⟨max δ ρ, fun t ht hnear => ?_⟩
  have hsmall : ρ.val < v t :=
    (show ρ.val ≤ (max δ ρ).val from le_max_right _ _).trans_lt hnear
  have hball : a + Pi.single j t ∈ vfBall a ρ := by
    intro k
    change ρ.val < v (a k + (Pi.single j t : Fin n → VF) k - a k)
    rw [add_sub_cancel_left]
    by_cases hk : k = j
    · subst k
      simpa only [Pi.single_eq_same] using hsmall
    · rw [Pi.single_eq_of_ne hk]
      exact gamma_lt_value_zero _
  rw [← he hball, ← he (mem_vfBall_self a ρ)]
  exact hδ t ht ((show δ.val ≤ (max δ ρ).val from le_max_left _ _).trans_lt hnear)

theorem HasVFJacobianAt.unique {f : (Fin n → VF) → Fin n → VF} {a : Fin n → VF} {J K : VF}
    (hJ : HasVFJacobianAt f a J) (hK : HasVFJacobianAt f a K) : J = K := by
  obtain ⟨A, hA, rfl⟩ := hJ
  obtain ⟨B, hB, rfl⟩ := hK
  have he : A = B := Matrix.ext fun i j => (hA i j).unique (hB i j)
  rw [he]

theorem HasVFJacobianAt.congr_on_vfBall {f g : (Fin n → VF) → Fin n → VF} {a : Fin n → VF}
    {J : VF} {ρ : Values.Gamma (M := M)}
    (hf : HasVFJacobianAt f a J) (he : Set.EqOn f g (vfBall a ρ)) :
    HasVFJacobianAt g a J := by
  obtain ⟨A, hA, hdet⟩ := hf
  exact ⟨A, fun i j => (hA i j).congr_on_vfBall he, hdet⟩

private theorem vfTupleValue_single (j : Fin n) (t : VF) :
    vfTupleValue (Pi.single j t) = v t := by
  apply le_antisymm
  · simpa only [Pi.single_eq_same] using vfTupleValue_le_component (Pi.single j t) j
  · obtain ⟨i, hi⟩ := vfTupleValue_eq_component (Pi.single j t) (Nat.zero_lt_of_lt j.isLt)
    rw [hi]
    by_cases he : i = j
    · subst i
      rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne he, map_zero, ← Values.infinity_eq_zero]
      exact Values.le_infinity _

theorem HasVFDerivativeAt.hasPartialAt
    {f : (Fin n → VF) → Fin m → VF} {a : Fin n → VF}
    {L : (Fin n → VF) →ₗ[VF] (Fin m → VF)} (h : HasVFDerivativeAt f a L)
    (j : Fin n) (i : Fin m) : HasVFPartialAt f a j i (LinearMap.toMatrix' L i j) := by
  intro ε
  obtain ⟨δ, hδ⟩ := h ε
  refine ⟨δ, ?_⟩
  intro t ht hclose
  have hne : (Pi.single j t : Fin n → VF) ≠ 0 := by
    intro he
    exact ht (by simpa only [Pi.single_eq_same, Pi.zero_apply] using congrFun he j)
  have hclose' : δ.val < vfTupleValue (Pi.single j t) := by rwa [vfTupleValue_single]
  have hsmall := (hδ (Pi.single j t) hne hclose').trans_le (vfTupleValue_le_component _ i)
  rw [vfTupleValue_single] at hsmall
  have hs : Pi.single j t = t • Pi.single j (1 : VF) := by
    funext k
    by_cases hk : k = j <;> simp [hk, Pi.single_apply]
  have hlin : L (Pi.single j t) i = LinearMap.toMatrix' L i j * t := by
    rw [hs]
    calc
      _ = t * L (Pi.single j (1 : VF)) i := congrFun (L.map_smul t _) i
      _ = _ := by rw [LinearMap.toMatrix'_apply, mul_comm]
  simpa only [Pi.sub_apply, hlin] using hsmall

theorem HasVFDerivativeAt.hasJacobianAt
    {f : (Fin n → VF) → Fin n → VF} {a : Fin n → VF}
    {L : (Fin n → VF) →ₗ[VF] (Fin n → VF)} (h : HasVFDerivativeAt f a L) :
    HasVFJacobianAt f a (LinearMap.toMatrix' L).det :=
  ⟨LinearMap.toMatrix' L, fun i j => h.hasPartialAt j i, rfl⟩

/-- At points of full differentiability, the partial Jacobian of the
composition is the product supplied by the valued-field chain rule. -/
theorem vfJacobian_comp_of_full_derivative
    {f g : (Fin n → VF) → Fin n → VF} {a : Fin n → VF}
    {L D : (Fin n → VF) →ₗ[VF] (Fin n → VF)}
    (hf : HasVFDerivativeAt f a L) (hg : HasVFDerivativeAt g (f a) D) :
    HasVFJacobianAt (g ∘ f) a ((LinearMap.toMatrix' D).det * (LinearMap.toMatrix' L).det) := by
  have h := (hg.comp hf).hasJacobianAt
  rwa [LinearMap.toMatrix'_comp, Matrix.det_mul] at h

end SpecialTransformations.Section9
