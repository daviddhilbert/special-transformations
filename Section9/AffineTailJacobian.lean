import Section9.AffineTail
import Section9.VFJacobian
import Section7.TupleCoordinates
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! For the lift with an affine tail, only three blocks of the full
derivative enter the determinant. The tail can depend on the head. -/

set_option backward.isDefEq.respectTransparency false

open SpecialTransformations.Section7
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section8

namespace SpecialTransformations.Section9

variable {K : Type*} [Field K] {k m : ℕ}

theorem det_eq_head_mul_tailSlopes
    (D : Matrix (Fin (k + m)) (Fin (k + m)) K)
    (A : Matrix (Fin k) (Fin k) K) (c : Fin m → K)
    (hA : ∀ i j, D (productLeft k m i) (productLeft k m j) = A i j)
    (hzero : ∀ i j, D (productLeft k m i) (productRight k m j) = 0)
    (hc : ∀ i j, D (productRight k m i) (productRight k m j) = if i = j then c i else 0) :
    D.det = A.det * ∏ j, c j := by
  let e : Fin k ⊕ Fin m ≃ Fin (k + m) := finSumFinEquiv
  let C := Matrix.of fun i j => D (productRight k m i) (productLeft k m j)
  have he : D.submatrix e e = Matrix.fromBlocks A 0 C (Matrix.diagonal c) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hA i j
      | inr j => exact hzero i j
    | inr i =>
      cases j with
      | inl j => rfl
      | inr j =>
        change D (productRight k m i) (productRight k m j) = Matrix.diagonal c i j
        rw [Matrix.diagonal_apply]
        exact hc i j
  rw [← Matrix.det_submatrix_equiv_self e D, he, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_diagonal]

def liftWithAffineTail (head : (Fin k → K) → Fin k → K)
    (a b c : (Fin k → K) → Fin m → K) (z : Fin (k + m) → K) : Fin (k + m) → K :=
  let x := z ∘ productLeft k m
  let y := z ∘ productRight k m
  productTuple (head x) (affineTail (a x) (b x) (c x) y)

theorem liftWithAffineTail_bijOn
    (head : (Fin k → K) → Fin k → K) (a b c : (Fin k → K) → Fin m → K)
    (X X' : Set (Fin k → K)) (Y Y' : Set (Fin m → K)) (hhead : Set.BijOn head X X')
    (htail : ∀ x ∈ X, Set.BijOn (affineTail (a x) (b x) (c x)) Y Y') :
    Set.BijOn (liftWithAffineTail head a b c)
      {z | z ∘ productLeft k m ∈ X ∧ z ∘ productRight k m ∈ Y}
      {z | z ∘ productLeft k m ∈ X' ∧ z ∘ productRight k m ∈ Y'} := by
  let l := productLeft k m
  let r := productRight k m
  let F := liftWithAffineTail head a b c
  have hL (x : Fin k → K) (y : Fin m → K) : productTuple x y ∘ l = x :=
    funext (productTuple_left x y)
  have hR (x : Fin k → K) (y : Fin m → K) : productTuple x y ∘ r = y :=
    funext (productTuple_right x y)
  have hFL (z : Fin (k + m) → K) : F z ∘ l = head (z ∘ l) := hL _ _
  have hFR (z : Fin (k + m) → K) : F z ∘ r =
      affineTail (a (z ∘ l)) (b (z ∘ l)) (c (z ∘ l)) (z ∘ r) := hR _ _
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    change F z ∘ l ∈ X' ∧ F z ∘ r ∈ Y'
    rw [hFL, hFR]
    exact ⟨hhead.mapsTo hz.1, (htail _ hz.1).mapsTo hz.2⟩
  · intro z hz z' hz' h
    change F z = F z' at h
    have hx : z ∘ l = z' ∘ l := hhead.injOn hz.1 hz'.1
      ((hFL z).symm.trans (h ▸ hFL z'))
    have hy : z ∘ r = z' ∘ r := by
      apply (htail _ hz.1).injOn hz.2 hz'.2
      have he := (hFR z).symm.trans (h ▸ hFR z')
      rw [← hx] at he
      exact he
    exact productTuple_ext (congrFun hx) (congrFun hy)
  · intro z hz
    obtain ⟨x, hx, hx'⟩ := hhead.surjOn hz.1
    obtain ⟨y, hy, hy'⟩ := (htail x hx).surjOn hz.2
    refine ⟨productTuple x y, ?_, ?_⟩
    · change productTuple x y ∘ l ∈ X ∧ productTuple x y ∘ r ∈ Y
      rw [hL, hR]
      exact ⟨hx, hy⟩
    · change F (productTuple x y) = z
      have hl : F (productTuple x y) ∘ l = z ∘ l := by
        rw [hFL, hL]
        exact hx'
      have hr : F (productTuple x y) ∘ r = z ∘ r := by
        rw [hFR, hL, hR]
        exact hy'
      apply productTuple_ext
      · exact congrFun hl
      · exact congrFun hr

section Derivative

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

local notation "VF" => VFType (M := M)
local notation "V" => Fin (k + m) → VF
local notation "X" => Fin k → VF
local notation "Y" => Fin m → VF
local notation "v" => Values.vfValueHom (M := M)

private theorem partial_of_exact_increment {F : V → V} {q : V} {i j : Fin (k + m)} {d : VF}
    (h : ∀ t : VF, F (q + Pi.single j t) i - F q i = d * t) :
    HasVFPartialAt F q j i d := by
  intro ε
  refine ⟨1, fun t ht _ => ?_⟩
  rw [h, sub_self, map_zero]
  exact value_lt_infinity (mul_ne_zero (finiteValue_ne_zero ε)
    (fun he => ht ((vfValue_eq_zero_iff t).mp he)))

set_option backward.isDefEq.respectTransparency true in
/-- The derivative of the tail in head directions can be arbitrary.
The full determinant uses the head determinant and the affine slopes
at the source head. -/
theorem det_liftWithAffineTail
    (F : V → V) (head : X → X) (a b c : X → Y) (x : X) (y : Y)
    (L : V →ₗ[VF] V) (D : X →ₗ[VF] X)
    (hL : HasVFDerivativeAt F (productTuple x y) L) (hD : HasVFDerivativeAt head x D)
    (ρ : Values.Gamma (M := M))
    (hF : Set.EqOn (liftWithAffineTail head a b c) F (vfBall (productTuple x y) ρ)) :
    (LinearMap.toMatrix' L).det = (LinearMap.toMatrix' D).det * ∏ j, c x j := by
  let l := productLeft k m
  let r := productRight k m
  let q := productTuple x y
  let H := liftWithAffineTail head a b c
  have hF' : Set.EqOn H F (vfBall q ρ) := hF
  have hleft : q ∘ l = x := funext fun i => productTuple_left x y i
  have hright : q ∘ r = y := funext fun i => productTuple_right x y i
  have hll (j : Fin k) (t : VF) : (q + Pi.single (l j) t) ∘ l = x + Pi.single j t := by
    funext i
    simp only [Function.comp_apply, Pi.add_apply, q, l, productTuple_left, Pi.single_apply,
      (productLeft k m).injective.eq_iff]
  have hlr (j : Fin m) (t : VF) : (q + Pi.single (r j) t) ∘ l = x := by
    funext i
    change q (l i) + (Pi.single (r j) t : V) (l i) = x i
    have hne : l i ≠ r j := productLeft_ne_right i j
    have hi : q (l i) = x i := congrFun hleft i
    rw [hi, Pi.single_eq_of_ne hne]
    exact add_zero _
  have hrr (j : Fin m) (t : VF) : (q + Pi.single (r j) t) ∘ r = y + Pi.single j t := by
    funext i
    simp only [Function.comp_apply, Pi.add_apply, q, r, productTuple_right, Pi.single_apply,
      (productRight k m).injective.eq_iff]
  have hhead (z : V) (i : Fin k) : H z (l i) = head (z ∘ l) i := productTuple_left _ _ _
  have htail (z : V) (i : Fin m) : H z (r i) =
      affineTail (a (z ∘ l)) (b (z ∘ l)) (c (z ∘ l)) (z ∘ r) i := productTuple_right _ _ _
  apply det_eq_head_mul_tailSlopes
  · intro i j
    have hp : HasVFPartialAt H q (l j) (l i) (LinearMap.toMatrix' D i j) := by
      intro ε
      obtain ⟨δ, hδ⟩ := hD.hasPartialAt j i ε
      refine ⟨δ, fun t ht hnear => ?_⟩
      simpa only [hhead, hll, hleft] using hδ t ht hnear
    exact (hL.hasPartialAt (l j) (l i)).unique (hp.congr_on_vfBall hF')
  · intro i j
    have hp : HasVFPartialAt H q (r j) (l i) 0 := by
      apply partial_of_exact_increment
      intro t
      rw [hhead, hhead, hlr, hleft, sub_self]
      exact (zero_mul t).symm
    exact (hL.hasPartialAt (r j) (l i)).unique (hp.congr_on_vfBall hF')
  · intro i j
    have hp : HasVFPartialAt H q (r j) (r i) (if i = j then c x i else 0) := by
      apply partial_of_exact_increment
      intro t
      rw [htail, htail, hlr, hrr, hleft, hright]
      exact affineTail_add_single (a x) (b x) (c x) y i j t
    exact (hL.hasPartialAt (r j) (r i)).unique (hp.congr_on_vfBall hF')

end Derivative

end SpecialTransformations.Section9
