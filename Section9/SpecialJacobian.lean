import Section9.MixedJacobian
import Section5.Core

/-! The determinant of a centripetal transformation at a point with
a full derivative in its fixed-label chart. The active coordinate is
translated by a constant on its own coordinate line. -/

set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section8

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

local notation "VF" => VFType (M := M)
local notation "V" => Fin n → VF
local notation "Γ" => Values.Gamma (M := M)
local notation "v" => Values.vfValueHom (M := M)

private theorem hasVFPartialAt_of_exact_axis {F : V → V} {a : V} {ρ : Γ}
    (i j : Fin n) (d : VF) (h : ∀ t : VF, ρ.val < v t →
      F (a + Pi.single j t) i = F a i + d * t) :
    HasVFPartialAt F a j i d := by
  intro ε
  refine ⟨ρ, fun t ht hclose => ?_⟩
  rw [h t hclose, add_sub_cancel_left, sub_self, map_zero]
  exact value_lt_infinity (mul_ne_zero (finiteValue_ne_zero ε)
    (fun he => ht ((vfValue_eq_zero_iff t).mp he)))

private theorem axis_mem_vfBall (a : V) (j : Fin n) (t : VF) (ρ : Γ)
    (ht : ρ.val < v t) : a + Pi.single j t ∈ vfBall a ρ := by
  intro i
  change ρ.val < v ((a i + (Pi.single j t : V) i) - a i)
  rw [add_sub_cancel_left]
  by_cases hij : i = j
  · subst i
    rw [Pi.single_eq_same]
    exact ht
  · rw [Pi.single_eq_of_ne hij]
    exact gamma_lt_value_zero ρ

private theorem det_eq_one_of_prescribed_rows {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (j : Fin n)
    (h : ∀ i ≠ j, ∀ k, A i k = (1 : Matrix (Fin n) (Fin n) K) i k)
    (hjj : A j j = 1) : A.det = 1 := by
  classical
  let I : Matrix (Fin n) (Fin n) K := 1
  have he : A = I.updateRow j (A j) := by
    ext i k
    by_cases hij : i = j
    · subst i
      rw [Matrix.updateRow_self]
    · rw [Matrix.updateRow_ne hij]
      exact h i hij k
  have hr : (∑ k, A j k • I k) = A j := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, I, Matrix.one_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      simp [hki]
    · simp
  rw [he]
  exact (congrArg (fun r => (I.updateRow j r).det) hr.symm).trans
    (by rw [Matrix.det_updateRow_sum, hjj, one_smul, show I = 1 from rfl, Matrix.det_one])

/-- A centripetal primitive has determinant one wherever it has a full
derivative in a fixed-label chart. This pointwise statement is used on
the generic locus to prove the approved replacement for Lemma 9.11. -/
theorem centripetal_det_eq_one {S : Set M} {A : Section5.DefSet (M := M) S n m}
    {j : Fin n} {k : Fin m} (D : Section5.Focus A j k) (p : A)
    {L : V →ₗ[VF] V}
    (hL : HasMixedVFDerivativeAt (Section5.Map.toImage D.etaMap) p L) :
    (LinearMap.toMatrix' L).det = 1 := by
  classical
  obtain ⟨F, hChart, hF⟩ := hL
  let a : V := p.val.1
  let r : Fin m → CanonicalRV.RVSort M := p.val.2
  let p₀ : Section5.Point (M := M) n m := (a, r)
  have hp₀ := p.property
  have hcentre : F a = (D.toFocusGeometry.eta p₀).1 := hChart.center
  change HasVFDerivativeAt F a L at hF
  obtain ⟨ρ, hρ⟩ := hChart
  have hrow : ∀ i ≠ j, ∀ l, LinearMap.toMatrix' L i l = (1 : Matrix (Fin n) (Fin n) VF) i l := by
    intro i hi l
    apply (hF.hasPartialAt l i).unique
    apply hasVFPartialAt_of_exact_axis (ρ := ρ)
    intro t ht
    let x : V := a + (Pi.single l t : V)
    obtain ⟨hxA, hx⟩ := hρ x (axis_mem_vfBall a l t ρ ht)
    have he : F x = (D.toFocusGeometry.eta (x, r)).1 := (congrArg Prod.fst hx).symm
    change F x i = F a i + _
    rw [he, hcentre, D.toFocusGeometry.eta_other _ _ hi, D.toFocusGeometry.eta_other _ _ hi]
    change x i = a i + _
    dsimp only [x, Pi.add_apply]
    by_cases hil : i = l
    · subst l
      simp
    · rw [Pi.single_eq_of_ne hil, Matrix.one_apply_ne hil, zero_mul, add_zero]
  have hjj : LinearMap.toMatrix' L j j = 1 := by
    apply (hF.hasPartialAt j j).unique
    apply hasVFPartialAt_of_exact_axis (ρ := ρ)
    intro t ht
    let x : V := a + (Pi.single j t : V)
    let q : Section5.Point (M := M) n m := (x, r)
    obtain ⟨hq, hFq⟩ := hρ x (axis_mem_vfBall a j t ρ ht)
    have he : F x = (D.toFocusGeometry.eta q).1 := (congrArg Prod.fst hFq).symm
    have hsame : Section5.SameRV p₀ q := by
      apply (Section5.sameRV_iff p₀ q).mpr
      refine ⟨fun i => ?_, rfl⟩
      by_cases hi : i = j
      · subst i
        exact (D.tagged p₀ hp₀).symm.trans (D.tagged q hq)
      · change Section5.rv (a i) = Section5.rv (a i + (Pi.single j t : V) i)
        rw [Pi.single_eq_of_ne hi, add_zero]
    have hErase : Section5.erase j p₀ = Section5.erase j q := by
      change (Function.update a j 0, r) = (Function.update x j 0, r)
      refine Prod.ext ?_ rfl
      funext i
      by_cases hi : i = j
      · subst i
        simp
      · simp [x, hi]
    have hqj : q.1 j = a j + t := by simp [q, x]
    change F x j = F a j + 1 * t
    rw [he, hcentre, one_mul]
    by_cases hp : p₀ ∈ D.locus
    · have hqL := (Section5.mem_iff_sameRV D.locus_pullback hsame).mp hp
      have hcent := D.independent p₀ ⟨hp₀, hp⟩ q ⟨hq, hqL⟩ hErase
      simp only [Section5.FocusGeometry.eta, if_pos hp, if_pos hqL,
        Section5.replace, Function.update_self, hqj, ← hcent]
      abel
    · have hqL := (Section5.mem_iff_sameRV D.locus_pullback hsame).not.mp hp
      simpa only [Section5.FocusGeometry.eta, if_neg hp, if_neg hqL] using hqj
  exact det_eq_one_of_prescribed_rows _ j hrow hjj

end SpecialTransformations.Section9
