import Section9.ResidueTangentChart
import Section9.RVJacobianDerivations
import Mathlib.RingTheory.Nullstellensatz

/-! The Nullstellensatz proves tangent soundness for an open polynomial
chart. One extra variable presents the localization as an affine
zero locus, so no choice of polynomial-ideal generators is needed. -/

set_option backward.isDefEq.respectTransparency false

open MvPolynomial

namespace SpecialTransformations.Section9

variable {K : Type} [Field K] {d m : ℕ}

noncomputable def residueChartIdeal (P : Fin m → MvPolynomial (Fin d) K) (R : MvPolynomial (Fin d) K) :
    Ideal (MvPolynomial (Fin d ⊕ Unit) K) :=
  Ideal.span (Set.range (fun i => rename Sum.inl (P i)) ∪ {X (.inr ()) * rename Sum.inl R - 1})

set_option maxHeartbeats 800000 in
theorem isPolynomialTangent_iff_of_radical_chart [IsAlgClosed K]
    (C : Set (Fin d → K)) (p : Fin d → K) (hp : p ∈ C)
    (P : Fin m → MvPolynomial (Fin d) K) (R : MvPolynomial (Fin d) K)
    (hP : ∀ i q, q ∈ C → (P i).eval q = 0) (hR : R.eval p ≠ 0)
    (hchart : ∀ q, (∀ i, (P i).eval q = 0) → R.eval q ≠ 0 → q ∈ C)
    (hrad : (residueChartIdeal P R).IsRadical) (h : Fin d → K) :
    IsPolynomialTangent C p h ↔ ∀ i, ∑ j, (pderiv j (P i)).eval p * h j = 0 := by
  classical
  refine ⟨fun ht i => ht (P i) (hP i), ?_⟩
  intro htest Q hQ
  let ι : Fin d → Fin d ⊕ Unit := Sum.inl
  let q := Sum.elim p (fun _ : Unit => (R.eval p)⁻¹)
  let s := Sum.elim h (fun _ : Unit => -(R.eval p)⁻¹ * (∑ j, (pderiv j R).eval p * h j) / R.eval p)
  let X₀ : MvPolynomial (Fin d ⊕ Unit) K := X (.inr ())
  let D (A : MvPolynomial (Fin d ⊕ Unit) K) := ∑ i, (pderiv i A).eval q * s i
  have hDmul (A B : MvPolynomial (Fin d ⊕ Unit) K) : D (A * B) = A.eval q * D B + B.eval q * D A := by
    have hprod (i : Fin d ⊕ Unit) :
        pderiv i (A * B) = A * pderiv i B + B * pderiv i A := by
      rw [pderiv_mul, add_comm, mul_comm (pderiv i A) B]
    simp only [D, hprod, map_add, map_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  have hDsub (A B : MvPolynomial (Fin d ⊕ Unit) K) : D (A - B) = D A - D B := by
    simp only [D, map_sub, sub_mul, Finset.sum_sub_distrib]
  have hDrename (A : MvPolynomial (Fin d) K) : D (rename ι A) = ∑ j, (pderiv j A).eval p * h j := by
    have hzero : pderiv (.inr ()) (rename ι A) = 0 := by
      induction A using MvPolynomial.induction_on with
      | C c => rw [rename_C, pderiv_C]
      | add A B hA hB => rw [map_add, map_add, hA, hB, add_zero]
      | mul_X A i hA =>
        rw [map_mul, rename_X, pderiv_mul, hA, pderiv_X_of_ne (Sum.inl_ne_inr), zero_mul, mul_zero, add_zero]
    simp only [D, Fintype.sum_sum_type, hzero, map_zero, zero_mul, Fintype.sum_unique, add_zero]
    simp only [ι, pderiv_rename Sum.inl_injective, eval_rename, q, s, Sum.elim_inl] <;> rfl
  let J : Ideal (MvPolynomial (Fin d ⊕ Unit) K) :=
    { carrier := {A | A.eval q = 0 ∧ D A = 0}
      zero_mem' := by simp [D]
      add_mem' := by
        rintro A B ⟨ha, hda⟩ ⟨hb, hdb⟩
        have he : D (A + B) = D A + D B := by
          simp only [D, map_add, add_mul, Finset.sum_add_distrib]
        exact ⟨by rw [map_add, ha, hb, add_zero], by rw [he, hda, hdb, add_zero]⟩
      smul_mem' := by
        rintro A B ⟨hb, hdb⟩
        change (A * B).eval q = 0 ∧ D (A * B) = 0
        exact ⟨by rw [map_mul, hb, mul_zero], by rw [hDmul, hb, hdb, mul_zero, zero_mul, add_zero]⟩ }
  have hIJ : residueChartIdeal P R ≤ J := by
    apply Ideal.span_le.mpr
    rintro A (⟨i, rfl⟩ | rfl)
    · change (rename ι (P i)).eval q = 0 ∧ D (rename ι (P i)) = 0
      rw [eval_rename, hDrename]
      exact ⟨hP i p hp, htest i⟩
    · change (X₀ * rename ι R - 1).eval q = 0 ∧ D (X₀ * rename ι R - 1) = 0
      constructor
      · rw [map_sub, map_mul, map_one, eval_X, eval_rename]
        change (R.eval p)⁻¹ * R.eval p - 1 = 0
        rw [inv_mul_cancel₀ hR, sub_self]
      · have hDX : D X₀ = s (.inr ()) := by
          simp only [D, X₀, pderiv_X, apply_ite (eval q), map_one, map_zero, ite_mul, one_mul, zero_mul]
          simp
        have hD1 : D 1 = 0 := by simp [D]
        rw [hDsub, hD1, sub_zero, hDmul, hDX, hDrename, eval_X, eval_rename]
        change (R.eval p)⁻¹ * (∑ j, (pderiv j R).eval p * h j) +
          R.eval p * (-(R.eval p)⁻¹ * (∑ j, (pderiv j R).eval p * h j) / R.eval p) = 0
        field_simp <;> ring
  have hmem : rename ι Q ∈ residueChartIdeal P R := by
    rw [← hrad.radical, ← vanishingIdeal_zeroLocus_eq_radical (K := K) (residueChartIdeal P R)]
    intro z hz
    let a := z ∘ ι
    have hA (i : Fin m) : (P i).eval a = 0 := by
      have he := hz _ (Ideal.subset_span (Or.inl (Set.mem_range_self i)))
      rwa [aeval_eq_eval, eval_rename] at he
    have hB : R.eval a ≠ 0 := by
      intro hzero
      have he := hz _ (Ideal.subset_span (Or.inr (Set.mem_singleton (X₀ * rename ι R - 1))))
      rw [aeval_eq_eval, map_sub, map_mul, eval_rename, hzero, mul_zero, map_one, zero_sub] at he
      exact (neg_ne_zero.mpr one_ne_zero) he
    rw [aeval_eq_eval, eval_rename]
    exact hQ a (hchart a hA hB)
  have hd := (show rename ι Q ∈ J from hIJ hmem).2
  rwa [hDrename] at hd

end SpecialTransformations.Section9
