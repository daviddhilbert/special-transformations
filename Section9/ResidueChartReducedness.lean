import Section9.OpenSquareSystem
import Section9.RadicalResidueChart
import Mathlib.Algebra.MvPolynomial.Equiv

/-! In an open residue chart, separate the input variables from the
output variables and the inverse of the open factor. This transfers
the relative étale presentation to the ideal in the tangent test. -/

set_option backward.isDefEq.respectTransparency false

open MvPolynomial
open SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {K : Type} [Field K] {n : ℕ}

noncomputable def residueOutputJacobian
    (P : Fin n → MvPolynomial (Fin (n + n)) K) : MvPolynomial (Fin (n + n)) K :=
  (Matrix.of fun i j => pderiv (productRight n n j) (P i)).det

theorem eval_residueOutputJacobian (P : Fin n → MvPolynomial (Fin (n + n)) K)
    (z : Fin (n + n) → K) : (residueOutputJacobian P).eval z =
      (Matrix.of fun i j => (pderiv (productRight n n j) (P i)).eval z).det := by
  let f : MvPolynomial (Fin (n + n)) K →+* K := eval z
  change f (residueOutputJacobian P) = _
  rw [residueOutputJacobian, RingHom.map_det] <;> rfl

private def outputFirst (n : ℕ) : Fin (n + n) ≃ Fin n ⊕ Fin n :=
  finSumFinEquiv.symm.trans (Equiv.sumComm _ _)

private def outputWithInverseFirst (n : ℕ) : Fin (n + n) ⊕ Unit ≃ (Fin n ⊕ Unit) ⊕ Fin n :=
  (Equiv.sumCongr (outputFirst n) (Equiv.refl Unit)).trans
    ((Equiv.sumAssoc (Fin n) (Fin n) Unit).trans
      ((Equiv.sumCongr (Equiv.refl (Fin n)) (Equiv.sumComm (Fin n) Unit)).trans
        (Equiv.sumAssoc (Fin n) Unit (Fin n)).symm))

noncomputable def residueChartOutputEquiv (K : Type) [CommRing K] (n : ℕ) :
    MvPolynomial (Fin (n + n)) K ≃ₐ[K] MvPolynomial (Fin n) (MvPolynomial (Fin n) K) :=
  (renameEquiv K (outputFirst n)).trans (sumAlgEquiv K (Fin n) (Fin n))

noncomputable def residueChartRingEquiv (K : Type) [CommRing K] (n : ℕ) :
    MvPolynomial (Fin (n + n) ⊕ Unit) K ≃ₐ[K]
      MvPolynomial (Fin n ⊕ Unit) (MvPolynomial (Fin n) K) :=
  (renameEquiv K (outputWithInverseFirst n)).trans (sumAlgEquiv K (Fin n ⊕ Unit) (Fin n))

private theorem outputPolynomialEquiv_derivative (P : MvPolynomial (Fin (n + n)) K) (j : Fin n) :
    residueChartOutputEquiv K n (pderiv (productRight n n j) P) =
      pderiv j (residueChartOutputEquiv K n P) := by
  let e := outputFirst n
  have hj : e (productRight n n j) = .inl j := by
    change Equiv.sumComm (Fin n) (Fin n) (finSumFinEquiv.symm (finSumFinEquiv (.inr j))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  change sumAlgEquiv K (Fin n) (Fin n) (rename e (pderiv (productRight n n j) P)) =
    pderiv j (sumAlgEquiv K (Fin n) (Fin n) (rename e P))
  rw [pderiv_sumAlgEquiv, ← hj, pderiv_rename e.injective]

private theorem outputChartEquiv_rename (P : MvPolynomial (Fin (n + n)) K) :
    residueChartRingEquiv K n (rename Sum.inl P) = rename Sum.inl (residueChartOutputEquiv K n P) := by
  let f := residueChartRingEquiv K n
  let g := residueChartOutputEquiv K n
  let r : MvPolynomial (Fin n) (MvPolynomial (Fin n) K) →ₐ[MvPolynomial (Fin n) K]
      MvPolynomial (Fin n ⊕ Unit) (MvPolynomial (Fin n) K) := rename Sum.inl
  have h : f.toAlgHom.comp (rename Sum.inl) = (r.restrictScalars K).comp g.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro j
    obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).surjective j
    rcases i with i | i
    · simp [f, g, r, residueChartRingEquiv, residueChartOutputEquiv, outputFirst, outputWithInverseFirst,
        AlgHom.comp_apply, renameEquiv_apply, sumAlgEquiv_X_inr, rename_C]
    · have hi : outputFirst n (finSumFinEquiv (.inr i)) = .inl i := by
        change Equiv.sumComm (Fin n) (Fin n) (finSumFinEquiv.symm (finSumFinEquiv (.inr i))) = _
        rw [Equiv.symm_apply_apply] <;> rfl
      have hi' : outputWithInverseFirst n (.inl (finSumFinEquiv (.inr i))) = .inl (.inl i) := by
        change (Equiv.sumAssoc (Fin n) Unit (Fin n)).symm
          ((Equiv.sumCongr (Equiv.refl (Fin n)) (Equiv.sumComm (Fin n) Unit))
            ((Equiv.sumAssoc (Fin n) (Fin n) Unit) (.inl (outputFirst n (finSumFinEquiv (.inr i)))))) = _
        rw [hi] <;> rfl
      simp only [f, g, r, residueChartRingEquiv, residueChartOutputEquiv, AlgHom.comp_apply,
        AlgHom.restrictScalars_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.trans_apply,
        renameEquiv_apply, rename_X, hi, hi', sumAlgEquiv_X_inl]
  exact AlgHom.congr_fun h P

private theorem outputChartEquiv_X :
    residueChartRingEquiv K n (X (.inr ())) = X (.inr ()) := by
  simp [residueChartRingEquiv, outputWithInverseFirst, renameEquiv_apply, sumAlgEquiv_X_inl]

theorem residueChartRingEquiv_input (P : MvPolynomial (Fin n) K) :
    residueChartRingEquiv K n (rename (Sum.inl ∘ productLeft n n) P) = C P := by
  let f := residueChartRingEquiv K n
  have h : f.toAlgHom.comp (rename (Sum.inl ∘ productLeft n n)) =
      IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) _ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [f, residueChartRingEquiv, outputFirst, outputWithInverseFirst, productLeft, AlgHom.comp_apply,
      renameEquiv_apply, sumAlgEquiv_X_inr]
  exact AlgHom.congr_fun h P

theorem residueChartOutputEquiv_jacobian (P : Fin n → MvPolynomial (Fin (n + n)) K) :
    residueChartOutputEquiv K n (residueOutputJacobian P) =
      jacobianPolynomial (fun i => residueChartOutputEquiv K n (P i)) := by
  let g := (residueChartOutputEquiv K n).toRingHom
  change g (Matrix.of fun i j => pderiv (productRight n n j) (P i)).det =
    (Matrix.of fun i j => pderiv j (residueChartOutputEquiv K n (P i))).det
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  exact outputPolynomialEquiv_derivative (P i) j

theorem residueChartIdeal_map_ringEquiv
    (P : Fin n → MvPolynomial (Fin (n + n)) K) (Q : MvPolynomial (Fin (n + n)) K) :
    Ideal.span (Set.range (openSquareEquations
      (fun i => residueChartOutputEquiv K n (P i)) (residueChartOutputEquiv K n Q))) =
      (residueChartIdeal P Q).map (residueChartRingEquiv K n).toRingHom := by
  let f := residueChartRingEquiv K n
  let g := residueChartOutputEquiv K n
  let P' i := g (P i)
  let Q' := g Q
  have he (i : Fin n) : f (rename Sum.inl (P i)) = openSquareEquations P' Q' (.inl i) :=
    outputChartEquiv_rename (P i)
  have hf : f (X (.inr ()) * rename Sum.inl Q - 1) = openSquareEquations P' Q' (.inr ()) := by
    rw [map_sub, map_mul, map_one, show f (X (.inr ())) = X (.inr ()) from outputChartEquiv_X,
      show f (rename Sum.inl Q) = rename Sum.inl (g Q) from outputChartEquiv_rename Q]
    rfl
  change Ideal.span _ = (Ideal.span _).map f.toRingHom
  rw [Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨i | ⟨⟩, rfl⟩
    · exact ⟨_, Or.inl ⟨i, rfl⟩, he i⟩
    · exact ⟨_, Or.inr rfl, hf⟩
  · rintro ⟨q, (⟨i, rfl⟩ | rfl), rfl⟩
    · exact ⟨.inl i, (he i).symm⟩
    · exact ⟨.inr (), hf.symm⟩

theorem residueChartIdeal_isRadical_of_outputJacobian
    (P : Fin n → MvPolynomial (Fin (n + n)) K) (Q T : MvPolynomial (Fin (n + n)) K)
    (hQ : Q = residueOutputJacobian P * T) : (residueChartIdeal P Q).IsRadical := by
  let g := residueChartOutputEquiv K n
  let P' i := g (P i)
  let Q' := g Q
  let T' := g T
  have hQ' : Q' = jacobianPolynomial P' * T' := by
    change g Q = _
    rw [hQ, map_mul, residueChartOutputEquiv_jacobian]
  let I := residueChartIdeal P Q
  let J := Ideal.span (Set.range (openSquareEquations P' Q'))
  let e := Ideal.quotientEquiv I J (residueChartRingEquiv K n).toRingEquiv (residueChartIdeal_map_ringEquiv P Q)
  haveI : IsReduced (_ ⧸ J) := openSquareSystem_reduced P' Q' T' hQ'
  exact (Ideal.isRadical_iff_quotient_reduced I).mpr (isReduced_of_injective e.toRingHom e.injective)

end SpecialTransformations.Section9
