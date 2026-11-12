module

public import Section9.ResidueChartReducedness
public import Section9.GenericChartSelector
public import Section9.ResidueChartDenominators
public import Section9.ResidueChartFormula

@[expose] public section

/-! On the generically étale square system, a single extra open
factor selects exactly the given constructible residue correspondence.
The selector is a polynomial over the same coefficient field. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Section7

namespace SpecialTransformations.Section9

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private theorem residueChartIdeal_le_ker_eval {E K : Type} [Field E] [Field K] [Algebra E K] {d m : ℕ}
    (P : Fin m → MvPolynomial (Fin d) E) (Q : MvPolynomial (Fin d) E) (z : Fin d → K)
    (hP : ∀ i, aeval z (P i) = 0) (hQ : aeval z Q ≠ 0) :
    let w := Sum.elim z (fun _ : Unit => (aeval z Q)⁻¹)
    residueChartIdeal P Q ≤ RingHom.ker (aeval w).toRingHom := by
  let w := Sum.elim z (fun _ : Unit => (aeval z Q)⁻¹)
  change residueChartIdeal P Q ≤ RingHom.ker (aeval w).toRingHom
  apply Ideal.span_le.mpr
  rintro p (⟨i, rfl⟩ | rfl)
  · change aeval w (rename Sum.inl (P i)) = 0
    rw [aeval_rename]
    exact hP i
  · let x : MvPolynomial (Fin d ⊕ Unit) E := X (.inr ())
    change aeval w (x * rename Sum.inl Q - 1) = 0
    rw [map_sub, map_mul, map_one, show aeval w x = w (.inr ()) from aeval_X w _, aeval_rename]
    change (aeval z Q)⁻¹ * aeval z Q - 1 = 0
    rw [inv_mul_cancel₀ hQ, sub_self]

theorem exists_generic_open_residueSelector {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (E : Subfield K) (C₀ : Set (Fin (n + n) → K)) (hC : (E : Set K).Definable Language.ring C₀)
    (P : Fin n → MvPolynomial (Fin (n + n)) E) :
    ∃ T : MvPolynomial (Fin (n + n)) E, ∀ z,
      AlgebraicIndependent E (z ∘ productLeft n n) →
      (∀ i, aeval z (P i) = 0) → aeval z (residueOutputJacobian P) ≠ 0 →
      (z ∈ C₀ ↔ aeval z T ≠ 0) := by
  let Q := residueOutputJacobian P
  let I := residueChartIdeal P Q
  let g := residueChartOutputEquiv E n
  let f := residueChartRingEquiv E n
  let P' i := g (P i)
  let Q' := g Q
  let J := Ideal.span (Set.range (openSquareEquations P' Q'))
  let R := MvPolynomial (Fin n) E
  let A := MvPolynomial (Fin n ⊕ Unit) R ⧸ J
  let e := Ideal.quotientEquiv I J f.toRingEquiv (residueChartIdeal_map_ringEquiv P Q)
  let q := e.toRingHom.comp (Ideal.Quotient.mk I)
  have hQ' : Q' = jacobianPolynomial P' * 1 := by
    rw [mul_one]
    exact residueChartOutputEquiv_jacobian P
  letI : Algebra.Etale R A := openSquareSystem_etale P' Q' 1 hQ'
  obtain ⟨φ, hφ, hdef⟩ := exists_ringQF_defining_set E C₀ hC
  let a (c : E) : A := q (C c)
  let x (i : Fin (n + n)) : A := q (X (.inl i))
  obtain ⟨s, hs⟩ := exists_genericChart_selector (R := R) a x φ hφ
  obtain ⟨S, hS⟩ := Ideal.Quotient.mk_surjective (e.symm s)
  have hqS : q S = s := (congrArg e hS).trans (e.apply_symm_apply s)
  obtain ⟨T, d, hT⟩ := exists_clear_residueChart_inverse (K := K) Q S
  refine ⟨T, fun z hz hP hQ => ?_⟩
  let z' := Sum.elim z (fun _ : Unit => (aeval z Q)⁻¹)
  let ev : MvPolynomial (Fin (n + n) ⊕ Unit) E →+* K := (aeval z').toRingHom
  have hvan : I ≤ RingHom.ker ev := residueChartIdeal_le_ker_eval P Q z hP hQ
  let F := (Ideal.Quotient.lift I ev hvan).comp e.symm.toRingHom
  have hF (p : MvPolynomial (Fin (n + n) ⊕ Unit) E) : F (q p) = aeval z' p := by
    change Ideal.Quotient.lift I ev hvan (e.symm (e (Ideal.Quotient.mk I p))) = _
    rw [e.symm_apply_apply] <;> rfl
  have hBase : F.comp (algebraMap R A) = (aeval (z ∘ productLeft n n)).toRingHom := by
    apply RingHom.ext
    intro p
    have hp : algebraMap R A p = q (rename (Sum.inl ∘ productLeft n n) p) := by
      change Ideal.Quotient.mk J (C p) = Ideal.Quotient.mk J (f (rename _ p))
      rw [residueChartRingEquiv_input]
    change F (algebraMap R A p) = _
    rw [hp, hF, aeval_rename] <;> rfl
  have hI : Function.Injective (F.comp (algebraMap R A)) := hBase.symm ▸ hz
  have ha : F ∘ a = E.subtype := by
    funext c
    change F (q (C c)) = c.val
    rw [hF, aeval_C] <;> rfl
  have hx : F ∘ x = z := by
    funext i
    change F (q (X (.inl i))) = z i
    rw [hF, aeval_X] <;> rfl
  have h := hs K F hI
  rw [ha, hx, ← hqS, hF] at h
  rw [hdef z, h, hT z hQ, mul_ne_zero_iff]
  change (aeval z' S ≠ 0) ↔ (aeval z Q ^ d ≠ 0 ∧ aeval z' S ≠ 0)
  exact (and_iff_right (pow_ne_zero d (show aeval z Q ≠ 0 from hQ))).symm

end SpecialTransformations.Section9
