module

public import Section3.GuardedRVArithmetic

@[expose] public section

/-!
# GuardedRVTerms

Finite normalization of every released RV term. Inverse and partial residue
operations retain their zero, pole and residue-domain branches. The finite
program is chosen from syntax, independently of a model or assignment.

See NORMAL-FORM-NOTE.md for the agreed statement and language conventions.
-/

/- Component: GuardedFractionCases -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm
open FiniteGuardedBranches

abbrev Program (I R V A : Type) := List (Branch (NFTest I R V) A)

namespace RVFraction
variable {I R V : Type}
noncomputable def inverseCases (F : RVFraction I R V) : Program I R V (RVFraction I R V) :=
  emit [.monomialZero F.outer true] zero ++
    emit [.monomialZero F.outer false,.polynomialZero F.numerator true] zero ++
    emit [.monomialZero F.outer false,.polynomialZero F.numerator false] (inv F)

/-- Some means an equal fraction with residue-valued outer monomial.
None records that the input lies outside the residue subset. -/
noncomputable def residueCases (F : RVFraction I R V) : Program I R V (Option (RVFraction I R V)) :=
  emit [.polynomialZero F.numerator true] (some zero) ++
    emit [.polynomialZero F.numerator false,.monomialResidue F.outer true] (some F) ++
    emit [.polynomialZero F.numerator false,.monomialResidue F.outer false] none

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)

private theorem run_emit_one {A : Type} (t : NFTest I R V) (u z : A) :
    z ∈ run (NFTest.holds a r y) (emit [t] u) ↔ NFTest.holds a r y t ∧ z=u := by
  simp [run_emit,satisfied]

private theorem run_emit_two {A : Type} (t u : NFTest I R V) (w z : A) :
    z ∈ run (NFTest.holds a r y) (emit [t,u] w) ↔
      NFTest.holds a r y t ∧ NFTest.holds a r y u ∧ z=w := by
  simp [run_emit,satisfied,and_assoc]

theorem inverseCases_sound (F G : RVFraction I R V) (hF : F.Prepared a r y)
    (hG : G ∈ run (NFTest.holds a r y) (inverseCases F)) :
    G.Prepared a r y ∧ G.eval a r y = (F.eval a r y)⁻¹ := by
  simp only [inverseCases,run_append,run_emit_one,run_emit_two] at hG
  rcases hG with (⟨hm,rfl⟩ | ⟨hm,hn,rfl⟩) | ⟨hm,hn,rfl⟩
  · refine ⟨prepared_zero a r y,?_⟩
    have h0 : F.outer.eval a r y=0 := hm.2
    rw [eval_zero,eval,h0,zero_mul,zero_div,inv_zero]
  · refine ⟨prepared_zero a r y,?_⟩
    have h0 : F.numerator.eval a r y=0 := hn.2
    rw [eval_zero,eval,h0,mul_zero,zero_div,inv_zero]
  · exact ⟨prepared_inv a r y F hF hm.2 hn.2,eval_inv a r y F⟩

theorem inverseCases_complete (F : RVFraction I R V) (hF : F.Prepared a r y) :
    ∃ G, G ∈ run (NFTest.holds a r y) (inverseCases F) := by
  have hm (pos : Bool) : NFTest.Safe a r y (.monomialZero F.outer pos) := ⟨hF.pole,hF.slots⟩
  have hn (pos : Bool) : NFTest.Safe a r y (.polynomialZero F.numerator pos) := hF.numerator
  by_cases hM : F.outer.eval a r y=0
  · refine ⟨zero,?_⟩
    simp only [inverseCases,run_append,run_emit_one,run_emit_two]
    exact Or.inl (Or.inl ⟨⟨hm true,hM⟩,by simp⟩)
  · by_cases hN : F.numerator.eval a r y=0
    · refine ⟨zero,?_⟩
      simp only [inverseCases,run_append,run_emit_one,run_emit_two]
      exact Or.inl (Or.inr ⟨⟨hm false,hM⟩,⟨hn true,hN⟩,by simp⟩)
    · refine ⟨inv F,?_⟩
      simp only [inverseCases,run_append,run_emit_one,run_emit_two]
      exact Or.inr ⟨⟨hm false,hM⟩,⟨hn false,hN⟩,by simp⟩

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

include hv in
theorem residueCases_sound (F : RVFraction I R V) (G : Option (RVFraction I R V))
    (hF : F.Prepared a r y) (hG : G ∈ run (NFTest.holds a r y) (residueCases F)) :
    match G with
    | some H => H.Prepared a r y ∧ inK (H.outer.eval a r y) ∧ H.eval a r y=F.eval a r y
    | none => ¬ inK (F.eval a r y) := by
  simp only [residueCases,run_append,run_emit_one,run_emit_two] at hG
  rcases hG with (⟨hn,rfl⟩ | ⟨hn,hm,rfl⟩) | ⟨hn,hm,rfl⟩
  · refine ⟨prepared_zero a r y,?_,?_⟩
    · change inK (Monomial.zero.eval a r y)
      rw [Monomial.eval_zero]
      exact KPolynomial.inK_zero
    · have hN : F.numerator.eval a r y=0 := hn.2
      rw [eval_zero,eval,hN,mul_zero,zero_div]
  · exact ⟨hF,hm.2,rfl⟩
  · exact fun h => hm.2 ((eval_inK_iff a r y v hv F hF hn.2).mp h)

theorem residueCases_complete (F : RVFraction I R V) (hF : F.Prepared a r y) :
    ∃ G, G ∈ run (NFTest.holds a r y) (residueCases F) := by
  have hm (pos : Bool) : NFTest.Safe a r y (.monomialResidue F.outer pos) := ⟨hF.pole,hF.slots⟩
  have hn (pos : Bool) : NFTest.Safe a r y (.polynomialZero F.numerator pos) := hF.numerator
  by_cases hN : F.numerator.eval a r y=0
  · refine ⟨some zero,?_⟩
    simp only [residueCases,run_append,run_emit_one,run_emit_two]
    exact Or.inl (Or.inl ⟨⟨hn true,hN⟩,by simp⟩)
  · by_cases hM : inK (F.outer.eval a r y)
    · refine ⟨some F,?_⟩
      simp only [residueCases,run_append,run_emit_one,run_emit_two]
      exact Or.inl (Or.inr ⟨⟨hn false,hN⟩,⟨hm true,hM⟩,by simp⟩)
    · refine ⟨none,?_⟩
      simp only [residueCases,run_append,run_emit_one,run_emit_two]
      exact Or.inr ⟨⟨hn false,hN⟩,⟨hm false,hM⟩,by simp⟩

end RVFraction
end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: GuardedTermNormalization -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm
open FiniteGuardedBranches

namespace RVExpr
variable {I R V : Type}
noncomputable def addOutput : Option (RVFraction I R V) → Option (RVFraction I R V) → RVFraction I R V
  | some F,some G => F.residueAdd G
  | _,_ => RVFraction.zero
noncomputable def negOutput : Option (RVFraction I R V) → RVFraction I R V
  | some F => F.residueNeg
  | none => RVFraction.zero

/-- A finite branch program determined solely by the source syntax.
All parameter and variable indices remain the original ones. -/
noncomputable def normalize : RVExpr I R V → Program I R V (RVFraction I R V)
  | .zero => pure RVFraction.zero
  | .one => pure RVFraction.one
  | .vf P => pure (RVFraction.ofMonomial (Monomial.vf P))
  | .parameter i => emit [.parameterZero i true] RVFraction.zero ++
      emit [.parameterZero i false] (RVFraction.ofMonomial (Monomial.parameter i))
  | .ofVariable i => emit [.variableZero i true] RVFraction.zero ++
      emit [.variableZero i false] (RVFraction.ofMonomial (Monomial.ofVariable i))
  | .mul P Q => bind (normalize P) (fun F => bind (normalize Q) (fun G => pure (F.mul G)))
  | .inv P => bind (normalize P) RVFraction.inverseCases
  | .addK P Q => bind (normalize P) (fun F => bind (normalize Q) (fun G =>
      bind F.residueCases (fun H => bind G.residueCases (fun K => pure (addOutput H K)))))
  | .negK P => bind (normalize P) (fun F => bind F.residueCases (fun G => pure (negOutput G)))

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

include hv in
theorem addOutput_sound (F G : RVFraction I R V) (H K : Option (RVFraction I R V))
    (hF : F.Prepared a r y) (hG : G.Prepared a r y)
    (hH : H ∈ run (NFTest.holds a r y) F.residueCases)
    (hK : K ∈ run (NFTest.holds a r y) G.residueCases) :
    (addOutput H K).Prepared a r y ∧
      (addOutput H K).eval a r y = ValuedModelMap.addK (F.eval a r y) (G.eval a r y) := by
  have hsH := RVFraction.residueCases_sound a r y v hv F H hF hH
  have hsK := RVFraction.residueCases_sound a r y v hv G K hG hK
  cases H with
  | none =>
    refine ⟨RVFraction.prepared_zero a r y,?_⟩
    change RVFraction.zero.eval a r y = _
    rw [RVFraction.eval_zero,ValuedModelMap.addK_junk _ _ (Or.inl hsH),RVOperations.zeroRV_eq]
  | some H =>
    cases K with
    | none =>
      refine ⟨RVFraction.prepared_zero a r y,?_⟩
      change RVFraction.zero.eval a r y = _
      rw [RVFraction.eval_zero,ValuedModelMap.addK_junk _ _ (Or.inr hsK),RVOperations.zeroRV_eq]
    | some K =>
      exact ⟨RVFraction.prepared_residueAdd a r y v hv H K hsH.1 hsK.1 hsH.2.1 hsK.2.1,
        (RVFraction.eval_residueAdd a r y v hv H K hsH.1 hsK.1 hsH.2.1 hsK.2.1).trans
          (congrArg₂ ValuedModelMap.addK hsH.2.2 hsK.2.2)⟩

include hv in
theorem negOutput_sound (F : RVFraction I R V) (G : Option (RVFraction I R V))
    (hF : F.Prepared a r y) (hG : G ∈ run (NFTest.holds a r y) F.residueCases) :
    (negOutput G).Prepared a r y ∧
      (negOutput G).eval a r y = ValuedModelMap.negK (F.eval a r y) := by
  have hs := RVFraction.residueCases_sound a r y v hv F G hF hG
  cases G with
  | none =>
    refine ⟨RVFraction.prepared_zero a r y,?_⟩
    change RVFraction.zero.eval a r y = _
    rw [RVFraction.eval_zero,ValuedModelMap.negK_junk _ hs,RVOperations.zeroRV_eq]
  | some G =>
    exact ⟨RVFraction.prepared_residueNeg a r y G hs.1,
      (RVFraction.eval_residueNeg a r y v hv G hs.1 hs.2.1).trans (congrArg ValuedModelMap.negK hs.2.2)⟩

include hv in
theorem normalize_sound (P : RVExpr I R V) (F : RVFraction I R V)
    (hF : F ∈ run (NFTest.holds a r y) P.normalize) :
    F.Prepared a r y ∧ F.eval a r y=P.eval a r y := by
  induction P generalizing F with
  | zero =>
    have he := (run_pure _ _ _).mp hF
    subst F
    exact ⟨RVFraction.prepared_zero a r y,RVFraction.eval_zero a r y⟩
  | one =>
    have he := (run_pure _ _ _).mp hF
    subst F
    exact ⟨RVFraction.prepared_one a r y,RVFraction.eval_one a r y⟩
  | vf P =>
    have he := (run_pure _ _ _).mp hF
    subst F
    refine ⟨RVFraction.prepared_ofMonomial a r y _ one_ne_zero ?_,?_⟩
    · simp [Monomial.ProperSlots,Monomial.vf]
    · exact (RVFraction.eval_ofMonomial a r y _).trans (Monomial.eval_vf P a r y)
  | parameter i =>
    have he : (NFTest.holds a r y (.parameterZero i true) ∧ F=RVFraction.zero) ∨
        (NFTest.holds a r y (.parameterZero i false) ∧ F=RVFraction.ofMonomial (Monomial.parameter i)) := by
      simpa [normalize,run_append,run_emit,satisfied] using hF
    rcases he with ⟨hi,rfl⟩ | ⟨hi,rfl⟩
    · exact ⟨RVFraction.prepared_zero a r y,(RVFraction.eval_zero a r y).trans hi.2.symm⟩
    · refine ⟨RVFraction.prepared_ofMonomial a r y _ one_ne_zero ?_,?_⟩
      · have hi0 : r i ≠ 0 := hi.2
        simp [Monomial.ProperSlots,Monomial.parameter,hi0]
      · exact (RVFraction.eval_ofMonomial a r y _).trans (Monomial.eval_parameter a r y i hi.2)
  | ofVariable i =>
    have he : (NFTest.holds a r y (.variableZero i true) ∧ F=RVFraction.zero) ∨
        (NFTest.holds a r y (.variableZero i false) ∧ F=RVFraction.ofMonomial (Monomial.ofVariable i)) := by
      simpa [normalize,run_append,run_emit,satisfied] using hF
    rcases he with ⟨hi,rfl⟩ | ⟨hi,rfl⟩
    · exact ⟨RVFraction.prepared_zero a r y,(RVFraction.eval_zero a r y).trans hi.2.symm⟩
    · refine ⟨RVFraction.prepared_ofMonomial a r y _ one_ne_zero ?_,?_⟩
      · have hi0 : y i ≠ 0 := hi.2
        simp [Monomial.ProperSlots,Monomial.ofVariable,hi0]
      · exact (RVFraction.eval_ofMonomial a r y _).trans (Monomial.eval_variable a r y i hi.2)
  | mul P Q ihP ihQ =>
    obtain ⟨G,hG,hF⟩ := (run_bind _ _ _ _).mp hF
    obtain ⟨H,hH,hF⟩ := (run_bind _ _ _ _).mp hF
    have he := (run_pure _ _ _).mp hF
    subst F
    have hg := ihP G hG
    have hh := ihQ H hH
    exact ⟨RVFraction.prepared_mul a r y v hv G H hg.1 hh.1,
      (RVFraction.eval_mul a r y v hv G H hg.1 hh.1).trans (congrArg₂ (·*·) hg.2 hh.2)⟩
  | inv P ihP =>
    obtain ⟨G,hG,hF⟩ := (run_bind _ _ _ _).mp hF
    have hg := ihP G hG
    have hs := RVFraction.inverseCases_sound a r y G F hg.1 hF
    exact ⟨hs.1,hs.2.trans (congrArg Inv.inv hg.2)⟩
  | addK P Q ihP ihQ =>
    obtain ⟨G,hG,hF⟩ := (run_bind _ _ _ _).mp hF
    obtain ⟨H,hH,hF⟩ := (run_bind _ _ _ _).mp hF
    obtain ⟨J,hJ,hF⟩ := (run_bind _ _ _ _).mp hF
    obtain ⟨K,hK,hF⟩ := (run_bind _ _ _ _).mp hF
    have he := (run_pure _ _ _).mp hF
    subst F
    have hg := ihP G hG
    have hh := ihQ H hH
    have hs := addOutput_sound a r y v hv G H J K hg.1 hh.1 hJ hK
    exact ⟨hs.1,hs.2.trans (congrArg₂ ValuedModelMap.addK hg.2 hh.2)⟩
  | negK P ihP =>
    obtain ⟨G,hG,hF⟩ := (run_bind _ _ _ _).mp hF
    obtain ⟨H,hH,hF⟩ := (run_bind _ _ _ _).mp hF
    have he := (run_pure _ _ _).mp hF
    subst F
    have hg := ihP G hG
    have hs := negOutput_sound a r y v hv G H hg.1 hH
    exact ⟨hs.1,hs.2.trans (congrArg ValuedModelMap.negK hg.2)⟩

include hv in
theorem normalize_complete (P : RVExpr I R V) :
    ∃ F, F ∈ run (NFTest.holds a r y) P.normalize := by
  induction P with
  | zero => exact ⟨RVFraction.zero,(run_pure _ _ _).mpr rfl⟩
  | one => exact ⟨RVFraction.one,(run_pure _ _ _).mpr rfl⟩
  | vf P => exact ⟨RVFraction.ofMonomial (Monomial.vf P),(run_pure _ _ _).mpr rfl⟩
  | parameter i =>
    by_cases hi : r i=0 <;>
      simp [normalize,run_append,run_emit,satisfied,NFTest.holds,NFTest.Safe,NFTest.predicate,NFTest.signed,hi]
  | ofVariable i =>
    by_cases hi : y i=0 <;>
      simp [normalize,run_append,run_emit,satisfied,NFTest.holds,NFTest.Safe,NFTest.predicate,NFTest.signed,hi]
  | mul P Q ihP ihQ =>
    obtain ⟨F,hF⟩ := ihP
    obtain ⟨G,hG⟩ := ihQ
    refine ⟨F.mul G,(run_bind _ _ _ _).mpr ⟨F,hF,?_⟩⟩
    exact (run_bind _ _ _ _).mpr ⟨G,hG,(run_pure _ _ _).mpr rfl⟩
  | inv P ihP =>
    obtain ⟨F,hF⟩ := ihP
    obtain ⟨G,hG⟩ := RVFraction.inverseCases_complete a r y F (normalize_sound a r y v hv P F hF).1
    exact ⟨G,(run_bind _ _ _ _).mpr ⟨F,hF,hG⟩⟩
  | addK P Q ihP ihQ =>
    obtain ⟨F,hF⟩ := ihP
    obtain ⟨G,hG⟩ := ihQ
    obtain ⟨H,hH⟩ := RVFraction.residueCases_complete a r y F (normalize_sound a r y v hv P F hF).1
    obtain ⟨K,hK⟩ := RVFraction.residueCases_complete a r y G (normalize_sound a r y v hv Q G hG).1
    refine ⟨addOutput H K,(run_bind _ _ _ _).mpr ⟨F,hF,?_⟩⟩
    refine (run_bind _ _ _ _).mpr ⟨G,hG,?_⟩
    refine (run_bind _ _ _ _).mpr ⟨H,hH,?_⟩
    exact (run_bind _ _ _ _).mpr ⟨K,hK,(run_pure _ _ _).mpr rfl⟩
  | negK P ihP =>
    obtain ⟨F,hF⟩ := ihP
    obtain ⟨G,hG⟩ := RVFraction.residueCases_complete a r y F (normalize_sound a r y v hv P F hF).1
    refine ⟨negOutput G,(run_bind _ _ _ _).mpr ⟨F,hF,?_⟩⟩
    exact (run_bind _ _ _ _).mpr ⟨G,hG,(run_pure _ _ _).mpr rfl⟩

end RVExpr
end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: MonomialCoefficientNormalization -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap
namespace SpecialTransformations.Section3.GuardedRVNormalForm.Monomial
variable {I R V : Type}

def eraseCoefficient (T : Monomial I R V) : Monomial I R V :=
  ⟨T.numerator,T.denominator,0,T.powers⟩
noncomputable def divideCoefficient (T U : Monomial I R V) : Monomial I R V :=
  ⟨T.numerator,T.denominator,T.coefficient-U.coefficient,T.powers⟩

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)

theorem rawEval_parameter (i : R) : rawEval (parameter i) a r y = r i := by
  simp only [rawEval,parameter,VFPolynomial.realize_one,map_one,one_div_one,
    Finsupp.prod_single_index,Finsupp.prod_zero_index,zpow_one,zpow_zero,one_mul,mul_one]

theorem rawEval_variable (i : V) : rawEval (ofVariable i) a r y = y i := by
  simp only [rawEval,ofVariable,VFPolynomial.realize_one,map_one,one_div_one,
    Finsupp.prod_single_index,Finsupp.prod_zero_index,zpow_one,zpow_zero,one_mul,mul_one]

theorem eval_eraseCoefficient (T : Monomial I R V) :
    (eraseCoefficient T).eval a r y = T.eval a r y / LaurentWords.eval r T.coefficient := by
  apply (eq_div_iff (LaurentWords.eval_ne_zero r T.coefficient)).mpr
  simp only [eval,eraseCoefficient,LaurentWords.eval_zero,mul_one]
  ac_rfl

theorem eval_divideCoefficient (T U : Monomial I R V) :
    (divideCoefficient T U).eval a r y = T.eval a r y / LaurentWords.eval r U.coefficient := by
  simp only [eval,divideCoefficient,sub_eq_add_neg,LaurentWords.eval_add,LaurentWords.eval_neg,
    div_eq_mul_inv,mul_assoc]
  rw [mul_comm (LaurentWords.eval r U.coefficient)⁻¹ (LaurentWords.eval y T.powers)]

theorem properSlots_eraseCoefficient (T : Monomial I R V) (hT : T.ProperSlots r y) :
    (eraseCoefficient T).ProperSlots r y := by
  exact ⟨by simp [eraseCoefficient],hT.2⟩

theorem properSlots_divideCoefficient (T U : Monomial I R V)
    (hT : T.ProperSlots r y) (hU : U.ProperSlots r y) :
    (divideCoefficient T U).ProperSlots r y := by
  constructor
  · intro i hi
    change i ∈ (T.coefficient-U.coefficient).support at hi
    rw [sub_eq_add_neg] at hi
    rcases Finset.mem_union.mp (Finsupp.support_add hi) with hi | hi
    · exact hT.1 i hi
    · exact hU.1 i (by simpa only [Finsupp.support_neg] using hi)
  · exact hT.2

theorem coefficient_normalize_equality (T U : Monomial I R V) (x z : RVSort M) :
    T.eval a r y*x=U.eval a r y*z ↔
      (eraseCoefficient T).eval a r y*x=(divideCoefficient U T).eval a r y*z := by
  rw [eval_eraseCoefficient,eval_divideCoefficient,div_mul_eq_mul_div₀,div_mul_eq_mul_div₀]
  exact (div_left_inj' (LaurentWords.eval_ne_zero r T.coefficient)).symm

end SpecialTransformations.Section3.GuardedRVNormalForm.Monomial

/- Component: NormalFormExpressionCompilation -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap
namespace SpecialTransformations.Section3.GuardedRVNormalForm

namespace RVExpr
variable {I R V : Type}
def npow (P : RVExpr I R V) : ℕ → RVExpr I R V
  | 0 => .one
  | n+1 => .mul P (npow P n)
def zpow (P : RVExpr I R V) : ℤ → RVExpr I R V
  | .ofNat n => npow P n
  | .negSucc n => .inv (npow P (n+1))
def productList : List (RVExpr I R V) → RVExpr I R V
  | [] => .one
  | P::Ps => .mul P (productList Ps)
noncomputable def coefficientWord (w : R →₀ ℤ) : RVExpr I R V :=
  productList (w.support.toList.map (fun i => zpow (.parameter i) (w i)))
noncomputable def variableWord (w : V →₀ ℤ) : RVExpr I R V :=
  productList (w.support.toList.map (fun i => zpow (.ofVariable i) (w i)))

def sumFin : {n : ℕ} → (Fin n → RVExpr I R V) → RVExpr I R V
  | 0,_ => .zero
  | n+1,f => .addK (f 0) (sumFin (fun i : Fin n => f i.succ))

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)

theorem eval_npow (P : RVExpr I R V) (n : ℕ) :
    (npow P n).eval a r y=(P.eval a r y)^n := by
  induction n with
  | zero => simp only [npow,eval,pow_zero]
  | succ n ih => simp only [npow,eval,ih,pow_succ']

theorem eval_zpow (P : RVExpr I R V) (n : ℤ) :
    (zpow P n).eval a r y=(P.eval a r y)^n := by
  cases n with
  | ofNat n =>
    change (npow P n).eval a r y=(P.eval a r y)^(n : ℤ)
    rw [zpow_natCast]
    exact eval_npow a r y P n
  | negSucc n =>
    simp only [zpow,eval,eval_npow,zpow_negSucc]

theorem eval_productList (Ps : List (RVExpr I R V)) :
    (productList Ps).eval a r y=(Ps.map (eval a r y)).prod := by
  induction Ps with
  | nil => rfl
  | cons P Ps ih => exact congrArg (fun z => P.eval a r y*z) ih

theorem eval_coefficientWord (w : R →₀ ℤ) :
    (coefficientWord w : RVExpr I R V).eval a r y=w.prod (fun i n => r i^n) := by
  simp only [coefficientWord,eval_productList,List.map_map,Function.comp_def,eval_zpow,eval]
  exact Finset.prod_map_toList _ _

theorem eval_variableWord (w : V →₀ ℤ) :
    (variableWord w : RVExpr I R V).eval a r y=w.prod (fun i n => y i^n) := by
  simp only [variableWord,eval_productList,List.map_map,Function.comp_def,eval_zpow,eval]
  exact Finset.prod_map_toList _ _

theorem eval_sumFin {n : ℕ} (f : Fin n → RVExpr I R V) :
    (sumFin f).eval a r y=KPolynomial.rvSum (fun i => (f i).eval a r y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact congrArg (ValuedModelMap.addK ((f 0).eval a r y)) (ih (fun i : Fin n => f i.succ))
end RVExpr

namespace Monomial
variable {I R V : Type}
noncomputable def expression (T : Monomial I R V) : RVExpr I R V :=
  .mul (.mul (.mul (.vf T.numerator) (.inv (.vf T.denominator)))
    (RVExpr.coefficientWord T.coefficient)) (RVExpr.variableWord T.powers)

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
theorem expression_eval (T : Monomial I R V) (a : I → VFType (M := M))
    (r : R → RVSort M) (y : V → RVSort M) :
    T.expression.eval a r y=T.rawEval a r y := by
  simp only [expression,RVExpr.eval,RVExpr.eval_coefficientWord,RVExpr.eval_variableWord,
    rawEval,div_eq_mul_inv]
end Monomial

namespace KPolynomial
variable {I R V : Type}
noncomputable def expression (P : KPolynomial I R V) : RVExpr I R V :=
  RVExpr.sumFin (fun i => (P.terms i).expression)

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
theorem expression_eval (P : KPolynomial I R V) (a : I → VFType (M := M))
    (r : R → RVSort M) (y : V → RVSort M) :
    P.expression.eval a r y=P.rawEval a r y := by
  simp only [expression,RVExpr.eval_sumFin,Monomial.expression_eval,rawEval]
end KPolynomial

end SpecialTransformations.Section3.GuardedRVNormalForm
