import Section3.GuardedRVArithmetic
import Section3.GuardedRVTerms

/-!
# GuardedRVLiterals

Signed equality and valuation literals with flat residue factors and explicit
guard clauses. Every raw-true clause certifies the domains of all its literals;
Boolean normalization preserves that certificate.

See NORMAL-FORM-NOTE.md for the agreed statement and language conventions.
-/

/- Component: GuardedLiteralSyntax -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm


namespace Monomial
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable {I R V M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- The syntax compiler uses only named RV inverse; its VF factor is the
leading term of the usual rational VF function on the explicit pole guard. -/
theorem rawEval_rational (T : Monomial I R V) (a : I → VFType (M := M))
    (r : R → RVSort M) (y : V → RVSort M) :
    T.rawEval a r y = RVOperations.rvHom (T.numerator.realize a / T.denominator.realize a) *
      T.coefficient.prod (fun i n => r i^n) * T.powers.prod (fun i n => y i^n) := by
  simp only [rawEval,map_div₀]
end Monomial

/-- Flat equality/inequality payload with the printed left coefficient one. -/
structure EqualityPayload (I R V : Type) where
  left : Monomial I R V
  left_coefficient : left.coefficient=0
  leftK : KPolynomial I R V
  right : Monomial I R V
  rightK : KPolynomial I R V

/-- Valuation comparisons have no residue-sum factor. -/
structure OrderPayload (I R V : Type) where
  left : Monomial I R V
  left_coefficient : left.coefficient=0
  right : Monomial I R V

inductive RVLiteral (I R V : Type) where
  | equality : EqualityPayload I R V → Bool → RVLiteral I R V
  | order : OrderPayload I R V → Bool → RVLiteral I R V

namespace RVLiteral
variable {I R V M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def Domain (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) : RVLiteral I R V → Prop
  | .equality E _ => E.left.PoleFree a ∧ E.leftK.Domain a r y ∧ E.right.PoleFree a ∧ E.rightK.Domain a r y
  | .order E _ => E.left.PoleFree a ∧ E.right.PoleFree a

noncomputable def comparison (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) :
    RVLiteral I R V → Prop
  | .equality E pos => NFTest.signed pos
      (E.left.rawEval a r y * E.leftK.rawEval a r y = E.right.rawEval a r y * E.rightK.rawEval a r y)
  | .order E pos => NFTest.signed pos (iLe (E.left.rawEval a r y).val (E.right.rawEval a r y).val)

noncomputable def holds (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)
    (L : RVLiteral I R V) : Prop := Domain a r y L ∧ comparison a r y L
end RVLiteral

namespace RVFraction
variable {I R V : Type}
noncomputable def equalityLiteral (F G : RVFraction I R V) (pos : Bool) : RVLiteral I R V :=
  .equality ⟨F.outer.eraseCoefficient,rfl,F.numerator.mul G.denominator,
    G.outer.divideCoefficient F.outer,G.numerator.mul F.denominator⟩ pos

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

include hv in
theorem equalityLiteral_domain (F G : RVFraction I R V) (pos : Bool)
    (hF : F.Prepared a r y) (hG : G.Prepared a r y) :
    RVLiteral.Domain a r y (equalityLiteral F G pos) := by
  exact ⟨hF.pole,
    KPolynomial.prepared_domain _ a r y (KPolynomial.prepared_mul v hv _ _ a r y hF.numerator hG.denominator),
    hG.pole,
    KPolynomial.prepared_domain _ a r y (KPolynomial.prepared_mul v hv _ _ a r y hG.numerator hF.denominator)⟩

include hv in
theorem equalityLiteral_correct (F G : RVFraction I R V) (pos : Bool)
    (hF : F.Prepared a r y) (hG : G.Prepared a r y) :
    RVLiteral.holds a r y (equalityLiteral F G pos) ↔ NFTest.signed pos (F.eval a r y=G.eval a r y) := by
  have hL := KPolynomial.prepared_mul v hv _ _ a r y hF.numerator hG.denominator
  have hR := KPolynomial.prepared_mul v hv _ _ a r y hG.numerator hF.denominator
  have hsL := Monomial.properSlots_eraseCoefficient r y F.outer hF.slots
  have hsR := Monomial.properSlots_divideCoefficient r y G.outer F.outer hG.slots hF.slots
  have hd := equalityLiteral_domain a r y v hv F G pos hF hG
  have hc : RVLiteral.comparison a r y (equalityLiteral F G pos) ↔
      NFTest.signed pos (F.eval a r y=G.eval a r y) := by
    simp only [RVLiteral.comparison,equalityLiteral]
    rw [← Monomial.eval_eq_rawEval _ a r y hsL,← Monomial.eval_eq_rawEval _ a r y hsR,
      ← KPolynomial.prepared_eval_eq_rawEval _ a r y hL,← KPolynomial.prepared_eval_eq_rawEval _ a r y hR,
      KPolynomial.eval_mul v hv _ _ a r y hF.numerator hG.denominator,
      KPolynomial.eval_mul v hv _ _ a r y hG.numerator hF.denominator]
    have he : F.outer.eval a r y*(F.numerator.eval a r y*G.denominator.eval a r y) =
        G.outer.eval a r y*(G.numerator.eval a r y*F.denominator.eval a r y) ↔ F.eval a r y=G.eval a r y := by
      simp only [eval]
      rw [div_eq_div_iff hF.denominator_ne_zero hG.denominator_ne_zero]
      simp only [mul_assoc]
    have hh := Monomial.coefficient_normalize_equality a r y F.outer G.outer
      (F.numerator.eval a r y*G.denominator.eval a r y)
      (G.numerator.eval a r y*F.denominator.eval a r y)
    cases pos <;> simp only [NFTest.signed,Bool.false_eq_true,if_false,if_true]
    · exact not_congr (hh.symm.trans he)
    · exact hh.symm.trans he
  exact ⟨fun h => hc.mp h.2,fun h => ⟨hd,hc.mpr h⟩⟩

end RVFraction
end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: GuardedOrderNormalization -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm
open FiniteGuardedBranches

theorem rvLe_iff_absolute {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (x y : RVSort M) : iLe x.val y.val ↔ RVOperations.absoluteHom y ≤ RVOperations.absoluteHom x :=
  Values.valueEquiv_rv_le Values.presentationValuation Values.presentation_compatible x y

namespace Monomial
variable {I R V M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)

theorem coefficient_normalize_order (T U : Monomial I R V) :
    iLe (T.eval a r y).val (U.eval a r y).val ↔
      iLe ((eraseCoefficient T).eval a r y).val ((divideCoefficient U T).eval a r y).val := by
  have hc : RVOperations.absoluteHom (LaurentWords.eval r T.coefficient) ≠ 0 := by
    intro h
    exact LaurentWords.eval_ne_zero r T.coefficient ((RVOperations.absolute_eq_zero _).mp h)
  rw [rvLe_iff_absolute,rvLe_iff_absolute,eval_eraseCoefficient,eval_divideCoefficient,map_div₀,map_div₀]
  exact (div_le_div_iff_of_pos_right (lt_of_le_of_ne zero_le (Ne.symm hc))).symm
end Monomial

namespace RVFraction
variable {I R V : Type}
noncomputable def valueCases (F : RVFraction I R V) : Program I R V (Monomial I R V) :=
  emit [.polynomialZero F.numerator true] Monomial.zero ++
    emit [.polynomialZero F.numerator false] F.outer

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

include hv in
theorem absolute_eq_outer (F : RVFraction I R V) (hF : F.Prepared a r y)
    (hN : F.numerator.eval a r y ≠ 0) :
    RVOperations.absoluteHom (F.eval a r y)=RVOperations.absoluteHom (F.outer.eval a r y) := by
  have hNK := KPolynomial.eval_inK v hv _ a r y (fun i => (hF.numerator i).2.2)
  have hDK := KPolynomial.eval_inK v hv _ a r y (fun i => (hF.denominator i).2.2)
  have hn := ((RVOperations.inK_iff _).mp hNK).resolve_left hN
  have hd := ((RVOperations.inK_iff _).mp hDK).resolve_left hF.denominator_ne_zero
  simp only [eval,map_div₀,map_mul,hn,hd,mul_one,div_one]

include hv in
theorem valueCases_sound (F : RVFraction I R V) (T : Monomial I R V)
    (hF : F.Prepared a r y) (hT : T ∈ run (NFTest.holds a r y) F.valueCases) :
    T.PoleFree a ∧ T.ProperSlots r y ∧
      RVOperations.absoluteHom (F.eval a r y)=RVOperations.absoluteHom (T.eval a r y) := by
  have hs : (NFTest.holds a r y (.polynomialZero F.numerator true) ∧ T=Monomial.zero) ∨
      (NFTest.holds a r y (.polynomialZero F.numerator false) ∧ T=F.outer) := by
    simpa [valueCases,run_append,run_emit,satisfied] using hT
  rcases hs with ⟨hn,rfl⟩ | ⟨hn,rfl⟩
  · refine ⟨one_ne_zero,?_,?_⟩
    · simp [Monomial.ProperSlots,Monomial.zero]
    · have hN : F.numerator.eval a r y=0 := hn.2
      simp only [eval,hN,mul_zero,zero_div,Monomial.eval_zero,map_zero]
  · exact ⟨hF.pole,hF.slots,absolute_eq_outer a r y v hv F hF hn.2⟩

theorem valueCases_complete (F : RVFraction I R V) (hF : F.Prepared a r y) :
    ∃ T, T ∈ run (NFTest.holds a r y) F.valueCases := by
  by_cases hn : F.numerator.eval a r y=0
  · refine ⟨Monomial.zero,?_⟩
    simp only [valueCases,run_append]
    apply Or.inl
    exact (run_emit _ _ _ _).mpr ⟨by
      simpa [satisfied] using (show NFTest.holds a r y (.polynomialZero F.numerator true) from ⟨hF.numerator,hn⟩),rfl⟩
  · refine ⟨F.outer,?_⟩
    simp only [valueCases,run_append]
    apply Or.inr
    exact (run_emit _ _ _ _).mpr ⟨by
      simpa [satisfied] using (show NFTest.holds a r y (.polynomialZero F.numerator false) from ⟨hF.numerator,hn⟩),rfl⟩
end RVFraction
end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: GuardedAtomPrograms -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm
open FiniteGuardedBranches

variable {I R V : Type}
noncomputable def monomialOrderLiteral (T U : Monomial I R V) (pos : Bool) : RVLiteral I R V :=
  .order ⟨T.eraseCoefficient,rfl,U.divideCoefficient T⟩ pos

noncomputable def equalityProgram (P Q : RVExpr I R V) (pos : Bool) : Program I R V (RVLiteral I R V) :=
  bind P.normalize (fun F => bind Q.normalize (fun G => pure (F.equalityLiteral G pos)))

noncomputable def orderProgram (P Q : RVExpr I R V) (pos : Bool) : Program I R V (RVLiteral I R V) :=
  bind P.normalize (fun F => bind Q.normalize (fun G => bind F.valueCases (fun T =>
    bind G.valueCases (fun U => pure (monomialOrderLiteral T U pos)))))

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

theorem monomialOrderLiteral_correct (T U : Monomial I R V) (pos : Bool)
    (hpT : T.PoleFree a) (hsT : T.ProperSlots r y) (hpU : U.PoleFree a) (hsU : U.ProperSlots r y) :
    RVLiteral.holds a r y (monomialOrderLiteral T U pos) ↔
      NFTest.signed pos (iLe (T.eval a r y).val (U.eval a r y).val) := by
  have hd : RVLiteral.Domain a r y (monomialOrderLiteral T U pos) := ⟨hpT,hpU⟩
  have hsL := Monomial.properSlots_eraseCoefficient r y T hsT
  have hsR := Monomial.properSlots_divideCoefficient r y U T hsU hsT
  have hc : RVLiteral.comparison a r y (monomialOrderLiteral T U pos) ↔
      NFTest.signed pos (iLe (T.eval a r y).val (U.eval a r y).val) := by
    simp only [RVLiteral.comparison,monomialOrderLiteral]
    rw [← Monomial.eval_eq_rawEval _ a r y hsL,← Monomial.eval_eq_rawEval _ a r y hsR]
    have he := Monomial.coefficient_normalize_order a r y T U
    cases pos <;> simp only [NFTest.signed,Bool.false_eq_true,if_false,if_true]
    · exact not_congr he.symm
    · exact he.symm
  exact ⟨fun h => hc.mp h.2,fun h => ⟨hd,hc.mpr h⟩⟩

include hv in
theorem equalityProgram_correct (P Q : RVExpr I R V) (pos : Bool) :
    (∃ L ∈ run (NFTest.holds a r y) (equalityProgram P Q pos), RVLiteral.holds a r y L) ↔
      NFTest.signed pos (P.eval a r y=Q.eval a r y) := by
  constructor
  · rintro ⟨L,hL,hc⟩
    obtain ⟨F,hF,hL⟩ := (run_bind _ _ _ _).mp hL
    obtain ⟨G,hG,hL⟩ := (run_bind _ _ _ _).mp hL
    have he := (run_pure _ _ _).mp hL
    subst L
    have hf := RVExpr.normalize_sound a r y v hv P F hF
    have hg := RVExpr.normalize_sound a r y v hv Q G hG
    have hh := (RVFraction.equalityLiteral_correct a r y v hv F G pos hf.1 hg.1).mp hc
    rwa [hf.2,hg.2] at hh
  · intro hc
    obtain ⟨F,hF⟩ := RVExpr.normalize_complete a r y v hv P
    obtain ⟨G,hG⟩ := RVExpr.normalize_complete a r y v hv Q
    have hf := RVExpr.normalize_sound a r y v hv P F hF
    have hg := RVExpr.normalize_sound a r y v hv Q G hG
    refine ⟨F.equalityLiteral G pos,(run_bind _ _ _ _).mpr ⟨F,hF,?_⟩,?_⟩
    · exact (run_bind _ _ _ _).mpr ⟨G,hG,(run_pure _ _ _).mpr rfl⟩
    · apply (RVFraction.equalityLiteral_correct a r y v hv F G pos hf.1 hg.1).mpr
      rwa [hf.2,hg.2]

include hv in
theorem orderProgram_correct (P Q : RVExpr I R V) (pos : Bool) :
    (∃ L ∈ run (NFTest.holds a r y) (orderProgram P Q pos), RVLiteral.holds a r y L) ↔
      NFTest.signed pos (iLe (P.eval a r y).val (Q.eval a r y).val) := by
  have hvalue (F G : RVFraction I R V) (T U : Monomial I R V)
      (hF : F.Prepared a r y) (hG : G.Prepared a r y)
      (hT : T ∈ run (NFTest.holds a r y) F.valueCases)
      (hU : U ∈ run (NFTest.holds a r y) G.valueCases) :
      RVLiteral.holds a r y (monomialOrderLiteral T U pos) ↔
        NFTest.signed pos (iLe (F.eval a r y).val (G.eval a r y).val) := by
    have ht := RVFraction.valueCases_sound a r y v hv F T hF hT
    have hu := RVFraction.valueCases_sound a r y v hv G U hG hU
    rw [monomialOrderLiteral_correct a r y T U pos ht.1 ht.2.1 hu.1 hu.2.1]
    have he : iLe (T.eval a r y).val (U.eval a r y).val ↔ iLe (F.eval a r y).val (G.eval a r y).val := by
      rw [rvLe_iff_absolute,rvLe_iff_absolute,← ht.2.2,← hu.2.2]
    cases pos <;> simp only [NFTest.signed,Bool.false_eq_true,if_false,if_true]
    · exact not_congr he
    · exact he
  constructor
  · rintro ⟨L,hL,hc⟩
    obtain ⟨F,hF,hL⟩ := (run_bind _ _ _ _).mp hL
    obtain ⟨G,hG,hL⟩ := (run_bind _ _ _ _).mp hL
    obtain ⟨T,hT,hL⟩ := (run_bind _ _ _ _).mp hL
    obtain ⟨U,hU,hL⟩ := (run_bind _ _ _ _).mp hL
    have he := (run_pure _ _ _).mp hL
    subst L
    have hf := RVExpr.normalize_sound a r y v hv P F hF
    have hg := RVExpr.normalize_sound a r y v hv Q G hG
    have hh := (hvalue F G T U hf.1 hg.1 hT hU).mp hc
    rwa [hf.2,hg.2] at hh
  · intro hc
    obtain ⟨F,hF⟩ := RVExpr.normalize_complete a r y v hv P
    obtain ⟨G,hG⟩ := RVExpr.normalize_complete a r y v hv Q
    have hf := RVExpr.normalize_sound a r y v hv P F hF
    have hg := RVExpr.normalize_sound a r y v hv Q G hG
    obtain ⟨T,hT⟩ := RVFraction.valueCases_complete a r y F hf.1
    obtain ⟨U,hU⟩ := RVFraction.valueCases_complete a r y G hg.1
    refine ⟨monomialOrderLiteral T U pos,(run_bind _ _ _ _).mpr ⟨F,hF,?_⟩,?_⟩
    · refine (run_bind _ _ _ _).mpr ⟨G,hG,?_⟩
      refine (run_bind _ _ _ _).mpr ⟨T,hT,?_⟩
      exact (run_bind _ _ _ _).mpr ⟨U,hU,(run_pure _ _ _).mpr rfl⟩
    · apply (hvalue F G T U hf.1 hg.1 hT hU).mpr
      rwa [hf.2,hg.2]

end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: PrimitiveGuardLiterals -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm

namespace Monomial
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable {I R V M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
theorem rawEval_zero (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) :
    (zero : Monomial I R V).rawEval a r y=0 := by
  simp only [rawEval,zero,VFPolynomial.realize_zero,map_zero,zero_div,zero_mul]
theorem rawEval_one (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) :
    (one : Monomial I R V).rawEval a r y=1 := by
  simp only [rawEval,one,VFPolynomial.realize_one,map_one,one_div_one,Finsupp.prod_zero_index,one_mul]
theorem rawEval_vf (P : VFPolynomial I) (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) :
    (vf P : Monomial I R V).rawEval a r y=RVOperations.rvHom (P.realize a) := by
  simp only [rawEval,vf,VFPolynomial.realize_one,map_one,div_one,Finsupp.prod_zero_index,mul_one]
end Monomial

namespace KPolynomial
variable {I R V M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
theorem rawEval_one (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) :
    (one : KPolynomial I R V).rawEval a r y=1 :=
  (prepared_eval_eq_rawEval one a r y (prepared_one a r y)).symm.trans (eval_one a r y)
theorem domain_one (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) :
    (one : KPolynomial I R V).Domain a r y := prepared_domain one a r y (prepared_one a r y)
end KPolynomial

namespace RVLiteral
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable {I R V : Type}
def monomialZero (T : Monomial I R V) (pos : Bool) : RVLiteral I R V :=
  .equality ⟨Monomial.zero,rfl,KPolynomial.one,T,KPolynomial.one⟩ pos
def polynomialZero (P : KPolynomial I R V) (pos : Bool) : RVLiteral I R V :=
  .equality ⟨Monomial.one,rfl,P,Monomial.zero,KPolynomial.one⟩ pos
def poleGuard (T : Monomial I R V) : RVLiteral I R V := monomialZero (Monomial.vf T.denominator) false

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)

theorem monomialZero_correct (T : Monomial I R V) (pos : Bool) :
    holds a r y (monomialZero T pos) ↔ T.PoleFree a ∧ NFTest.signed pos (T.rawEval a r y=0) := by
  have hd : Domain a r y (monomialZero T pos) ↔ T.PoleFree a := by
    exact ⟨fun h => h.2.2.1,fun h => ⟨one_ne_zero,KPolynomial.domain_one a r y,h,KPolynomial.domain_one a r y⟩⟩
  have hc : comparison a r y (monomialZero T pos) ↔ NFTest.signed pos (T.rawEval a r y=0) := by
    change NFTest.signed pos (Monomial.zero.rawEval a r y*KPolynomial.one.rawEval a r y =
      T.rawEval a r y*KPolynomial.one.rawEval a r y) ↔ _
    rw [Monomial.rawEval_zero,KPolynomial.rawEval_one,zero_mul,mul_one]
    cases pos <;> simp only [NFTest.signed,Bool.false_eq_true,if_false,if_true,eq_comm]
  exact and_congr hd hc

theorem polynomialZero_correct (P : KPolynomial I R V) (pos : Bool) :
    holds a r y (polynomialZero P pos) ↔ P.Domain a r y ∧ NFTest.signed pos (P.rawEval a r y=0) := by
  have hd : Domain a r y (polynomialZero P pos) ↔ P.Domain a r y := by
    exact ⟨fun h => h.2.1,fun h => ⟨one_ne_zero,h,one_ne_zero,KPolynomial.domain_one a r y⟩⟩
  have hc : comparison a r y (polynomialZero P pos) ↔ NFTest.signed pos (P.rawEval a r y=0) := by
    change NFTest.signed pos (Monomial.one.rawEval a r y*P.rawEval a r y =
      Monomial.zero.rawEval a r y*KPolynomial.one.rawEval a r y) ↔ _
    rw [Monomial.rawEval_one,Monomial.rawEval_zero,KPolynomial.rawEval_one,one_mul,zero_mul]
  exact and_congr hd hc

theorem poleGuard_correct (T : Monomial I R V) : holds a r y (poleGuard T) ↔ T.PoleFree a := by
  rw [poleGuard,monomialZero_correct]
  change (1 : VFType (M := M)) ≠ 0 ∧ ¬ ((Monomial.vf T.denominator).rawEval a r y=0) ↔ T.denominator.realize a ≠ 0
  constructor
  · intro h
    apply (RVOperations.rv_ne_zero _).mp
    have h0 := h.2
    rwa [Monomial.rawEval_vf] at h0
  · intro h
    refine ⟨one_ne_zero,?_⟩
    rw [Monomial.rawEval_vf]
    exact (RVOperations.rv_ne_zero _).mpr h

noncomputable def parameterGuards (w : R →₀ ℤ) : List (RVLiteral I R V) :=
  w.support.toList.map (fun i => monomialZero (Monomial.parameter i) false)
noncomputable def variableGuards (w : V →₀ ℤ) : List (RVLiteral I R V) :=
  w.support.toList.map (fun i => monomialZero (Monomial.ofVariable i) false)
noncomputable def slotGuards (T : Monomial I R V) : List (RVLiteral I R V) :=
  parameterGuards T.coefficient ++ variableGuards T.powers

theorem parameterGuards_correct (w : R →₀ ℤ) :
    (∀ L ∈ parameterGuards w, holds a r y L) ↔ ∀ i ∈ w.support, r i ≠ 0 := by
  constructor
  · intro h i hi
    have hm := h (monomialZero (Monomial.parameter i) false) (List.mem_map.mpr ⟨i,by simpa using hi,rfl⟩)
    have h0 : (Monomial.parameter i).rawEval a r y ≠ 0 := ((monomialZero_correct a r y _ false).mp hm).2
    rwa [Monomial.rawEval_parameter] at h0
  · intro h L hL
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hL
    apply (monomialZero_correct a r y _ false).mpr
    refine ⟨one_ne_zero,?_⟩
    change (Monomial.parameter i).rawEval a r y ≠ 0
    rw [Monomial.rawEval_parameter]
    exact h i (by simpa using hi)

theorem variableGuards_correct (w : V →₀ ℤ) :
    (∀ L ∈ variableGuards w, holds a r y L) ↔ ∀ i ∈ w.support, y i ≠ 0 := by
  constructor
  · intro h i hi
    have hm := h (monomialZero (Monomial.ofVariable i) false) (List.mem_map.mpr ⟨i,by simpa using hi,rfl⟩)
    have h0 : (Monomial.ofVariable i).rawEval a r y ≠ 0 := ((monomialZero_correct a r y _ false).mp hm).2
    rwa [Monomial.rawEval_variable] at h0
  · intro h L hL
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hL
    apply (monomialZero_correct a r y _ false).mpr
    refine ⟨one_ne_zero,?_⟩
    change (Monomial.ofVariable i).rawEval a r y ≠ 0
    rw [Monomial.rawEval_variable]
    exact h i (by simpa using hi)

theorem slotGuards_correct (T : Monomial I R V) :
    (∀ L ∈ slotGuards T, holds a r y L) ↔ T.ProperSlots r y := by
  rw [slotGuards]
  have he := FiniteGuardedBranches.satisfied_append (holds a r y)
    (parameterGuards (I := I) (V := V) T.coefficient) (variableGuards (I := I) (R := R) T.powers)
  exact he.trans (and_congr (parameterGuards_correct a r y _) (variableGuards_correct a r y _))

end RVLiteral
end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: GuardTestDNF -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm

abbrev LiteralDNF (I R V : Type) := PolarityDNF.DNF (RVLiteral I R V)

namespace LiteralDNF
variable {I R V : Type}
def single (L : RVLiteral I R V) : LiteralDNF I R V := [ [L] ]
noncomputable def safe (T : Monomial I R V) : LiteralDNF I R V :=
  [RVLiteral.poleGuard T :: RVLiteral.slotGuards T]
noncomputable def monomialZero (T : Monomial I R V) (pos : Bool) : LiteralDNF I R V :=
  PolarityDNF.conj (safe T) (single (RVLiteral.monomialZero T pos))
noncomputable def residueBranch (T : Monomial I R V) (pos : Bool) : LiteralDNF I R V :=
  if pos then PolarityDNF.disj (single (RVLiteral.monomialZero T true))
    (PolarityDNF.conj (single (monomialOrderLiteral T Monomial.one true))
      (single (monomialOrderLiteral Monomial.one T true)))
  else PolarityDNF.conj (single (RVLiteral.monomialZero T false))
    (PolarityDNF.disj (single (monomialOrderLiteral T Monomial.one false))
      (single (monomialOrderLiteral Monomial.one T false)))
noncomputable def monomialResidue (T : Monomial I R V) (pos : Bool) : LiteralDNF I R V :=
  PolarityDNF.conj (safe T) (residueBranch T pos)

def all : List (LiteralDNF I R V) → LiteralDNF I R V
  | [] => [ [] ]
  | D::Ds => PolarityDNF.conj D (all Ds)
noncomputable def prepared (P : KPolynomial I R V) : LiteralDNF I R V :=
  all ((List.finRange P.size).map (fun i => monomialResidue (P.terms i) true))
noncomputable def polynomialZero (P : KPolynomial I R V) (pos : Bool) : LiteralDNF I R V :=
  PolarityDNF.conj (prepared P) (single (RVLiteral.polynomialZero P pos))
noncomputable def test : NFTest I R V → LiteralDNF I R V
  | .parameterZero i pos => single (RVLiteral.monomialZero (Monomial.parameter i) pos)
  | .variableZero i pos => single (RVLiteral.monomialZero (Monomial.ofVariable i) pos)
  | .monomialZero T pos => monomialZero T pos
  | .polynomialZero P pos => polynomialZero P pos
  | .monomialResidue T pos => monomialResidue T pos

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)

theorem single_correct (L : RVLiteral I R V) :
    PolarityDNF.holds (RVLiteral.holds a r y) (single L) ↔ RVLiteral.holds a r y L := by
  simp [single,PolarityDNF.holds]

theorem safe_correct (T : Monomial I R V) :
    PolarityDNF.holds (RVLiteral.holds a r y) (safe T) ↔ T.PoleFree a ∧ T.ProperSlots r y := by
  simp only [safe,PolarityDNF.holds,List.mem_singleton,exists_eq_left]
  have he : (∀ L ∈ RVLiteral.poleGuard T :: RVLiteral.slotGuards T, RVLiteral.holds a r y L) ↔
      RVLiteral.holds a r y (RVLiteral.poleGuard T) ∧ (∀ L ∈ RVLiteral.slotGuards T, RVLiteral.holds a r y L) := by
    simp
  exact he.trans (and_congr (RVLiteral.poleGuard_correct a r y T) (RVLiteral.slotGuards_correct a r y T))

theorem all_correct (Ds : List (LiteralDNF I R V)) :
    PolarityDNF.holds (RVLiteral.holds a r y) (all Ds) ↔
      ∀ D ∈ Ds, PolarityDNF.holds (RVLiteral.holds a r y) D := by
  induction Ds with
  | nil => simp [all,PolarityDNF.holds]
  | cons D Ds ih => simp [all,PolarityDNF.holds_conj,ih]

theorem monomialZero_correct (T : Monomial I R V) (pos : Bool) :
    PolarityDNF.holds (RVLiteral.holds a r y) (monomialZero T pos) ↔
      NFTest.holds a r y (.monomialZero T pos) := by
  rw [monomialZero,PolarityDNF.holds_conj,safe_correct,single_correct,RVLiteral.monomialZero_correct]
  simp only [NFTest.holds,NFTest.Safe,NFTest.predicate]
  constructor
  · rintro ⟨⟨hp,hs⟩,_,he⟩
    exact ⟨⟨hp,hs⟩,by rwa [Monomial.eval_eq_rawEval T a r y hs]⟩
  · rintro ⟨⟨hp,hs⟩,he⟩
    exact ⟨⟨hp,hs⟩,hp,by rwa [Monomial.eval_eq_rawEval T a r y hs] at he⟩

theorem inK_iff_zero_or_orders (x : RVSort M) :
    inK x ↔ x=0 ∨ (iLe x.val (1 : RVSort M).val ∧ iLe (1 : RVSort M).val x.val) := by
  rw [RVOperations.inK_iff,rvLe_iff_absolute,rvLe_iff_absolute,map_one]
  exact or_congr Iff.rfl ⟨fun h => by rw [h]; exact ⟨le_rfl,le_rfl⟩,
    fun h => le_antisymm h.2 h.1⟩

theorem residueBranch_correct (T : Monomial I R V) (pos : Bool)
    (hp : T.PoleFree a) (hs : T.ProperSlots r y) :
    PolarityDNF.holds (RVLiteral.holds a r y) (residueBranch T pos) ↔
      NFTest.signed pos (inK (T.eval a r y)) := by
  have hOne : (Monomial.one : Monomial I R V).ProperSlots r y := by
    simp [Monomial.ProperSlots,Monomial.one]
  have hz (b : Bool) : RVLiteral.holds a r y (RVLiteral.monomialZero T b) ↔
      NFTest.signed b (T.eval a r y=0) := by
    rw [RVLiteral.monomialZero_correct]
    constructor
    · rintro ⟨_,h⟩
      rwa [Monomial.eval_eq_rawEval T a r y hs]
    · intro h
      exact ⟨hp,by rwa [Monomial.eval_eq_rawEval T a r y hs] at h⟩
  have hl (b : Bool) := monomialOrderLiteral_correct a r y T Monomial.one b hp hs one_ne_zero hOne
  have hr (b : Bool) := monomialOrderLiteral_correct a r y Monomial.one T b one_ne_zero hOne hp hs
  have hi := inK_iff_zero_or_orders (T.eval a r y)
  cases pos
  · simp only [residueBranch,Bool.false_eq_true,if_false,if_true,PolarityDNF.holds_conj,
      PolarityDNF.holds_disj,single_correct,hz,hl,hr,Monomial.eval_one,NFTest.signed]
    rw [hi]
    tauto
  · simp only [residueBranch,Bool.false_eq_true,if_false,if_true,PolarityDNF.holds_conj,
      PolarityDNF.holds_disj,single_correct,hz,hl,hr,Monomial.eval_one,NFTest.signed]
    exact hi.symm

theorem monomialResidue_correct (T : Monomial I R V) (pos : Bool) :
    PolarityDNF.holds (RVLiteral.holds a r y) (monomialResidue T pos) ↔
      NFTest.holds a r y (.monomialResidue T pos) := by
  rw [monomialResidue,PolarityDNF.holds_conj,safe_correct]
  simp only [NFTest.holds,NFTest.Safe,NFTest.predicate]
  apply and_congr_right
  rintro ⟨hp,hs⟩
  exact residueBranch_correct a r y T pos hp hs

theorem prepared_correct (P : KPolynomial I R V) :
    PolarityDNF.holds (RVLiteral.holds a r y) (prepared P) ↔ P.Prepared a r y := by
  rw [prepared,all_correct]
  constructor
  · intro h i
    have hi : monomialResidue (P.terms i) true ∈
        (List.finRange P.size).map (fun j => monomialResidue (P.terms j) true) :=
      List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
    have hs := (monomialResidue_correct a r y (P.terms i) true).mp (h _ hi)
    exact ⟨hs.1.1,hs.1.2,hs.2⟩
  · intro h D hD
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hD
    apply (monomialResidue_correct a r y (P.terms i) true).mpr
    exact ⟨⟨(h i).1,(h i).2.1⟩,(h i).2.2⟩

theorem polynomialZero_correct (P : KPolynomial I R V) (pos : Bool) :
    PolarityDNF.holds (RVLiteral.holds a r y) (polynomialZero P pos) ↔
      NFTest.holds a r y (.polynomialZero P pos) := by
  rw [polynomialZero,PolarityDNF.holds_conj,prepared_correct,single_correct,RVLiteral.polynomialZero_correct]
  simp only [NFTest.holds,NFTest.Safe,NFTest.predicate]
  constructor
  · rintro ⟨hp,_,he⟩
    exact ⟨hp,by rwa [KPolynomial.prepared_eval_eq_rawEval P a r y hp]⟩
  · rintro ⟨hp,he⟩
    exact ⟨hp,KPolynomial.prepared_domain P a r y hp,
      by rwa [KPolynomial.prepared_eval_eq_rawEval P a r y hp] at he⟩

theorem test_correct (t : NFTest I R V) :
    PolarityDNF.holds (RVLiteral.holds a r y) (test t) ↔ NFTest.holds a r y t := by
  cases t with
  | parameterZero i pos =>
    rw [test,single_correct,RVLiteral.monomialZero_correct]
    change ((Monomial.parameter i).PoleFree a ∧ NFTest.signed pos ((Monomial.parameter i).rawEval a r y=0)) ↔
      (True ∧ NFTest.signed pos (r i=0))
    rw [Monomial.rawEval_parameter]
    exact and_congr ⟨fun _ => True.intro,fun _ => one_ne_zero⟩ Iff.rfl
  | variableZero i pos =>
    rw [test,single_correct,RVLiteral.monomialZero_correct]
    change ((Monomial.ofVariable i).PoleFree a ∧ NFTest.signed pos ((Monomial.ofVariable i).rawEval a r y=0)) ↔
      (True ∧ NFTest.signed pos (y i=0))
    rw [Monomial.rawEval_variable]
    exact and_congr ⟨fun _ => True.intro,fun _ => one_ne_zero⟩ Iff.rfl
  | monomialZero T pos => exact monomialZero_correct a r y T pos
  | polynomialZero P pos => exact polynomialZero_correct a r y P pos
  | monomialResidue T pos => exact monomialResidue_correct a r y T pos

end LiteralDNF
end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: GuardedBooleanNormalization -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm
open FiniteGuardedBranches

namespace LiteralDNF
variable {I R V : Type}
def any : List (LiteralDNF I R V) → LiteralDNF I R V
  | [] => []
  | D::Ds => PolarityDNF.disj D (any Ds)
noncomputable def program (B : Program I R V (RVLiteral I R V)) : LiteralDNF I R V :=
  any (B.map (fun b => PolarityDNF.conj (all (b.guards.map test)) (single b.value)))

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)

theorem any_correct (Ds : List (LiteralDNF I R V)) :
    PolarityDNF.holds (RVLiteral.holds a r y) (any Ds) ↔
      ∃ D ∈ Ds, PolarityDNF.holds (RVLiteral.holds a r y) D := by
  induction Ds with
  | nil => simp [any,PolarityDNF.holds]
  | cons D Ds ih => simp [any,PolarityDNF.holds_disj,ih]

theorem program_correct (B : Program I R V (RVLiteral I R V)) :
    PolarityDNF.holds (RVLiteral.holds a r y) (program B) ↔
      ∃ L ∈ run (NFTest.holds a r y) B, RVLiteral.holds a r y L := by
  rw [program,any_correct]
  constructor
  · rintro ⟨D,hD,hc⟩
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hD
    obtain ⟨hg,hv⟩ := (PolarityDNF.holds_conj _ _ _).mp hc
    have hall := (all_correct a r y (b.guards.map test)).mp hg
    refine ⟨b.value,⟨b,hb,?_,rfl⟩,(single_correct a r y b.value).mp hv⟩
    intro t ht
    exact (test_correct a r y t).mp (hall (test t) (List.mem_map.mpr ⟨t,ht,rfl⟩))
  · rintro ⟨L,⟨b,hb,hg,rfl⟩,hv⟩
    refine ⟨_,List.mem_map.mpr ⟨b,hb,rfl⟩,?_⟩
    apply (PolarityDNF.holds_conj _ _ _).mpr
    refine ⟨(all_correct a r y (b.guards.map test)).mpr ?_,(single_correct a r y b.value).mpr hv⟩
    rintro D hD
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hD
    exact (test_correct a r y t).mpr (hg t ht)

end LiteralDNF

inductive RVAtom (I R V : Type) where
  | equality : RVExpr I R V → RVExpr I R V → RVAtom I R V
  | order : RVExpr I R V → RVExpr I R V → RVAtom I R V

namespace RVAtom
variable {I R V : Type}
noncomputable def normalForm (pos : Bool) : RVAtom I R V → LiteralDNF I R V
  | .equality P Q => LiteralDNF.program (equalityProgram P Q pos)
  | .order P Q => LiteralDNF.program (orderProgram P Q pos)

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
noncomputable def eval (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) : RVAtom I R V → Prop
  | .equality P Q => P.eval a r y=Q.eval a r y
  | .order P Q => iLe (P.eval a r y).val (Q.eval a r y).val

variable (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

include hv in
theorem normalForm_correct (pos : Bool) (A : RVAtom I R V) :
    PolarityDNF.holds (RVLiteral.holds a r y) (A.normalForm pos) ↔ NFTest.signed pos (A.eval a r y) := by
  cases A with
  | equality P Q => exact (LiteralDNF.program_correct a r y _).trans (equalityProgram_correct a r y v hv P Q pos)
  | order P Q => exact (LiteralDNF.program_correct a r y _).trans (orderProgram_correct a r y v hv P Q pos)
end RVAtom

noncomputable def booleanNormalForm {I R V : Type} (E : PolarityDNF.Expr (RVAtom I R V)) : LiteralDNF I R V :=
  PolarityDNF.translate RVAtom.normalForm true E

theorem booleanNormalForm_correct {I R V M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)
    (E : PolarityDNF.Expr (RVAtom I R V)) :
    PolarityDNF.holds (RVLiteral.holds a r y) (booleanNormalForm E) ↔ E.eval (RVAtom.eval a r y) := by
  exact PolarityDNF.translate_correct (RVAtom.eval a r y) (RVLiteral.holds a r y) RVAtom.normalForm
    (RVAtom.normalForm_correct a r y Values.presentationValuation Values.presentation_compatible) E true

end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: DNFDomainCertificates -/
namespace SpecialTransformations.Section3.PolarityDNF
variable {A : Type*}

/-- A true clause contains enough explicit comparison guards to certify
all of its partial-term domains. -/
def Certified (domain comparison : A → Prop) (D : DNF A) : Prop :=
  ∀ C ∈ D, (∀ a ∈ C, comparison a) → ∀ a ∈ C, domain a

theorem Certified.holds_iff {domain comparison : A → Prop} {D : DNF A}
    (hD : Certified domain comparison D) :
    holds (fun a => domain a ∧ comparison a) D ↔ holds comparison D := by
  constructor
  · rintro ⟨C,hC,h⟩
    exact ⟨C,hC,fun a ha => (h a ha).2⟩
  · rintro ⟨C,hC,h⟩
    exact ⟨C,hC,fun a ha => ⟨hD C hC h a ha,h a ha⟩⟩

theorem certified_false (domain comparison : A → Prop) : Certified domain comparison ([] : DNF A) := by
  intro C hC
  cases hC

theorem certified_true (domain comparison : A → Prop) : Certified domain comparison ([ [] ] : DNF A) := by
  intro C hC
  simp only [List.mem_singleton] at hC
  subst C
  simp

theorem certified_single {domain comparison : A → Prop} {a : A} (ha : domain a) :
    Certified domain comparison [ [a] ] := by
  intro C hC hp
  simp only [List.mem_singleton] at hC
  subst C
  intro b hb
  simp only [List.mem_singleton] at hb
  subst b
  exact ha

theorem Certified.disj {domain comparison : A → Prop} {D E : DNF A}
    (hD : Certified domain comparison D) (hE : Certified domain comparison E) :
    Certified domain comparison (disj D E) := by
  intro C hC
  rcases List.mem_append.mp hC with hC | hC
  · exact hD C hC
  · exact hE C hC

theorem Certified.conj_of_prefix {domain comparison : A → Prop} {D E : DNF A}
    (hD : Certified domain comparison D)
    (hE : holds (fun a => domain a ∧ comparison a) D → Certified domain comparison E) :
    Certified domain comparison (conj D E) := by
  intro C hC hp
  obtain ⟨F,hF,hC⟩ := List.mem_flatMap.mp hC
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hC
  have hpF : ∀ a ∈ F, comparison a := fun a ha => hp a (List.mem_append.mpr (Or.inl ha))
  have hpG : ∀ a ∈ G, comparison a := fun a ha => hp a (List.mem_append.mpr (Or.inr ha))
  have hdomF := hD F hF hpF
  have hdomG := hE ⟨F,hF,fun a ha => ⟨hdomF a ha,hpF a ha⟩⟩ G hG hpG
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hdomF a ha
  · exact hdomG a ha

theorem Certified.conj {domain comparison : A → Prop} {D E : DNF A}
    (hD : Certified domain comparison D) (hE : Certified domain comparison E) :
    Certified domain comparison (conj D E) := hD.conj_of_prefix (fun _ => hE)

theorem translate_certified {B : Type*} (domain comparison : A → Prop)
    (atomNF : Bool → B → DNF A) (ha : ∀ pos b, Certified domain comparison (atomNF pos b))
    (E : Expr B) (pos : Bool) : Certified domain comparison (translate atomNF pos E) := by
  induction E generalizing pos with
  | falsum => cases pos <;> first | exact certified_true _ _ | exact certified_false _ _
  | atom b => exact ha pos b
  | imp P Q ihP ihQ =>
    cases pos
    · exact (ihP true).conj (ihQ false)
    · exact (ihP false).disj (ihQ true)

end SpecialTransformations.Section3.PolarityDNF

/- Component: LiteralGuardCertificates -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm

namespace RVLiteral
variable {I R V M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)

theorem monomialZero_domain (T : Monomial I R V) (pos : Bool) (hp : T.PoleFree a) :
    Domain a r y (monomialZero T pos) :=
  ⟨one_ne_zero,KPolynomial.domain_one a r y,hp,KPolynomial.domain_one a r y⟩

theorem polynomialZero_domain (P : KPolynomial I R V) (pos : Bool) (hp : P.Domain a r y) :
    Domain a r y (polynomialZero P pos) :=
  ⟨one_ne_zero,hp,one_ne_zero,KPolynomial.domain_one a r y⟩

theorem poleGuard_domain (T : Monomial I R V) : Domain a r y (poleGuard T) :=
  monomialZero_domain a r y _ _ one_ne_zero

theorem slotGuards_domains (T : Monomial I R V) : ∀ L ∈ slotGuards T, Domain a r y L := by
  intro L hL
  rcases List.mem_append.mp hL with hL | hL
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hL
    exact monomialZero_domain a r y _ _ one_ne_zero
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hL
    exact monomialZero_domain a r y _ _ one_ne_zero
end RVLiteral

namespace LiteralDNF
variable {I R V M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)

abbrev Certified (D : LiteralDNF I R V) :=
  PolarityDNF.Certified (RVLiteral.Domain a r y) (RVLiteral.comparison a r y) D

theorem single_certified (L : RVLiteral I R V) (hL : RVLiteral.Domain a r y L) :
    Certified a r y (single L) := PolarityDNF.certified_single hL

theorem safe_certified (T : Monomial I R V) : Certified a r y (safe T) := by
  intro C hC hp
  simp only [safe,List.mem_singleton] at hC
  subst C
  intro L hL
  rcases List.mem_cons.mp hL with rfl | hL
  · exact RVLiteral.poleGuard_domain a r y T
  · exact RVLiteral.slotGuards_domains a r y T L hL

theorem monomialZero_certified (T : Monomial I R V) (pos : Bool) : Certified a r y (monomialZero T pos) := by
  apply (safe_certified a r y T).conj_of_prefix
  intro h
  have hs := (safe_correct a r y T).mp h
  exact single_certified a r y _ (RVLiteral.monomialZero_domain a r y T pos hs.1)

theorem residueBranch_certified (T : Monomial I R V) (pos : Bool) (hp : T.PoleFree a) :
    Certified a r y (residueBranch T pos) := by
  have hz (b : Bool) := single_certified a r y _ (RVLiteral.monomialZero_domain a r y T b hp)
  have hl (b : Bool) : Certified a r y (single (monomialOrderLiteral T Monomial.one b)) :=
    single_certified a r y _ ⟨hp,one_ne_zero⟩
  have hr (b : Bool) : Certified a r y (single (monomialOrderLiteral Monomial.one T b)) :=
    single_certified a r y _ ⟨one_ne_zero,hp⟩
  cases pos
  · exact (hz false).conj ((hl false).disj (hr false))
  · exact (hz true).disj ((hl true).conj (hr true))

theorem monomialResidue_certified (T : Monomial I R V) (pos : Bool) :
    Certified a r y (monomialResidue T pos) := by
  apply (safe_certified a r y T).conj_of_prefix
  intro h
  exact residueBranch_certified a r y T pos ((safe_correct a r y T).mp h).1

theorem all_certified (Ds : List (LiteralDNF I R V)) (hD : ∀ D ∈ Ds, Certified a r y D) :
    Certified a r y (all Ds) := by
  induction Ds with
  | nil => exact PolarityDNF.certified_true _ _
  | cons D Ds ih =>
    exact (hD D (List.mem_cons_self)).conj (ih (fun E hE => hD E (List.mem_cons_of_mem _ hE)))

theorem prepared_certified (P : KPolynomial I R V) : Certified a r y (prepared P) := by
  apply all_certified
  intro D hD
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hD
  exact monomialResidue_certified a r y _ true

theorem polynomialZero_certified (P : KPolynomial I R V) (pos : Bool) :
    Certified a r y (polynomialZero P pos) := by
  apply (prepared_certified a r y P).conj_of_prefix
  intro h
  have hp := (prepared_correct a r y P).mp h
  exact single_certified a r y _ (RVLiteral.polynomialZero_domain a r y P pos (KPolynomial.prepared_domain P a r y hp))

theorem test_certified (t : NFTest I R V) : Certified a r y (test t) := by
  cases t with
  | parameterZero i pos => exact single_certified a r y _ (RVLiteral.monomialZero_domain a r y _ _ one_ne_zero)
  | variableZero i pos => exact single_certified a r y _ (RVLiteral.monomialZero_domain a r y _ _ one_ne_zero)
  | monomialZero T pos => exact monomialZero_certified a r y T pos
  | polynomialZero P pos => exact polynomialZero_certified a r y P pos
  | monomialResidue T pos => exact monomialResidue_certified a r y T pos
end LiteralDNF
end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: NormalFormCertificates -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm
open FiniteGuardedBranches

namespace LiteralDNF
variable {I R V M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)

theorem any_certified (Ds : List (LiteralDNF I R V)) (hD : ∀ D ∈ Ds, Certified a r y D) :
    Certified a r y (any Ds) := by
  induction Ds with
  | nil => exact PolarityDNF.certified_false _ _
  | cons D Ds ih =>
    exact (hD D (by simp)).disj (ih (fun E hE => hD E (List.mem_cons_of_mem _ hE)))

theorem program_certified (B : Program I R V (RVLiteral I R V))
    (hB : ∀ L ∈ run (NFTest.holds a r y) B, RVLiteral.Domain a r y L) :
    Certified a r y (program B) := by
  apply any_certified
  intro D hD
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hD
  have hprefix : Certified a r y (all (b.guards.map test)) := by
    apply all_certified
    intro E hE
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hE
    exact test_certified a r y t
  apply hprefix.conj_of_prefix
  intro h
  have hall := (all_correct a r y (b.guards.map test)).mp h
  have hg : satisfied (NFTest.holds a r y) b.guards := by
    intro t ht
    exact (test_correct a r y t).mp (hall (test t) (List.mem_map.mpr ⟨t,ht,rfl⟩))
  exact single_certified a r y b.value (hB b.value ⟨b,hb,hg,rfl⟩)
end LiteralDNF

variable {I R V M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

include hv in
theorem equalityProgram_domains (P Q : RVExpr I R V) (pos : Bool)
    (L : RVLiteral I R V) (hL : L ∈ run (NFTest.holds a r y) (equalityProgram P Q pos)) :
    RVLiteral.Domain a r y L := by
  obtain ⟨F,hF,hL⟩ := (run_bind _ _ _ _).mp hL
  obtain ⟨G,hG,hL⟩ := (run_bind _ _ _ _).mp hL
  have he := (run_pure _ _ _).mp hL
  subst L
  exact RVFraction.equalityLiteral_domain a r y v hv F G pos
    (RVExpr.normalize_sound a r y v hv P F hF).1 (RVExpr.normalize_sound a r y v hv Q G hG).1

include hv in
theorem orderProgram_domains (P Q : RVExpr I R V) (pos : Bool)
    (L : RVLiteral I R V) (hL : L ∈ run (NFTest.holds a r y) (orderProgram P Q pos)) :
    RVLiteral.Domain a r y L := by
  obtain ⟨F,hF,hL⟩ := (run_bind _ _ _ _).mp hL
  obtain ⟨G,hG,hL⟩ := (run_bind _ _ _ _).mp hL
  obtain ⟨T,hT,hL⟩ := (run_bind _ _ _ _).mp hL
  obtain ⟨U,hU,hL⟩ := (run_bind _ _ _ _).mp hL
  have he := (run_pure _ _ _).mp hL
  subst L
  have hf := RVExpr.normalize_sound a r y v hv P F hF
  have hg := RVExpr.normalize_sound a r y v hv Q G hG
  have ht := RVFraction.valueCases_sound a r y v hv F T hf.1 hT
  have hu := RVFraction.valueCases_sound a r y v hv G U hg.1 hU
  exact ⟨ht.1,hu.1⟩

include hv in
theorem RVAtom.normalForm_certified (pos : Bool) (A : RVAtom I R V) :
    LiteralDNF.Certified a r y (A.normalForm pos) := by
  cases A with
  | equality P Q => exact LiteralDNF.program_certified a r y _ (equalityProgram_domains a r y v hv P Q pos)
  | order P Q => exact LiteralDNF.program_certified a r y _ (orderProgram_domains a r y v hv P Q pos)

theorem booleanNormalForm_certified (E : PolarityDNF.Expr (RVAtom I R V)) :
    LiteralDNF.Certified a r y (booleanNormalForm E) :=
  PolarityDNF.translate_certified _ _ RVAtom.normalForm
    (RVAtom.normalForm_certified a r y Values.presentationValuation Values.presentation_compatible) E true

theorem booleanNormalForm_raw_correct (E : PolarityDNF.Expr (RVAtom I R V)) :
    PolarityDNF.holds (RVLiteral.comparison a r y) (booleanNormalForm E) ↔ E.eval (RVAtom.eval a r y) :=
  (booleanNormalForm_certified a r y E).holds_iff.symm.trans (booleanNormalForm_correct a r y E)

end SpecialTransformations.Section3.GuardedRVNormalForm
