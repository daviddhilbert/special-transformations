module

public import CanonicalResidueOperations
public import Mathlib
public import Section3.RVOperations
public import Section3.RingSyntax

@[expose] public section

/-!
# GuardedRVArithmetic

Rational RV monomials, genuine flat residue polynomials, finite guarded branches,
and original-slot syntax. Internal clipping is removed only under retained
nonzero guards; public domains use ordinary absorbing-zero semantics.

See NORMAL-FORM-NOTE.md for the agreed statement and language conventions.
-/

/- Component: LaurentWords -/
namespace SpecialTransformations.Section3.LaurentWords
open Classical
variable {ι A : Type*} [CommGroupWithZero A]

/-- Internal total nonzero input. Final literal semantics use the original
inputs; the support bridge below requires their retained nonzero guards. -/
noncomputable def clip (x : A) : A := by
  classical
  exact if x = 0 then 1 else x

theorem clip_ne_zero (x : A) : clip x ≠ 0 := by
  by_cases hx : x=0
  · simp only [clip,if_pos hx,ne_eq,one_ne_zero,not_false_eq_true]
  · simpa only [clip,if_neg hx] using hx

theorem clip_eq_of_ne_zero {x : A} (hx : x ≠ 0) : clip x = x := by
  simp only [clip,if_neg hx]

noncomputable def eval (v : ι → A) (w : ι →₀ ℤ) : A :=
  w.prod (fun i n => clip (v i) ^ n)

theorem eval_zero (v : ι → A) : eval v (0 : ι →₀ ℤ) = 1 := by simp only [eval,Finsupp.prod_zero_index]

theorem eval_add (v : ι → A) (w u : ι →₀ ℤ) : eval v (w+u) = eval v w * eval v u := by
  apply Finsupp.prod_add_index'
  · intro i
    exact zpow_zero _
  · intro i a b
    exact zpow_add₀ (clip_ne_zero (v i)) a b

theorem eval_ne_zero (v : ι → A) (w : ι →₀ ℤ) : eval v w ≠ 0 := by
  classical
  unfold eval Finsupp.prod
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact zpow_ne_zero _ (clip_ne_zero (v i))

theorem eval_neg (v : ι → A) (w : ι →₀ ℤ) : eval v (-w) = (eval v w)⁻¹ := by
  have hh : eval v w * eval v (-w) = 1 := by rw [← eval_add,add_neg_cancel,eval_zero]
  calc
    eval v (-w) = (eval v w)⁻¹ * (eval v w * eval v (-w)) := by
      rw [← mul_assoc,inv_mul_cancel₀ (eval_ne_zero v w),one_mul]
    _ = (eval v w)⁻¹ := by rw [hh,mul_one]

theorem eval_single (v : ι → A) (i : ι) (n : ℤ) : eval v (Finsupp.single i n) = clip (v i)^n := by
  classical
  simp only [eval,Finsupp.prod_single_index,zpow_zero]

/-- On the retained support guards the internal evaluation is exactly the
ordinary Laurent monomial in the original RV variables and parameters. -/
theorem eval_eq_raw (v : ι → A) (w : ι →₀ ℤ) (hNZ : ∀ i ∈ w.support, v i ≠ 0) :
    eval v w = w.prod (fun i n => v i^n) := by
  classical
  unfold eval Finsupp.prod
  apply Finset.prod_congr rfl
  intro i hi
  change clip (v i) ^ (w i) = v i ^ (w i)
  rw [clip_eq_of_ne_zero (hNZ i hi)]

end SpecialTransformations.Section3.LaurentWords

/- Component: ResidueRVAlgebra -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.ResidueRVAlgebra
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

/-- The actual residue field embeds multiplicatively into RV with zero.
This gives inverse/division laws without extending residue addition to RV. -/
noncomputable def residueRVHom : Residue v →*₀ RVSort M where
  toFun := CanonicalResidue.toRV v hv
  map_zero' := (CanonicalResidue.toRV_zero v hv).trans RVOperations.zeroRV_eq
  map_one' := (CanonicalResidue.toRV_one v hv).trans RVOperations.oneRV_eq
  map_mul' a b := (CanonicalResidue.toRV_mul v hv a b).trans (RVOperations.mulRV_eq _ _)

theorem residueRVHom_injective : Function.Injective (residueRVHom v hv) :=
  CanonicalResidue.toRV_injective v hv

theorem residueRVHom_inK (a : Residue v) : inK (residueRVHom v hv a) :=
  (CanonicalResidue.equiv v hv a).property

theorem residueRVHom_add (a b : Residue v) :
    residueRVHom v hv (a+b) = addK (residueRVHom v hv a) (residueRVHom v hv b) :=
  CanonicalResidue.toRV_add v hv a b

theorem residueRVHom_neg (a : Residue v) :
    residueRVHom v hv (-a) = negK (residueRVHom v hv a) := CanonicalResidue.toRV_neg v hv a

theorem residueRVHom_inv (a : Residue v) :
    residueRVHom v hv a⁻¹ = (residueRVHom v hv a)⁻¹ := map_inv₀ (residueRVHom v hv) a

theorem residueRVHom_div (a b : Residue v) :
    residueRVHom v hv (a/b) = residueRVHom v hv a / residueRVHom v hv b :=
  map_div₀ (residueRVHom v hv) a b

theorem inK_iff_exists_residue (x : RVSort M) : inK x ↔ ∃ a : Residue v, residueRVHom v hv a = x := by
  constructor
  · intro hx
    refine ⟨(CanonicalResidue.equiv v hv).symm ⟨x,hx⟩,?_⟩
    exact congrArg (fun z : CanonicalResidue.KSort M => z.val)
      ((CanonicalResidue.equiv v hv).apply_symm_apply ⟨x,hx⟩)
  · rintro ⟨a,rfl⟩
    exact residueRVHom_inK v hv a

include hv in
theorem inK_mul (x y : RVSort M) (hx : inK x) (hy : inK y) : inK (x*y) := by
  obtain ⟨a,rfl⟩ := (inK_iff_exists_residue v hv x).mp hx
  obtain ⟨b,rfl⟩ := (inK_iff_exists_residue v hv y).mp hy
  rw [← map_mul]
  exact residueRVHom_inK v hv (a*b)

include hv in
theorem inK_inv (x : RVSort M) (hx : inK x) : inK x⁻¹ := by
  obtain ⟨a,rfl⟩ := (inK_iff_exists_residue v hv x).mp hx
  rw [← residueRVHom_inv]
  exact residueRVHom_inK v hv a⁻¹

include hv in
theorem inK_div (x y : RVSort M) (hx : inK x) (hy : inK y) : inK (x/y) := by
  simpa only [div_eq_mul_inv] using inK_mul v hv x y⁻¹ hx (inK_inv v hv y hy)

include hv in
theorem inK_mul_iff_left (x y : RVSort M) (hy : inK y) (hy0 : y ≠ 0) :
    inK (x*y) ↔ inK x := by
  constructor
  · intro h
    have hh := inK_mul v hv (x*y) y⁻¹ h (inK_inv v hv y hy)
    rwa [mul_assoc,mul_inv_cancel₀ hy0,mul_one] at hh
  · intro h
    exact inK_mul v hv x y h hy

include hv in
theorem fraction_add (a b c d : RVSort M) (ha : inK a) (hb : inK b)
    (hc : inK c) (hd : inK d) (hb0 : b ≠ 0) (hd0 : d ≠ 0) :
    addK (a/b) (c/d) = addK (a*d) (c*b) / (b*d) := by
  obtain ⟨a,rfl⟩ := (inK_iff_exists_residue v hv a).mp ha
  obtain ⟨b,rfl⟩ := (inK_iff_exists_residue v hv b).mp hb
  obtain ⟨c,rfl⟩ := (inK_iff_exists_residue v hv c).mp hc
  obtain ⟨d,rfl⟩ := (inK_iff_exists_residue v hv d).mp hd
  have hb0' : b ≠ 0 := fun h => hb0 (by rw [h,map_zero])
  have hd0' : d ≠ 0 := fun h => hd0 (by rw [h,map_zero])
  rw [← map_div₀,← map_div₀,← residueRVHom_add,← map_mul,← map_mul,
    ← residueRVHom_add,← map_mul,← map_div₀]
  congr 1
  field_simp
  <;> ring

theorem neg_one_image : residueRVHom v hv (-1) = RVOperations.rvHom (-1 : VFType (M := M)) := by
  rw [residueRVHom_neg,map_one]
  have hu : iUnits (encodedRv (1 : VFType (M := M))).val := by
    rw [RVOperations.rv_one]
    exact (RVOperations.units_iff_absolute_one (1 : RVSort M) one_ne_zero).mpr (map_one _)
  change negK (1 : RVSort M) = encodedRv (-1 : VFType (M := M))
  rw [← RVOperations.rv_one]
  exact ValuedModelMap.negK_units _ hu

include hv in
theorem fraction_neg (a b : RVSort M) (ha : inK a) (hb : inK b) :
    negK (a/b) = RVOperations.rvHom (-1 : VFType (M := M)) * a/b := by
  obtain ⟨a,rfl⟩ := (inK_iff_exists_residue v hv a).mp ha
  obtain ⟨b,rfl⟩ := (inK_iff_exists_residue v hv b).mp hb
  rw [← map_div₀,← residueRVHom_neg,← neg_one_image v hv,← map_mul,← map_div₀]
  congr 1
  ring

end SpecialTransformations.Section3.ResidueRVAlgebra

/- Component: RationalMonomialSyntax -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.GuardedRVNormalForm

abbrev VFPolynomial (I : Type) := Language.ring.Term I
namespace VFPolynomial
variable {I : Type}
def zero : VFPolynomial I := .func .zero Fin.elim0
def one : VFPolynomial I := .func .one Fin.elim0
def mul (P Q : VFPolynomial I) : VFPolynomial I := .func .mul ![P,Q]
def add (P Q : VFPolynomial I) : VFPolynomial I := .func .add ![P,Q]
def neg (P : VFPolynomial I) : VFPolynomial I := .func .neg ![P]

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
theorem realize_zero (a : I → VFType (M := M)) : (zero : VFPolynomial I).realize a = 0 := rfl
theorem realize_one (a : I → VFType (M := M)) : (one : VFPolynomial I).realize a = 1 := rfl
theorem realize_mul (P Q : VFPolynomial I) (a : I → VFType (M := M)) :
    (mul P Q).realize a = P.realize a * Q.realize a := rfl
theorem realize_add (P Q : VFPolynomial I) (a : I → VFType (M := M)) :
    (add P Q).realize a = P.realize a + Q.realize a := rfl
theorem realize_neg (P : VFPolynomial I) (a : I → VFType (M := M)) :
    (neg P).realize a = -(P.realize a) := rfl
end VFPolynomial

/-- Pure syntax. VF factors use numerator/denominator polynomial expressions
in original VF slots; RV parameter words and RV variable exponents are kept
separate so the printed left coefficient can ultimately be removed. -/
structure Monomial (I R V : Type) where
  numerator : VFPolynomial I
  denominator : VFPolynomial I
  coefficient : R →₀ ℤ
  powers : V →₀ ℤ

namespace Monomial
variable {I R V : Type}
def zero : Monomial I R V := ⟨VFPolynomial.zero,VFPolynomial.one,0,0⟩
def one : Monomial I R V := ⟨VFPolynomial.one,VFPolynomial.one,0,0⟩
def vf (P : VFPolynomial I) : Monomial I R V := ⟨P,VFPolynomial.one,0,0⟩
noncomputable def parameter (r : R) : Monomial I R V := ⟨VFPolynomial.one,VFPolynomial.one,Finsupp.single r 1,0⟩
noncomputable def ofVariable (i : V) : Monomial I R V := ⟨VFPolynomial.one,VFPolynomial.one,0,Finsupp.single i 1⟩
noncomputable def mul (P Q : Monomial I R V) : Monomial I R V :=
  ⟨VFPolynomial.mul P.numerator Q.numerator,VFPolynomial.mul P.denominator Q.denominator,
    P.coefficient+Q.coefficient,P.powers+Q.powers⟩
noncomputable def inv (P : Monomial I R V) : Monomial I R V :=
  ⟨P.denominator,P.numerator,-P.coefficient,-P.powers⟩

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def eval (P : Monomial I R V) (a : I → VFType (M := M))
    (r : R → CanonicalRV.RVSort M) (y : V → CanonicalRV.RVSort M) : CanonicalRV.RVSort M :=
  (RVOperations.rvHom (P.numerator.realize a) / RVOperations.rvHom (P.denominator.realize a)) *
    LaurentWords.eval r P.coefficient * LaurentWords.eval y P.powers

/-- Ordinary released Laurent semantics, including absorbing-zero inputs.
The clipped evaluation above is only an internal normalization device. -/
noncomputable def rawEval (P : Monomial I R V) (a : I → VFType (M := M))
    (r : R → CanonicalRV.RVSort M) (y : V → CanonicalRV.RVSort M) : CanonicalRV.RVSort M :=
  (RVOperations.rvHom (P.numerator.realize a) / RVOperations.rvHom (P.denominator.realize a)) *
    P.coefficient.prod (fun i n => r i^n) * P.powers.prod (fun i n => y i^n)

def PoleFree (P : Monomial I R V) (a : I → VFType (M := M)) : Prop := P.denominator.realize a ≠ 0

def ProperSlots (P : Monomial I R V) (r : R → CanonicalRV.RVSort M) (y : V → CanonicalRV.RVSort M) : Prop :=
  (∀ i ∈ P.coefficient.support, r i ≠ 0) ∧ ∀ i ∈ P.powers.support, y i ≠ 0

theorem eval_zero (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (y : V → CanonicalRV.RVSort M) :
    eval (zero : Monomial I R V) a r y = 0 := by
  simp only [eval,zero,VFPolynomial.realize_zero,VFPolynomial.realize_one,map_zero,map_one,
    zero_div,LaurentWords.eval_zero,zero_mul]

theorem eval_one (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (y : V → CanonicalRV.RVSort M) :
    eval (one : Monomial I R V) a r y = 1 := by
  simp only [eval,one,VFPolynomial.realize_one,map_one,one_div_one,LaurentWords.eval_zero,one_mul]

theorem eval_vf (P : VFPolynomial I) (a : I → VFType (M := M))
    (r : R → CanonicalRV.RVSort M) (y : V → CanonicalRV.RVSort M) :
    eval (vf P : Monomial I R V) a r y = RVOperations.rvHom (P.realize a) := by
  simp only [eval,vf,VFPolynomial.realize_one,map_one,div_one,LaurentWords.eval_zero,mul_one]

theorem eval_parameter (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (y : V → CanonicalRV.RVSort M) (i : R) (hi : r i ≠ 0) : eval (parameter i) a r y = r i := by
  simp only [eval,parameter,VFPolynomial.realize_one,map_one,one_div_one,LaurentWords.eval_single,
    LaurentWords.eval_zero,zpow_one,LaurentWords.clip_eq_of_ne_zero hi,one_mul,mul_one]

theorem eval_variable (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (y : V → CanonicalRV.RVSort M) (i : V) (hi : y i ≠ 0) : eval (ofVariable i) a r y = y i := by
  simp only [eval,ofVariable,VFPolynomial.realize_one,map_one,one_div_one,LaurentWords.eval_single,
    LaurentWords.eval_zero,zpow_one,LaurentWords.clip_eq_of_ne_zero hi,one_mul,mul_one]

theorem eval_mul (P Q : Monomial I R V) (a : I → VFType (M := M))
    (r : R → CanonicalRV.RVSort M) (y : V → CanonicalRV.RVSort M) :
    eval (mul P Q) a r y = eval P a r y * eval Q a r y := by
  simp only [eval,mul,VFPolynomial.realize_mul,map_mul,LaurentWords.eval_add]
  rw [← div_mul_div_comm]
  ac_rfl

theorem eval_inv (P : Monomial I R V) (a : I → VFType (M := M))
    (r : R → CanonicalRV.RVSort M) (y : V → CanonicalRV.RVSort M) :
    eval (inv P) a r y = (eval P a r y)⁻¹ := by
  simp only [eval,inv,LaurentWords.eval_neg,mul_inv_rev,inv_div]
  ac_rfl

theorem eval_eq_raw (P : Monomial I R V) (a : I → VFType (M := M))
    (r : R → CanonicalRV.RVSort M) (y : V → CanonicalRV.RVSort M) (h : ProperSlots P r y) :
    eval P a r y =
      (RVOperations.rvHom (P.numerator.realize a) / RVOperations.rvHom (P.denominator.realize a)) *
        P.coefficient.prod (fun i n => r i^n) * P.powers.prod (fun i n => y i^n) := by
  rw [eval,LaurentWords.eval_eq_raw r P.coefficient h.1,LaurentWords.eval_eq_raw y P.powers h.2]

theorem eval_eq_rawEval (P : Monomial I R V) (a : I → VFType (M := M))
    (r : R → CanonicalRV.RVSort M) (y : V → CanonicalRV.RVSort M) (h : ProperSlots P r y) :
    eval P a r y = rawEval P a r y := eval_eq_raw P a r y h

theorem poleFree_mul (P Q : Monomial I R V) (a : I → VFType (M := M))
    (hP : PoleFree P a) (hQ : PoleFree Q a) : PoleFree (mul P Q) a := by
  change (VFPolynomial.mul P.denominator Q.denominator).realize a ≠ 0
  rw [VFPolynomial.realize_mul]
  exact mul_ne_zero hP hQ

theorem poleFree_inv (P : Monomial I R V) (a : I → VFType (M := M))
    (hP : P.numerator.realize a ≠ 0) : PoleFree (inv P) a := hP

theorem properSlots_mul (P Q : Monomial I R V)
    (r : R → CanonicalRV.RVSort M) (y : V → CanonicalRV.RVSort M)
    (hP : ProperSlots P r y) (hQ : ProperSlots Q r y) : ProperSlots (mul P Q) r y := by
  constructor
  · intro i hi
    change i ∈ (P.coefficient+Q.coefficient).support at hi
    rcases Finset.mem_union.mp (Finsupp.support_add hi) with hi | hi
    · exact hP.1 i hi
    · exact hQ.1 i hi
  · intro i hi
    change i ∈ (P.powers+Q.powers).support at hi
    rcases Finset.mem_union.mp (Finsupp.support_add hi) with hi | hi
    · exact hP.2 i hi
    · exact hQ.2 i hi

theorem properSlots_inv (P : Monomial I R V)
    (r : R → CanonicalRV.RVSort M) (y : V → CanonicalRV.RVSort M)
    (hP : ProperSlots P r y) : ProperSlots (inv P) r y := by
  simpa only [ProperSlots,inv,Finsupp.support_neg] using hP

end Monomial
end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: PolarityDNF -/
namespace SpecialTransformations.Section3.PolarityDNF
variable {α β : Type*}

inductive Expr (α : Type*) where
  | falsum : Expr α
  | atom : α → Expr α
  | imp : Expr α → Expr α → Expr α

def Expr.eval (p : α → Prop) : Expr α → Prop
  | .falsum => False
  | .atom a => p a
  | .imp φ ψ => φ.eval p → ψ.eval p

abbrev DNF (β : Type*) := List (List β)
def holds (p : β → Prop) (D : DNF β) : Prop := ∃ C ∈ D, ∀ b ∈ C, p b

def disj (D E : DNF β) : DNF β := D ++ E
def conj (D E : DNF β) : DNF β := D.flatMap (fun C => E.map (fun F => C ++ F))

theorem holds_false (p : β → Prop) : ¬ holds p ([] : DNF β) := by simp [holds]
theorem holds_true (p : β → Prop) : holds p ([ [] ] : DNF β) := by simp [holds]
theorem holds_disj (p : β → Prop) (D E : DNF β) : holds p (disj D E) ↔ holds p D ∨ holds p E := by
  simp only [holds,disj,List.mem_append]
  aesop

theorem holds_conj (p : β → Prop) (D E : DNF β) : holds p (conj D E) ↔ holds p D ∧ holds p E := by
  simp only [holds,conj,List.mem_flatMap,List.mem_map,List.mem_append]
  aesop

/-- Polarity is pushed to source atoms, so already-guarded clauses never
need to be negated. Atom translation constructs its own positive domains. -/
def translate (atomNF : Bool → α → DNF β) : Bool → Expr α → DNF β
  | pos,.falsum => if pos then [] else [ [] ]
  | pos,.atom a => atomNF pos a
  | pos,.imp φ ψ => if pos then disj (translate atomNF false φ) (translate atomNF true ψ)
      else conj (translate atomNF true φ) (translate atomNF false ψ)

theorem translate_correct (p : α → Prop) (q : β → Prop) (atomNF : Bool → α → DNF β)
    (ha : ∀ pos a, holds q (atomNF pos a) ↔ if pos then p a else ¬ p a)
    (φ : Expr α) (pos : Bool) :
    holds q (translate atomNF pos φ) ↔ if pos then φ.eval p else ¬ φ.eval p := by
  induction φ generalizing pos with
  | falsum => cases pos <;> simp [translate,Expr.eval,holds]
  | atom a => exact ha pos a
  | imp φ ψ ihφ ihψ =>
    cases pos
    · simp only [translate,Bool.false_eq_true,if_false,holds_conj,ihφ,ihψ,if_true,Expr.eval]
      tauto
    · simp only [translate,if_true,holds_disj,ihφ,ihψ,Bool.false_eq_true,if_false,Expr.eval]
      tauto

end SpecialTransformations.Section3.PolarityDNF

/- Component: FlatKPolynomialSyntax -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm

/-- A genuinely flat residue polynomial: more than one monomial and no
nested residue operation in a summand. Domain conditions are interpreted
separately and kept by the branch construction. -/
structure KPolynomial (I R V : Type) where
  size : ℕ
  terms : Fin size → Monomial I R V
  two_le : 2 ≤ size

namespace KPolynomial
variable {I R V : Type}
def zero : KPolynomial I R V := ⟨2,![Monomial.zero,Monomial.zero],by decide⟩
def one : KPolynomial I R V := ⟨2,![Monomial.one,Monomial.zero],by decide⟩
noncomputable def add (P Q : KPolynomial I R V) : KPolynomial I R V :=
  ⟨P.size+Q.size,Sum.elim P.terms Q.terms ∘ finSumFinEquiv.symm,by have := P.two_le; omega⟩
noncomputable def mul (P Q : KPolynomial I R V) : KPolynomial I R V :=
  ⟨P.size*Q.size,fun i =>
    let j : Fin P.size × Fin Q.size := finProdFinEquiv.symm i
    Monomial.mul (P.terms j.1) (Q.terms j.2),
    le_trans (by decide : 2 ≤ 2*2) (Nat.mul_le_mul P.two_le Q.two_le)⟩
noncomputable def scalar (T : Monomial I R V) (P : KPolynomial I R V) : KPolynomial I R V :=
  ⟨P.size,fun i => Monomial.mul T (P.terms i),P.two_le⟩

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
noncomputable def rvSum : {n : ℕ} → (Fin n → RVSort M) → RVSort M
  | 0,_ => 0
  | n+1,f => addK (f 0) (rvSum (fun i : Fin n => f i.succ))

noncomputable def eval (P : KPolynomial I R V) (a : I → VFType (M := M))
    (r : R → RVSort M) (y : V → RVSort M) : RVSort M := rvSum (fun i => (P.terms i).eval a r y)

def Prepared (P : KPolynomial I R V) (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) : Prop :=
  ∀ i, (P.terms i).PoleFree a ∧ (P.terms i).ProperSlots r y ∧ inK ((P.terms i).eval a r y)

/-- Exact ordinary flat-term evaluation. Zero RV variables are allowed. -/
noncomputable def rawEval (P : KPolynomial I R V) (a : I → VFType (M := M))
    (r : R → RVSort M) (y : V → RVSort M) : RVSort M := rvSum (fun i => (P.terms i).rawEval a r y)

/-- The agreed rational version of the printed domain: VF poles are
excluded and every ordinary summand belongs to the residue subset,
including its zero. It does not require nonzero RV coordinates. -/
def Domain (P : KPolynomial I R V) (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) : Prop :=
  ∀ i, (P.terms i).PoleFree a ∧ inK ((P.terms i).rawEval a r y)

theorem prepared_domain (P : KPolynomial I R V) (a : I → VFType (M := M))
    (r : R → RVSort M) (y : V → RVSort M) (hP : Prepared P a r y) : Domain P a r y := by
  intro i
  refine ⟨(hP i).1,?_⟩
  rw [← Monomial.eval_eq_rawEval (P.terms i) a r y (hP i).2.1]
  exact (hP i).2.2

theorem prepared_eval_eq_rawEval (P : KPolynomial I R V) (a : I → VFType (M := M))
    (r : R → RVSort M) (y : V → RVSort M) (hP : Prepared P a r y) : eval P a r y = rawEval P a r y := by
  unfold eval rawEval
  congr 1
  funext i
  exact Monomial.eval_eq_rawEval (P.terms i) a r y (hP i).2.1

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

theorem rvSum_image {n : ℕ} (a : Fin n → Residue v) :
    rvSum (fun i => ResidueRVAlgebra.residueRVHom v hv (a i)) =
      ResidueRVAlgebra.residueRVHom v hv (∑ i, a i) := by
  induction n with
  | zero => simp only [rvSum,Finset.univ_eq_empty,Finset.sum_empty,map_zero]
  | succ n ih =>
    rw [rvSum,Fin.sum_univ_succ,ResidueRVAlgebra.residueRVHom_add]
    rw [← ih (fun i : Fin n => a i.succ)]

theorem eval_eq_residue_sum (P : KPolynomial I R V) (a : I → VFType (M := M))
    (r : R → RVSort M) (y : V → RVSort M)
    (hK : ∀ i, inK ((P.terms i).eval a r y)) :
    eval P a r y = ResidueRVAlgebra.residueRVHom v hv
      (∑ i, (CanonicalResidue.equiv v hv).symm ⟨(P.terms i).eval a r y,hK i⟩) := by
  have he (i : Fin P.size) : ResidueRVAlgebra.residueRVHom v hv
      ((CanonicalResidue.equiv v hv).symm ⟨(P.terms i).eval a r y,hK i⟩) = (P.terms i).eval a r y :=
    congrArg (fun z : CanonicalResidue.KSort M => z.val)
      ((CanonicalResidue.equiv v hv).apply_symm_apply ⟨(P.terms i).eval a r y,hK i⟩)
  unfold eval
  rw [← funext he]
  exact rvSum_image v hv _

include hv in
theorem eval_inK (P : KPolynomial I R V) (a : I → VFType (M := M))
    (r : R → RVSort M) (y : V → RVSort M) (hK : ∀ i, inK ((P.terms i).eval a r y)) :
    inK (eval P a r y) := by
  rw [eval_eq_residue_sum v hv P a r y hK]
  exact ResidueRVAlgebra.residueRVHom_inK v hv _

end KPolynomial
end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: RVTermSyntax -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap
namespace SpecialTransformations.Section3.GuardedRVNormalForm

inductive RVExpr (I R V : Type) where
  | zero : RVExpr I R V
  | one : RVExpr I R V
  | vf : VFPolynomial I → RVExpr I R V
  | parameter : R → RVExpr I R V
  | ofVariable : V → RVExpr I R V
  | mul : RVExpr I R V → RVExpr I R V → RVExpr I R V
  | inv : RVExpr I R V → RVExpr I R V
  | addK : RVExpr I R V → RVExpr I R V → RVExpr I R V
  | negK : RVExpr I R V → RVExpr I R V

namespace RVExpr
variable {I R V ι : Type}
def toTerm (fv : I → ι) (fr : R → ι) (fy : V → ι) : RVExpr I R V → LRV.Term ι
  | .zero => .func Fn.rvZero Fin.elim0
  | .one => .func Fn.rvOne Fin.elim0
  | .vf P => .func Fn.rvMap ![(RingSyntax.ofRingTerm P).relabel fv]
  | .parameter i => .var (fr i)
  | .ofVariable i => .var (fy i)
  | .mul P Q => .func Fn.rvMul ![P.toTerm fv fr fy,Q.toTerm fv fr fy]
  | .inv P => .func Fn.rvInv ![P.toTerm fv fr fy]
  | .addK P Q => .func Fn.kAdd ![P.toTerm fv fr fy,Q.toTerm fv fr fy]
  | .negK P => .func Fn.kNeg ![P.toTerm fv fr fy]

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
noncomputable def eval (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) :
    RVExpr I R V → RVSort M
  | .zero => 0
  | .one => 1
  | .vf P => RVOperations.rvHom (P.realize a)
  | .parameter i => r i
  | .ofVariable i => y i
  | .mul P Q => P.eval a r y * Q.eval a r y
  | .inv P => (P.eval a r y)⁻¹
  | .addK P Q => ValuedModelMap.addK (P.eval a r y) (Q.eval a r y)
  | .negK P => ValuedModelMap.negK (P.eval a r y)

private theorem realize_func0 (f : Fn 0) (w : ι → M) :
    (Term.func f Fin.elim0 : LRV.Term ι).realize w = Structure.funMap (L := LRV) f Fin.elim0 := by
  change Structure.funMap (L := LRV) f (fun i => _) = _
  congr 1
  funext i
  exact i.elim0

private theorem realize_func1 (f : Fn 1) (t : LRV.Term ι) (w : ι → M) :
    (Term.func f ![t] : LRV.Term ι).realize w = Structure.funMap (L := LRV) f ![t.realize w] := by
  change Structure.funMap (L := LRV) f (fun i => _) = _
  congr 1
  funext i
  fin_cases i
  rfl

private theorem realize_func2 (f : Fn 2) (t u : LRV.Term ι) (w : ι → M) :
    (Term.func f ![t,u] : LRV.Term ι).realize w = Structure.funMap (L := LRV) f ![t.realize w,u.realize w] := by
  change Structure.funMap (L := LRV) f (fun i => _) = _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- This bridge uses the original released operations, including residue
junk-zero behavior. Role maps only reindex original variable/parameter slots. -/
theorem toTerm_realize (fv : I → ι) (fr : R → ι) (fy : V → ι)
    (w : ι → M) (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)
    (hv : ∀ i, w (fv i) = (a i).val) (hr : ∀ i, w (fr i) = (r i).val)
    (hy : ∀ i, w (fy i) = (y i).val) (P : RVExpr I R V) :
    (P.toTerm fv fr fy).realize w = (P.eval a r y).val := by
  induction P with
  | zero =>
    simp only [toTerm,eval,realize_func0]
    exact (RVOperations.zero_val (M := M)).symm
  | one =>
    simp only [toTerm,eval,realize_func0]
    exact (RVOperations.one_val (M := M)).symm
  | vf P =>
    simp only [toTerm,eval,realize_func1]
    change iRv (((RingSyntax.ofRingTerm P).relabel fv).realize w) = _
    rw [Term.realize_relabel]
    have he : w ∘ fv = fun i => (a i).val := funext hv
    rw [he,RingSyntax.realizes P a]
    rfl
  | parameter i => exact hr i
  | ofVariable i => exact hy i
  | mul P Q ihP ihQ =>
    simp only [toTerm,eval,realize_func2]
    change iRVMul ((P.toTerm fv fr fy).realize w) ((Q.toTerm fv fr fy).realize w) = _
    rw [ihP,ihQ]
    exact (RVOperations.mul_val _ _).symm
  | inv P ih =>
    simp only [toTerm,eval,realize_func1]
    change iRVInvFn ((P.toTerm fv fr fy).realize w) = _
    rw [ih]
    exact (RVOperations.inv_val _).symm
  | addK P Q ihP ihQ =>
    simp only [toTerm,eval,realize_func2]
    change iKAdd ((P.toTerm fv fr fy).realize w) ((Q.toTerm fv fr fy).realize w) = _
    rw [ihP,ihQ]
    rfl
  | negK P ih =>
    simp only [toTerm,eval,realize_func1]
    change TrivCase.iKNeg ((P.toTerm fv fr fy).realize w) = _
    rw [ih]
    rfl

end RVExpr
end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: NormalFormLanguageBridge -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GuardedRVNormalForm
variable {α : Type} {n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag)

abbrev VFSlot := {i : α ⊕ Fin n // Sum.elim sα sn i = .vf}
abbrev RVParameterSlot := {i : α // sα i = .rv}
abbrev RVVariableSlot := {i : Fin n // sn i = .rv}

def vfSlotMap (i : VFSlot sα sn) : α ⊕ Fin n := i.val
def rvParameterMap (i : RVParameterSlot sα) : α ⊕ Fin n := .inl i.val
def rvVariableMap (i : RVVariableSlot sn) : α ⊕ Fin n := .inr i.val

def VFRepresentation (t : LRV.Term (α ⊕ Fin n)) : Prop :=
  ∃ P : VFPolynomial (VFSlot sα sn), (RingSyntax.ofRingTerm P).relabel (vfSlotMap sα sn) = t

def RVRepresentation (t : LRV.Term (α ⊕ Fin n)) : Prop :=
  ∃ P : RVExpr (VFSlot sα sn) (RVParameterSlot sα) (RVVariableSlot sn),
    P.toTerm (vfSlotMap sα sn) (rvParameterMap (n := n) sα) (rvVariableMap (α := α) sn) = t

/-- Every VF term is a polynomial expression, and every RV term is built
from those polynomial atoms and the released RV/residue operations. This is
syntax-only and uses exactly the original variable and parameter indices. -/
theorem source_term_representations (t : LRV.Term (α ⊕ Fin n)) :
    (TmSort sα sn t = some .vf → VFRepresentation sα sn t) ∧
      (TmSort sα sn t = some .rv → RVRepresentation sα sn t) := by
  induction t with
  | var i =>
    constructor
    · intro hs
      have hi : Sum.elim sα sn i = .vf := by cases i <;> exact Option.some.inj hs
      exact ⟨.var ⟨i,hi⟩,rfl⟩
    · intro hs
      cases i with
      | inl a => exact ⟨.parameter ⟨a,Option.some.inj hs⟩,rfl⟩
      | inr i => exact ⟨.ofVariable ⟨i,Option.some.inj hs⟩,rfl⟩
  | func f ts ih =>
    constructor
    · intro hs
      obtain ⟨hargs,hres⟩ := (tmSort_func_iff sα sn f ts).mp hs
      cases f with
      | vfZero =>
        refine ⟨VFPolynomial.zero,?_⟩
        change (Term.func Fn.vfZero _ : LRV.Term (α ⊕ Fin n)) = _
        congr 1
        funext i
        exact i.elim0
      | vfOne =>
        refine ⟨VFPolynomial.one,?_⟩
        change (Term.func Fn.vfOne _ : LRV.Term (α ⊕ Fin n)) = _
        congr 1
        funext i
        exact i.elim0
      | vfAdd =>
        obtain ⟨P,hP⟩ := (ih 0).1 (hargs 0)
        obtain ⟨Q,hQ⟩ := (ih 1).1 (hargs 1)
        refine ⟨VFPolynomial.add P Q,?_⟩
        change (Term.func Fn.vfAdd _ : LRV.Term (α ⊕ Fin n)) = _
        congr 1
        funext i
        fin_cases i
        · exact hP
        · exact hQ
      | vfMul =>
        obtain ⟨P,hP⟩ := (ih 0).1 (hargs 0)
        obtain ⟨Q,hQ⟩ := (ih 1).1 (hargs 1)
        refine ⟨VFPolynomial.mul P Q,?_⟩
        change (Term.func Fn.vfMul _ : LRV.Term (α ⊕ Fin n)) = _
        congr 1
        funext i
        fin_cases i
        · exact hP
        · exact hQ
      | vfNeg =>
        obtain ⟨P,hP⟩ := (ih 0).1 (hargs 0)
        refine ⟨VFPolynomial.neg P,?_⟩
        change (Term.func Fn.vfNeg _ : LRV.Term (α ⊕ Fin n)) = _
        congr 1
        funext i
        fin_cases i
        exact hP
      | rvOne | rvZero | rvMul | rvInv | kAdd | kNeg | rvMap => cases hres
    · intro hs
      obtain ⟨hargs,hres⟩ := (tmSort_func_iff sα sn f ts).mp hs
      cases f with
      | vfZero | vfOne | vfAdd | vfMul | vfNeg => cases hres
      | rvOne =>
        refine ⟨.one,?_⟩
        change (Term.func Fn.rvOne _ : LRV.Term (α ⊕ Fin n)) = _
        congr 1
        funext i
        exact i.elim0
      | rvZero =>
        refine ⟨.zero,?_⟩
        change (Term.func Fn.rvZero _ : LRV.Term (α ⊕ Fin n)) = _
        congr 1
        funext i
        exact i.elim0
      | rvMul =>
        obtain ⟨P,hP⟩ := (ih 0).2 (hargs 0)
        obtain ⟨Q,hQ⟩ := (ih 1).2 (hargs 1)
        refine ⟨.mul P Q,?_⟩
        change (Term.func Fn.rvMul _ : LRV.Term (α ⊕ Fin n)) = _
        congr 1
        funext i
        fin_cases i
        · exact hP
        · exact hQ
      | rvInv =>
        obtain ⟨P,hP⟩ := (ih 0).2 (hargs 0)
        refine ⟨.inv P,?_⟩
        change (Term.func Fn.rvInv _ : LRV.Term (α ⊕ Fin n)) = _
        congr 1
        funext i
        fin_cases i
        exact hP
      | kAdd =>
        obtain ⟨P,hP⟩ := (ih 0).2 (hargs 0)
        obtain ⟨Q,hQ⟩ := (ih 1).2 (hargs 1)
        refine ⟨.addK P Q,?_⟩
        change (Term.func Fn.kAdd _ : LRV.Term (α ⊕ Fin n)) = _
        congr 1
        funext i
        fin_cases i
        · exact hP
        · exact hQ
      | kNeg =>
        obtain ⟨P,hP⟩ := (ih 0).2 (hargs 0)
        refine ⟨.negK P,?_⟩
        change (Term.func Fn.kNeg _ : LRV.Term (α ⊕ Fin n)) = _
        congr 1
        funext i
        fin_cases i
        exact hP
      | rvMap =>
        obtain ⟨P,hP⟩ := (ih 0).1 (hargs 0)
        refine ⟨.vf P,?_⟩
        change (Term.func Fn.rvMap _ : LRV.Term (α ⊕ Fin n)) = _
        congr 1
        funext i
        fin_cases i
        exact hP

end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: KPolynomialAlgebra -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm.KPolynomial
variable {I R V M Γ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

noncomputable def lift (x : RVSort M) (hx : inK x) : Residue v :=
  (CanonicalResidue.equiv v hv).symm ⟨x,hx⟩

theorem image_lift (x : RVSort M) (hx : inK x) :
    ResidueRVAlgebra.residueRVHom v hv (lift v hv x hx) = x :=
  congrArg (fun z : CanonicalResidue.KSort M => z.val)
    ((CanonicalResidue.equiv v hv).apply_symm_apply ⟨x,hx⟩)

theorem rvSum_eq_lift_sum {n : ℕ} (x : Fin n → RVSort M) (hx : ∀ i, inK (x i)) :
    rvSum x = ResidueRVAlgebra.residueRVHom v hv (∑ i, lift v hv (x i) (hx i)) := by
  have he : (fun i => ResidueRVAlgebra.residueRVHom v hv (lift v hv (x i) (hx i))) = x :=
    funext (fun i => image_lift v hv (x i) (hx i))
  exact (congrArg rvSum he.symm).trans (rvSum_image v hv _)

include hv in
theorem rvSum_append {m n : ℕ} (x : Fin m → RVSort M) (y : Fin n → RVSort M)
    (hx : ∀ i, inK (x i)) (hy : ∀ i, inK (y i)) :
    rvSum (Sum.elim x y ∘ finSumFinEquiv.symm) = addK (rvSum x) (rvSum y) := by
  let a := fun i => lift v hv (x i) (hx i)
  let b := fun i => lift v hv (y i) (hy i)
  have he : (Sum.elim x y ∘ finSumFinEquiv.symm) =
      fun i => ResidueRVAlgebra.residueRVHom v hv (Sum.elim a b (finSumFinEquiv.symm i)) := by
    funext i
    dsimp only [Function.comp_def]
    cases h : finSumFinEquiv.symm i with
    | inl j => exact (image_lift v hv (x j) (hx j)).symm
    | inr j => exact (image_lift v hv (y j) (hy j)).symm
  rw [he,rvSum_image,rvSum_eq_lift_sum v hv x hx,rvSum_eq_lift_sum v hv y hy,
    ← ResidueRVAlgebra.residueRVHom_add]
  congr 1
  simp only [a,b,Equiv.sum_comp,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]

include hv in
theorem rvSum_cauchy {m n : ℕ} (x : Fin m → RVSort M) (y : Fin n → RVSort M)
    (hx : ∀ i, inK (x i)) (hy : ∀ i, inK (y i)) :
    rvSum (fun i : Fin (m*n) => x (finProdFinEquiv.symm i).1 * y (finProdFinEquiv.symm i).2) =
      rvSum x * rvSum y := by
  let a := fun i => lift v hv (x i) (hx i)
  let b := fun i => lift v hv (y i) (hy i)
  have he : (fun i : Fin (m*n) => x (finProdFinEquiv.symm i).1 * y (finProdFinEquiv.symm i).2) =
      fun i : Fin (m*n) => ResidueRVAlgebra.residueRVHom v hv
        (a (finProdFinEquiv.symm i).1 * b (finProdFinEquiv.symm i).2) := by
    funext i
    rw [map_mul,image_lift,image_lift]
  rw [he,rvSum_image,rvSum_eq_lift_sum v hv x hx,rvSum_eq_lift_sum v hv y hy,← map_mul]
  congr 1
  calc
    _ = ∑ j : Fin m × Fin n, a j.1 * b j.2 := (finProdFinEquiv.symm).sum_comp _
    _ = (∑ i, a i) * (∑ j, b j) := by
      simp only [Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm

include hv in
theorem rvSum_scalar {n : ℕ} (c : RVSort M) (x : Fin n → RVSort M)
    (hc : inK c) (hx : ∀ i, inK (x i)) :
    rvSum (fun i => c*x i) = c*rvSum x := by
  let a := lift v hv c hc
  let b := fun i => lift v hv (x i) (hx i)
  have he : (fun i => c*x i) = fun i => ResidueRVAlgebra.residueRVHom v hv (a*b i) := by
    funext i
    rw [map_mul,image_lift,image_lift]
  rw [he,rvSum_image,rvSum_eq_lift_sum v hv x hx]
  rw [← image_lift v hv c hc,← map_mul]
  congr 1
  exact (Finset.mul_sum _ _ _).symm

theorem inK_zero : inK (0 : RVSort M) := (RVOperations.inK_iff _).mpr (Or.inl rfl)
theorem inK_one : inK (1 : RVSort M) := (RVOperations.inK_iff _).mpr (Or.inr (map_one _))

theorem addK_zero_right (x : RVSort M) (hx : inK x) : addK x 0 = x := by
  simpa only [RVOperations.zeroRV_eq] using ValuedModelMap.addK_zero x hx

theorem eval_zero (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) :
    eval (zero : KPolynomial I R V) a r y = 0 := by
  change addK (Monomial.eval Monomial.zero a r y)
    (addK (Monomial.eval Monomial.zero a r y) 0) = 0
  rw [Monomial.eval_zero,addK_zero_right _ inK_zero,addK_zero_right _ inK_zero]

theorem eval_one (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) :
    eval (one : KPolynomial I R V) a r y = 1 := by
  change addK (Monomial.eval Monomial.one a r y)
    (addK (Monomial.eval Monomial.zero a r y) 0) = 1
  rw [Monomial.eval_one,Monomial.eval_zero,addK_zero_right _ inK_zero,addK_zero_right _ inK_one]

theorem prepared_zero (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) :
    Prepared (zero : KPolynomial I R V) a r y := by
  have h0 : (Monomial.zero : Monomial I R V).PoleFree a ∧
      (Monomial.zero : Monomial I R V).ProperSlots r y ∧ inK (Monomial.zero.eval a r y) := by
    refine ⟨one_ne_zero,?_,?_⟩
    · simp [Monomial.ProperSlots,Monomial.zero]
    · rw [Monomial.eval_zero]
      exact inK_zero
  intro i
  fin_cases i <;> exact h0

theorem prepared_one (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) :
    Prepared (one : KPolynomial I R V) a r y := by
  have h0 := prepared_zero a r y (0 : Fin 2)
  have h1 : (Monomial.one : Monomial I R V).PoleFree a ∧
      (Monomial.one : Monomial I R V).ProperSlots r y ∧ inK (Monomial.one.eval a r y) := by
    refine ⟨one_ne_zero,?_,?_⟩
    · simp [Monomial.ProperSlots,Monomial.one]
    · rw [Monomial.eval_one]
      exact inK_one
  intro i
  fin_cases i
  · exact h1
  · exact h0


variable (P Q : KPolynomial I R V) (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)

include hv in
theorem eval_add (hP : Prepared P a r y) (hQ : Prepared Q a r y) :
    eval (add P Q) a r y = addK (eval P a r y) (eval Q a r y) := by
  have he : (fun i : Fin (P.size+Q.size) =>
      (Sum.elim P.terms Q.terms (finSumFinEquiv.symm i)).eval a r y) =
        Sum.elim (fun i => (P.terms i).eval a r y) (fun i => (Q.terms i).eval a r y) ∘ finSumFinEquiv.symm := by
    funext i
    dsimp only [Function.comp_def]
    cases finSumFinEquiv.symm i <;> rfl
  exact (congrArg rvSum he).trans
    (rvSum_append v hv _ _ (fun i => (hP i).2.2) (fun i => (hQ i).2.2))

include hv in
theorem eval_mul (hP : Prepared P a r y) (hQ : Prepared Q a r y) :
    eval (mul P Q) a r y = eval P a r y * eval Q a r y := by
  unfold eval mul
  simp only [Monomial.eval_mul]
  exact rvSum_cauchy v hv (fun i => (P.terms i).eval a r y)
    (fun i => (Q.terms i).eval a r y) (fun i => (hP i).2.2) (fun i => (hQ i).2.2)

include hv in
theorem eval_scalar (T : Monomial I R V) (hT : inK (T.eval a r y)) (hP : Prepared P a r y) :
    eval (scalar T P) a r y = T.eval a r y * eval P a r y := by
  unfold eval scalar
  simp only [Monomial.eval_mul]
  exact rvSum_scalar v hv (T.eval a r y) (fun i => (P.terms i).eval a r y) hT (fun i => (hP i).2.2)

theorem prepared_add (hP : Prepared P a r y) (hQ : Prepared Q a r y) :
    Prepared (add P Q) a r y := by
  intro i
  change let j := finSumFinEquiv.symm i
         (Sum.elim P.terms Q.terms j).PoleFree a ∧
           (Sum.elim P.terms Q.terms j).ProperSlots r y ∧ inK ((Sum.elim P.terms Q.terms j).eval a r y)
  dsimp only
  cases finSumFinEquiv.symm i with
  | inl j => exact hP j
  | inr j => exact hQ j

include hv in
theorem prepared_mul (hP : Prepared P a r y) (hQ : Prepared Q a r y) :
    Prepared (mul P Q) a r y := by
  intro i
  let j : Fin P.size × Fin Q.size := finProdFinEquiv.symm i
  refine ⟨Monomial.poleFree_mul _ _ a (hP j.1).1 (hQ j.2).1,
    Monomial.properSlots_mul _ _ r y (hP j.1).2.1 (hQ j.2).2.1,?_⟩
  change inK ((Monomial.mul (P.terms j.1) (Q.terms j.2)).eval a r y)
  rw [Monomial.eval_mul]
  exact ResidueRVAlgebra.inK_mul v hv _ _ (hP j.1).2.2 (hQ j.2).2.2

include hv in
theorem prepared_scalar (T : Monomial I R V) (hp : T.PoleFree a) (hs : T.ProperSlots r y)
    (hT : inK (T.eval a r y)) (hP : Prepared P a r y) : Prepared (scalar T P) a r y := by
  intro i
  refine ⟨Monomial.poleFree_mul _ _ a hp (hP i).1,
    Monomial.properSlots_mul _ _ r y hs (hP i).2.1,?_⟩
  change inK ((Monomial.mul T (P.terms i)).eval a r y)
  rw [Monomial.eval_mul]
  exact ResidueRVAlgebra.inK_mul v hv _ _ hT (hP i).2.2


end SpecialTransformations.Section3.GuardedRVNormalForm.KPolynomial

/- Component: RationalFractionSyntax -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm

structure RVFraction (I R V : Type) where
  outer : Monomial I R V
  numerator : KPolynomial I R V
  denominator : KPolynomial I R V

namespace RVFraction
variable {I R V : Type}
def ofMonomial (T : Monomial I R V) : RVFraction I R V := ⟨T,KPolynomial.one,KPolynomial.one⟩
def zero : RVFraction I R V := ofMonomial Monomial.zero
def one : RVFraction I R V := ofMonomial Monomial.one
noncomputable def mul (F G : RVFraction I R V) : RVFraction I R V :=
  ⟨F.outer.mul G.outer,F.numerator.mul G.numerator,F.denominator.mul G.denominator⟩
noncomputable def inv (F : RVFraction I R V) : RVFraction I R V :=
  ⟨F.outer.inv,F.denominator,F.numerator⟩
noncomputable def absorb (F : RVFraction I R V) : RVFraction I R V :=
  ⟨Monomial.one,F.numerator.scalar F.outer,F.denominator⟩
noncomputable def residueAdd (F G : RVFraction I R V) : RVFraction I R V :=
  ⟨Monomial.one,
    ((F.numerator.scalar F.outer).mul G.denominator).add
      ((G.numerator.scalar G.outer).mul F.denominator),
    F.denominator.mul G.denominator⟩
noncomputable def residueNeg (F : RVFraction I R V) : RVFraction I R V :=
  ⟨(Monomial.vf (VFPolynomial.neg VFPolynomial.one)).mul F.outer,F.numerator,F.denominator⟩

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
noncomputable def eval (F : RVFraction I R V) (a : I → VFType (M := M))
    (r : R → RVSort M) (y : V → RVSort M) : RVSort M :=
  F.outer.eval a r y * F.numerator.eval a r y / F.denominator.eval a r y

structure Prepared (F : RVFraction I R V) (a : I → VFType (M := M))
    (r : R → RVSort M) (y : V → RVSort M) : Prop where
  pole : F.outer.PoleFree a
  slots : F.outer.ProperSlots r y
  numerator : F.numerator.Prepared a r y
  denominator : F.denominator.Prepared a r y
  denominator_ne_zero : F.denominator.eval a r y ≠ 0

variable (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)

theorem eval_ofMonomial (T : Monomial I R V) :
    (ofMonomial T).eval a r y = T.eval a r y := by
  simp only [eval,ofMonomial,KPolynomial.eval_one,mul_one,div_one]

theorem prepared_ofMonomial (T : Monomial I R V) (hp : T.PoleFree a) (hs : T.ProperSlots r y) :
    (ofMonomial T).Prepared a r y := by
  refine ⟨hp,hs,KPolynomial.prepared_one a r y,KPolynomial.prepared_one a r y,?_⟩
  change KPolynomial.one.eval a r y ≠ 0
  rw [KPolynomial.eval_one]
  exact one_ne_zero

theorem eval_zero : (zero : RVFraction I R V).eval a r y = 0 := by
  rw [zero,eval_ofMonomial,Monomial.eval_zero]

theorem eval_one : (one : RVFraction I R V).eval a r y = 1 := by
  rw [one,eval_ofMonomial,Monomial.eval_one]

theorem prepared_zero : (zero : RVFraction I R V).Prepared a r y := by
  apply prepared_ofMonomial
  · exact one_ne_zero
  · simp [Monomial.ProperSlots,Monomial.zero]

theorem prepared_one : (one : RVFraction I R V).Prepared a r y := by
  apply prepared_ofMonomial
  · exact one_ne_zero
  · simp [Monomial.ProperSlots,Monomial.one]

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

include hv in
theorem eval_mul (F G : RVFraction I R V) (hF : F.Prepared a r y) (hG : G.Prepared a r y) :
    (mul F G).eval a r y = F.eval a r y * G.eval a r y := by
  simp only [eval,mul,Monomial.eval_mul,KPolynomial.eval_mul v hv _ _ a r y hF.numerator hG.numerator,
    KPolynomial.eval_mul v hv _ _ a r y hF.denominator hG.denominator]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ac_rfl

include hv in
theorem prepared_mul (F G : RVFraction I R V) (hF : F.Prepared a r y) (hG : G.Prepared a r y) :
    (mul F G).Prepared a r y := by
  refine ⟨Monomial.poleFree_mul _ _ a hF.pole hG.pole,
    Monomial.properSlots_mul _ _ r y hF.slots hG.slots,
    KPolynomial.prepared_mul v hv _ _ a r y hF.numerator hG.numerator,
    KPolynomial.prepared_mul v hv _ _ a r y hF.denominator hG.denominator,?_⟩
  change (F.denominator.mul G.denominator).eval a r y ≠ 0
  rw [KPolynomial.eval_mul v hv _ _ a r y hF.denominator hG.denominator]
  exact mul_ne_zero hF.denominator_ne_zero hG.denominator_ne_zero

theorem eval_inv (F : RVFraction I R V) : (inv F).eval a r y = (F.eval a r y)⁻¹ := by
  simp only [eval,inv,Monomial.eval_inv,div_eq_mul_inv,mul_inv_rev,inv_inv]
  ac_rfl

theorem numerator_ne_zero_of_outer_ne_zero (T : Monomial I R V) (ht : T.eval a r y ≠ 0) :
    T.numerator.realize a ≠ 0 := by
  intro he
  apply ht
  simp only [Monomial.eval,he,map_zero,zero_div,zero_mul]

theorem prepared_inv (F : RVFraction I R V) (hF : F.Prepared a r y)
    (hM : F.outer.eval a r y ≠ 0) (hN : F.numerator.eval a r y ≠ 0) :
    (inv F).Prepared a r y :=
  ⟨Monomial.poleFree_inv _ a (numerator_ne_zero_of_outer_ne_zero a r y F.outer hM),
    Monomial.properSlots_inv _ r y hF.slots,hF.denominator,hF.numerator,hN⟩

include hv in
theorem eval_absorb (F : RVFraction I R V) (hF : F.Prepared a r y) (hK : inK (F.outer.eval a r y)) :
    (absorb F).eval a r y = F.eval a r y := by
  simp only [eval,absorb,Monomial.eval_one,one_mul,
    KPolynomial.eval_scalar v hv _ a r y F.outer hK hF.numerator]

include hv in
theorem prepared_absorb (F : RVFraction I R V) (hF : F.Prepared a r y) (hK : inK (F.outer.eval a r y)) :
    (absorb F).Prepared a r y := by
  refine ⟨one_ne_zero,?_,?_,hF.denominator,hF.denominator_ne_zero⟩
  · simp [absorb,Monomial.ProperSlots,Monomial.one]
  · exact KPolynomial.prepared_scalar v hv _ a r y F.outer hF.pole hF.slots hK hF.numerator

include hv in
theorem eval_inK_iff (F : RVFraction I R V) (hF : F.Prepared a r y)
    (hN : F.numerator.eval a r y ≠ 0) :
    inK (F.eval a r y) ↔ inK (F.outer.eval a r y) := by
  have hNK := KPolynomial.eval_inK v hv F.numerator a r y (fun i => (hF.numerator i).2.2)
  have hDK := KPolynomial.eval_inK v hv F.denominator a r y (fun i => (hF.denominator i).2.2)
  rw [eval,mul_div_assoc]
  exact ResidueRVAlgebra.inK_mul_iff_left v hv _ _
    (ResidueRVAlgebra.inK_div v hv _ _ hNK hDK) (div_ne_zero hN hF.denominator_ne_zero)

include hv in
theorem prepared_residueAdd (F G : RVFraction I R V) (hF : F.Prepared a r y) (hG : G.Prepared a r y)
    (hFK : inK (F.outer.eval a r y)) (hGK : inK (G.outer.eval a r y)) :
    (residueAdd F G).Prepared a r y := by
  have hf := KPolynomial.prepared_scalar v hv F.numerator a r y F.outer hF.pole hF.slots hFK hF.numerator
  have hg := KPolynomial.prepared_scalar v hv G.numerator a r y G.outer hG.pole hG.slots hGK hG.numerator
  refine ⟨one_ne_zero,?_,?_,?_,?_⟩
  · simp [residueAdd,Monomial.ProperSlots,Monomial.one]
  · exact KPolynomial.prepared_add _ _ a r y
      (KPolynomial.prepared_mul v hv _ _ a r y hf hG.denominator)
      (KPolynomial.prepared_mul v hv _ _ a r y hg hF.denominator)
  · exact KPolynomial.prepared_mul v hv _ _ a r y hF.denominator hG.denominator
  · change (F.denominator.mul G.denominator).eval a r y ≠ 0
    rw [KPolynomial.eval_mul v hv _ _ a r y hF.denominator hG.denominator]
    exact mul_ne_zero hF.denominator_ne_zero hG.denominator_ne_zero

include hv in
theorem eval_residueAdd (F G : RVFraction I R V) (hF : F.Prepared a r y) (hG : G.Prepared a r y)
    (hFK : inK (F.outer.eval a r y)) (hGK : inK (G.outer.eval a r y)) :
    (residueAdd F G).eval a r y = addK (F.eval a r y) (G.eval a r y) := by
  have hf := KPolynomial.prepared_scalar v hv F.numerator a r y F.outer hF.pole hF.slots hFK hF.numerator
  have hg := KPolynomial.prepared_scalar v hv G.numerator a r y G.outer hG.pole hG.slots hGK hG.numerator
  have hf' := KPolynomial.prepared_mul v hv _ _ a r y hf hG.denominator
  have hg' := KPolynomial.prepared_mul v hv _ _ a r y hg hF.denominator
  simp only [eval,residueAdd,Monomial.eval_one,one_mul,
    KPolynomial.eval_add v hv _ _ a r y hf' hg',
    KPolynomial.eval_mul v hv _ _ a r y hf hG.denominator,
    KPolynomial.eval_mul v hv _ _ a r y hg hF.denominator,
    KPolynomial.eval_mul v hv _ _ a r y hF.denominator hG.denominator,
    KPolynomial.eval_scalar v hv _ a r y F.outer hFK hF.numerator,
    KPolynomial.eval_scalar v hv _ a r y G.outer hGK hG.numerator]
  exact (ResidueRVAlgebra.fraction_add v hv _ _ _ _
    (ResidueRVAlgebra.inK_mul v hv _ _ hFK
      (KPolynomial.eval_inK v hv _ a r y (fun i => (hF.numerator i).2.2)))
    (KPolynomial.eval_inK v hv _ a r y (fun i => (hF.denominator i).2.2))
    (ResidueRVAlgebra.inK_mul v hv _ _ hGK
      (KPolynomial.eval_inK v hv _ a r y (fun i => (hG.numerator i).2.2)))
    (KPolynomial.eval_inK v hv _ a r y (fun i => (hG.denominator i).2.2))
    hF.denominator_ne_zero hG.denominator_ne_zero).symm

theorem prepared_residueNeg (F : RVFraction I R V) (hF : F.Prepared a r y) :
    (residueNeg F).Prepared a r y := by
  refine ⟨Monomial.poleFree_mul _ _ a one_ne_zero hF.pole,
    Monomial.properSlots_mul _ _ r y ?_ hF.slots,hF.numerator,hF.denominator,hF.denominator_ne_zero⟩
  simp [Monomial.ProperSlots,Monomial.vf]

include hv in
theorem eval_residueNeg (F : RVFraction I R V) (hF : F.Prepared a r y)
    (hFK : inK (F.outer.eval a r y)) :
    (residueNeg F).eval a r y = negK (F.eval a r y) := by
  simp only [eval,residueNeg,Monomial.eval_mul,Monomial.eval_vf,
    VFPolynomial.realize_neg,VFPolynomial.realize_one,mul_assoc]
  exact (ResidueRVAlgebra.fraction_neg v hv _ _
    (ResidueRVAlgebra.inK_mul v hv _ _ hFK
      (KPolynomial.eval_inK v hv _ a r y (fun i => (hF.numerator i).2.2)))
    (KPolynomial.eval_inK v hv _ a r y (fun i => (hF.denominator i).2.2))).symm

end RVFraction
end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: FiniteGuardedBranches -/
namespace SpecialTransformations.Section3.FiniteGuardedBranches
variable {T A B : Type*}
structure Branch (T A : Type*) where
  guards : List T
  value : A

def satisfied (p : T → Prop) (g : List T) : Prop := ∀ t ∈ g, p t

def run (p : T → Prop) (branches : List (Branch T A)) : Set A :=
  {a | ∃ b ∈ branches, satisfied p b.guards ∧ b.value = a}

def pure (a : A) : List (Branch T A) := [⟨[],a⟩]
def emit (g : List T) (a : A) : List (Branch T A) := [⟨g,a⟩]
def bind (branches : List (Branch T A)) (f : A → List (Branch T B)) : List (Branch T B) :=
  branches.flatMap (fun b => (f b.value).map (fun c => ⟨b.guards++c.guards,c.value⟩))

theorem satisfied_append (p : T → Prop) (g h : List T) :
    satisfied p (g++h) ↔ satisfied p g ∧ satisfied p h := by
  simp only [satisfied,List.mem_append]
  aesop

theorem run_pure (p : T → Prop) (a b : A) : b ∈ run p (pure a) ↔ b = a := by
  simp [run,pure,satisfied,eq_comm]

theorem run_emit (p : T → Prop) (g : List T) (a b : A) :
    b ∈ run p (emit g a) ↔ satisfied p g ∧ b = a := by
  simp [run,emit,eq_comm]

theorem run_append (p : T → Prop) (branches more : List (Branch T A)) (a : A) :
    a ∈ run p (branches++more) ↔ a ∈ run p branches ∨ a ∈ run p more := by
  simp only [run,Set.mem_setOf_eq,List.mem_append]
  aesop

theorem run_bind (p : T → Prop) (branches : List (Branch T A))
    (f : A → List (Branch T B)) (b : B) :
    b ∈ run p (bind branches f) ↔ ∃ a ∈ run p branches, b ∈ run p (f a) := by
  simp only [run,bind,Set.mem_setOf_eq,List.mem_flatMap,List.mem_map]
  constructor
  · rintro ⟨_,⟨d,hd,c,hc,rfl⟩,hg,he⟩
    obtain ⟨hg,hg'⟩ := (satisfied_append p d.guards c.guards).mp hg
    exact ⟨d.value,⟨d,hd,hg,rfl⟩,c,hc,hg',he⟩
  · rintro ⟨a,⟨d,hd,hg,rfl⟩,c,hc,hg',he⟩
    exact ⟨_,⟨d,hd,c,hc,rfl⟩,(satisfied_append p d.guards c.guards).mpr ⟨hg,hg'⟩,he⟩

end SpecialTransformations.Section3.FiniteGuardedBranches

/- Component: NormalFormTests -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm

inductive NFTest (I R V : Type) where
  | parameterZero : R → Bool → NFTest I R V
  | variableZero : V → Bool → NFTest I R V
  | monomialZero : Monomial I R V → Bool → NFTest I R V
  | polynomialZero : KPolynomial I R V → Bool → NFTest I R V
  | monomialResidue : Monomial I R V → Bool → NFTest I R V

namespace NFTest
variable {I R V M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def signed (pos : Bool) (P : Prop) : Prop := if pos then P else ¬P

def Safe (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) : NFTest I R V → Prop
  | .parameterZero _ _ | .variableZero _ _ => True
  | .monomialZero T _ | .monomialResidue T _ => T.PoleFree a ∧ T.ProperSlots r y
  | .polynomialZero P _ => P.Prepared a r y

noncomputable def predicate (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M) :
    NFTest I R V → Prop
  | .parameterZero i pos => signed pos (r i=0)
  | .variableZero i pos => signed pos (y i=0)
  | .monomialZero T pos => signed pos (T.eval a r y=0)
  | .polynomialZero P pos => signed pos (P.eval a r y=0)
  | .monomialResidue T pos => signed pos (inK (T.eval a r y))

noncomputable def holds (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)
    (t : NFTest I R V) : Prop := Safe a r y t ∧ predicate a r y t

theorem signed_true (P : Prop) : signed true P ↔ P := Iff.rfl
theorem signed_false (P : Prop) : signed false P ↔ ¬ P := Iff.rfl

theorem raw_monomial_test (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)
    (T : Monomial I R V) (pos : Bool) :
    holds a r y (.monomialZero T pos) ↔
      T.PoleFree a ∧ T.ProperSlots r y ∧ signed pos (T.rawEval a r y=0) := by
  simp only [holds,Safe,predicate]
  constructor
  · rintro ⟨⟨hp,hs⟩,he⟩
    exact ⟨hp,hs,by rwa [Monomial.eval_eq_rawEval T a r y hs] at he⟩
  · rintro ⟨hp,hs,he⟩
    exact ⟨⟨hp,hs⟩,by rwa [Monomial.eval_eq_rawEval T a r y hs]⟩

theorem raw_polynomial_test (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)
    (P : KPolynomial I R V) (pos : Bool) :
    holds a r y (.polynomialZero P pos) ↔
      P.Prepared a r y ∧ signed pos (P.rawEval a r y=0) := by
  simp only [holds,Safe,predicate]
  constructor
  · rintro ⟨hp,he⟩
    exact ⟨hp,by rwa [KPolynomial.prepared_eval_eq_rawEval P a r y hp] at he⟩
  · rintro ⟨hp,he⟩
    exact ⟨hp,by rwa [KPolynomial.prepared_eval_eq_rawEval P a r y hp]⟩

end NFTest
end SpecialTransformations.Section3.GuardedRVNormalForm
