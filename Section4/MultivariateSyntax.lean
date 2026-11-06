import Section4.RealPresentations
import Section3.PolynomialSyntax
import Mathlib.Algebra.MvPolynomial.Basic

set_option backward.isDefEq.respectTransparency false

/-! The finite-VF-tuple version of Section3.PolynomialSyntax. This is a
syntax bridge inside the released LRV language, used for the local argument
in 4.6. The earlier coefficient interpretation is reused as given. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section4.MultivariateSyntax

variable {M : Type} [LRV.Structure M]

private theorem eval_fn0 {β : Type} (f : Fn 0) (ts : Fin 0 → LRV.Term β) (v : β → M) :
    (Term.func f ts).realize v = Structure.funMap (L := LRV) f Fin.elim0 := by
  change Structure.funMap (L := LRV) f (fun i => (ts i).realize v) = _
  congr 1
  funext i
  exact i.elim0

private theorem eval_fn1 {β : Type} (f : Fn 1) (ts : Fin 1 → LRV.Term β) (v : β → M) :
    (Term.func f ts).realize v = Structure.funMap (L := LRV) f ![(ts 0).realize v] := by
  change Structure.funMap (L := LRV) f (fun i => (ts i).realize v) = _
  congr 1
  funext i
  fin_cases i
  rfl

private theorem eval_fn2 {β : Type} (f : Fn 2) (ts : Fin 2 → LRV.Term β) (v : β → M) :
    (Term.func f ts).realize v = Structure.funMap (L := LRV) f ![(ts 0).realize v, (ts 1).realize v] := by
  change Structure.funMap (L := LRV) f (fun i => (ts i).realize v) = _
  congr 1
  funext i
  fin_cases i <;> rfl

variable [hM : M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

noncomputable def toPolynomial (p : Parameters S) (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E) :
    LRV.Term (Fin p.length ⊕ Fin n) → MvPolynomial (Fin n) E
  | .var (.inl i) => MvPolynomial.C (PolynomialSyntax.coefficient p E hp i)
  | .var (.inr i) => MvPolynomial.X i
  | .func .vfZero _ => 0
  | .func .vfOne _ => 1
  | .func .vfAdd ts => toPolynomial p E hp (ts 0) + toPolynomial p E hp (ts 1)
  | .func .vfMul ts => toPolynomial p E hp (ts 0) * toPolynomial p E hp (ts 1)
  | .func .vfNeg ts => -toPolynomial p E hp (ts 0)
  | .func _ _ => 0

theorem realizes (p : Parameters S) (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E)
    (t : LRV.Term (Fin p.length ⊕ Fin n))
    (ht : TmSort p.sorts (fun _ => .vf) t = some .vf) (x : Fin n → VFType (M := M)) :
    t.realize (Sum.elim p.values (vfValues x)) =
      ((toPolynomial p E hp t).eval₂ E.subtype x).val := by
  classical
  induction t with
  | var i =>
    cases i with
    | inl i =>
      have hi : p.sorts i = .vf := Option.some.inj ht
      have hv : iVF (p.values i) := by
        have hv := p.sorted i
        rw [hi] at hv
        exact hv
      simp only [toPolynomial, MvPolynomial.eval₂_C]
      change p.values i = (PolynomialSyntax.coefficient p E hp i).val.val
      simp [PolynomialSyntax.coefficient, hv]
    | inr i => simp [toPolynomial, Term.realize, vfValues]
  | func f ts ih =>
    obtain ⟨harg, hres⟩ := (tmSort_func_iff p.sorts (fun _ => .vf) f ts).mp ht
    cases f with
    | vfZero =>
      rw [eval_fn0]
      simp only [toPolynomial, MvPolynomial.eval₂_zero]
      rfl
    | vfOne =>
      rw [eval_fn0]
      simp only [toPolynomial, MvPolynomial.eval₂_one]
      rfl
    | vfAdd =>
      rw [eval_fn2, ih 0 (harg 0), ih 1 (harg 1)]
      simp only [toPolynomial, MvPolynomial.eval₂_add]
      rfl
    | vfMul =>
      rw [eval_fn2, ih 0 (harg 0), ih 1 (harg 1)]
      simp only [toPolynomial, MvPolynomial.eval₂_mul]
      rfl
    | vfNeg =>
      rw [eval_fn1, ih 0 (harg 0)]
      simp only [toPolynomial, MvPolynomial.eval₂_neg]
      rfl
    | rvOne => cases hres
    | rvZero => cases hres
    | rvMul => cases hres
    | rvInv => cases hres
    | kAdd => cases hres
    | kNeg => cases hres
    | rvMap => cases hres

end SpecialTransformations.Section4.MultivariateSyntax
