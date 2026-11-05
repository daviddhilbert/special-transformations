import Section3.PolynomialSyntax
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.MixedPolynomialSyntax
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {A : Set M} {m : ℕ}

/-- One VF coordinate followed by any finite RV tuple. -/
def contextSort {m : ℕ} : Fin (m + 1) → SortTag := Fin.cons .vf (fun _ => .rv)

noncomputable def toPolynomial (p : Parameters A) (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E) :
    LRV.Term (Fin p.length ⊕ Fin (m + 1)) → Polynomial E
  | .var (.inl i) => Polynomial.C (PolynomialSyntax.coefficient p E hp i)
  | .var (.inr i) => if i = 0 then Polynomial.X else 0
  | .func .vfZero _ => 0
  | .func .vfOne _ => 1
  | .func .vfAdd ts => toPolynomial p E hp (ts 0) + toPolynomial p E hp (ts 1)
  | .func .vfMul ts => toPolynomial p E hp (ts 0) * toPolynomial p E hp (ts 1)
  | .func .vfNeg ts => -toPolynomial p E hp (ts 0)
  | .func _ _ => 0

omit hM in
private theorem eval_fn0 {β : Type} (f : Fn 0) (ts : Fin 0 → LRV.Term β) (v : β → M) :
    (Term.func f ts).realize v = Structure.funMap (L := LRV) f Fin.elim0 := by
  change Structure.funMap (L := LRV) f (fun i => (ts i).realize v) = _
  congr 1; funext i; exact i.elim0

omit hM in
private theorem eval_fn1 {β : Type} (f : Fn 1) (ts : Fin 1 → LRV.Term β) (v : β → M) :
    (Term.func f ts).realize v = Structure.funMap (L := LRV) f ![(ts 0).realize v] := by
  change Structure.funMap (L := LRV) f (fun i => (ts i).realize v) = _
  congr 1; funext i; fin_cases i; rfl

omit hM in
private theorem eval_fn2 {β : Type} (f : Fn 2) (ts : Fin 2 → LRV.Term β) (v : β → M) :
    (Term.func f ts).realize v = Structure.funMap (L := LRV) f ![(ts 0).realize v, (ts 1).realize v] := by
  change Structure.funMap (L := LRV) f (fun i => (ts i).realize v) = _
  congr 1; funext i; fin_cases i <;> rfl

theorem realizes (p : Parameters A) (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E)
    (t : LRV.Term (Fin p.length ⊕ Fin (m + 1)))
    (ht : TmSort p.sorts (contextSort (m := m)) t = some .vf)
    (x : VFType (M := M)) (ys : Fin m → M) :
    t.realize (Sum.elim p.values (Fin.cons x.val ys)) =
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
      simp only [toPolynomial, Polynomial.eval₂_C]
      change p.values i = (PolynomialSyntax.coefficient p E hp i).val.val
      simp [PolynomialSyntax.coefficient, hv]
    | inr i =>
      cases i using Fin.cases with
      | zero => simp [toPolynomial, Term.realize]
      | succ j => cases ht
  | func f ts ih =>
    obtain ⟨harg, hres⟩ := (tmSort_func_iff p.sorts (contextSort (m := m)) f ts).mp ht
    cases f with
    | vfZero =>
      rw [eval_fn0]
      simp only [toPolynomial, Polynomial.eval₂_zero]
      rfl
    | vfOne =>
      rw [eval_fn0]
      simp only [toPolynomial, Polynomial.eval₂_one]
      rfl
    | vfAdd =>
      rw [eval_fn2, ih 0 (harg 0), ih 1 (harg 1)]
      simp only [toPolynomial, Polynomial.eval₂_add]
      rfl
    | vfMul =>
      rw [eval_fn2, ih 0 (harg 0), ih 1 (harg 1)]
      simp only [toPolynomial, Polynomial.eval₂_mul]
      rfl
    | vfNeg =>
      rw [eval_fn1, ih 0 (harg 0)]
      simp only [toPolynomial, Polynomial.eval₂_neg]
      rfl
    | rvOne => cases hres
    | rvZero => cases hres
    | rvMul => cases hres
    | rvInv => cases hres
    | kAdd => cases hres
    | kNeg => cases hres
    | rvMap => cases hres

end SpecialTransformations.Section3.MixedPolynomialSyntax