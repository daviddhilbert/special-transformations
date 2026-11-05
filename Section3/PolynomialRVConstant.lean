import Section3.BallTranslation
import VFAlgClosed
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private theorem rv_mul_congr (a b c d : VFType (M := M))
    (ha : iRv a.val = iRv c.val) (hb : iRv b.val = iRv d.val) :
    iRv (a * b).val = iRv (c * d).val := by
  change iRv (iVFMul a.val b.val) = iRv (iVFMul c.val d.val)
  rw [rv_mul_hom_of_model hM a.property b.property,
    rv_mul_hom_of_model hM c.property d.property, ha, hb]

private theorem rv_prod_congr (s : Multiset (VFType (M := M)))
    (f g : VFType (M := M) → VFType (M := M))
    (h : ∀ a ∈ s, iRv (f a).val = iRv (g a).val) :
    iRv (s.map f).prod.val = iRv (s.map g).prod.val := by
  revert h
  induction s using Multiset.induction_on with
  | empty => intro h; rfl
  | cons a s ih =>
    intro h
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact rv_mul_congr _ _ _ _ (h a (Multiset.mem_cons_self a s))
      (ih (fun b hb => h b (Multiset.mem_cons_of_mem hb)))

theorem polynomial_rv_eq_of_linear_factors (p : Polynomial (VFType (M := M)))
    (x y : VFType (M := M))
    (h : ∀ c ∈ p.roots, iRv (x - c).val = iRv (y - c).val) :
    iRv (p.eval x).val = iRv (p.eval y).val := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  calc
    iRv (p.eval x).val = iRv (p.leadingCoeff * (p.roots.map (x - ·)).prod).val :=
      congrArg (fun z : VFType (M := M) => iRv z.val)
        ((IsAlgClosed.splits p).eval_eq_prod_roots x)
    _ = iRv (p.leadingCoeff * (p.roots.map (y - ·)).prod).val :=
      rv_mul_congr _ _ _ _ rfl (rv_prod_congr p.roots (x - ·) (y - ·) h)
    _ = iRv (p.eval y).val := congrArg (fun z : VFType (M := M) => iRv z.val)
      ((IsAlgClosed.splits p).eval_eq_prod_roots y).symm

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

include hv in
theorem polynomial_rv_constant_openDisc (p : Polynomial (VFType (M := M)))
    (a : VFType (M := M)) (r : Balls.Radius Γ)
    (hroot : ∀ c ∈ p.roots, c ∉ Balls.openDisc v a r)
    (x y : VFType (M := M)) (hx : x ∈ Balls.openDisc v a r)
    (hy : y ∈ Balls.openDisc v a r) : iRv (p.eval x).val = iRv (p.eval y).val := by
  apply polynomial_rv_eq_of_linear_factors p x y
  intro c hc
  exact Balls.rv_sub_constant_openDisc v hv a c r (hroot c hc) x y hx hy

include hv in
theorem polynomial_rv_constant_closedDisc (p : Polynomial (VFType (M := M)))
    (a : VFType (M := M)) (r : Balls.Radius Γ)
    (hroot : ∀ c ∈ p.roots, c ∉ Balls.closedDisc v a r)
    (x y : VFType (M := M)) (hx : x ∈ Balls.closedDisc v a r)
    (hy : y ∈ Balls.closedDisc v a r) : iRv (p.eval x).val = iRv (p.eval y).val := by
  apply polynomial_rv_eq_of_linear_factors p x y
  intro c hc
  exact Balls.rv_sub_constant_closedDisc v hv a c r (hroot c hc) x y hx hy

end SpecialTransformations.Section3
