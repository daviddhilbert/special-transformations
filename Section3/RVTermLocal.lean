module

public import Section3.PolynomialSyntax
public import Section3.PolynomialLocal

@[expose] public section
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {A : Set M}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

private theorem eval_rvMap {α : Type} (ts : Fin 1 → LRV.Term α) (v : α → M) :
    (Term.func Fn.rvMap ts).realize v = iRv ((ts 0).realize v) := by
  change Structure.funMap (L := LRV) Fn.rvMap (fun i => (ts i).realize v) = _
  have he : (fun i => (ts i).realize v) = ![(ts 0).realize v] := by
    funext i; fin_cases i; rfl
  rw [he]; rfl

theorem rvTerm_local (p : Parameters A) (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : VFType (M := M)) (ha : Transcendental E a)
    (t : LRV.Term (Fin p.length ⊕ Fin 1))
    (ht : TmSort p.sorts (fun _ => .vf) t = some .rv) :
    {x : VFType (M := M) | t.realize (Sum.elim p.values ![x.val]) =
      t.realize (Sum.elim p.values ![a.val])} ∈ 𝓝 a := by
  induction t with
  | var i =>
    cases i with
    | inl i => exact Filter.Eventually.of_forall (fun _ => rfl)
    | inr i => cases ht
  | func f ts ih =>
    obtain ⟨harg, hres⟩ := (tmSort_func_iff p.sorts (fun _ => .vf) f ts).mp ht
    have hfunc {k : ℕ} (f : Fn k) (ts : Fin k → LRV.Term (Fin p.length ⊕ Fin 1))
        (h : ∀ i, {x : VFType (M := M) | (ts i).realize (Sum.elim p.values ![x.val]) =
          (ts i).realize (Sum.elim p.values ![a.val])} ∈ 𝓝 a) :
        {x : VFType (M := M) | (Term.func f ts).realize (Sum.elim p.values ![x.val]) =
          (Term.func f ts).realize (Sum.elim p.values ![a.val])} ∈ 𝓝 a := by
      filter_upwards [(Filter.eventually_all).mpr h] with x hx
      change Structure.funMap (L := LRV) f _ = Structure.funMap (L := LRV) f _
      congr 1
      funext i; exact hx i
    cases f with
    | vfZero => cases hres
    | vfOne => cases hres
    | vfAdd => cases hres
    | vfMul => cases hres
    | vfNeg => cases hres
    | rvZero => exact hfunc _ _ (fun i => i.elim0)
    | rvOne => exact hfunc _ _ (fun i => i.elim0)
    | rvMul => exact hfunc _ _ (fun i => ih i (harg i))
    | rvInv => exact hfunc _ _ (fun i => ih i (harg i))
    | kAdd => exact hfunc _ _ (fun i => ih i (harg i))
    | kNeg => exact hfunc _ _ (fun i => ih i (harg i))
    | rvMap =>
      let q := PolynomialSyntax.toPolynomial p E hp (ts 0)
      have hterm (x : VFType (M := M)) :
          (Term.func Fn.rvMap ts).realize (Sum.elim p.values ![x.val]) =
            iRv ((q.eval₂ E.subtype x).val) := by
        rw [eval_rvMap, PolynomialSyntax.realizes p E hp (ts 0) (harg 0) x]
      by_cases hq : q = 0
      · filter_upwards [] with x
        rw [hterm x, hterm a, hq]
        simp
      · have hqa : q.eval₂ E.subtype a ≠ 0 := by
          intro hz
          exact ha ⟨q, hq, hz⟩
        have hnear := polynomial_rv_locally_constant hv (q.map E.subtype) a
          (by simpa only [Polynomial.eval_map] using hqa)
        filter_upwards [hnear] with x hx
        rw [hterm x, hterm a]
        simpa only [Polynomial.eval_map] using hx

end SpecialTransformations.Section3