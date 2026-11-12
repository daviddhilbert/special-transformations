module

public import Section4.MultivariateLocal

@[expose] public section

/-! At an independent VF tuple, the local constancy of an RV term is
uniform in every free RV coordinate. A well-sorted VF subterm uses
only the VF coordinates and the original named coefficients. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8.MixedLocal

def tupleSort (n m : ℕ) : Fin (n + m) → SortTag :=
  Sum.elim (fun _ => .vf) (fun _ => .rv) ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).symm

variable {M : Type} [LRV.Structure M] {α : Type} {n m : ℕ}

def tupleCode (a : Fin n → VFType (M := M)) (b : Fin m → CanonicalRV.RVSort M) : Fin (n + m) → M :=
  Sum.elim (vfValues a) (rvValues b) ∘ (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).symm

theorem tupleCode_sorted (a : Fin n → VFType (M := M)) (b : Fin m → CanonicalRV.RVSort M) :
    ∀ i, sortEval (tupleSort n m i) (tupleCode a b i) := by
  intro i
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  change sortEval (Sum.elim (fun _ => .vf) (fun _ => .rv) (e.symm i))
    (Sum.elim (vfValues a) (rvValues b) (e.symm i))
  cases e.symm i with
  | inl j => exact (a j).property
  | inr j => exact (b j).property

def restrictVF : LRV.Term (α ⊕ Fin (n + m)) → LRV.Term (α ⊕ Fin n)
  | .var (.inl i) => .var (.inl i)
  | .var (.inr j) => match (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).symm j with
    | .inl i => .var (.inr i)
    | .inr _ => .func Fn.vfZero Fin.elim0
  | .func f ts => .func f (fun i => restrictVF (ts i))

private theorem vf_result_args {l : ℕ} (f : Fn l) (hf : Fn.resSort f = .vf) (i : Fin l) :
    Fn.argSort f i = .vf := by
  cases f <;> first | rfl | exact i.elim0 | cases hf

theorem restrictVF_spec (sα : α → SortTag) (p : α → M)
    (t : LRV.Term (α ⊕ Fin (n + m))) (ht : TmSort sα (tupleSort n m) t = some .vf) :
    TmSort sα (fun _ => .vf) (restrictVF t) = some .vf ∧
      ∀ (a : Fin n → VFType (M := M)) (b : Fin m → CanonicalRV.RVSort M),
        t.realize (Sum.elim p (tupleCode a b)) = (restrictVF t).realize (Sum.elim p (vfValues a)) := by
  induction t with
  | var i =>
    rcases i with i | i
    · exact ⟨ht, fun _ _ => rfl⟩
    · let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
      cases he : e.symm i with
      | inl j =>
        constructor
        · simp only [restrictVF, show (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).symm i = .inl j from he,
            TmSort]
        · intro a b
          simp only [restrictVF, tupleCode, Term.realize, Sum.elim_inr, Function.comp_apply,
            show (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).symm i = .inl j from he, Sum.elim_inl]
      | inr j =>
        change some (Sum.elim (fun _ => SortTag.vf) (fun _ => SortTag.rv) (e.symm i)) = some .vf at ht
        rw [he] at ht
        cases ht
  | func f ts ih =>
    obtain ⟨hargs, hres⟩ := (tmSort_func_iff sα (tupleSort n m) f ts).mp ht
    have h (i) : TmSort sα (tupleSort n m) (ts i) = some .vf := by
      rw [← vf_result_args f hres i]
      exact hargs i
    constructor
    · change TmSort sα (fun _ => .vf) (.func f (fun i => restrictVF (ts i))) = some .vf
      apply (tmSort_func_iff sα (fun _ => .vf) f _).mpr
      exact ⟨fun i => by rw [vf_result_args f hres i]; exact (ih i (h i)).1, hres⟩
    · intro a b
      change Structure.funMap (L := LRV) f _ = Structure.funMap (L := LRV) f _
      congr 1
      funext i
      exact (ih i (h i)).2 a b

variable [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem rvTerm_uniform_local {S : Set M} (p : Parameters S) (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin n → VFType (M := M)) (ha : AlgebraicIndependent E a)
    (t : LRV.Term (Fin p.length ⊕ Fin (n + m)))
    (ht : TmSort p.sorts (tupleSort n m) t = some .rv) :
    ∀ᶠ x in 𝓝 a, ∀ b : Fin m → CanonicalRV.RVSort M,
      t.realize (Sum.elim p.values (tupleCode x b)) = t.realize (Sum.elim p.values (tupleCode a b)) := by
  induction t with
  | var i =>
    rcases i with i | i
    · exact Filter.Eventually.of_forall (fun _ _ => rfl)
    · let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
      cases he : e.symm i with
      | inl j =>
        change some (Sum.elim (fun _ => SortTag.vf) (fun _ => SortTag.rv) (e.symm i)) = some .rv at ht
        rw [he] at ht
        cases ht
      | inr j =>
        exact Filter.Eventually.of_forall (fun x b => by
          change Sum.elim (vfValues x) (rvValues b) (e.symm i) =
            Sum.elim (vfValues a) (rvValues b) (e.symm i)
          rw [he]
          rfl)
  | func f ts ih =>
    obtain ⟨harg, hres⟩ := (tmSort_func_iff p.sorts (tupleSort n m) f ts).mp ht
    have hfunc {l : ℕ} (g : Fn l) (us : Fin l → LRV.Term (Fin p.length ⊕ Fin (n + m)))
        (h : ∀ i, ∀ᶠ x in 𝓝 a, ∀ b : Fin m → CanonicalRV.RVSort M,
          (us i).realize (Sum.elim p.values (tupleCode x b)) =
            (us i).realize (Sum.elim p.values (tupleCode a b))) :
        ∀ᶠ x in 𝓝 a, ∀ b : Fin m → CanonicalRV.RVSort M,
          (Term.func g us).realize (Sum.elim p.values (tupleCode x b)) =
            (Term.func g us).realize (Sum.elim p.values (tupleCode a b)) := by
      filter_upwards [Filter.eventually_all.mpr h] with x hx b
      change Structure.funMap (L := LRV) g _ = Structure.funMap (L := LRV) g _
      congr 1
      funext i
      exact hx i b
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
      let u : LRV.Term (Fin p.length ⊕ Fin n) := .func Fn.rvMap (fun i => restrictVF (ts i))
      have hu : TmSort p.sorts (fun _ => .vf) u = some .rv :=
        tmSort_func p.sorts (fun _ => .vf) Fn.rvMap _ (fun i => (restrictVF_spec p.sorts p.values _ (harg i)).1)
      have he (x : Fin n → VFType (M := M)) (b : Fin m → CanonicalRV.RVSort M) :
          (Term.func Fn.rvMap ts).realize (Sum.elim p.values (tupleCode x b)) =
            u.realize (Sum.elim p.values (vfValues x)) := by
        change Structure.funMap (L := LRV) Fn.rvMap _ = Structure.funMap (L := LRV) Fn.rvMap _
        congr 1
        funext i
        exact (restrictVF_spec p.sorts p.values _ (harg i)).2 x b
      filter_upwards [MultivariateLocal.rvTerm_local p E hp hv a ha u hu] with x hx b
      exact (he x b).trans (hx.trans (he a b).symm)

end SpecialTransformations.Section8.MixedLocal
