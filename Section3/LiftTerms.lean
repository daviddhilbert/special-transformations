module

public import Section3.RVRepresentatives

@[expose] public section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.RVRepresentatives
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

def decode : SortTag → VFType (M := M) → M
  | .vf, x => x.val
  | .rv, x => iRv x.val

noncomputable def liftFn {k : ℕ} (f : Fn k) (x : Fin k → VFType (M := M)) :
    VFType (M := M) := match f with
  | .vfZero | .rvZero => 0
  | .vfOne | .rvOne => 1
  | .vfAdd => x 0 + x 1
  | .vfMul | .rvMul => x 0 * x 1
  | .vfNeg => -x 0
  | .rvInv => (x 0)⁻¹
  | .kAdd => add v (x 0) (x 1)
  | .kNeg => neg v (x 0)
  | .rvMap => x 0

omit hM in
private theorem nullary (f : Fn 0) (x : Fin 0 → M) :
    Structure.funMap (L := LRV) f x = Structure.funMap (L := LRV) f Fin.elim0 := by
  congr 1
  funext i; exact i.elim0

omit hM in
private theorem unary (f : Fn 1) (x : Fin 1 → M) :
    Structure.funMap (L := LRV) f x = Structure.funMap (L := LRV) f ![x 0] := by
  congr 1
  funext i; fin_cases i; rfl

omit hM in
private theorem binary (f : Fn 2) (x : Fin 2 → M) :
    Structure.funMap (L := LRV) f x = Structure.funMap (L := LRV) f ![x 0, x 1] := by
  congr 1
  funext i; fin_cases i <;> rfl

include hv in
theorem liftFn_correct {k : ℕ} (f : Fn k) (x : Fin k → VFType (M := M)) :
    decode (Fn.resSort f) (liftFn v f x) =
      Structure.funMap (L := LRV) f (fun i => decode (Fn.argSort f i) (x i)) := by
  cases f with
  | vfZero => rw [nullary]; rfl
  | vfOne => rw [nullary]; rfl
  | vfAdd => rw [binary]; rfl
  | vfMul => rw [binary]; rfl
  | vfNeg => rw [unary]; rfl
  | rvZero => rw [nullary]; exact RVCalc.rv_zero_eq hM
  | rvOne => rw [nullary]; exact RVCalc.rv_one hM
  | rvMul =>
    rw [binary]
    exact congrArg Subtype.val (ValuedModelMap.encodedRv_mul (x 0) (x 1))
  | rvInv => rw [unary]; exact inv_correct (x 0)
  | kAdd => rw [binary]; exact congrArg Subtype.val (add_correct v hv (x 0) (x 1))
  | kNeg => rw [unary]; exact congrArg Subtype.val (neg_correct v hv (x 0))
  | rvMap => rw [unary]; rfl

noncomputable def liftTerm {α : Type} (w : α → VFType (M := M)) :
    LRV.Term α → VFType (M := M)
  | .var i => w i
  | .func f ts => liftFn v f (fun i => liftTerm w (ts i))

include hv in
theorem liftTerm_correct {α : Type} {n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag)
    (w : α ⊕ Fin n → VFType (M := M)) (t : LRV.Term (α ⊕ Fin n))
    (σ : SortTag) (ht : TmSort sα sn t = some σ) :
    decode σ (liftTerm v w t) =
      t.realize (fun i => decode (Sum.elim sα sn i) (w i)) := by
  induction t generalizing σ with
  | var i =>
    cases i with
    | inl i => cases ht; rfl
    | inr i => cases ht; rfl
  | func f ts ih =>
    obtain ⟨harg, hres⟩ := (tmSort_func_iff sα sn f ts).mp ht
    subst σ
    change decode (Fn.resSort f) (liftFn v f _) = _
    calc
      _ = Structure.funMap (L := LRV) f
          (fun i => decode (Fn.argSort f i) (liftTerm v w (ts i))) :=
        liftFn_correct v hv f _
      _ = _ := by
        change Structure.funMap (L := LRV) f _ = Structure.funMap (L := LRV) f _
        congr 1
        funext i
        exact ih i _ (harg i)

end SpecialTransformations.Section3.RVRepresentatives
