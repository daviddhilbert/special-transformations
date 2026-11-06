import Section4.ResidueScaledPredicates
import Section3.Parameters

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

def residueInputs (s : Fin n → CanonicalRV.RVSort M) (x : Fin n → ModelResidue M) : Fin n → M :=
  fun i => (s i * residueRV (x i)).val

def residueEval (p : Parameters S) (s : Fin n → CanonicalRV.RVSort M)
    (t : LRV.Term (Fin p.length ⊕ Fin n)) (x : Fin n → ModelResidue M) : M :=
  t.realize (Sum.elim p.values (residueInputs s x))

def TermRepresentation (p : Parameters S) (s : Fin n → CanonicalRV.RVSort M)
    (t : LRV.Term (Fin p.length ⊕ Fin n)) : SortTag → Prop
  | .vf => ∃ a : VFType (M := M), ∀ x, residueEval p s t x = a.val
  | .rv => ∃ f : (Fin n → ModelResidue M) → CanonicalRV.RVSort M,
      Scaled f ∧ ∀ x, residueEval p s t x = (f x).val

private theorem eval_nullary {β : Type} (f : Fn 0) (ts : Fin 0 → LRV.Term β) (v : β → M) :
    (Term.func f ts).realize v = Structure.funMap (L := LRV) f Fin.elim0 := by
  change Structure.funMap (L := LRV) f _ = _
  congr 1
  funext i
  exact i.elim0

private theorem eval_unary {β : Type} (f : Fn 1) (ts : Fin 1 → LRV.Term β) (v : β → M) :
    (Term.func f ts).realize v = Structure.funMap (L := LRV) f ![(ts 0).realize v] := by
  change Structure.funMap (L := LRV) f _ = _
  congr 1
  funext i
  fin_cases i
  rfl

private theorem eval_binary {β : Type} (f : Fn 2) (ts : Fin 2 → LRV.Term β) (v : β → M) :
    (Term.func f ts).realize v = Structure.funMap (L := LRV) f ![(ts 0).realize v, (ts 1).realize v] := by
  change Structure.funMap (L := LRV) f _ = _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- On a fixed value fibre, VF terms are constant and RV terms have one
fixed RV coefficient multiplying a pure residue-field definable function.
This is a syntactic consequence of the released language, with all its
named RV inversion and total residue-operation branches retained. -/
theorem term_representation (p : Parameters S) (s : Fin n → CanonicalRV.RVSort M)
    (t : LRV.Term (Fin p.length ⊕ Fin n)) :
    ∀ σ, TmSort p.sorts (fun _ => .rv) t = some σ → TermRepresentation p s t σ := by
  induction t with
  | var z =>
    intro σ ht
    cases z with
    | inl i =>
      have hi : p.sorts i = σ := Option.some.inj ht
      have hs := p.sorted i
      rw [hi] at hs
      cases σ with
      | vf => exact ⟨⟨p.values i, hs⟩, fun _ => rfl⟩
      | rv => exact ⟨fun _ => ⟨p.values i, hs⟩, scaled_const _, fun _ => rfl⟩
    | inr i =>
      have hi : SortTag.rv = σ := Option.some.inj ht
      cases hi
      exact ⟨fun x => s i * residueRV (x i), scaled_coordinate _ _, fun _ => rfl⟩
  | func f ts ih =>
    intro σ ht
    obtain ⟨harg, hres⟩ := (tmSort_func_iff p.sorts (fun _ => .rv) f ts).mp ht
    cases f with
    | vfZero =>
      cases hres
      exact ⟨0, fun x => by unfold residueEval; rw [eval_nullary]; rfl⟩
    | vfOne =>
      cases hres
      exact ⟨1, fun x => by unfold residueEval; rw [eval_nullary]; rfl⟩
    | vfAdd =>
      cases hres
      obtain ⟨a, ha⟩ := ih 0 .vf (harg 0)
      obtain ⟨b, hb⟩ := ih 1 .vf (harg 1)
      refine ⟨a + b, fun x => ?_⟩
      change (Term.func Fn.vfAdd ts).realize _ = _
      rw [eval_binary, ← residueEval, ← residueEval, ha, hb]
      rfl
    | vfMul =>
      cases hres
      obtain ⟨a, ha⟩ := ih 0 .vf (harg 0)
      obtain ⟨b, hb⟩ := ih 1 .vf (harg 1)
      refine ⟨a * b, fun x => ?_⟩
      change (Term.func Fn.vfMul ts).realize _ = _
      rw [eval_binary, ← residueEval, ← residueEval, ha, hb]
      rfl
    | vfNeg =>
      cases hres
      obtain ⟨a, ha⟩ := ih 0 .vf (harg 0)
      refine ⟨-a, fun x => ?_⟩
      change (Term.func Fn.vfNeg ts).realize _ = _
      rw [eval_unary, ← residueEval, ha]
      rfl
    | rvZero =>
      cases hres
      refine ⟨fun _ => 0, scaled_const 0, fun x => ?_⟩
      unfold residueEval
      rw [eval_nullary, RVOperations.zero_val]
      rfl
    | rvOne =>
      cases hres
      refine ⟨fun _ => 1, scaled_const 1, fun x => ?_⟩
      unfold residueEval
      rw [eval_nullary, RVOperations.one_val]
      rfl
    | rvMul =>
      cases hres
      obtain ⟨a, ha, hea⟩ := ih 0 .rv (harg 0)
      obtain ⟨b, hb, heb⟩ := ih 1 .rv (harg 1)
      refine ⟨fun x => a x * b x, ha.mul hb, fun x => ?_⟩
      change (Term.func Fn.rvMul ts).realize _ = _
      rw [eval_binary, ← residueEval, ← residueEval, hea, heb, RVOperations.mul_val]
      rfl
    | rvInv =>
      cases hres
      obtain ⟨a, ha, hea⟩ := ih 0 .rv (harg 0)
      refine ⟨fun x => (a x)⁻¹, ha.inv, fun x => ?_⟩
      change (Term.func Fn.rvInv ts).realize _ = _
      rw [eval_unary, ← residueEval, hea, RVOperations.inv_val]
      rfl
    | kAdd =>
      cases hres
      obtain ⟨a, ha, hea⟩ := ih 0 .rv (harg 0)
      obtain ⟨b, hb, heb⟩ := ih 1 .rv (harg 1)
      refine ⟨fun x => ValuedModelMap.addK (a x) (b x), ha.addK hb, fun x => ?_⟩
      change (Term.func Fn.kAdd ts).realize _ = _
      rw [eval_binary, ← residueEval, ← residueEval, hea, heb]
      rfl
    | kNeg =>
      cases hres
      obtain ⟨a, ha, hea⟩ := ih 0 .rv (harg 0)
      refine ⟨fun x => ValuedModelMap.negK (a x), ha.negK, fun x => ?_⟩
      change (Term.func Fn.kNeg ts).realize _ = _
      rw [eval_unary, ← residueEval, hea]
      rfl
    | rvMap =>
      cases hres
      obtain ⟨a, ha⟩ := ih 0 .vf (harg 0)
      refine ⟨fun _ => CanonicalRV.encodedRv a, scaled_const _, fun x => ?_⟩
      change (Term.func Fn.rvMap ts).realize _ = _
      rw [eval_unary, ← residueEval, ha]
      rfl

end SpecialTransformations.Section4.ResiduePurity

end
