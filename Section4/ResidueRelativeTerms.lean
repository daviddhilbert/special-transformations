module

public import Section4.ResidueRelativePredicates
public import Section4.ResidueTermInterpretation
public import SubstructureField

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity.Scoped

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

structure TermContext (p : Parameters S) (s : Fin n → CanonicalRV.RVSort M) where
  vfBase : LRV.Substructure M
  coefficients : CoefficientContext M
  vf_parameters : ∀ i (hi : iVF (p.values i)), p.values i ∈ vfBase
  rv_parameters : ∀ i (hi : iRV (p.values i)),
    (⟨p.values i, hi⟩ : CanonicalRV.RVSort M) ∈ coefficients.coefficients
  rv_of_vf : ∀ a : VFType (M := M), a.val ∈ vfBase →
    CanonicalRV.encodedRv a ∈ coefficients.coefficients
  scales : ∀ i, s i ∈ coefficients.coefficients

def Representation {p : Parameters S} {s : Fin n → CanonicalRV.RVSort M}
    (Q : TermContext p s) (t : LRV.Term (Fin p.length ⊕ Fin n)) : SortTag → Prop
  | .vf => ∃ a : VFType (M := M), a.val ∈ Q.vfBase ∧ ∀ x, residueEval p s t x = a.val
  | .rv => ∃ f : (Fin n → ModelResidue M) → CanonicalRV.RVSort M,
      ScaledOver Q.coefficients f ∧ ∀ x, residueEval p s t x = (f x).val

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

theorem term_representation {p : Parameters S} {s : Fin n → CanonicalRV.RVSort M}
    (Q : TermContext p s) (t : LRV.Term (Fin p.length ⊕ Fin n)) :
    ∀ σ, TmSort p.sorts (fun _ => .rv) t = some σ → Representation Q t σ := by
  induction t with
  | var z =>
    intro σ ht
    cases z with
    | inl i =>
      have hi : p.sorts i = σ := Option.some.inj ht
      have hs := p.sorted i
      rw [hi] at hs
      cases σ with
      | vf => exact ⟨⟨p.values i, hs⟩, Q.vf_parameters i hs, fun _ => rfl⟩
      | rv => exact ⟨fun _ => ⟨p.values i, hs⟩,
          scaledOver_const _ (Q.rv_parameters i hs), fun _ => rfl⟩
    | inr i =>
      have hi : SortTag.rv = σ := Option.some.inj ht
      cases hi
      exact ⟨fun x => s i * residueRV (x i), scaledOver_coordinate _ (Q.scales i) _, fun _ => rfl⟩
  | func f ts ih =>
    intro σ ht
    obtain ⟨harg, hres⟩ := (tmSort_func_iff p.sorts (fun _ => .rv) f ts).mp ht
    cases f with
    | vfZero =>
      cases hres
      exact ⟨0, (SubstructureField.vfRing Q.vfBase).zero_mem,
        fun x => by unfold residueEval; rw [eval_nullary]; rfl⟩
    | vfOne =>
      cases hres
      exact ⟨1, (SubstructureField.vfRing Q.vfBase).one_mem,
        fun x => by unfold residueEval; rw [eval_nullary]; rfl⟩
    | vfAdd =>
      cases hres
      obtain ⟨a, haB, ha⟩ := ih 0 .vf (harg 0)
      obtain ⟨b, hbB, hb⟩ := ih 1 .vf (harg 1)
      refine ⟨a + b, (SubstructureField.vfRing Q.vfBase).add_mem haB hbB, fun x => ?_⟩
      change (Term.func Fn.vfAdd ts).realize _ = _
      rw [eval_binary, ← residueEval, ← residueEval, ha, hb]
      rfl
    | vfMul =>
      cases hres
      obtain ⟨a, haB, ha⟩ := ih 0 .vf (harg 0)
      obtain ⟨b, hbB, hb⟩ := ih 1 .vf (harg 1)
      refine ⟨a * b, (SubstructureField.vfRing Q.vfBase).mul_mem haB hbB, fun x => ?_⟩
      change (Term.func Fn.vfMul ts).realize _ = _
      rw [eval_binary, ← residueEval, ← residueEval, ha, hb]
      rfl
    | vfNeg =>
      cases hres
      obtain ⟨a, haB, ha⟩ := ih 0 .vf (harg 0)
      refine ⟨-a, (SubstructureField.vfRing Q.vfBase).neg_mem haB, fun x => ?_⟩
      change (Term.func Fn.vfNeg ts).realize _ = _
      rw [eval_unary, ← residueEval, ha]
      rfl
    | rvZero =>
      cases hres
      refine ⟨fun _ => 0, scaledOver_const 0 Q.coefficients.zero_mem, fun x => ?_⟩
      unfold residueEval
      rw [eval_nullary, RVOperations.zero_val]
      rfl
    | rvOne =>
      cases hres
      refine ⟨fun _ => 1, scaledOver_const 1 Q.coefficients.one_mem, fun x => ?_⟩
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
      obtain ⟨a, haB, ha⟩ := ih 0 .vf (harg 0)
      refine ⟨fun _ => CanonicalRV.encodedRv a,
        scaledOver_const _ (Q.rv_of_vf a haB), fun x => ?_⟩
      change (Term.func Fn.rvMap ts).realize _ = _
      rw [eval_unary, ← residueEval, ha]
      rfl

end SpecialTransformations.Section4.ResiduePurity.Scoped

end
