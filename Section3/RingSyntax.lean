module

public import VFValued
public import Mathlib.ModelTheory.Algebra.Ring.FreeCommRing

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.RingSyntax

def vfFn : {n : ℕ} → FirstOrder.ringFunc n → Fn n
  | _, .zero => .vfZero
  | _, .one => .vfOne
  | _, .add => .vfAdd
  | _, .mul => .vfMul
  | _, .neg => .vfNeg

def ofRingTerm {α : Type} : Language.ring.Term α → LRV.Term α
  | .var a => .var a
  | .func f ts => .func (vfFn f) (fun i => ofRingTerm (ts i))

theorem sorted {α : Type} {n : ℕ} (t : Language.ring.Term (α ⊕ Fin n)) :
    TmSort (fun _ => .vf) (fun _ => .vf) (ofRingTerm t) = some .vf := by
  induction t with
  | var a => cases a <;> rfl
  | func f ts ih =>
    cases f <;> apply tmSort_func <;> intro i <;> first | exact ih i | exact i.elim0

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem realizes {α : Type} (t : Language.ring.Term α) (v : α → VFType (M := M)) :
    (ofRingTerm t).realize (fun a => (v a).val) = (t.realize v).val := by
  induction t with
  | var a => rfl
  | func f ts ih =>
    change Structure.funMap (L := LRV) (vfFn f)
      (fun i => (ofRingTerm (ts i)).realize (fun a => (v a).val)) = _
    rw [funext ih]
    cases f <;> congr 1 <;> funext i <;> fin_cases i <;> rfl

end SpecialTransformations.Section3.RingSyntax