module

public import Section3.RingSyntax
public import Section3.DefinableConstants

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Barycentre
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

noncomputable def linearPolynomial (k : ℕ) : FreeCommRing (Fin 1 ⊕ Fin k) :=
  (k : FreeCommRing (Fin 1 ⊕ Fin k)) * FreeCommRing.of (Sum.inl 0) -
    ∑ i : Fin k, FreeCommRing.of (Sum.inr i)

noncomputable def linearTerm (k : ℕ) : LRV.Term (Fin 1 ⊕ Fin k) :=
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing (linearPolynomial k))

theorem linearTerm_sorted (k : ℕ) :
    TmSort (fun _ => .vf) (fun _ => .vf) (linearTerm k) = some .vf := RingSyntax.sorted _

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem linearTerm_realize (k : ℕ) (z : VFType (M := M)) (c : Fin k → VFType (M := M)) :
    (linearTerm k).realize (Sum.elim (fun _ => z.val) (fun i => (c i).val)) =
      ((k : VFType (M := M)) * z - ∑ i, c i).val := by
  have he : (fun a => ((Sum.elim (fun _ : Fin 1 => z) c) a).val) =
      Sum.elim (fun _ => z.val) (fun i => (c i).val) := by
    funext a
    cases a <;> rfl
  rw [← he]
  unfold linearTerm
  rw [RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
  simp only [linearPolynomial, map_sub, map_mul, map_natCast, map_sum,
    FreeCommRing.lift_of, Sum.elim_inl, Sum.elim_inr]

omit hM in
theorem linearTerm_zero_definable (S : Set M) (k : ℕ) :
    S.Definable LRV {w : Fin 1 ⊕ Fin k → M | (linearTerm k).realize w = iVFZero} := by
  have hz : (∅ : Set M).DefinableFun LRV (fun w : Fin 1 ⊕ Fin k → M => iVFZero) :=
    DefinableConstants.constant
      (DefinableConstants.function_symbol (L := LRV) Fn.vfZero Fin.elim0
        (fun i => i.elim0))
  exact ((linearTerm k).definableFun_realize.ofPred_eq hz).mono (Set.empty_subset S)

end SpecialTransformations.Section3.Barycentre
