import Section3.RingSyntax
import Section3.Parameters
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.PolynomialRoots
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

noncomputable def generic (k : ℕ) : FreeCommRing (Fin k ⊕ Fin 1) :=
  ∑ i : Fin k, FreeCommRing.of (Sum.inl i) * FreeCommRing.of (Sum.inr 0) ^ i.val

noncomputable def term (k : ℕ) : LRV.Term (Fin k ⊕ Fin 1) :=
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing (generic k))

theorem term_sorted (k : ℕ) : TmSort (fun _ => .vf) (fun _ => .vf) (term k) = some .vf :=
  RingSyntax.sorted _

theorem term_realize (k : ℕ) (c : Fin k → VFType (M := M)) (x : VFType (M := M)) :
    (term k).realize (Sum.elim (fun i => (c i).val) ![x.val]) =
      ((∑ i : Fin k, c i * x ^ i.val) : VFType (M := M)).val := by
  have he : (fun a => ((Sum.elim c ![x]) a).val) =
      Sum.elim (fun i => (c i).val) ![x.val] := by
    funext a
    cases a with
    | inl i => rfl
    | inr i => fin_cases i; rfl
  rw [← he]
  unfold term
  rw [RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
  simp only [generic, map_sum, map_mul, map_pow, FreeCommRing.lift_of,
    Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero]

theorem eval₂_eq_sum (E : Subfield (VFType (M := M))) (p : Polynomial E) (x : VFType (M := M)) :
    p.eval₂ E.subtype x = ∑ i : Fin (p.natDegree + 1), (p.coeff i.val).val * x ^ i.val := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact (Fin.sum_univ_eq_sum_range
    (fun i : ℕ => E.subtype (p.coeff i) * x ^ i) (p.natDegree + 1)).symm

end SpecialTransformations.Section3.PolynomialRoots