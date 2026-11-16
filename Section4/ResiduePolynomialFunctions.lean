module

public import Section4.ResidueFieldFunctions
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

open Classical FirstOrder FirstOrder.Language

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {K : Type} [Field K]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem Relative.Fun.pow {ι : Type} {E : Subfield K} {f : (ι → K) → K}
    (hf : Relative.Fun E f) (n : ℕ) : Relative.Fun E (fun x => (f x) ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using Relative.constant (ι := ι) 1 E.one_mem
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem polynomial_eval_definableFun (E : Subfield K) (p : Polynomial E) :
    Relative.Fun E (fun x : Fin 1 → K => p.eval₂ E.subtype (x 0)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval₂_add] using hp.add hq
  | monomial n c =>
    simpa only [Polynomial.eval₂_monomial, Subfield.subtype_apply] using
      (Relative.constant (ι := Fin 1) c.val c.property).mul
        ((Relative.projection (E := E) (0 : Fin 1)).pow n)

theorem polynomial_roots_definable (E : Subfield K) (p : Polynomial E) :
    (E : Set K).Definable₁ Language.ring {x : K | p.eval₂ E.subtype x = 0} :=
  (polynomial_eval_definableFun E p).eq_const 0 E.zero_mem

theorem polynomial_roots_finite (E : Subfield K) (p : Polynomial E) (hp : p ≠ 0) :
    {x : K | p.eval₂ E.subtype x = 0}.Finite := by
  have hmap : p.map E.subtype ≠ 0 := by
    intro he
    apply hp
    exact (Polynomial.map_injective E.subtype E.subtype.injective)
      (by simpa only [Polynomial.map_zero] using he)
  convert Polynomial.finite_setOfPred_isRoot hmap using 1
  ext x
  change p.eval₂ E.subtype x = 0 ↔ (p.map E.subtype).eval x = 0
  rw [Polynomial.eval_map]

end SpecialTransformations.Section4.ResiduePurity

end
