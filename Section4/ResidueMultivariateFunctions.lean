module

public import Section4.ResidueFieldFunctions
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

open Classical FirstOrder FirstOrder.Language

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {K : Type} [Field K]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem mvPolynomial_eval_definableFun {ι : Type} (E : Subfield K)
    (p : MvPolynomial ι E) : Relative.Fun E (fun x : ι → K => p.eval₂ E.subtype x) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval₂_C, Subfield.subtype_apply] using
      Relative.constant (ι := ι) c.val c.property
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using hp.add hq
  | mul_X p i hp =>
    simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using
      hp.mul (Relative.projection (E := E) i)

theorem mvPolynomial_zeroSet_definable {ι : Type} (E : Subfield K)
    (p : MvPolynomial ι E) : Relative.Def E {x : ι → K | p.eval₂ E.subtype x = 0} :=
  (mvPolynomial_eval_definableFun E p).eq_const 0 E.zero_mem

end SpecialTransformations.Section4.ResiduePurity

end
