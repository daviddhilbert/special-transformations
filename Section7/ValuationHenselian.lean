import RVHenselLifting
import Mathlib.RingTheory.Henselian

/-!
# The ordinary henselian local ring of an algebraically closed valued field

The released ACVF-QE theorem `RVCalc.exists_root_of_eval_lt_one` supplies
monic root lifting in the field. This file proves the bridge to Mathlib's
actual `HenselianLocalRing` on the valuation ring. The derivative-unit
condition is not needed for this existence argument over an algebraically
closed field. No generalized-Hensel or Section 7 lifting conclusion is an
input.
-/

open Polynomial IsLocalRing

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [IsAlgClosed K] [LinearOrderedCommGroupWithZero Γ]

theorem valuationRing_henselian (v : Valuation K Γ) : HenselianLocalRing v.valuationSubring := by
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a₀ hfa _
  let ι : v.valuationSubring →+* K := v.valuationSubring.subtype
  let p : K[X] := f.map ι
  have heval (a : v.valuationSubring) : p.eval (a : K) = ι (f.eval a) := by
    exact Polynomial.eval_map_apply ι (p := f) a
  have hsmall : v (p.eval (a₀ : K)) < 1 := by
    rw [heval]
    exact (Valuation.mem_maximalIdeal_iff K v).mp hfa
  obtain ⟨b, hb, hclose⟩ := RVCalc.exists_root_of_eval_lt_one v (hf.map ι) hsmall
  have hclose' : v (b - (a₀ : K)) < 1 := by
    rw [show b - (a₀ : K) = -((a₀ : K) - b) by ring, Valuation.map_neg v]
    exact hclose
  have hbval : v b ≤ 1 := by
    have he : b = (b - (a₀ : K)) + (a₀ : K) := by ring
    rw [he]
    exact (v.map_add _ _).trans
      (max_le hclose'.le ((Valuation.mem_valuationSubring_iff v _).mp a₀.property))
  let b₀ : v.valuationSubring :=
    ⟨b, (Valuation.mem_valuationSubring_iff v b).mpr hbval⟩
  refine ⟨b₀, ?_, ?_⟩
  · change f.eval b₀ = 0
    apply (show Function.Injective ι from Subtype.val_injective)
    change ι (f.eval b₀) = 0
    rw [← heval]
    exact hb
  · apply (Valuation.mem_maximalIdeal_iff K v).mpr
    exact hclose'

end SpecialTransformations.Section7
