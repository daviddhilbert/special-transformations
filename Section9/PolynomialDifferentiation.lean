import Section9.DerivativeCoordinates
import Section9.ValuedPolynomialTaylor
import Section9.VFJacobian

/-! The VF derivative of an evaluated polynomial system. This is the
analytic bridge needed when differentiating the equations satisfied by
the chosen Section 7 lift. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section8

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}
variable {R : Type*} [CommRing R] [Algebra R (VFType (M := M))]

local notation "VF" => VFType (M := M)
local notation "Γ" => Values.Gamma (M := M)
local notation "v" => Values.vfValueHom (M := M)

/-- The polynomial derivative is the matrix of evaluated formal partial
derivatives, over the actual VF and with arbitrary valuation rank. -/
theorem hasVFDerivativeAt_aeval
    (P : Fin m → MvPolynomial (Fin n) R) (a : Fin n → VF) :
    HasVFDerivativeAt (fun x i => aeval x (P i)) a
      (Matrix.toLin' (Matrix.of fun i j => aeval a (pderiv j (P i)))) := by
  apply hasVFDerivativeAt_of_components
  intro i ε
  let G := MonoidWithZeroHom.ValueGroup₀ (.ofClass (Values.presentationValuation (M := M)))
  let w : Valuation VF G := Values.presentationValuation.restrict
  let φ : Values.GammaTop (M := M) ≃ OrderDual G := Values.paperValueEquiv
  let ψ (z : Values.GammaTop (M := M)) : G := OrderDual.ofDual (φ z)
  have hψ (z : VF) : ψ (v z) = w z :=
    Values.valueEquiv_apply_vf Values.presentationValuation Values.presentation_compatible z
  have hψ0 : ψ 0 = 0 := Values.paperValue_zero
  have hψmul (a b : Values.GammaTop (M := M)) : ψ (a * b) = ψ a * ψ b :=
    Values.paperValue_mul a b
  let E := ψ ε.val
  have hE : 0 < E :=
    pos_iff_ne_zero.mpr (fun h => finiteValue_ne_zero ε (φ.injective (h.trans hψ0.symm)))
  obtain ⟨B, C, hB, hC, hTaylor⟩ := exists_value_polynomialTaylor_bounds w (P i) a
  have hC₀ : 0 < C := zero_lt_one.trans_le hC
  let T : G := min 1 (E / C)
  have hT : 0 < T := lt_min zero_lt_one (div_pos hE hC₀)
  have hpre : ψ (φ.symm (OrderDual.toDual T)) = T := φ.apply_symm_apply _
  let δ : Γ := ⟨φ.symm (OrderDual.toDual T), fun h => hT.ne (by
    rw [← hψ0]
    exact (congrArg ψ (Values.infinity_eq_zero.symm.trans h.symm)).trans hpre)⟩
  refine ⟨δ, fun h hn hclose => ?_⟩
  let r : G := ψ (vfTupleValue h)
  have hlt : r < T := (show r < ψ δ.val from hclose).trans_eq hpre
  have hpos : 0 < r := pos_iff_ne_zero.mpr (fun hz =>
    vfTupleValue_ne_zero hn (φ.injective (hz.trans hψ0.symm)))
  have hcoord (j : Fin n) : w (h j) ≤ r := by
    rw [← hψ]
    exact vfTupleValue_le_component h j
  have hbound := (hTaylor r (hlt.trans_le (min_le_left _ _)).le h hcoord).2
  have hs : C * r < E := (mul_comm C r) ▸
    (lt_div_iff₀ hC₀).mp (hlt.trans_le (min_le_right _ _))
  change ψ (v (polynomialRemainder (P i) a h)) < ψ (ε.val * vfTupleValue h)
  rw [hψmul, hψ]
  exact hbound.trans_lt (by
    change C * r ^ 2 < E * r
    rw [pow_two, ← mul_assoc]
    exact mul_lt_mul_of_pos_right hs hpos)

end SpecialTransformations.Section9
