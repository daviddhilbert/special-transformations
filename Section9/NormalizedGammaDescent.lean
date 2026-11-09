import Section9.CoarsenedGaussTuple
import Section9.GammaJacobianBounds
import Section9.GraphJacobianIdentification
import Section9.HenselizedGraphData

/-! Intrinsic Gamma descent on the normalized polydiscs. The input
about henselization concerns algebraic graph fields for the coarsening.
All derivative and model-theoretic steps are separate from that input. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ] {n r s : ℕ}
local notation "VF" => VFType (M := M)
local notation "V" => Fin n → VF

theorem normalizedGammaDescent_of_henselized_graphs [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hE : Cardinal.mk (vfParameterField S) < κ) [IsAlgClosed (vfParameterField S)]
    (v : Valuation VF Γ) (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    (hne : (coefficientThresholds v (vfParameterField S)).Nonempty)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} (f : Map A B) (g : Map B A)
    (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f)
    (hA : ∀ x : V, (∃ p : A, p.val.1 = x) ↔ ∀ i, v (x i) < 1)
    (hB : ∀ x : V, (∃ p : B, p.val.1 = x) ↔ ∀ i, v (x i) < 1)
    (c : vfParameterField S) (hc₀ : c ≠ 0)
    (hconst : ∀ p : A, AlgebraicIndependent (vfParameterField S) p.val.1 →
      ∃ J : VF, HasMixedVFJacobianAt f p J ∧ v J = v (c : VF))
    (hgraph : let E := vfParameterField S
      let w := (thresholdCoarsening v (coefficientThresholds v E) hne
        (coefficientThresholds_lt_one v E) (coefficientThresholds_halve v E)).valuation
      ∀ x y : V, (∀ i, w (x i) = 1) → IsGaussEvaluation (E := E) w x →
        (∀ i, IsAlgebraic (IntermediateField.adjoin E (Set.range x)) (y i)) →
        Nonempty (HenselizedGraphData w E x y)) :
    v (c : VF) = 1 := by
  let E := vfParameterField S
  let T := coefficientThresholds v E
  let ht := coefficientThresholds_lt_one v E
  let hh := coefficientThresholds_halve v E
  let w := (thresholdCoarsening v T hne ht hh).valuation
  letI : Valued VF Γ := Valued.mk' v
  have hwmono := thresholdCoarsening_le_of_fine_le v T hne ht hh
  obtain ⟨x, hx, hGauss, hInd⟩ := exists_coarsened_gauss_tuple hκ hs v hv E hE hne n
  obtain ⟨p, hp⟩ := (hA x).mpr (fun i => (hx i).2.1)
  obtain ⟨q, hq⟩ := (hB x).mpr (fun i => (hx i).2.1)
  have boundAt {a b : ℕ} {U : DefSet (rawMixedSpace (M := M) n a) S}
      {W : DefSet (rawMixedSpace (M := M) n b) S} (F : Map U W) (u : U)
      (hu : u.val.1 = x) (hInt : ∀ i, w ((F u).val.1 i) ≤ 1) :
      ∃ L : V →ₗ[VF] V, HasMixedVFDerivativeAt F u L ∧ ∀ i j, w (LinearMap.toMatrix' L i j) ≤ 1 := by
    have hAlg (i : Fin n) : IsAlgebraic (IntermediateField.adjoin E (Set.range x)) ((F u).val.1 i) := by
      have h := map_output_vf_coordinate_isAlgebraic hc F u i
      rw [tupleField_eq_adjoin, hu] at h
      exact h
    obtain ⟨data⟩ := hgraph x (F u).val.1 (fun i => (hx i).2.2) hGauss hAlg
    obtain ⟨L, fL, aL, φ, X, Y, D, hX, hY, hD, hbound⟩ :=
      exists_bounded_graph_derivations_of_henselization w E x (F u).val.1 (fun i => (hx i).2.2.le) hGauss data
    letI := fL
    letI := aL
    let J : Matrix (Fin n) (Fin n) VF := Matrix.of fun i j => φ (D j (Y i))
    have hder := hasMixedVFDerivativeAt_of_graph_derivations hc hκ.le hs hsmall hv F u
      (hu.symm ▸ hInd) φ X Y (fun i => (hX i).trans (congrFun hu i).symm) hY D hD
    refine ⟨Matrix.toLin' J, hder, fun i j => ?_⟩
    rw [LinearMap.toMatrix'_toLin']
    exact (hbound j (Y i)).trans (by rw [hY i]; exact hInt i)
  have hwInt (z : VF) (hz : v z < 1) : w z ≤ 1 := by
    rw [← map_one w]
    exact hwmono z 1 (by rw [map_one]; exact hz.le)
  obtain ⟨L, hL, hLbound⟩ := boundAt f p hp (fun i => hwInt _ ((hB (f p).val.1).mp ⟨f p, rfl⟩ i))
  obtain ⟨D, hD, hDbound⟩ := boundAt g q hq (fun i => hwInt _ ((hA (g q).val.1).mp ⟨g q, rfl⟩ i))
  have hgp : AlgebraicIndependent E (g q).val.1 := independent_map_of_finiteFibres hc g
    (Map.finiteFibres_of_injective hfg.injective) q (hq.symm ▸ hInd)
  obtain ⟨L', hL'⟩ := mixedDifferentiableAt_of_independent hc hκ.le hs hsmall hv f (g q) hgp
  have hvalue (u : A) (hu : AlgebraicIndependent E u.val.1) (P : V →ₗ[VF] V)
      (hP : HasMixedVFDerivativeAt f u P) : v (LinearMap.toMatrix' P).det = v (c : VF) := by
    obtain ⟨J, hJ, hvc⟩ := hconst u hu
    obtain ⟨F, hF, hP'⟩ := hP
    exact (congrArg v ((show HasMixedVFJacobianAt f u _ from ⟨F, hF, hP'.hasJacobianAt⟩).unique hJ)).trans hvc
  have hcK : (c : VF) ≠ 0 := fun h => hc₀ (Subtype.ext h)
  have hvc : v (c : VF) ≠ 0 := v.ne_zero_iff.mpr hcK
  have ht₁ (h : 1 < v (c : VF)) : (v (c : VF))⁻¹ ∈ T := by
    refine ⟨(inv_lt_one₀ (zero_lt_one.trans h)).mpr h, c⁻¹, inv_ne_zero hc₀, ?_⟩
    exact map_inv₀ v (c : VF)
  have ht₂ (h : v (c : VF) < 1) : v (c : VF) ∈ T := ⟨h, c, hc₀, rfl⟩
  exact mixed_constantJacobian_value_one_of_coarsened_bounds f g hgf hfg v T hne ht hh
    _ hvc ht₁ ht₂ q (LinearMap.toMatrix' L) D hD (hvalue p (hp.symm ▸ hInd) L hL)
    L' hL' (hvalue (g q) hgp L' hL') hLbound hDbound

end SpecialTransformations.Section9
