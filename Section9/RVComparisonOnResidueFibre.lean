import Section9.NormalizedRVComparison
import Section9.RVGraphJacobianComparison
import Section9.AffineMixedDerivative
import Section9.NormalizedVFRepresentatives
import Section9.ResidueFiniteProjection
import Section9.ResidueJacobianExistence

/-! Pointwise comparison for an arbitrary definable lift, in the
original VF coordinates. The residue chart and genericity conditions
are imposed on its fixed value fibre. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open FirstOrder FirstOrder.Language IsLocalRing MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ}
local notation "VF" => VFType (M := M)
local notation "RV" => CanonicalRV.RVSort M
local notation "k" => ModelResidue M
local notation "v" => Values.presentationValuation (M := M)
local notation "O" => Valuation.valuationSubring (Values.presentationValuation (M := M))
local notation "V" => Fin n → VF
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem rvComparison_on_independent_residue_fibre [CharZero VF] [CharZero k]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    [IsAlgClosed (vfParameterField S)]
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (hf : Function.Bijective f) (p : A) (a b : V) (x y : Fin n → O)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hNameA : ∀ i, ((a i)⁻¹).val ∈ S) (hNameB : ∀ i, ((b i)⁻¹).val ∈ S) (h0 : (0 : VF).val ∈ S)
    (hx : ∀ i, a i * (x i : VF) = p.val.1 i) (hy : ∀ i, b i * (y i : VF) = (f p).val.1 i)
    (hxUnit : ∀ i, v (x i : VF) = 1) (hx₀ : ∀ i, residue O (x i) ≠ 0) (hy₀ : ∀ i, residue O (y i) ≠ 0)
    (hi : Function.Injective (eval₂Hom (residueFieldInclusion v (vfParameterField S)) (residue O ∘ x)))
    (C : Set (Fin (n+n) → RV))
    (hC : Relative.Def (residueCoefficientField (vfParameterField S))
      (normalizedCorrespondence C (tupleRV a) (tupleRV b)))
    (hp : productTuple (residue O ∘ x) (residue O ∘ y) ∈ normalizedCorrespondence C (tupleRV a) (tupleRV b))
    (hvertical : ∀ z, IsPolynomialTangent (normalizedCorrespondence C (tupleRV a) (tupleRV b))
      (productTuple (residue O ∘ x) (residue O ∘ y)) (productTuple 0 z) → z = 0)
    (hhorizontal : ∀ z, IsPolynomialTangent (normalizedCorrespondence C (tupleRV a) (tupleRV b))
      (productTuple (residue O ∘ x) (residue O ∘ y)) (productTuple z 0) → z = 0)
    (hgraph : HenselizedGaussGraphInput VF) :
    ∃ L, HasMixedVFDerivativeAt f p L ∧
      IsRVJacobianAt C (tupleRV p.val.1) (tupleRV (f p).val.1)
        (CanonicalRV.encodedRv (LinearMap.toMatrix' L).det) := by
  let u := affineMixedImage A (fun i => (a i)⁻¹) 0 hNameA (fun _ => h0)
  let w := affineMixedImage B (fun i => (b i)⁻¹) 0 hNameB (fun _ => h0)
  have hu := affineMixedImage_bijective A _ 0 hNameA (fun _ => h0) (fun i => inv_ne_zero (ha i))
  let u' := u.inverse hu
  let F := w.comp (f.comp u')
  have hu' : Function.Bijective u' := (Equiv.ofBijective u hu).symm.bijective
  have hpu : u' (u p) = p := Map.inverse_apply u hu p
  have hx' (i : Fin n) : (x i : VF) = (u p).val.1 i := by
    change _ = (a i)⁻¹ * p.val.1 i + 0
    rw [← hx i, add_zero, ← mul_assoc, inv_mul_cancel₀ (ha i), one_mul]
  have hy' (i : Fin n) : (y i : VF) = (F (u p)).val.1 i := by
    change _ = (w (f (u' (u p)))).val.1 i
    rw [hpu]
    change _ = (b i)⁻¹ * (f p).val.1 i + 0
    rw [← hy i, add_zero, ← mul_assoc, inv_mul_cancel₀ (hb i), one_mul]
  obtain ⟨J', D, hJ', hD, hdet, hred⟩ := normalized_rvJacobian_of_henselized_graphs
    hc hκ hs hsmall F (u p) x y hx' hy' hxUnit hi _ hC hp hvertical hhorizontal hgraph
  letI := Valued.mk' v
  have hInd : AlgebraicIndependent (vfParameterField S) (u p).val.1 := by
    rw [← (show (fun i => (x i : VF)) = (u p).val.1 from funext hx')]
    exact algebraicIndependent_of_isGaussEvaluation v _
      (isGaussEvaluation_of_independent_residues v _ x hi)
  have hpInd₀ := independent_map_of_finiteFibres hc u' (Map.finiteFibres_of_injective hu'.injective) (u p) hInd
  have hpInd : AlgebraicIndependent (vfParameterField S) p.val.1 := hpu ▸ hpInd₀
  have hfInd := independent_map_of_finiteFibres hc f (Map.finiteFibres_of_injective hf.injective) p hpInd
  have hpre := hasMixedVFDerivativeAt_of_affine_formula hc hκ hs hsmall Values.presentation_compatible u' (u p)
    hInd a 0 (fun z => by
      funext i
      have h := congrFun (congrArg (fun p : V × (Fin r → RV) => p.1)
        (affineMixedImage_inverse_apply A _ 0 hNameA (fun _ => h0) (fun j => inv_ne_zero (ha j)) z)) i
      simpa only [inv_inv, Pi.zero_apply, mul_zero] using h)
  have hpost := hasMixedVFDerivativeAt_of_affine_formula hc hκ hs hsmall Values.presentation_compatible w (f p)
    hfInd (fun i => (b i)⁻¹) 0 (fun _ => rfl)
  obtain ⟨L, hL⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall Values.presentation_compatible f p hpInd
  obtain ⟨K, hK⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall Values.presentation_compatible
    (f.comp u') (u p) hInd
  have hL' : HasMixedVFDerivativeAt f (u' (u p)) L := hpu.symm ▸ hL
  have hpost' : HasMixedVFDerivativeAt w ((f.comp u') (u p)) (vfDiagonalLinear (fun i => (b i)⁻¹)) :=
    show HasMixedVFDerivativeAt w (f (u' (u p))) _ from hpu.symm ▸ hpost
  obtain ⟨_, _, hfirst⟩ := mixedVFJacobian_comp_of_full_derivative hpre hL'
  obtain ⟨hKJ, _, hFJ⟩ := mixedVFJacobian_comp_of_full_derivative hK hpost'
  let J := (LinearMap.toMatrix' L).det
  have hEq : J' = ((∏ i, (b i)⁻¹) * J) * ∏ i, a i := by
    rw [hJ'.unique hFJ, hKJ.unique hfirst, det_vfDiagonalLinear, det_vfDiagonalLinear, mul_assoc]
  have ha' : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => ha i)
  have hb' : (∏ i, b i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hb i)
  have hInv : (∏ i, (b i)⁻¹) = (∏ i, b i)⁻¹ :=
    Finset.prod_inv_distrib b
  have hscale : ((∏ i, b i) / ∏ i, a i) * J' = J := by
    rw [hEq, hInv]
    field_simp
  have hRV := isRVJacobianAt_of_normalized_determinant C a b x y ha hb hx₀ hy₀ D hdet J' hred hp hD
  rw [hscale, funext hx, funext hy] at hRV
  exact ⟨L, hL, hRV⟩

theorem rvComparison_at_generic_fixed_value_pair [CharZero VF] [CharZero k]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    [IsAlgClosed (vfParameterField S)]
    (B₀ B₁ : LRV.Substructure M) (hB₁ : Cardinal.mk B₁ < κ)
    (h₀ : residueParameterField B₀ ≤ residueCoefficientField (vfParameterField S))
    (h₁ : residueCoefficientField (vfParameterField S) ≤ residueParameterField B₁)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (hf : Function.Bijective f) (p : A) (a b : V)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hNameA : ∀ i, ((a i)⁻¹).val ∈ S) (hNameB : ∀ i, ((b i)⁻¹).val ∈ S)
    (hZero : (0 : VF).val ∈ S)
    (haVal : ∀ i, Values.vrv (tupleRV p.val.1 i) = Values.vrv (tupleRV a i))
    (hbVal : ∀ i, Values.vrv (tupleRV (f p).val.1 i) = Values.vrv (tupleRV b i))
    (C : Set (Fin (n+n) → RV))
    (hC : Relative.Def (residueParameterField B₀) (normalizedCorrespondence C (tupleRV a) (tupleRV b)))
    (hPair : productTuple (tupleRV p.val.1) (tupleRV (f p).val.1) ∈ C)
    (hfinR : ∀ x : Fin n → k,
      {y | productTuple x y ∈ normalizedCorrespondence C (tupleRV a) (tupleRV b)}.Finite)
    (hfinL : ∀ y : Fin n → k,
      {x | productTuple x y ∈ normalizedCorrespondence C (tupleRV a) (tupleRV b)}.Finite)
    (hInd : AlgebraicIndependent (residueParameterField B₁)
      (residueNormalize (tupleRV a) (tupleRV p.val.1)))
    (hgraph : HenselizedGaussGraphInput VF) :
    ∃ L, HasMixedVFDerivativeAt f p L ∧
      IsRVJacobianAt C (tupleRV p.val.1) (tupleRV (f p).val.1)
        (CanonicalRV.encodedRv (LinearMap.toMatrix' L).det) := by
  let E := residueCoefficientField (vfParameterField S)
  let L := residueParameterField B₁
  let C' := normalizedCorrespondence C (tupleRV a) (tupleRV b)
  letI : IsAlgClosed VF := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed k := ValOneEC.Johnson.isAlgClosed_residueField v
  obtain ⟨x, hx, hxUnit, hxRes, hx₀⟩ := exists_normalized_VF_representatives a p.val.1 ha haVal
  obtain ⟨y, hy, _, hyRes, hy₀⟩ := exists_normalized_VF_representatives b (f p).val.1 hb hbVal
  let X := residue O ∘ x
  let Y := residue O ∘ y
  have hp : productTuple X Y ∈ C' := by
    change residueScale (productTuple (tupleRV a) (tupleRV b)) (productTuple X Y) ∈ C ∧
      ∀ i, productTuple X Y i ≠ 0
    constructor
    · have he : residueScale (productTuple (tupleRV a) (tupleRV b)) (productTuple X Y) =
          productTuple (residueScale (tupleRV a) X) (residueScale (tupleRV b) Y) := by
        apply productTuple_ext
        · intro i
          simp only [residueScale, productTuple_left]
        · intro i
          simp only [residueScale, productTuple_right]
      rwa [he, show X = _ from hxRes, show Y = _ from hyRes, residueScale_normalize _ _ haVal,
        residueScale_normalize _ _ hbVal]
    · intro i
      obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective i
      · exact (productTuple_left X Y j).symm ▸ hx₀ j
      · exact (productTuple_right X Y j).symm ▸ hy₀ j
  have hX : AlgebraicIndependent L X := by
    change AlgebraicIndependent L (residue O ∘ x)
    rwa [hxRes]
  have hC₁ : Relative.Def L C' := hC.mono (h₀.trans h₁)
  have hY : AlgebraicIndependent L Y := residue_independent_target_of_finite_reverse L C' hC₁ X Y hp (hfinL Y) hX
  obtain ⟨hvert, hhor⟩ := residue_tangent_kernels_eq_zero_of_independent_projections
    hs B₁ hB₁ C' hC₁ hfinR hfinL X Y hp hX hY
  letI : Algebra E L := (Subfield.inclusion h₁).toAlgebra
  letI : IsScalarTower E L k := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hX' : AlgebraicIndependent E X := hX.restrictScalars (algebraMap E L).injective
  exact rvComparison_on_independent_residue_fibre hc hκ hs hsmall f hf p a b x y ha hb hNameA hNameB
    hZero hx hy hxUnit hx₀ hy₀ (residueCoefficient_eval_injective_of_independent _ X hX') C
    (hC.mono h₀) hp hvert hhor hgraph

end SpecialTransformations.Section9
