module

public import Section9.HenselizedGraphData
public import Section9.GraphResidueFieldRestriction
public import Section9.GraphJacobianIdentification
public import Section9.ResidueGraphDerivative
public import Section9.RVDeterminantReduction
public import Section9.ResidueCoefficientBase

@[expose] public section

/-! The pointwise comparison for an actual normalized lift. The
derivative is computed on the graph field in VF and reduces to the
residue tangent matrix at the same graph point. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language IsLocalRing MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ}
local notation "VF" => VFType (M := M)
local notation "k" => ModelResidue M
local notation "v" => Values.presentationValuation (M := M)
local notation "O" => Valuation.valuationSubring (Values.presentationValuation (M := M))

theorem normalized_rvJacobian_of_henselized_graphs [CharZero VF] [CharZero k]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    [IsAlgClosed (vfParameterField S)]
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (p : A) (x y : Fin n → O)
    (hx : ∀ i, (x i : VF) = p.val.1 i) (hy : ∀ i, (y i : VF) = (f p).val.1 i)
    (hxUnit : ∀ i, v (x i : VF) = 1)
    (hi : Function.Injective (eval₂Hom (residueFieldInclusion v (vfParameterField S)) (residue O ∘ x)))
    (C : Set (Fin (n + n) → k)) (hC : Relative.Def (residueCoefficientField (vfParameterField S)) C)
    (hp : productTuple (residue O ∘ x) (residue O ∘ y) ∈ C)
    (hvertical : ∀ z, IsPolynomialTangent C (productTuple (residue O ∘ x) (residue O ∘ y))
      (productTuple 0 z) → z = 0)
    (hhorizontal : ∀ z, IsPolynomialTangent C (productTuple (residue O ∘ x) (residue O ∘ y))
      (productTuple z 0) → z = 0)
    (hgraph : HenselizedGaussGraphInput VF) :
    ∃ J : VF, ∃ D : Matrix (Fin n) (Fin n) k,
      HasMixedVFJacobianAt f p J ∧
      IsResidueJacobianMap (M := M) C (productTuple (residue O ∘ x) (residue O ∘ y)) (Matrix.toLin' D) ∧
      D.det ≠ 0 ∧ CanonicalRV.encodedRv J = residueRV D.det := by
  let E := vfParameterField S
  let C₀ := residueCoefficientField E
  letI : IsAlgClosed VF := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed k := ValOneEC.Johnson.isAlgClosed_residueField v
  letI : IsAlgClosed C₀ := residueCoefficientField_isAlgClosed E
  let x₀ := p.val.1
  let y₀ := (f p).val.1
  letI := Valued.mk' v
  have hGauss : IsGaussEvaluation (E := E) v x₀ := by
    rw [← (show (fun i => (x i : VF)) = x₀ from funext hx)]
    exact isGaussEvaluation_of_independent_residues v E x hi
  have hInd := algebraicIndependent_of_isGaussEvaluation v x₀ hGauss
  have hAlg (i : Fin n) : IsAlgebraic (IntermediateField.adjoin E (Set.range x₀)) (y₀ i) := by
    have h := map_output_vf_coordinate_isAlgebraic hc f p i
    rwa [tupleField_eq_adjoin] at h
  have hx₀ (i : Fin n) : v (x₀ i) = 1 := (congrArg v (hx i)).symm.trans (hxUnit i)
  obtain ⟨data⟩ := hgraph _ v E x₀ y₀ hx₀ hGauss hAlg
  let L := data.field
  let A₀ := E.comap L.subtype
  let w := (v).comap L.subtype
  let X := graphTuple L x₀ data.input_mem
  let Y := graphTuple L y₀ data.output_mem
  obtain ⟨D, hD, hbound⟩ := HenselizedGraphData.exists_coordinate_derivations v E x₀ y₀
    (fun i => (hx₀ i).le) hGauss data
  let X₁ (i : Fin n) : w.valuationSubring := ⟨X i, (hx₀ i).le⟩
  let Y₁ (i : Fin n) : w.valuationSubring :=
    ⟨Y i, calc
      v (y₀ i) = v (y i : VF) := (congrArg v (hy i)).symm
      _ ≤ 1 := (y i).property⟩
  let g := residueFieldInclusion v L
  let g₀ := residueFieldInclusion v E
  let e := g₀.rangeRestrictFieldEquiv
  let j := (coefficientResidueIntoGraph v E L data.coefficients).comp e.symm.toRingHom
  have hj (a : C₀) : g (residueFieldInclusion w A₀ (j a)) = (a : k) := by
    change g (residueFieldInclusion w A₀ (coefficientResidueIntoGraph v E L data.coefficients (e.symm a))) = _
    rw [coefficientResidueIntoGraph_commutes]
    exact g₀.rangeRestrictFieldEquiv_apply_symm_apply a
  have hX : (g ∘ residue w.valuationSubring) ∘ X₁ = residue O ∘ x := by
    funext i
    change (residueFieldInclusion v L) (residue w.valuationSubring (X₁ i)) = residue O (x i)
    rw [residueFieldInclusion, ResidueField.map_residue]
    exact congrArg (residue O) (Subtype.ext (hx i).symm)
  have hY : (g ∘ residue w.valuationSubring) ∘ Y₁ = residue O ∘ y := by
    funext i
    change (residueFieldInclusion v L) (residue w.valuationSubring (Y₁ i)) = residue O (y i)
    rw [residueFieldInclusion, ResidueField.map_residue]
    exact congrArg (residue O) (Subtype.ext (hy i).symm)
  let T : Matrix (Fin n) (Fin n) O := Matrix.of fun i j =>
    ⟨(D j (Y i)).val, (hbound j (Y i)).trans (Y₁ i).property⟩
  have hJ := isResidueJacobianMap_of_bounded_graph_derivations w A₀ C₀ g j hj C hC X₁ Y₁ D
    (fun j i => by
      change D j (X i) = _
      rw [hD]
      by_cases h : i = j
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (Ne.symm h), if_neg h]) hbound
    (by dsimp only; rwa [hX, hY])
    (by dsimp only; rwa [hX, hY])
    (by dsimp only; rwa [hX, hY])
  have hred : (Matrix.of fun i j => (g ∘ residue w.valuationSubring)
      ⟨D j (Y i), (hbound j (Y i)).trans (Y₁ i).property⟩) = T.map (residue O) := by
    ext i j
    change residueFieldInclusion v L (residue w.valuationSubring _) = _
    rw [residueFieldInclusion, ResidueField.map_residue]
    rfl
  dsimp only at hJ
  rw [hX, hY, hred] at hJ
  let e' := graphCoefficientEquiv E L data.coefficients
  letI : Algebra E A₀ := e'.symm.toRingHom.toAlgebra
  letI : Algebra E L := (A₀.subtype.comp e'.symm.toRingHom).toAlgebra
  letI : IsScalarTower E A₀ L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g' : L →ₐ[E] VF := {toRingHom := L.subtype, commutes' := fun _ => rfl}
  have hVF := hasMixedVFDerivativeAt_of_graph_derivations hc hκ hs hsmall Values.presentation_compatible f p hInd
    g' X Y (fun _ => rfl) (fun _ => rfl) (fun j => (D j).restrictScalars E) hD
  obtain ⟨F, hF, hDer⟩ := hVF
  refine ⟨(T.map (O).subtype).det, T.map (residue O), ⟨F, hF, ?_⟩, hJ.1, hJ.2, ?_⟩
  · have hMatrix : (Matrix.of fun i j => g' ((D j).restrictScalars E (Y i))) =
        T.map (O).subtype := by
      ext i j
      rfl
    have hJac := hDer.hasJacobianAt
    rw [LinearMap.toMatrix'_toLin', hMatrix] at hJac
    exact hJac
  · exact encodedRv_det_of_integral_matrix v Values.presentation_compatible T hJ.2

end SpecialTransformations.Section9
