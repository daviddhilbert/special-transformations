import Section9.ResidueOpenCharts
import Section9.VolumeResidueCorrespondence
import Section4.SmallGeneratedBase
import Section7.ResidueCharacteristic

/-! Every tuple of nonzero scales admits an open residue chart with
an input cut for the finite-volume correspondence. The coefficients
are allowed to depend on the scales at this stage. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "RV" => CanonicalRV.RVSort M
local notation "k" => ModelResidue M

theorem exists_volume_residue_chart
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : BaseContext M)
    {U V : RVObject (M := M) (B.base : Set M) n} (e : U ≅ V)
    (a b : Fin n → RV) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    let C := normalizedCorrespondence (volumeCorrespondence e.hom.map).carrier a b
    ∃ E : LRV.Substructure M, B.base ≤ E ∧ Cardinal.mk E < B.κ ∧
      ∃ (P : Fin n → MvPolynomial (Fin (n+n)) (residueParameterField E))
        (T : MvPolynomial (Fin (n+n)) (residueParameterField E))
        (D : MvPolynomial (Fin n) (residueParameterField E)), D ≠ 0 ∧
        let Q := residueOutputJacobian P * T
        let R := (Matrix.of fun i j => pderiv (productLeft n n j) (P i)).det
        (∀ z ∈ C, ∀ i, aeval z (P i) = 0) ∧
        (∀ z, (∀ i, aeval z (P i) = 0) → aeval z Q ≠ 0 → z ∈ C) ∧
        (∀ z ∈ C, aeval (z ∘ productLeft n n) D ≠ 0 → aeval z Q ≠ 0 ∧ aeval z R ≠ 0) := by
  let t := rvValues a
  let s := rvValues b
  let F := Set.range t ∪ Set.range s
  let E := Substructure.closure LRV ((B.base : Set M) ∪ F)
  have hBE : B.base ≤ E := fun _ h => Substructure.subset_closure (Or.inl h)
  have hE : Cardinal.mk E < B.κ := small_generated_finite_extension B.uncountable B.base B.small F
    ((Set.finite_range t).union (Set.finite_range s))
  let C := normalizedCorrespondence (volumeCorrespondence e.hom.map).carrier a b
  have hC : Relative.Def (residueParameterField E) C :=
    normalizedCorrespondence_definable_of_base hc E ((volumeCorrespondence e.hom.map).extend hBE) a b ha hb
      (fun i => Substructure.subset_closure (Or.inr (Or.inl (Set.mem_range_self i))))
      (fun i => Substructure.subset_closure (Or.inr (Or.inr (Set.mem_range_self i))))
  obtain ⟨hR, hL⟩ := normalizedVolumeCorrespondence_finite e a b ha hb
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed k := ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  letI : CharZero k := residueField_charZero_of_model00 Values.presentationValuation
    Values.presentation_compatible B.model00
  exact ⟨E, hBE, hE, exists_residue_chart_with_input_cut B.saturated E hE C hC hR hL⟩

end SpecialTransformations.Section9
