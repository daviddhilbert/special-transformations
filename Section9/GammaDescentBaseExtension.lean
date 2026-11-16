module

public import Section9.NormalizedGammaDescent
public import Section9.SmallValuedCoefficients
public import Section9.CoarsenedResidueCharacteristic
public import Section7.ResidueCharacteristic
public import Section4.MapParameters
public import Section4.FullDimension

@[expose] public section

/-! The auxiliary algebraically closed coefficient field of the
intrinsic Gamma argument is chosen inside the monster. In the
normalized statement the original definable maps keep their base. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language IsLocalRing
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ] {n r s : ℕ}
local notation "VF" => VFType (M := M)
local notation "V" => Fin n → VF

theorem algebraicIndependent_of_subfield_le {K ι : Type} [Field K]
    {E F : Subfield K} (hEF : E ≤ F) (x : ι → K) (hx : AlgebraicIndependent F x) :
    AlgebraicIndependent E x := by
  letI : Algebra E F := (Subfield.inclusion hEF).toAlgebra
  letI : IsScalarTower E F K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact hx.restrictScalars (algebraMap E F).injective

private theorem graphInput_for_coarsening
    (v : Valuation VF Γ) [CharZero (ResidueField v.valuationSubring)]
    (E : Subfield VF) [IsAlgClosed E] (hne : (coefficientThresholds v E).Nonempty)
    (hgraph : HenselizedGaussGraphInput VF) :
    let w := (thresholdCoarsening v (coefficientThresholds v E) hne
      (coefficientThresholds_lt_one v E) (coefficientThresholds_halve v E)).valuation
    ∀ x y : V, (∀ i, w (x i) = 1) → IsGaussEvaluation (E := E) w x →
      (∀ i, IsAlgebraic (IntermediateField.adjoin E (Set.range x)) (y i)) →
      Nonempty (HenselizedGraphData w E x y) := by
  let U := coefficientThresholds v E
  let ht := coefficientThresholds_lt_one v E
  let hh := coefficientThresholds_halve v E
  let w := (thresholdCoarsening v U hne ht hh).valuation
  letI : CharZero (ResidueField w.valuationSubring) := residueCharZero_of_coarsening v w
    (thresholdCoarsening_le_of_fine_le v U hne ht hh)
  exact hgraph _ w E

private theorem normalizedGammaDescent_on_closed_base [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) {T : Set M}
    (hT : Cardinal.mk T < κ) (hE : Cardinal.mk (vfParameterField T) < κ)
    [IsAlgClosed (vfParameterField T)] (v : Valuation VF Γ)
    (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    [CharZero (ResidueField v.valuationSubring)] (hne : (coefficientThresholds v (vfParameterField T)).Nonempty)
    {A : DefSet (rawMixedSpace (M := M) n r) T} {B : DefSet (rawMixedSpace (M := M) n s) T}
    (f : Map A B) (g : Map B A) (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f)
    (hA : ∀ x : V, (∃ p : A, p.val.1 = x) ↔ ∀ i, v (x i) < 1)
    (hB : ∀ x : V, (∃ p : B, p.val.1 = x) ↔ ∀ i, v (x i) < 1)
    (c : vfParameterField T) (hc₀ : c ≠ 0)
    (hconst : ∀ p : A, AlgebraicIndependent (vfParameterField T) p.val.1 →
      ∃ J : VF, HasMixedVFJacobianAt f p J ∧ v J = v (c : VF))
    (hgraph : HenselizedGaussGraphInput VF) : v (c : VF) = 1 := by
  apply normalizedGammaDescent_of_henselized_graphs hc hκ hs hT hE v hv hne f g hgf hfg hA hB c hc₀ hconst
  exact graphInput_for_coarsening v (vfParameterField T) hne hgraph

set_option maxHeartbeats 400000 in
private theorem normalizedGammaDescent_over_extension [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    {S T : Set M} (hST : S ⊆ T) (hT : Cardinal.mk T < κ) (hE : Cardinal.mk (vfParameterField T) < κ)
    [IsAlgClosed (vfParameterField T)] (v : Valuation VF Γ)
    (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    [CharZero (ResidueField v.valuationSubring)]
    (hne : (coefficientThresholds v (vfParameterField T)).Nonempty)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} (f : Map A B) (g : Map B A)
    (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f)
    (hA : ∀ x : V, (∃ p : A, p.val.1 = x) ↔ ∀ i, v (x i) < 1)
    (hB : ∀ x : V, (∃ p : B, p.val.1 = x) ↔ ∀ i, v (x i) < 1)
    (c : vfParameterField T) (hc₀ : c ≠ 0)
    (hconst : ∀ p : A, AlgebraicIndependent (vfParameterField S) p.val.1 →
      ∃ J : VF, HasMixedVFJacobianAt f p J ∧ v J = v (c : VF))
    (hgraph : HenselizedGaussGraphInput VF) : v (c : VF) = 1 := by
  let E := vfParameterField T
  let F := f.extend hST
  let G := g.extend hST
  have hsE : vfParameterField S ≤ E := Subfield.closure_mono (fun _ h => hST h)
  have hconst' (p : A.extend hST) (hp : AlgebraicIndependent E p.val.1) :
      ∃ J : VF, HasMixedVFJacobianAt F p J ∧ v J = v (c : VF) := by
    change ∃ J : VF, HasMixedVFJacobianAt f p J ∧ v J = v (c : VF)
    exact hconst p (algebraicIndependent_of_subfield_le hsE p.val.1 hp)
  exact normalizedGammaDescent_on_closed_base hc hκ hs hT hE v hv hne F G hgf hfg hA hB c hc₀ hconst' hgraph

theorem normalizedGammaDescent_of_reference_input [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (v : Valuation VF Γ) (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} (f : Map A B) (g : Map B A)
    (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f)
    (hA : ∀ x : V, (∃ p : A, p.val.1 = x) ↔ ∀ i, v (x i) < 1)
    (hB : ∀ x : V, (∃ p : B, p.val.1 = x) ↔ ∀ i, v (x i) < 1)
    (c : VF) (hc₀ : c ≠ 0)
    (hconst : ∀ p : A, AlgebraicIndependent (vfParameterField S) p.val.1 →
      ∃ J : VF, HasMixedVFJacobianAt f p J ∧ v J = v c)
    (hgraph : HenselizedGaussGraphInput VF) : v c = 1 := by
  letI : Valued VF Γ := Valued.mk' v
  obtain ⟨d, hd₀, hd⟩ := model_valuation_nontrivial hv
  obtain ⟨T, hST, hT, hE, hclosed, hnames⟩ :=
    exists_small_algClosed_vfParameter_extension hκ S hsmall (![c,d] : Fin 2 → VF)
  let E := vfParameterField T
  letI : IsAlgClosed E := hclosed
  let c' : E := ⟨c, hnames 0⟩
  let d' : E := ⟨d, hnames 1⟩
  have hne : (coefficientThresholds v E).Nonempty := ⟨v d, hd, d', fun h => hd₀ (congrArg Subtype.val h), rfl⟩
  letI : CharZero (ResidueField v.valuationSubring) := residueField_charZero_of_model00 v hv h00
  exact normalizedGammaDescent_over_extension hc hκ hs hST hT hE v hv hne f g hgf hfg hA hB c'
    (fun h => hc₀ (congrArg Subtype.val h)) hconst hgraph

end SpecialTransformations.Section9
