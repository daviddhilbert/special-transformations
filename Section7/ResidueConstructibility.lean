module

public import Section7.FieldConstructibility
public import Section4.ResidueNormalization
public import Section4.MapParameters
public import VFAlgClosed

@[expose] public section

/-! Remark 7.5: actual constructibility over the original residue parameter
field. The comparison is stated as a pullback from Spec E[X] through the
evaluation-kernel map, so tuples are not confused with prime ideals. -/

open Classical FirstOrder FirstOrder.Language Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section4.ResiduePurity

namespace SpecialTransformations.Section7

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- Every original-base definable RV set, restricted to the full residue
field (including zero), is the pullback of a constructible subset of the
prime spectrum over that base's residue parameter field. -/
theorem remark_7_5 (hcan : CanonicalStructure.IsCanonical (M := M))
    (B : LRV.Substructure M) {n : ℕ}
    (A : DefSet (Section4.rawRVSpace (M := M) n) (B : Set M)) :
    ∃ C : Set (PrimeSpectrum (MvPolynomial (Fin n) (residueParameterField B))),
      IsConstructible C ∧ ∀ a : Fin n → ModelResidue M,
        (fun i => residueRV (a i)) ∈ A.carrier ↔ fieldTuplePrime (residueParameterField B) a ∈ C := by
  let E := residueParameterField B
  let s : Fin n → CanonicalRV.RVSort M := fun _ => 1
  have hs (i : Fin n) : s i ∈ extendedCoefficients B E := by
    apply extendedCoefficients_base B E
    change (1 : CanonicalRV.RVSort M).val ∈ B
    rw [RVOperations.one_val]
    exact SubstructureRVGroup.rvOne_mem B
  let A' : DefSet (Section4.rawRVSpace (M := M) n) (residueExtendedBase B E) :=
    A.extend Set.subset_union_left
  have hD := normalizedResidueSet_definable hcan B E le_rfl A' s hs
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  have hset : normalizedResidueSet A' s =
      {a : Fin n → ModelResidue M | (fun i => residueRV (a i)) ∈ A.carrier} := by
    ext a
    change (residueScale s a ∈ A.carrier ∧ residueZeroPattern s a) ↔ _
    have hscale : residueScale s a = fun i => residueRV (a i) := by
      funext i
      change (1 : CanonicalRV.RVSort M) * residueRV (a i) = _
      exact one_mul _
    have hzero : residueZeroPattern s a := by
      intro i hi
      exact (one_ne_zero hi).elim
    rw [hscale]
    exact and_iff_left hzero
  have hpure : (E : Set (ModelResidue M)).Definable Language.ring
      {a : Fin n → ModelResidue M | (fun i => residueRV (a i)) ∈ A.carrier} := by
    rw [← hset]
    exact hD
  exact field_definable_constructible E _ hpure

end SpecialTransformations.Section7
