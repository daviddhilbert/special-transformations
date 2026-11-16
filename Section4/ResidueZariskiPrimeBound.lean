module

public import Section4.ResiduePolynomialCover
public import Section4.ResidueRVSet
public import Section4.RVSequenceBounds
public import Section4.Imported.PolynomialCoordinateBasis
public import Section4.Imported.NoetherNormalizationTrdeg
public import Mathlib.RingTheory.Nullstellensatz

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry
open RB31E2E.PolynomialPrimeTrdegHeight

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def residueVanishingIdeal {n : ℕ} (D : Set (Fin n → ModelResidue M)) :
    Ideal (MvPolynomial (Fin n) (ModelResidue M)) :=
  MvPolynomial.vanishingIdeal (ModelResidue M) D

theorem mem_residueVanishingIdeal_iff {n : ℕ} (D : Set (Fin n → ModelResidue M))
    (p : MvPolynomial (Fin n) (ModelResidue M)) :
    p ∈ residueVanishingIdeal D ↔ ∀ a ∈ D, p.eval a = 0 := by
  rw [residueVanishingIdeal, MvPolynomial.mem_vanishingIdeal_iff]
  simp only [MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id]

theorem residue_selection_dependent_of_arity_gt_dimension
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    (B : LRV.Substructure M) {n d : ℕ}
    (D : Set (Fin n → ModelResidue M)) (hD : Relative.Def (residueParameterField B) D)
    (v : Fin d → Fin n)
    (hd : rvDim (residueRVSet hcan (residueParameterField B) (B : Set M)
      (residueParameterField_le_definableField B) D hD) < d) :
    ∀ a ∈ D, ¬ AlgebraicIndependent (residueParameterField B) (a ∘ v) := by
  intro a ha hind
  have hr := (residue_independent_iff_rvTupleRank_eq_arity hcan hex B (a ∘ v)).mp hind
  have hb := (rvTupleRank_subsequence_le hcan hex (B : Set M) (residueRV ∘ a) v).trans
    (rvTupleRank_le_rvDim hcan hex
      (residueRVSet hcan (residueParameterField B) (B : Set M)
        (residueParameterField_le_definableField B) D hD)
      ⟨residueRV ∘ a, a, ha, rfl⟩)
  change rvTupleRank hcan hex (B : Set M) (residueRV ∘ (a ∘ v)) ≤ _ at hb
  rw [hr] at hb
  exact (not_le_of_gt hd) hb

/-- Every prime component of the actual residue vanishing ideal has
function-field transcendence degree bounded by the genuine RV dimension. -/
theorem residue_prime_quotient_trdeg_le_dimension
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    {n : ℕ} (D : Set (Fin n → ModelResidue M)) (hD : Relative.Def (residueParameterField B) D)
    (P : Ideal (MvPolynomial (Fin n) (ModelResidue M))) [P.IsPrime]
    (hIP : residueVanishingIdeal D ≤ P) :
    (Algebra.trdeg (ModelResidue M)
      (FractionRing (MvPolynomial (Fin n) (ModelResidue M) ⧸ P))).toNat ≤
      rvDim (residueRVSet hcan (residueParameterField B) (B : Set M)
        (residueParameterField_le_definableField B) D hD) := by
  let K := ModelResidue M
  let E := residueParameterField B
  let Q := MvPolynomial (Fin n) K ⧸ P
  let A := residueRVSet hcan E (B : Set M)
    (residueParameterField_le_definableField B) D hD
  obtain ⟨I, hI⟩ := exists_coordinateIndex_transcendenceBasis P
  letI : Fintype I := Fintype.ofFinite I
  let d := Fintype.card I
  let e : Fin d ≃ I := (Fintype.equivFin I).symm
  let v : Fin d → Fin n := fun i => (e i).val
  have hcard : (Algebra.trdeg K (FractionRing Q)).toNat = d := by
    rw [FieldArithmetic.Chapter06.trdeg_fractionRing K Q, ← hI.cardinalMk_eq_trdeg]
    simp only [Cardinal.mk_fintype, Cardinal.toNat_natCast, d]
  rw [hcard]
  by_contra hn
  have hd : rvDim A < d := Nat.lt_of_not_ge hn
  obtain ⟨p, hp, hpa⟩ := exists_residue_polynomial_vanishing_on_selection hs B hB D hD v
    (residue_selection_dependent_of_arity_gt_dimension hcan hex B D hD v hd)
  let q := p.map E.subtype
  have hq : q ≠ 0 := by
    intro hz
    apply hp
    exact (MvPolynomial.map_injective E.subtype Subtype.val_injective)
      (by simpa only [map_zero] using hz)
  have hrename : MvPolynomial.rename v q ∈ residueVanishingIdeal D := by
    apply (mem_residueVanishingIdeal_iff D _).mpr
    intro a ha
    simpa only [MvPolynomial.eval_rename, q, MvPolynomial.eval_map] using hpa a ha
  have hind : AlgebraicIndependent K (fun i : Fin d => quotientCoordinate P (v i)) :=
    hI.1.comp e e.injective
  have heval : (Ideal.Quotient.mkₐ K P).comp (MvPolynomial.rename v) =
      MvPolynomial.aeval (fun i : Fin d => quotientCoordinate P (v i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    change Ideal.Quotient.mk P (MvPolynomial.rename v (MvPolynomial.X i)) =
      Ideal.Quotient.mk P (MvPolynomial.X (v i))
    exact congrArg (Ideal.Quotient.mk P) (MvPolynomial.rename_X v i)
  have hzero : MvPolynomial.aeval (fun i : Fin d => quotientCoordinate P (v i)) q = 0 := by
    rw [← heval]
    change Ideal.Quotient.mk P (MvPolynomial.rename v q) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hIP hrename)
  exact hq (hind.eq_zero_of_aeval_eq_zero q hzero)

end SpecialTransformations.Section4.ResiduePurity

end
