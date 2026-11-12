module

public import Section4.PolynomialCover
public import Section4.TupleIndependence
public import Section4.Imported.PolynomialCoordinateBasis
public import Section4.Imported.NoetherNormalizationTrdeg
public import Mathlib.RingTheory.Nullstellensatz

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry
open RB31E2E.PolynomialPrimeTrdegHeight

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The actual polynomial ideal of the VF projection, over the ambient
valued field. Its zero locus is the algebraic Zariski closure. -/
def vfVanishingIdeal {S : Set M} {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) :
    Ideal (MvPolynomial (Fin n) (VFType (M := M))) :=
  MvPolynomial.vanishingIdeal (VFType (M := M)) (Prod.fst '' A.carrier)

theorem mem_vfVanishingIdeal_iff {S : Set M} {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (p : MvPolynomial (Fin n) (VFType (M := M))) :
    p ∈ vfVanishingIdeal A ↔ ∀ a : A, p.eval a.val.1 = 0 := by
  rw [vfVanishingIdeal, MvPolynomial.mem_vanishingIdeal_iff]
  constructor
  · intro h a
    simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id] using
      h a.val.1 ⟨a.val, a.property, rfl⟩
  · rintro h x ⟨a, ha, rfl⟩
    simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id] using h ⟨a, ha⟩

theorem selection_dependent_of_arity_gt_vfDim
    (hcan : CanonicalStructure.IsCanonical (M := M))
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    {S : Set M} {n r d : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S)
    (v : Fin d → Fin n) (hd : vfDim Δ A < d) (a : A) :
    ¬ AlgebraicIndependent (vfParameterField S) (a.val.1 ∘ v) := by
  intro hind
  have hr : vfTupleTrdeg S (a.val.1 ∘ v) = (d : Cardinal) :=
    (tupleField_trdeg_eq_arity_iff (vfParameterField S) _).mpr hind
  have h := (vfTupleTrdeg_select_le S a.val.1 v).trans (vfTupleTrdeg_le_vfDim hcan Δ hΔ A a)
  rw [hr] at h
  have h' : d ≤ vfDim Δ A := by exact_mod_cast h
  exact (not_le_of_gt hd) h'

/-- Every prime component of the actual vanishing ideal has function-field
transcendence degree at most the definable VF dimension. The compactness
argument uses equations over the original parameter field. -/
theorem prime_quotient_trdeg_le_vfDim
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : DefinableGeometry.Space LRV M) (hΔ : Δ.RVCoded)
    {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S)
    (P : Ideal (MvPolynomial (Fin n) (VFType (M := M)))) [P.IsPrime]
    (hIP : vfVanishingIdeal A ≤ P) :
    (Algebra.trdeg (VFType (M := M))
      (FractionRing (MvPolynomial (Fin n) (VFType (M := M)) ⧸ P))).toNat ≤ vfDim Δ A := by
  let K := VFType (M := M)
  let E := vfParameterField (M := M) S
  let B := MvPolynomial (Fin n) K ⧸ P
  obtain ⟨I, hI⟩ := exists_coordinateIndex_transcendenceBasis P
  letI : Fintype I := Fintype.ofFinite I
  let d := Fintype.card I
  let e : Fin d ≃ I := (Fintype.equivFin I).symm
  let v : Fin d → Fin n := fun i => (e i).val
  have hcard : (Algebra.trdeg K (FractionRing B)).toNat = d := by
    rw [FieldArithmetic.Chapter06.trdeg_fractionRing K B, ← hI.cardinalMk_eq_trdeg]
    simp only [Cardinal.mk_fintype, Cardinal.toNat_natCast, d]
  rw [hcard]
  by_contra hn
  have hd : vfDim Δ A < d := Nat.lt_of_not_ge hn
  obtain ⟨p, hp, hpa⟩ := exists_polynomial_vanishing_on_selection hs hsmall A v
    (selection_dependent_of_arity_gt_vfDim hcan Δ hΔ A v hd)
  let q := p.map E.subtype
  have hq : q ≠ 0 := by
    intro hzero
    apply hp
    exact (MvPolynomial.map_injective E.subtype Subtype.val_injective)
      (by simpa only [map_zero] using hzero)
  have hrename : MvPolynomial.rename v q ∈ vfVanishingIdeal A := by
    apply (mem_vfVanishingIdeal_iff A _).mpr
    intro a
    simpa only [MvPolynomial.eval_rename, q, MvPolynomial.eval_map] using hpa a
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

end SpecialTransformations.Section4

end
