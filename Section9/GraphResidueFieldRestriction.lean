module

public import Section9.GaussFieldRestriction
public import Section9.GaussEvaluation

@[expose] public section

/-! The two copies of the coefficient residue field agree inside the
ambient residue field when the valuation is restricted to a graph
subfield. -/

set_option backward.isDefEq.respectTransparency false

open IsLocalRing

namespace SpecialTransformations.Section9

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

public def coefficientValuationRingEquiv (v : Valuation K Γ) (E L : Subfield K) (h : E ≤ L) :
    (v.comap E.subtype).valuationSubring ≃+*
      ((v.comap L.subtype).comap (E.comap L.subtype).subtype).valuationSubring :=
  let e := graphCoefficientEquiv E L h
  { toFun := fun a => ⟨e.symm a.val, a.property⟩
    invFun := fun a => ⟨e a.val, a.property⟩
    left_inv := fun a => Subtype.ext (e.apply_symm_apply a.val)
    right_inv := fun a => Subtype.ext (e.symm_apply_apply a.val)
    map_mul' := fun a b => Subtype.ext (map_mul e.symm a.val b.val)
    map_add' := fun a b => Subtype.ext (map_add e.symm a.val b.val) }

public instance coefficientValuationRingEquiv_isLocalHom (v : Valuation K Γ)
    (E L : Subfield K) (h : E ≤ L) :
    IsLocalHom (coefficientValuationRingEquiv v E L h).toRingHom := by
  let e := coefficientValuationRingEquiv v E L h
  exact isLocalHom_of_leftInverse e.symm.toRingHom e.symm_apply_apply

noncomputable def coefficientResidueIntoGraph (v : Valuation K Γ) (E L : Subfield K) (h : E ≤ L) :
    ResidueField (v.comap E.subtype).valuationSubring →+*
      ResidueField ((v.comap L.subtype).comap (E.comap L.subtype).subtype).valuationSubring :=
  ResidueField.map (coefficientValuationRingEquiv v E L h).toRingHom

theorem coefficientResidueIntoGraph_commutes (v : Valuation K Γ) (E L : Subfield K) (h : E ≤ L)
    (a : ResidueField (v.comap E.subtype).valuationSubring) :
    residueFieldInclusion v L (residueFieldInclusion (v.comap L.subtype) (E.comap L.subtype)
      (coefficientResidueIntoGraph v E L h a)) = residueFieldInclusion v E a := by
  obtain ⟨c, rfl⟩ := residue_surjective a
  simp only [coefficientResidueIntoGraph, residueFieldInclusion, ResidueField.map_residue]
  rfl

end SpecialTransformations.Section9
