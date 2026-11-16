module

public import Section9.HenselizedGraphData
public import Mathlib.RingTheory.Etale.Basic

@[expose] public section

namespace SpecialTransformations.Section9

theorem etaleCovered_of_commuting_equivs {K L : Type} [CommRing K] [CommRing L]
    (A B : Subring K) (A' B' : Subring L) (hAB : A ≤ B) (hA'B' : A' ≤ B')
    (eA : A' ≃+* A) (eB : B' ≃+* B)
    (he : ∀ a : A', eB (Subring.inclusion hA'B' a) = Subring.inclusion hAB (eA a))
    (h : EtaleCovered A B hAB) : EtaleCovered A' B' hA'B' := by
  letI : Algebra A B := (Subring.inclusion hAB).toAlgebra
  letI : Algebra A' B' := (Subring.inclusion hA'B').toAlgebra
  letI : Algebra A' A := eA.toRingHom.toAlgebra
  let e : A' ≃ₐ[A'] A := AlgEquiv.ofBijective (Algebra.ofId A' A) eA.bijective
  letI : Algebra.FormallyEtale A' A := Algebra.FormallyEtale.of_equiv e
  intro b
  obtain ⟨T, rT, aT, et, f, x, hx⟩ := h (eB b)
  letI := rT
  letI := aT
  letI := et
  letI : Algebra A' T := ((algebraMap A T).comp eA.toRingHom).toAlgebra
  letI : IsScalarTower A' A T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra.FormallyEtale A' T := Algebra.FormallyEtale.comp A' A T
  let f' : T →ₐ[A'] B' :=
    { toRingHom := eB.symm.toRingHom.comp f.toRingHom
      commutes' := fun a => by
        apply eB.injective
        change eB (eB.symm (f (algebraMap A T (eA a)))) = eB (Subring.inclusion hA'B' a)
        rw [eB.apply_symm_apply, he, f.commutes]
        rfl }
  refine ⟨T, rT, inferInstance, inferInstance, f', x, ?_⟩
  change eB.symm (f x) = b
  rw [hx, eB.symm_apply_apply]

def valuationRingInside_comap_equiv {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (F L : Subfield K) (hFL : F ≤ L) :
    valuationRingInside (v.comap L.subtype) (F.comap L.subtype) ≃+* valuationRingInside v F where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, hFL x.property.1⟩, x.property⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem etaleCovered_comap_valuationRingInside {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (F H L : Subfield K) (hFH : F ≤ H) (hHL : H ≤ L)
    (h : EtaleCovered (valuationRingInside v F) (valuationRingInside v H) (valuationRingInside_mono v hFH)) :
    let w := v.comap L.subtype
    let h' : F.comap L.subtype ≤ H.comap L.subtype := fun _ hx => hFH hx
    EtaleCovered (valuationRingInside w (F.comap L.subtype)) (valuationRingInside w (H.comap L.subtype))
      (valuationRingInside_mono w h') := by
  exact etaleCovered_of_commuting_equivs _ _ _ _ _ _
    (valuationRingInside_comap_equiv v F L (hFH.trans hHL)) (valuationRingInside_comap_equiv v H L hHL)
    (fun _ => rfl) h


end SpecialTransformations.Section9
