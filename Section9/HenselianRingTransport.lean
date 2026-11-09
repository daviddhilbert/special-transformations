import Section9.ValuedEtaleDerivation
import Mathlib.RingTheory.Henselian

open Polynomial IsLocalRing

namespace SpecialTransformations.Section9

theorem henselian_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] [HenselianLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) : HenselianLocalRing S := by
  letI : IsLocalHom e.symm.toRingHom := isLocalHom_of_leftInverse e.toRingHom e.apply_symm_apply
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a hfa hda
  let g := f.map e.symm.toRingHom
  have hEval (y : S) : g.eval (e.symm y) = e.symm (f.eval y) := Polynomial.eval_map_apply e.symm.toRingHom y
  have hg : g.eval (e.symm a) ∈ maximalIdeal R := by
    rw [hEval]
    change f.eval a ∈ (maximalIdeal R).comap e.symm.toRingHom
    rwa [maximalIdeal_comap]
  have hgd : IsUnit (g.derivative.eval (e.symm a)) := by
    change IsUnit ((f.map e.symm.toRingHom).derivative.eval (e.symm a))
    rw [Polynomial.derivative_map]
    have he := Polynomial.eval_map_apply e.symm.toRingHom (p := f.derivative) a
    exact he.symm ▸ hda.map e.symm.toRingHom
  obtain ⟨b, hb, hba⟩ := HenselianLocalRing.is_henselian g (hf.map e.symm.toRingHom) (e.symm a) hg hgd
  refine ⟨e b, ?_, ?_⟩
  · change f.eval (e b) = 0
    apply e.symm.injective
    rw [← hEval, e.symm_apply_apply, map_zero]
    exact hb
  · rw [← maximalIdeal_comap e.symm.toRingHom]
    change e.symm (e b - a) ∈ maximalIdeal R
    rw [map_sub, e.symm_apply_apply]
    exact hba

def valuationSubringInside_equiv {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (F : Subfield K) :
    (v.comap F.subtype).valuationSubring ≃+* valuationRingInside v F where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl


end SpecialTransformations.Section9
