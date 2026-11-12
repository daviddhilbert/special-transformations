module

public import Section9.EmbeddedHenselization
public import Section9.GaussExtension
public import Section9.NestedGaussField
public import Section9.EtaleCoverTransport
public import Section9.HenselizedGraphData
public import VFAlgClosed

@[expose] public section

open FirstOrder FirstOrder.Language IsLocalRing
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section9

/-- Henselianity persists under a finite extension. In residue
characteristic zero the fundamental equality gives residue degree
equal to field degree when the values are unchanged. -/
def FiniteHenselianExtensionReference : Prop :=
  ∀ (L G : Type) [Field L] [LinearOrderedCommGroupWithZero G]
    (v : Valuation L G) (H : Subfield L) [FiniteDimensional H L]
    [HenselianLocalRing (v.comap H.subtype).valuationSubring]
    [CharZero (ResidueField v.valuationSubring)],
    (∀ z : L, ∃ c : H, v (c : L) = v z) →
    HenselianLocalRing v.valuationSubring ∧
      letI := (residueFieldInclusion v H).toAlgebra
      Module.finrank H L = Module.finrank
        (ResidueField (v.comap H.subtype).valuationSubring) (ResidueField v.valuationSubring)

theorem henselizedGaussGraphInput_of_finite_extension_reference (K : Type) [Field K] [IsAlgClosed K]
    (hfinite : FiniteHenselianExtensionReference) : HenselizedGaussGraphInput K := by
  intro G _ v _ E _ n m x y hx hGauss hy
  let F := IntermediateField.adjoin E (Set.range x)
  obtain ⟨d⟩ := exists_embedded_valuation_henselization v F.toSubfield
  let H := d.field
  letI : Algebra F H := (Subfield.inclusion d.contains).toAlgebra
  letI : IsScalarTower F H K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra.IsAlgebraic F H := d.algebraic
  let L := (IntermediateField.adjoin H (Set.range y)).toSubfield
  have hHL : H ≤ L := fun a ha => (IntermediateField.adjoin H (Set.range y)).algebraMap_mem ⟨a, ha⟩
  letI : Algebra H L := (Subfield.inclusion hHL).toAlgebra
  letI : FiniteDimensional H L := IntermediateField.finiteDimensional_adjoin (by
    rintro z ⟨i, rfl⟩
    exact ((hy i).tower_top H).isIntegral)
  letI : Algebra F L := ((algebraMap H L).comp (algebraMap F H)).toAlgebra
  letI : IsScalarTower F H L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra.IsAlgebraic H L := Algebra.IsAlgebraic.of_finite H L
  letI : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.trans F H L
  let g : L →ₐ[F] K := { toRingHom := L.subtype, commutes' := fun _ => rfl }
  have hFL : F.toSubfield ≤ L := d.contains.trans hHL
  have hEF : E ≤ F.toSubfield := fun a ha => F.algebraMap_mem ⟨a, ha⟩
  have hEL : E ≤ L := hEF.trans hFL
  have hX (i : Fin n) : x i ∈ L := hFL (IntermediateField.subset_adjoin _ _ (Set.mem_range_self i))
  have hY (i : Fin m) : y i ∈ L := IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)
  let X := graphTuple L x hX
  let F' := IntermediateField.adjoin (E.comap L.subtype) (Set.range X)
  let H' := H.comap L.subtype
  let w := v.comap L.subtype
  have hmap : F'.toSubfield.map L.subtype = F.toSubfield := map_adjoin_range_subfield E L hEL X
  have hF' : F'.toSubfield = F.toSubfield.comap L.subtype := by
    ext z
    constructor
    · intro hz
      change z.val ∈ F.toSubfield
      rw [← hmap]
      exact ⟨z, hz, rfl⟩
    · intro hz
      change z.val ∈ F.toSubfield at hz
      rw [← hmap] at hz
      obtain ⟨a, ha, he⟩ := hz
      exact (Subtype.ext he : a = z) ▸ ha
  have hF'H : F'.toSubfield ≤ H' := by
    rw [hF']
    exact fun _ hz => d.contains hz
  have hF'L : Algebra.IsAlgebraic F' L := ⟨fun z =>
    isAlgebraic_in_nested_gaussField E L hEL X z ((Algebra.IsAlgebraic.isAlgebraic z).algHom g)⟩
  have hsame (z : L) : ∃ a ∈ F', v (a : K) = v (z : K) := by
    obtain ⟨c, hc⟩ := exists_same_value_of_isAlgebraic_over_gaussField v E x
      (fun i => (hx i).le) hGauss (z : K) ((Algebra.IsAlgebraic.isAlgebraic z).algHom g)
    let a : L := ⟨c.val, hEL c.property⟩
    have ha : a ∈ F'.toSubfield := by
      rw [hF']
      exact hEF c.property
    exact ⟨a, ha, hc.symm⟩
  let eH := graphCoefficientEquiv H L hHL
  letI : Algebra H' H := eH.toRingHom.toAlgebra
  letI : IsScalarTower H' H L := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  letI : Module.Finite H' H := Module.Finite.of_surjective (Algebra.linearMap H' H) eH.surjective
  letI : FiniteDimensional H' L := Module.Finite.trans (R := H') H L
  let r := (valuationSubringInside_equiv w H').trans
    ((valuationRingInside_comap_equiv v H L hHL).trans (valuationSubringInside_equiv v H).symm)
  letI : HenselianLocalRing (v.comap H.subtype).valuationSubring := d.henselian
  letI : HenselianLocalRing (w.comap H'.subtype).valuationSubring := henselian_of_ringEquiv r.symm
  letI : CharZero (ResidueField w.valuationSubring) := residueCharZero_of_subfield v L
  have hs (z : L) : ∃ c : H', w (c : L) = w z := by
    obtain ⟨a, ha, he⟩ := hsame z
    exact ⟨⟨a, hF'H ha⟩, he⟩
  obtain ⟨hHen, hDegree⟩ := hfinite L G w H' hs
  have hEt : EtaleCovered (valuationRingInside w F'.toSubfield) (valuationRingInside w H')
      (valuationRingInside_mono w hF'H) := by
    simpa only [hF'] using etaleCovered_comap_valuationRingInside v F.toSubfield H L d.contains hHL d.etaleCover
  refine ⟨?_⟩
  exact {
    field := L
    coefficients := hEL
    input_mem := hX
    output_mem := hY
    henselization := H'
    contains_gauss_field := hF'H
    algebraic_graph := hF'L
    finite_graph := inferInstance
    henselian_graph := hHen
    residue_charZero := inferInstance
    etale_cover := hEt
    immediate := fun z _ => hsame z
    residue_degree := hDegree
  }


theorem acvf_henselizedGaussGraphInput_of_finite_extension_reference
    {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] (hfinite : FiniteHenselianExtensionReference) :
    HenselizedGaussGraphInput (VFType (M := M)) := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  exact henselizedGaussGraphInput_of_finite_extension_reference _ hfinite

end SpecialTransformations.Section9
