import Section9.OrdinaryHenselization
import Section9.FilteredValuation
import Section9.HenselianRingTransport
import Section9.HenselizedValuationImage
import Section9.HenselizationEtaleCover
import Section9.GaussEvaluation
import Section7.ValuationHenselian

open CategoryTheory IsLocalRing

namespace SpecialTransformations.Section9

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

structure EmbeddedValuationHenselization (v : Valuation K Γ) (F : Subfield K) where
  field : Subfield K
  contains : F ≤ field
  henselian : HenselianLocalRing (v.comap field.subtype).valuationSubring
  etaleCover : EtaleCovered (valuationRingInside v F) (valuationRingInside v field)
    (valuationRingInside_mono v contains)
  algebraic : letI : Algebra F field := (Subfield.inclusion contains).toAlgebra
    Algebra.IsAlgebraic F field

theorem exists_embedded_valuation_henselization [IsAlgClosed K]
    (v : Valuation K Γ) (F : Subfield K) : Nonempty (EmbeddedValuationHenselization v F) := by
  let A := valuationRingInside v F
  let S := v.valuationSubring
  let eA := valuationSubringInside_equiv v F
  have hPre : PreValuationRing A := ⟨fun a b => by
    obtain ⟨d, hd | hd⟩ := ValuationRing.cond (eA.symm a) (eA.symm b)
    · exact ⟨eA d, Or.inl (by simpa only [map_mul, RingEquiv.apply_symm_apply] using congrArg eA hd)⟩
    · exact ⟨eA d, Or.inr (by simpa only [map_mul, RingEquiv.apply_symm_apply] using congrArg eA hd)⟩⟩
  letI : ValuationRing A := { toPreValuationRing := hPre }
  let j : A →+* S := (valuationRingInclusion v F).comp eA.symm.toRingHom
  letI : Algebra A S := j.toAlgebra
  have hj : Function.Injective (algebraMap A S) := fun a b h =>
    Subtype.ext (congrArg (fun x : S => x.val) h)
  letI : IsLocalHom eA.symm.toRingHom := isLocalHom_of_leftInverse eA.toRingHom eA.apply_symm_apply
  letI : IsLocalHom (algebraMap A S) := inferInstanceAs (IsLocalHom ((valuationRingInclusion v F).comp eA.symm.toRingHom))
  letI : HenselianLocalRing S := SpecialTransformations.Section7.valuationRing_henselian v
  obtain ⟨T, rT, aT, lT, hl, hH, hInd, f, hf⟩ := exists_ordinaryHenselization_local_map A S
  letI := rT
  letI := aT
  letI := lT
  letI := hl
  letI := hH
  letI : IsLocalHom f.toRingHom := ⟨fun a ha => hf.map_nonunit a ha⟩
  obtain ⟨hfi, hAlg, hdom, hval⟩ := indEtale_localRing_valuationRing f hj hInd
  letI := hdom
  letI := hval
  let g := v.valuationSubring.subtype.comp f.toRingHom
  have hg : Function.Injective g := Subtype.val_injective.comp hfi
  let i : FractionRing T →+* K := IsFractionRing.lift hg
  let H := i.fieldRange
  have he (a : A) : g (algebraMap A T a) = (a : K) := by
    exact congrArg Subtype.val (f.commutes a)
  have hAH (a : A) : (a : K) ∈ H := by
    refine ⟨algebraMap T (FractionRing T) (algebraMap A T a), ?_⟩
    exact (IsFractionRing.lift_algebraMap hg _).trans (he a)
  have hFH : F ≤ H := by
    intro z hz
    by_cases h : v z ≤ 1
    · exact hAH ⟨z, hz, h⟩
    · have hv : 1 < v z := lt_of_not_ge h
      have hz' : v z⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact (inv_le_one₀ (zero_lt_one.trans hv)).mpr hv.le
      simpa only [inv_inv] using H.inv_mem (hAH ⟨z⁻¹, F.inv_mem hz, hz'⟩)
  let B := valuationRingInside v H
  have hAB : A ≤ B := valuationRingInside_mono v hFH
  letI : Algebra A B := (Subring.inclusion hAB).toAlgebra
  have hR : g.range = B := localValuationRing_range_eq_intersection v f.toRingHom hg
  have hmem (t : T) : g t ∈ B := by rw [← hR]; exact ⟨t, rfl⟩
  let fB : T →ₐ[A] B :=
    { toRingHom := g.codRestrict B hmem
      commutes' := fun a => Subtype.ext (he a) }
  have hfB : Function.Bijective fB := ⟨fun _ _ h => hg (congrArg (fun x : B => x.val) h), fun b => by
    obtain ⟨t, ht⟩ := (show (b : K) ∈ g.range by rw [hR]; exact b.property)
    exact ⟨t, Subtype.ext ht⟩⟩
  let eB := (AlgEquiv.ofBijective fB hfB).toRingEquiv
  have hhen : HenselianLocalRing (v.comap H.subtype).valuationSubring :=
    henselian_of_ringEquiv (eB.trans (valuationSubringInside_equiv v H).symm)
  have hEt : EtaleCovered A B hAB := etaleCovered_of_indEtale_of_surjective A B hAB fB hfB.surjective hInd
  refine ⟨⟨H, hFH, hhen, hEt, ?_⟩⟩
  letI : Algebra F H := (Subfield.inclusion hFH).toAlgebra
  let jF : A →+* F :=
    { toFun := fun a => ⟨a.val, a.property.1⟩
      map_zero' := rfl, map_one' := rfl, map_add' := fun _ _ => rfl, map_mul' := fun _ _ => rfl }
  letI : Algebra A F := jF.toAlgebra
  letI : Algebra A H := ((algebraMap F H).comp jF).toAlgebra
  letI : IsScalarTower A F H := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra.IsAlgebraic A T := hAlg
  letI : Algebra.IsAlgebraic T (FractionRing T) := IsLocalization.isAlgebraic _ (nonZeroDivisors T)
  letI : Algebra.IsAlgebraic A (FractionRing T) := Algebra.IsAlgebraic.trans A T (FractionRing T)
  let r : FractionRing T →ₐ[A] H :=
    { toRingHom := i.codRestrict H.toSubring (fun x => ⟨x, rfl⟩)
      commutes' := fun a => Subtype.ext (by
        change i (algebraMap A (FractionRing T) a) = (a : K)
        rw [IsScalarTower.algebraMap_apply A T (FractionRing T)]
        exact (IsFractionRing.lift_algebraMap hg _).trans (he a)) }
  letI : Algebra.IsAlgebraic A H := ⟨fun z => by
    obtain ⟨x, hx⟩ := z.property
    have hz : r x = z := Subtype.ext hx
    rw [← hz]
    exact (Algebra.IsAlgebraic.isAlgebraic x).algHom r⟩
  exact Algebra.IsAlgebraic.extendScalars (show Function.Injective jF from
    fun a b h => Subtype.ext (congrArg (fun x : F => x.val) h))


end SpecialTransformations.Section9
