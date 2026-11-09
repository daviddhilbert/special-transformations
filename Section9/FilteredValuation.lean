import StacksFrontier.RingTheory.Henselian.Henselization.Existence
import Mathlib.RingTheory.Etale.Basic
import Section9.LocalFlatValuation
import Section9.AlgebraicLocalStage
open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace SpecialTransformations.Section9

private theorem exists_local_etale_valuation_stage {A R T S : Type}
    [CommRing A] [IsDomain A] [ValuationRing A] [CommRing R] [Algebra A R] [Algebra.Etale A R]
    [CommRing T] [Algebra A T] [IsLocalRing T] [CommRing S] [IsDomain S] [Algebra A S]
    (f : R →ₐ[A] T) (h : T →ₐ[A] S) (hinj : Function.Injective (algebraMap A S)) :
    ∃ (V : Type) (rV : CommRing V), letI := rV
      ∃ aV : Algebra A V, letI := aV
        ∃ (_ : IsDomain V) (_ : ValuationRing V), Algebra.IsAlgebraic A V ∧
          ∃ (j : R →+* V) (g : V →ₐ[A] T), g.toRingHom.comp j = f.toRingHom ∧
            Function.Injective (h.comp g) := by
  let m := (maximalIdeal T).comap f.toRingHom
  letI : m.IsPrime := Ideal.IsPrime.comap f.toRingHom
  let V := Localization.AtPrime m
  have hunit (x : m.primeCompl) : IsUnit (f x) := notMem_maximalIdeal.mp x.property
  let g : V →ₐ[A] T := IsLocalization.liftAlgHom (M := m.primeCompl) hunit
  let j : R →+* V := algebraMap R V
  have hgj : g.toRingHom.comp j = f.toRingHom := IsLocalization.lift_comp hunit
  let F := (h.comp g).toRingHom
  have hF : F.comp (algebraMap A V) = algebraMap A S := by
    apply RingHom.ext
    intro a
    exact (h.comp g).commutes a
  have hFA : Function.Injective (F.comp (algebraMap A V)) := by rwa [hF]
  have hAV : Function.Injective (algebraMap A V) := Function.Injective.of_comp (f := F) hFA
  letI : FaithfulSMul A V := (faithfulSMul_iff_algebraMap_injective A V).mpr hAV
  obtain ⟨hd, hv⟩ := local_valuationRing_of_flat_formallyUnramified A V
  letI : IsDomain V := hd
  exact ⟨V, inferInstance, inferInstance, hd, hv, algebraic_local_stage A V,
    j, g, hgj, local_stage_map_injective F hFA⟩

theorem indEtale_localRing_valuationRing {A T S : Type}
    [CommRing A] [IsDomain A] [ValuationRing A] [CommRing T] [Algebra A T] [IsLocalRing T]
    [CommRing S] [IsDomain S] [Algebra A S] (h : T →ₐ[A] S)
    (hAS : Function.Injective (algebraMap A S))
    (hind : (CommAlgCat.etale A).ind.{0} (CommAlgCat.of A T)) :
    Function.Injective h ∧ Algebra.IsAlgebraic A T ∧ ∃ (_ : IsDomain T), ValuationRing T := by
  obtain ⟨I, cI, hI, c, hc⟩ := hind
  letI := cI
  letI := hI
  have hpair (a b : T) : ∃ (V : Type) (rV : CommRing V), letI := rV
      ∃ (_ : IsDomain V) (_ : ValuationRing V),
        ∃ (g : V →+* T) (x y : V),
          g x = a ∧ g y = b ∧ Function.Injective (h.toRingHom.comp g) ∧ IsAlgebraic A a := by
    obtain ⟨i, x, hx⟩ := CommAlgCat.exists_app_eq c.isColimit a
    obtain ⟨j, y, hy⟩ := CommAlgCat.exists_app_eq c.isColimit b
    let k := IsFiltered.max i j
    let ik := IsFiltered.leftToMax i j
    let jk := IsFiltered.rightToMax i j
    let R : Type := c.diag.obj k
    let f : R →ₐ[A] T := (c.ι.app k).hom
    letI : Algebra.Etale A R := hc k
    obtain ⟨V, rV, aV, hd, hv, hAlg, j', g, hgj, hg⟩ := exists_local_etale_valuation_stage f h hAS
    letI := rV
    letI := aV
    have hcomp {l : I} (u : l ⟶ k) (z : c.diag.obj l) :
        f (c.diag.map u z) = c.ι.app l z := by
      have he := c.ι.naturality u
      change c.diag.map u ≫ c.ι.app k = c.ι.app l ≫ 𝟙 (CommAlgCat.of A T) at he
      exact ConcreteCategory.congr_hom he z
    have hga : g (j' (c.diag.map ik x)) = a := (RingHom.congr_fun hgj _).trans ((hcomp ik x).trans hx)
    refine ⟨V, rV, hd, hv, g.toRingHom, j' (c.diag.map ik x), j' (c.diag.map jk y), hga, ?_, hg, ?_⟩
    · exact (RingHom.congr_fun hgj _).trans ((hcomp jk y).trans hy)
    · rw [← hga]
      apply (hAlg.isAlgebraic (j' (c.diag.map ik x))).ringHom_of_comp_eq (RingHom.id A) g.toRingHom
      · exact fun _ _ h => h
      · apply RingHom.ext
        intro a
        exact (g.commutes a).symm
  have hinj : Function.Injective h := by
    intro a b hab
    obtain ⟨V, rV, _, _, g, x, y, rfl, rfl, hg, _⟩ := hpair a b
    letI := rV
    exact congrArg g (hg hab)
  letI : IsDomain T := hinj.isDomain h.toRingHom
  have hAlg : Algebra.IsAlgebraic A T := ⟨fun a => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := hpair a a
    exact h⟩
  have hPre : PreValuationRing T := ⟨fun a b => by
    obtain ⟨V, rV, hd, hv, g, x, y, rfl, rfl, _⟩ := hpair a b
    letI := rV
    letI := hd
    letI := hv
    obtain ⟨z, hxy | hyx⟩ := ValuationRing.cond x y
    · exact ⟨g z, Or.inl ((map_mul g x z).symm.trans (congrArg g hxy))⟩
    · exact ⟨g z, Or.inr ((map_mul g y z).symm.trans (congrArg g hyx))⟩⟩
  exact ⟨hinj, hAlg, inferInstance, { toPreValuationRing := hPre }⟩


end SpecialTransformations.Section9
