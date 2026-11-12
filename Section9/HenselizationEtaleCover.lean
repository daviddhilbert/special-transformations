module

public import StacksFrontier.RingTheory.Henselian.Henselization.Existence
public import Section9.EtaleDerivationBound

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace SpecialTransformations.Section9

theorem etaleCovered_of_indEtale_of_surjective {K R : Type} [CommRing K] [CommRing R]
    (A B : Subring K) (hAB : A ≤ B) [Algebra A R]
    (f : letI : Algebra A B := (Subring.inclusion hAB).toAlgebra
      R →ₐ[A] B) (hf : Function.Surjective f)
    (h : (CommAlgCat.etale A).ind (CommAlgCat.of A R)) : EtaleCovered A B hAB := by
  letI : Algebra A B := (Subring.inclusion hAB).toAlgebra
  intro b
  obtain ⟨y, rfl⟩ := hf b
  obtain ⟨I, cI, hI, c, hc⟩ := h
  letI := cI
  letI := hI
  obtain ⟨i, x, hx⟩ := CommAlgCat.exists_app_eq c.isColimit y
  let T : Type := c.diag.obj i
  letI : Algebra.Etale A T := hc i
  exact ⟨T, inferInstance, inferInstance, inferInstance, f.comp (c.ι.app i).hom, x, congrArg f hx⟩


end SpecialTransformations.Section9
