module

public import StacksFrontier.RingTheory.Henselian.Henselization.Existence
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty

@[expose] public section

open CategoryTheory IsLocalRing

namespace SpecialTransformations.Section9

theorem exists_ordinaryHenselization_local_map (A S : Type)
    [CommRing A] [IsLocalRing A] [CommRing S] [HenselianLocalRing S]
    [Algebra A S] [IsLocalHom (algebraMap A S)] :
    ∃ (T : Type) (rT : CommRing T), letI := rT
      ∃ aT : Algebra A T, letI := aT
        ∃ (_ : IsLocalRing T) (_ : IsLocalHom (algebraMap A T)),
          HenselianLocalRing T ∧ (CommAlgCat.etale A).ind.{0} (CommAlgCat.of A T) ∧
          ∃ f : T →ₐ[A] S, IsLocalHom f := by
  obtain ⟨T, rT, aT, lT, hlocal, hH, hInd, _, hRes⟩ := IsLocalRing.exists_henselization A
  letI := rT
  letI := aT
  letI := lT
  letI := hlocal
  let e : CommAlgCat.of A T ≅ CommAlgCat.of A (ULift T) := CommAlgCat.isoMk ULift.algEquiv.symm
  have hInd' : (CommAlgCat.etale A).ind (CommAlgCat.of A (ULift T)) :=
    ((CommAlgCat.etale A).ind).prop_of_iso e hInd
  let f : T →ₐ[A] S := HenselianLocalRing.indEtaleAlgHom hInd' hRes.surjective
  exact ⟨T, rT, aT, lT, hlocal, hH, hInd, f,
    HenselianLocalRing.isLocalHom_indEtaleAlgHom hInd' hRes.surjective⟩

end SpecialTransformations.Section9
