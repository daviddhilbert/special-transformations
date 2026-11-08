import Section7.Imported.EtaleLifting
import Section7.Imported.UnramifiedUniqueness

namespace SpecialTransformations.Section7

open IsLocalRing

theorem etale_residuePoint_injective
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] :
    Function.Injective
      ((Algebra.ofId R (ResidueField R)).comp : (S →ₐ[R] R) → S →ₐ[R] ResidueField R) := by
  intro f g h
  exact Imported.UnramifiedUniqueness.ext_of_quotient_eq R S (maximalIdeal R)
    (maximalIdeal_le_jacobson ⊥) h

theorem etale_residuePoint_bijective
    {R S : Type*} [CommRing R] [HenselianLocalRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] :
    Function.Bijective
      ((Algebra.ofId R (ResidueField R)).comp : (S →ₐ[R] R) → S →ₐ[R] ResidueField R) :=
  ⟨etale_residuePoint_injective, Imported.EtaleLifting.residuePoint_lifts⟩

end SpecialTransformations.Section7
