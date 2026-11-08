import Section3.GuardedRVLiterals

/-!
# Guarded monomial coefficients in the original VF subfield

Given representatives of the named RV parameters in the original subfield,
the coefficient of every ordinary Laurent monomial belongs to that same
subfield. The free variables still range over the ambient VF. This is an
identity for the released totalized evaluation; the rational pole and
residue-domain guards are retained separately by the normal form.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GuardedRVNormalForm

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

theorem ringTerm_realize_map {R S ι : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : ι → R) (t : Language.ring.Term ι) :
    f (t.realize a) = t.realize (fun i => f (a i)) := by
  induction t with
  | var i => rfl
  | func g ts ih => cases g <;> simp_all [Term.realize]

variable {M I R V : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def originalMonomialCoefficient (E : Subfield (VFType (M := M)))
    (T : Monomial I R V) (a : I → E) (r : R → E) : E :=
  (T.numerator.realize a / T.denominator.realize a) *
    T.coefficient.prod (fun i m => r i ^ m)

theorem monomial_rawEval_eq_encoded (E : Subfield (VFType (M := M)))
    (T : Monomial I R V) (a : I → E) (r : R → E) (x : V → VFType (M := M)) :
    T.rawEval (fun i => (a i : VFType (M := M)))
      (fun i => CanonicalRV.encodedRv (r i : VFType (M := M)))
      (fun i => CanonicalRV.encodedRv (x i)) =
    CanonicalRV.encodedRv ((originalMonomialCoefficient E T a r : VFType (M := M)) *
      T.powers.prod (fun i m => x i ^ m)) := by
  change T.rawEval (fun i => E.subtype (a i))
      (fun i => RVOperations.rvHom (E.subtype (r i))) (fun i => RVOperations.rvHom (x i)) =
    RVOperations.rvHom (E.subtype (originalMonomialCoefficient E T a r) *
      T.powers.prod (fun i m => x i ^ m))
  rw [Monomial.rawEval_rational]
  simp only [originalMonomialCoefficient, Finsupp.prod, map_mul, map_div₀,
    map_prod, map_zpow₀, ringTerm_realize_map]

end SpecialTransformations.Section7
