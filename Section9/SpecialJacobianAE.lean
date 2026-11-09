import Section9.SpecialJacobianGeneric
import Section9.MixedDifferentiationAE

/-! The approved almost-everywhere form of Lemma 9.11, for the actual
Section 5 special bijections and their inverses. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n r s : ℕ}

theorem lemma_9_11_ae [CharZero (VFType (M := M))]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    {A : Section5.DefSet (M := M) S n r} {B : Section5.DefSet (M := M) S n s}
    (T : Section5.SpecialBijection A B) :
    ∃ (E : DefSet (rawMixedSpace (M := M) n r) S)
      (D : DefSet (rawMixedSpace (M := M) n s) S),
      E.carrier ⊆ (rawSpecialSet hc A).carrier ∧
      D.carrier ⊆ (rawSpecialSet hc B).carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧ vfDim (rawRVSpace (M := M) 1) D < n ∧
      (∀ p : A, p.val ∉ E.carrier → HasMixedVFJacobianAt T.toMap p 1) ∧
      (∀ p : B, p.val ∉ D.carrier → HasMixedVFJacobianAt T.inverseMap p 1) := by
  letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) :=
    Valued.mk' Values.presentationValuation
  obtain ⟨E, hE, hdimE, hforward⟩ := exists_mixedJacobianOne_exception hc hs hsmall hn
    (rawSpecialMap hc T.toMap)
    (specialChain_det_one_of_independent hc hκ hs hsmall Values.presentation_compatible T.chain)
  obtain ⟨D, hD, hdimD, hinverse⟩ := exists_mixedJacobianOne_exception hc hs hsmall hn
    (rawSpecialMap hc T.inverseMap)
    (specialInverse_det_one_of_independent hc hκ hs hsmall Values.presentation_compatible T)
  exact ⟨E, D, hE, hD, hdimE, hdimD, hforward, hinverse⟩

theorem lemma_9_11_zero_arity
    {A : Section5.DefSet (M := M) S 0 r} {B : Section5.DefSet (M := M) S 0 s}
    (T : Section5.SpecialBijection A B) :
    (∀ p : A, HasMixedVFJacobianAt T.toMap p 1) ∧
      ∀ p : B, HasMixedVFJacobianAt T.inverseMap p 1 :=
  ⟨hasMixedVFJacobianAt_zero_arity T.toMap, hasMixedVFJacobianAt_zero_arity T.inverseMap⟩

end SpecialTransformations.Section9
