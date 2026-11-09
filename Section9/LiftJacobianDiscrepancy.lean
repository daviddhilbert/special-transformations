import Section9.RVJacobianException
import Section9.LiftLabelRepresentatives

/-! Project the actual derivative discrepancy to the original labels.
This projection is definable even when the RV Jacobian itself is only
specified by its pointwise residue tangent relation. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}

theorem exists_liftJacobian_discrepancy
    (hn : 0 < n) (U V : RVObject (M := M) S n) (f : Map (rvLift U) (rvLift V))
    (ω : Map U.domain (DefSet.univ (rawRVSpace (M := M) 1) S)) :
    ∃ E : DefSet (rawRVSpace (M := M) U.arity) S, E.carrier ⊆ U.domain.carrier ∧
      ∀ u : U.domain, u.val ∈ E.carrier ↔
        ∃ p : rvLift U, liftLabelMap U p = u ∧
          ¬ ∃ L, HasMixedVFDerivativeAt f p L ∧
            CanonicalRV.encodedRv (LinearMap.toMatrix' L).det = (ω u).val 0 := by
  obtain ⟨H, hH⟩ := exists_mixedRVJacobian_good_locus hn f (ω.comp (liftLabelMap U))
  let A := (rvLift U).sdiff H
  let l := (liftLabelMap U).restrict (show A.carrier ⊆ (rvLift U).carrier from Set.diff_subset)
  refine ⟨l.image, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    exact (l p).property
  · intro u
    constructor
    · rintro ⟨p, he⟩
      let q : rvLift U := ⟨p.val, p.property.1⟩
      have hq : liftLabelMap U q = u := Subtype.ext he
      refine ⟨q, hq, ?_⟩
      rw [← hq]
      exact fun h => p.property.2 ((hH q).mpr h)
    · rintro ⟨p, hp, hbad⟩
      have hb : p.val ∉ H.carrier := by
        intro h
        apply hbad
        rw [← hp]
        exact (hH p).mp h
      exact ⟨⟨p.val, p.property, hb⟩, congrArg Subtype.val hp⟩

end SpecialTransformations.Section9
