import Section9.LiftJacobianDiscrepancy
import Section9.GammaMixedJacobianValue
import Section9.GammaPointMaps
import Section5.GammaLiftRelation

/-! **Lemma (L).** The derivative discrepancy locus of a lift with a Gamma
graph, projected to the source labels, is Gamma-definable.

Gamma counterpart of `exists_liftJacobian_discrepancy`. The prescribed form
is assumed nonzero (as in Theorem 9.16, where its Gamma value is the Gamma
Jacobian). Then a point is good iff the RV reduction of the total mixed
Jacobian (zero where no derivative exists) equals the prescribed value, so
the Gamma total Jacobian (`gamma_total_mixed_jacobian_graph`) suffices. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput vfAt)

namespace SpecialTransformations.Section9.GammaLift

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}

theorem gamma_liftJacobian_discrepancy (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} (hn : 0 < n) (U V : RVObject (M := M) S n) (f : Map (rvLift U) (rvLift V))
    (hf : GammaGraphDefinable B (fun (p : Point (M := M) n U.arity) (q : Point (M := M) n V.arity) =>
      ∃ a : rvLift U, a.val = p ∧ (f a).val = q))
    (ω : Map U.domain (DefSet.univ (rawRVSpace (M := M) 1) S))
    (hω : GammaGraphDefinable B (fun (p : Point (M := M) 0 U.arity) (q : Point (M := M) 0 1) =>
      ∃ u : U.domain, u.val = p.2 ∧ (ω u).val = q.2))
    (hω0 : ∀ u, (ω u).val 0 ≠ 0) :
    ∃ E : DefSet (rawRVSpace (M := M) U.arity) S, E.carrier ⊆ U.domain.carrier ∧
      GammaSetDefinable B {p : Point (M := M) 0 U.arity | p.2 ∈ E.carrier} ∧
      ∀ u : U.domain, u.val ∈ E.carrier ↔
        ∃ p : rvLift U, liftLabelMap U p = u ∧
          ¬ ∃ L, HasMixedVFDerivativeAt f p L ∧
            CanonicalRV.encodedRv (LinearMap.toMatrix' L).det = (ω u).val 0 := by
  obtain ⟨E, hE, hchar⟩ := exists_liftJacobian_discrepancy hn U V f ω
  refine ⟨E, hE, ?_, hchar⟩
  have L := gammaLogicInput B
  have hT := gamma_total_mixed_jacobian_graph hc hn f hf
  have h1 := L.comp_graph hT (gamma_scalar_rv_graph (B := B))
  have h2 := L.comp_graph (gamma_label_graph (B := B) (n := n) (m := U.arity)) hω
  have hGood := L.image_graph (L.swap_graph (Section5.GammaGraphDefinable.inter h1 h2))
  have hDom := L.image_graph (L.swap_graph hf)
  have hE' := L.image_graph (L.restrict_graph (L.sdiff hDom hGood)
    (gamma_label_graph (B := B) (n := n) (m := U.arity)))
  convert hE' using 1
  ext y
  constructor
  · intro hy
    let u : U.domain := ⟨y.2, hE hy⟩
    obtain ⟨p, hp, hbad⟩ := (hchar u).mp hy
    have hpy : p.val.2 = y.2 := congrArg Subtype.val hp
    refine ⟨p.val, ⟨⟨_, p, rfl, rfl⟩, ?_⟩, ?_⟩
    · rintro ⟨w, ⟨z, ⟨hpA, hJ⟩, hw⟩, ⟨q, hq, u', hu', hw'⟩⟩
      have hu'u : u' = u := Subtype.ext (by rw [hu', hq]; exact hpy)
      subst hu'u
      have hval : CanonicalRV.encodedRv (vfAt z 0) = (ω u).val 0 := by
        have h₁ := congrArg (fun x : Point (M := M) 0 1 => x.2 0) hw
        have h₂ := congrFun hw' 0
        exact h₁.symm.trans h₂.symm
      have hpp : (⟨p.val, hpA⟩ : rvLift U) = p := rfl
      rcases (mem_totalMixedJacobianCodes_iff f p (vfAt z 0)).mp hJ with ⟨L', hL', hdet⟩ | ⟨_, h0⟩
      · exact hbad ⟨L', hL', by rw [hdet]; exact hval⟩
      · apply hω0 u
        rw [← hval, h0]
        exact Subtype.ext ((RVCalc.rv_zero_eq ‹M ⊨ Axioms.ACVF›).trans RVOperations.zero_val.symm)
    · rw [hpy]
      exact Prod.ext (funext (fun i => Fin.elim0 i)) rfl
  · rintro ⟨p, ⟨⟨q, a, ha, hq⟩, hng⟩, hy⟩
    subst ha
    have hy2 : y.2 = a.val.2 := congrArg Prod.snd hy
    let u := liftLabelMap U a
    have hu : u.val = y.2 := hy2.symm
    change y.2 ∈ E.carrier
    rw [← hu]
    refine (hchar u).mpr ⟨a, rfl, ?_⟩
    rintro ⟨L', hL', hdet⟩
    apply hng
    let J := (LinearMap.toMatrix' L').det
    refine ⟨(Fin.elim0, (ω u).val), ⟨((fun _ => J), Fin.elim0), ⟨a.property, ?_⟩, ?_⟩,
      ⟨(Fin.elim0, a.val.2), rfl, u, rfl, rfl⟩⟩
    · exact (mem_totalMixedJacobianCodes_iff f a J).mpr (Or.inl ⟨L', hL', rfl⟩)
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      funext i
      fin_cases i
      exact hdet.symm

end SpecialTransformations.Section9.GammaLift
