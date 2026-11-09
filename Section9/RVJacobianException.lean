import Section9.MixedDifferentiationAE
import Section9.MixedJacobianValue
import Section4.CodeMaps
import Section4.RVRestrictions

/-! A generic prescribed RV determinant yields one same-base VF-small
exception, using the definable graph of the full mixed determinant. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
local notation "VF" => VFType (M := M)

private noncomputable def encodedRvMap (S : Set M) :
    Map (DefSet.univ (rawVFSpace (M := M) 1) S) (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let P := rawVFSpace (M := M) 1
  let Q := rawRVSpace (M := M) 1
  let R (a : P.Carrier) : Q.Carrier := fun i => CanonicalRV.encodedRv (a i)
  let F (z : P.Index → M) : Q.Index → M := fun i => iRv (z i)
  have hF (z : P.domain) : rvValues (R (P.decode z)) = F z.val := by
    funext i
    change iRv ((P.decode z i).val) = iRv (z.val i)
    exact congrArg iRv (congrFun (vfValues_decode z) i)
  have hdom (z : P.domain) : F z.val ∈ Q.domain := ⟨R (P.decode z), hF z⟩
  refine Map.ofCodes _ R F (fun i => ?_) hdom (fun z => ?_)
  · exact (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (show S.DefinableMap LRV (fun z : Fin 1 → M => ![z i]) from
        fun j => by fin_cases j; exact Set.DefinableFun.proj LRV)
  · exact rvValues_injective ((rvValues_decode ⟨F z.val, hdom z⟩).trans (hF z).symm)

theorem exists_mixedRVJacobian_good_locus (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (ω : Map A (DefSet.univ (rawRVSpace (M := M) 1) S)) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S, ∀ p : A,
      p.val ∈ E.carrier ↔
        ∃ L, HasMixedVFDerivativeAt f p L ∧
          CanonicalRV.encodedRv (LinearMap.toMatrix' L).det = (ω p).val 0 := by
  obtain ⟨D, hD⟩ := exists_totalMixedJacobianMap f
  let P := rawMixedSpace (M := M) n r
  let Q := rawRVSpace (M := M) 1
  let v := (encodedRvMap S).comp D
  let h := v.pair ω
  have hDiag : (Q.prod Q).Definable S {z | z.1 = z.2} := by
    have he : (Q.prod Q).preimage {z | z.1 = z.2} = Q.relation Q Eq := by
      ext z
      exact ⟨by rintro ⟨⟨ha, hb⟩, he⟩; exact ⟨ha, hb, he⟩,
        by rintro ⟨ha, hb, he⟩; exact ⟨⟨ha, hb⟩, he⟩⟩
    change S.Definable LRV ((Q.prod Q).preimage {z | z.1 = z.2})
    rw [he]
    exact Q.diagonal_definable.mono (Set.empty_subset S)
  let H := {x | ∃ p : A, p.val = x ∧ (h p).val.1 = (h p).val.2}
  let G := {x | ∃ p : A, p.val = x ∧ ∃ L, HasMixedVFDerivativeAt f p L}
  have hH : P.Definable S H := h.definable_preimage hDiag
  have hG : P.Definable S G := mixedDifferentiabilityLocus_definable hn f
  have hgood (p : A) (L) (hL : HasMixedVFDerivativeAt f p L) :
      (h p).val.1 0 = CanonicalRV.encodedRv (LinearMap.toMatrix' L).det := by
    change CanonicalRV.encodedRv ((D p).val 0) = _
    rw [hD p L hL]
  refine ⟨⟨G ∩ H, hG.inter P hH⟩, fun p => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨p₁, hp₁, L, hL⟩, ⟨p₂, hp₂, he⟩⟩
    have h₁ : p₁ = p := Subtype.ext hp₁
    have h₂ : p₂ = p := Subtype.ext hp₂
    subst p₁
    subst p₂
    exact ⟨L, hL, (hgood p L hL).symm.trans (congrFun he 0)⟩
  · rintro ⟨L, hL, hJ⟩
    refine ⟨⟨p, rfl, L, hL⟩, ⟨p, rfl, ?_⟩⟩
    funext i
    fin_cases i
    exact (hgood p L hL).trans hJ

theorem exists_mixedRVJacobian_exception
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (ω : Map A (DefSet.univ (rawRVSpace (M := M) 1) S))
    (hgen : ∀ p : A, AlgebraicIndependent (vfParameterField S) p.val.1 →
      ∃ L, HasMixedVFDerivativeAt f p L ∧ CanonicalRV.encodedRv (LinearMap.toMatrix' L).det = (ω p).val 0) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S, E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧
      ∀ p : A, p.val ∉ E.carrier → ∃ J : VF, HasMixedVFJacobianAt f p J ∧
        CanonicalRV.encodedRv J = (ω p).val 0 := by
  obtain ⟨H, hH⟩ := exists_mixedRVJacobian_good_locus hn f ω
  let E := A.sdiff H
  refine ⟨E, Set.diff_subset, ?_, ?_⟩
  · apply mixed_vfDim_lt_of_no_independent hc hs hsmall _ (rawRVSpace_rvCoded 1) hn
    intro p hp
    let q : A := ⟨p.val, p.property.1⟩
    exact p.property.2 ((hH q).mpr (hgen q hp))
  · intro p hp
    have hp' : p.val ∈ H.carrier := by
      by_contra hh
      exact hp ⟨p.property, hh⟩
    obtain ⟨_, ⟨F, hF, hd⟩, hJ⟩ := (hH p).mp hp'
    exact ⟨_, ⟨F, hF, hd.hasJacobianAt⟩, hJ⟩

end SpecialTransformations.Section9
