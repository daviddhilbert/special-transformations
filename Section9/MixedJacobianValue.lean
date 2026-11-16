module

public import Section9.MixedDerivativeFormula
public import Section4.FunctionalRelations
public import Section4.VFRealFibres

@[expose] public section

/-! The full mixed Jacobian as a definable VF value, with zero on the
locus where a full derivative is absent. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
local notation "VF" => VFType (M := M)

variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) n s) S}

private def fullJacobianDomain (f : Map A B) : Set ((Fin n ⊕ Fin r) → M) :=
  (fun z => z ∘ Sum.inl) '' mixedJacobianCodes f

def totalMixedJacobianCodes (f : Map A B) : Set (((Fin n ⊕ Fin r) ⊕ Fin 1) → M) :=
  mixedJacobianCodes f ∪ {z | z ∘ Sum.inl ∉ fullJacobianDomain f ∧ z (.inr 0) = iVFZero}

theorem totalMixedJacobianCodes_definable (hn : 0 < n) (f : Map A B) :
    S.Definable LRV (totalMixedJacobianCodes f) := by
  have h := mixedJacobianCodes_definable hn f
  have hD : S.Definable LRV (fullJacobianDomain f) := h.image_comp Sum.inl
  have hz : S.DefinableFun LRV (fun _ : ((Fin n ⊕ Fin r) ⊕ Fin 1) → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  exact h.union ((hD.compl.preimage_comp Sum.inl).inter ((Set.DefinableFun.proj LRV).ofPred_eq hz))

theorem mem_totalMixedJacobianCodes_iff (f : Map A B) (p : A) (J : VF) :
    Sum.elim (mixedValues p.val) (fun _ : Fin 1 => J.val) ∈ totalMixedJacobianCodes f ↔
      (∃ L, HasMixedVFDerivativeAt f p L ∧ (LinearMap.toMatrix' L).det = J) ∨
      (¬ ∃ L, HasMixedVFDerivativeAt f p L) ∧ J = 0 := by
  have hD : mixedValues p.val ∈ fullJacobianDomain f ↔ ∃ L, HasMixedVFDerivativeAt f p L := by
    constructor
    · rintro ⟨z, ⟨q, hq, L, hL, _⟩, hz⟩
      have he : q = p := Subtype.ext (mixedValues_injective (hq.trans hz))
      exact ⟨L, he ▸ hL⟩
    · rintro ⟨L, hL⟩
      exact ⟨Sum.elim (mixedValues p.val) (fun _ => (LinearMap.toMatrix' L).det.val),
        ⟨p, rfl, L, hL, rfl⟩, rfl⟩
  apply or_congr
  · constructor
    · rintro ⟨q, hq, L, hL, hJ⟩
      have he : q = p := Subtype.ext (mixedValues_injective hq)
      exact ⟨L, he ▸ hL, Subtype.ext hJ⟩
    · rintro ⟨L, hL, rfl⟩
      exact ⟨p, rfl, L, hL, rfl⟩
  · change (mixedValues p.val ∉ fullJacobianDomain f ∧ J.val = (0 : VF).val) ↔ _
    exact and_congr (not_congr hD) Subtype.val_inj

theorem existsUnique_totalMixedJacobianValue (f : Map A B) (p : A) :
    ∃! J : VF, Sum.elim (mixedValues p.val) (fun _ : Fin 1 => J.val) ∈ totalMixedJacobianCodes f := by
  classical
  by_cases h : ∃ L, HasMixedVFDerivativeAt f p L
  · obtain ⟨L, hL⟩ := h
    refine ⟨(LinearMap.toMatrix' L).det, (mem_totalMixedJacobianCodes_iff f p _).mpr
      (Or.inl ⟨L, hL, rfl⟩), fun J hJ => ?_⟩
    rcases (mem_totalMixedJacobianCodes_iff f p _).mp hJ with ⟨D, hD, rfl⟩ | hzero
    · obtain ⟨F, hF, hf⟩ := hL
      obtain ⟨G, hG, hg⟩ := hD
      exact HasMixedVFJacobianAt.unique ⟨G, hG, hg.hasJacobianAt⟩ ⟨F, hF, hf.hasJacobianAt⟩
    · exact (hzero.1 ⟨L, hL⟩).elim
  · refine ⟨0, (mem_totalMixedJacobianCodes_iff f p _).mpr (Or.inr ⟨h, rfl⟩), fun J hJ => ?_⟩
    rcases (mem_totalMixedJacobianCodes_iff f p _).mp hJ with ⟨L, hL, _⟩ | hzero
    · exact (h ⟨L, hL⟩).elim
    · exact hzero.2

theorem exists_totalMixedJacobianMap_of_pos (hn : 0 < n) (f : Map A B) :
    ∃ j : Map A (DefSet.univ (rawVFSpace (M := M) 1) S),
      ∀ p L, HasMixedVFDerivativeAt f p L → (j p).val 0 = (LinearMap.toMatrix' L).det := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawVFSpace (M := M) 1
  let R (x : P.Carrier) (y : Q.Carrier) :=
    x ∈ A.carrier ∧ Sum.elim (mixedValues x) (fun i => (y i).val) ∈ totalMixedJacobianCodes f
  have hR : P.RelationDefinable Q S R := by
    have h := (A.definable.preimage_comp (Sum.inl : P.Index → P.Index ⊕ Q.Index)).inter
      (((Q.domain_definable.mono (Set.empty_subset S)).preimage_comp Sum.inr).inter
        (totalMixedJacobianCodes_definable hn f))
    change S.Definable LRV (P.relation Q R)
    convert h using 1
    ext z
    constructor
    · rintro ⟨hx, hy, hA, hz⟩
      refine ⟨⟨hx, hA⟩, hy, ?_⟩
      change Sum.elim (mixedValues (P.decode ⟨_, hx⟩)) (vfValues (Q.decode ⟨_, hy⟩)) ∈ _ at hz
      rw [mixedValues_decode, vfValues_decode] at hz
      exact (Sum.elim_comp_inl_inr z) ▸ hz
    · rintro ⟨⟨hx,hA⟩, hy, hz⟩
      refine ⟨hx, hy, hA, ?_⟩
      change Sum.elim (mixedValues (P.decode ⟨_, hx⟩)) (vfValues (Q.decode ⟨_, hy⟩)) ∈ _
      rw [mixedValues_decode, vfValues_decode]
      exact (Sum.elim_comp_inl_inr z).symm ▸ hz
  have hdom (x y) (h : R x y) : x ∈ A.carrier ∧ y ∈ (DefSet.univ Q S).carrier :=
    ⟨h.1, Set.mem_univ _⟩
  have hcode (y : Q.Carrier) : (fun i => (y i).val) = fun _ => (y 0).val := by
    funext i
    fin_cases i
    rfl
  have htotal (p : A) : ∃ y, R p.val y := by
    obtain ⟨J, hJ, _⟩ := existsUnique_totalMixedJacobianValue f p
    exact ⟨fun _ => J, p.property, hJ⟩
  have huniq (x y z) (hy : R x y) (hz : R x z) : y = z := by
    obtain ⟨J, _, hJ⟩ := existsUnique_totalMixedJacobianValue f ⟨x, hy.1⟩
    have hy' := hy.2
    have hz' := hz.2
    rw [hcode y] at hy'
    rw [hcode z] at hz'
    funext i
    fin_cases i
    exact (hJ _ hy').trans (hJ _ hz').symm
  let J : Map A (DefSet.univ Q S) := Map.ofFunctionalRelation hR hdom htotal huniq
  refine ⟨J, fun p L hL => ?_⟩
  have he := huniq p.val (J p).val (fun _ => (LinearMap.toMatrix' L).det)
    (Map.ofFunctionalRelation_graph hR hdom htotal huniq p)
    ⟨p.property, (mem_totalMixedJacobianCodes_iff f p _).mpr (Or.inl ⟨L, hL, rfl⟩)⟩
  exact congrFun he 0

theorem exists_totalMixedJacobianMap (f : Map A B) :
    ∃ j : Map A (DefSet.univ (rawVFSpace (M := M) 1) S),
      ∀ p L, HasMixedVFDerivativeAt f p L → (j p).val 0 = (LinearMap.toMatrix' L).det := by
  by_cases hn : 0 < n
  · exact exists_totalMixedJacobianMap_of_pos hn f
  have hzero : n = 0 := by omega
  subst n
  let P := rawMixedSpace (M := M) 0 r
  let Q := rawVFSpace (M := M) 1
  let C (z : P.Index → M) : Q.Index → M := fun _ => iVFOne
  have hdom (z : P.domain) : C z.val ∈ Q.domain := ⟨fun _ => (1 : VF), rfl⟩
  let J : Map A (DefSet.univ Q S) := Map.ofCodes A (fun _ _ => (1 : VF)) C
    (fun _ => DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfOne Fin.elim0 (fun i => i.elim0))) hdom
    (fun z => vfValues_injective (vfValues_decode ⟨C z.val,hdom z⟩))
  refine ⟨J, fun p L hL => ?_⟩
  obtain ⟨F, hF, hD⟩ := hL
  exact (hasMixedVFJacobianAt_zero_arity f p).unique ⟨F, hF, hD.hasJacobianAt⟩

end SpecialTransformations.Section9
