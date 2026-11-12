module

public import Section9.WeightedLiftJacobian
public import Section9.MixedJacobianValue
public import Section9.MixedDifferentiationAE

@[expose] public section

/-! A definable exception for the determinant value of a weighted lift.
The defining test compares the values of `J * ∏ xᵢ` and `∏ yᵢ` in VF,
so it introduces neither new parameters nor choices of Gamma codes. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9
open scoped BigOperators

namespace SpecialTransformations.Section10

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
local notation "VF" => VFType (M := M)
local notation "v" => Values.vfValueHom (M := M)

private theorem valueProducts_definable (S : Set M) (n : ℕ) :
    (((rawVFSpace (M := M) n).prod ((rawVFSpace n).prod (rawVFSpace 1)))).Definable S
      {p | v (p.2.2 0 * ∏ i, p.1 i) = v (∏ i, p.2.1 i)} := by
  classical
  let Q := (rawVFSpace (M := M) n).prod ((rawVFSpace n).prod (rawVFSpace 1))
  let x (i : Fin n) : Q.Index := .inl i
  let y (i : Fin n) : Q.Index := .inr (.inl i)
  let j : Q.Index := .inr (.inr (0 : Fin 1))
  let a : LRV.Term Q.Index := RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing
    (FreeCommRing.of j * ∏ i, FreeCommRing.of (x i)))
  let b : LRV.Term Q.Index := RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing
    (∏ i, FreeCommRing.of (y i)))
  have hd := (Q.definable_domain S).inter (termValueEq_definable S a b)
  have hEq (z : Q.Index → M) (hz : z ∈ Q.domain) :
      let p := Q.decode ⟨z, hz⟩
      termValueEq a b z ↔ v (p.2.2 0 * ∏ i, p.1 i) = v (∏ i, p.2.1 i) := by
    let p := Q.decode ⟨z, hz⟩
    let t : Q.Index → VF := Sum.elim p.1 (Sum.elim p.2.1 p.2.2)
    have hz' : z = fun i => (t i).val := by
      funext i
      rcases i with i | (i | i)
      · exact (congrFun (vfValues_decode ⟨z ∘ Sum.inl, hz.1⟩) i).symm
      · exact (congrFun (vfValues_decode ⟨z ∘ Sum.inr ∘ Sum.inl, hz.2.1⟩) i).symm
      · exact (congrFun (vfValues_decode ⟨z ∘ Sum.inr ∘ Sum.inr, hz.2.2⟩) i).symm
    have ha : a.realize z = (p.2.2 0 * ∏ i, p.1 i).val := by
      dsimp only [a]
      rw [hz', RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
      simp only [map_mul, map_prod, FreeCommRing.lift_of] <;> rfl
    have hb : b.realize z = (∏ i, p.2.1 i).val := by
      dsimp only [b]
      rw [hz', RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
      simp only [map_prod, FreeCommRing.lift_of] <;> rfl
    change termValueEq a b z ↔ _
    rw [termValueEq_realize, ha, hb]
    change (VFValued.predV (∏ i, p.2.1 i) (p.2.2 0 * ∏ i, p.1 i) ∧
      VFValued.predV (p.2.2 0 * ∏ i, p.1 i) (∏ i, p.2.1 i)) ↔ _
    rw [Values.vf_pred_iff_gamma_le, Values.vf_pred_iff_gamma_le]
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
  change S.Definable LRV (Q.preimage _)
  convert hd using 1
  ext z
  exact ⟨fun ⟨hz, h⟩ => ⟨hz, (hEq z hz).mpr h⟩, fun ⟨hz, h⟩ => ⟨hz, (hEq z hz).mp h⟩⟩

/-- If the determinant has the weighted value at every independent
source tuple, it has that value outside a same-base VF-small set. -/
theorem exists_weightedJacobian_exception [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hS : Cardinal.mk S < κ) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B)
    (hgeneric : ∀ p : A, AlgebraicIndependent (vfParameterField S) p.val.1 →
      ∃ J : VF, HasMixedVFJacobianAt f p J ∧
        v (J * ∏ i, p.val.1 i) = v (∏ i, (f p).val.1 i)) :
    ∃ Z : DefSet (rawMixedSpace (M := M) n r) S, vfDim (rawRVSpace (M := M) 1) Z < n ∧
      ∀ p : A, p.val ∉ Z.carrier → ∃ J : VF, HasMixedVFJacobianAt f p J ∧
        v (J * ∏ i, p.val.1 i) = v (∏ i, (f p).val.1 i) := by
  obtain ⟨D, hD⟩ := exists_totalMixedJacobianMap f
  let P := rawMixedSpace (M := M) n r
  let input := Map.fst (rawVFSpace n) (rawRVSpace r) S A
  let output := (Map.fst (rawVFSpace n) (rawRVSpace s) S B).comp f
  let F := input.pair (output.pair D)
  let H := {x : P.Carrier | ∃ p : A, p.val = x ∧
    v ((D p).val 0 * ∏ i, p.val.1 i) = v (∏ i, (f p).val.1 i)}
  have hH : P.Definable S H := F.definable_preimage (valueProducts_definable S n)
  let T := {x : P.Carrier | ∃ p : A, p.val = x ∧ ∃ L, HasMixedVFDerivativeAt f p L}
  have hT : P.Definable S T := mixedDifferentiabilityLocus_definable hn f
  let Z : DefSet P S := ⟨A.carrier \ (T ∩ H), A.definable.sdiff P (hT.inter P hH)⟩
  refine ⟨Z, ?_, ?_⟩
  · apply mixed_vfDim_lt_of_no_independent hc hs hS _ (rawRVSpace_rvCoded 1) hn Z
    intro p hp
    let a : A := ⟨p.val, p.property.1⟩
    let _ : Valued VF (Values.presentationType (M := M)) := Valued.mk' Values.presentationValuation
    obtain ⟨L, hL⟩ := mixedDifferentiableAt_of_independent hc hκ hs hS
      Values.presentation_compatible f a hp
    obtain ⟨J, hJ, hv⟩ := hgeneric a hp
    obtain ⟨G, hG, hder⟩ := hL
    have he := (HasMixedVFJacobianAt.unique ⟨G, hG, hder.hasJacobianAt⟩ hJ)
    have hval := (hD a L ⟨G, hG, hder⟩).trans he
    exact p.property.2 ⟨⟨a, rfl, L, G, hG, hder⟩, ⟨a, rfl, hval.symm ▸ hv⟩⟩
  · intro p hp
    have h : p.val ∈ T ∩ H := by
      by_contra hn'
      exact hp ⟨p.property, hn'⟩
    obtain ⟨a, ha, L, hL⟩ := h.1
    obtain ⟨b, hb, hval⟩ := h.2
    have he : a = p := Subtype.ext ha
    have he' : b = p := Subtype.ext hb
    subst a
    subst b
    have hdet := hD p L hL
    obtain ⟨G, hG, hder⟩ := hL
    exact ⟨_, ⟨G, hG, hder.hasJacobianAt⟩, hdet ▸ hval⟩

end SpecialTransformations.Section10
