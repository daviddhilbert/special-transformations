import Section8.IsolationGeometry
import Section4.VFAlgebraicCoordinates

/-! Lemma 8.2 on the actual VF sorts of the canonical presentation.
The exceptional set is formed over the original base. -/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] {n m : ℕ}

def isolatedInputs (G : Set (Fin n ⊕ Fin m → M)) : Set (Fin n → M) :=
  {a | ∃ t : Fin 2 → M, Sum.elim a t ∈ inputIsolation G}

theorem isolatedInputs_definable {S : Set M} {G : Set (Fin n ⊕ Fin m → M)}
    (hG : S.Definable LRV G) : S.Definable LRV (isolatedInputs G) :=
  (inputIsolation_definable hG).exists_of_finite

noncomputable def isolatedInputsObject {S : Set M} {G : Set (Fin n ⊕ Fin m → M)}
    (hG : S.Definable LRV G) : DefSet (rawMixedSpace (M := M) n 0) S where
  carrier := {p | vfValues p.1 ∈ isolatedInputs G}
  definable := by
    let P := rawMixedSpace (M := M) n 0
    have h := (P.definable_domain S).inter
      ((isolatedInputs_definable hG).preimage_comp (Sum.inl : Fin n → Fin n ⊕ Fin 0))
    change S.Definable LRV (P.preimage {p | vfValues p.1 ∈ isolatedInputs G})
    convert h using 1
    ext z
    have he (hz : z ∈ P.domain) : vfValues (P.decode ⟨z, hz⟩).1 = z ∘ Sum.inl :=
      funext (fun i => congrFun (mixedValues_decode ⟨z, hz⟩) (.inl i))
    constructor
    · rintro ⟨hz, hmem⟩
      exact ⟨hz, Eq.mp (congrArg (fun x => x ∈ isolatedInputs G) (he hz)) hmem⟩
    · rintro ⟨hz, hmem⟩
      exact ⟨hz, Eq.mpr (congrArg (fun x => x ∈ isolatedInputs G) (he hz)) hmem⟩

private theorem defSet_eq_of_carrier_eq {P : Space LRV M} {S : Set M}
    {A B : DefSet P S} (h : A.carrier = B.carrier) : A = B := by
  cases A
  cases B
  cases h
  rfl

variable [hM : M ⊨ Axioms.ACVF]

theorem mem_isolatedInputs_iff
    (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (a : Fin n → VFType (M := M)) :
    vfValues a ∈ isolatedInputs (vfGraph f) ↔
      ∃ r s : VFType (M := M), r ≠ 0 ∧ s ≠ 0 ∧
        ∀ b : Fin n → VFType (M := M),
          vfValues b ∈ uniformBall (vfValues a) r.val →
          vfValues (f b) ∈ uniformBall (vfValues (f a)) s.val → b = a := by
  constructor
  · rintro ⟨t, ht⟩
    have h := ((mem_fixedIsolation_vfGraph_iff f a t).mp ht).2.1
    obtain ⟨r, hrt⟩ := CanonicalRV.encodedRv_surjective ⟨t 0, (h 0).1⟩
    obtain ⟨s, hst⟩ := CanonicalRV.encodedRv_surjective ⟨t 1, (h 1).1⟩
    have hr' : iRv r.val = t 0 := congrArg Subtype.val hrt
    have hs' : iRv s.val = t 1 := congrArg Subtype.val hst
    have hr : r ≠ 0 := fun h0 => (h 0).2 (hr'.symm.trans ((CanonicalRV.encodedRv_zero_iff r).mpr h0))
    have hs : s ≠ 0 := fun h0 => (h 1).2 (hs'.symm.trans ((CanonicalRV.encodedRv_zero_iff s).mpr h0))
    have he : ![iRv r.val, iRv s.val] = t := by
      funext i
      fin_cases i
      · exact hr'
      · exact hs'
    exact ⟨r, s, hr, hs, (mem_fixedIsolation_iff_unique f a r s hr hs).mp (he.symm ▸ ht)⟩
  · rintro ⟨r, s, hr, hs, h⟩
    exact ⟨![iRv r.val, iRv s.val], (mem_fixedIsolation_iff_unique f a r s hr hs).mpr h⟩

/-- The graph isolation set has strictly smaller VF dimension than the
positive input arity, using the Section 4 dimension in the normalized
language. `hΔ` is the Section 4 presentation condition for the auxiliary
Gamma space. -/
theorem lemma_8_2 (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : Space LRV M) (hΔ : Δ.RVCoded) (hn : 0 < n)
    (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (hf : S.Definable LRV (vfGraph f)) : vfDim Δ (isolatedInputsObject hf) < n := by
  classical
  let A := isolatedInputsObject hf
  change vfDim Δ A < n
  by_cases hne : A.carrier.Nonempty
  · apply lt_of_le_of_ne (vfDim_le_arity Δ A)
    intro hdim
    obtain ⟨a, ha⟩ := exists_independent_of_full_dimension hc hs hsmall Δ hΔ A hne hdim
    obtain ⟨t, ht⟩ := a.property
    obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
    letI := hΓ
    letI : Valued (VFType (M := M)) Γ := Valued.mk' v
    exact independent_not_isolated hv hc hf hn a.val.1 ha t ht
  · have hA : A.carrier = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have he : A = DefSet.empty (rawMixedSpace (M := M) n 0) S :=
      defSet_eq_of_carrier_eq hA
    have hz : vfDim Δ (DefSet.empty (rawMixedSpace (M := M) n 0) S) = 0 :=
      Dimension.dim_empty rawVFSpace (AuxiliaryCoordinates.space Δ) (.rv 0)
    rw [he, hz]
    exact hn

end SpecialTransformations.Section8
