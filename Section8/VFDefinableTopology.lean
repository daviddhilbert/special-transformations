module

public import Section8.VFNeighbourhoods
public import Section8.NeighbourhoodRelations
public import Section4.FullDimension

@[expose] public section

/-! Closure in the valuation topology is definable over the same base.
In positive VF arity, closure preserves the strict dimension drop. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] {n : ℕ}

def vfRawUniverse (n : ℕ) : Set (Fin n → M) := {x | ∀ i, iVF (x i)}

theorem vfRawUniverse_definable (S : Set M) (n : ℕ) : S.Definable LRV (vfRawUniverse n) := by
  change S.Definable LRV {z : Fin n → M | ∀ i, iVF (z i)}
  rw [Set.ofPred_forall]
  exact Set.definable_iInter_of_finite (fun i => ((definableAt_sort S .vf).raw_definable).preimage_comp
    (fun _ : Fin 1 => i))

def vfRawClosure (A : Set (Fin n → M)) : Set (Fin n → M) :=
  {a | a ∈ vfRawUniverse n ∧ ∀ r : M, iVF r → r ≠ iVFZero →
    ∃ x ∈ A, x ∈ uniformBall a r}

theorem vfRawClosure_definable {S : Set M} {A : Set (Fin n → M)}
    (hA : S.Definable LRV A) : S.Definable LRV (vfRawClosure A) := by
  let Z := Fin n ⊕ Fin 1
  let W := Z ⊕ Fin n
  let idx : (Fin n ⊕ Fin n) ⊕ Fin 1 → W := Sum.elim
    (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)
  have hHit := ((hA.preimage_comp (Sum.inr : Fin n → W)).inter
    ((uniformBallRelation_definable S n).preimage_comp idx)).exists_of_finite
  have hsort := ((definableAt_sort S .vf).raw_definable).preimage_comp (Sum.inr : Fin 1 → Z)
  have hzero : S.DefinableFun LRV (fun _ : Z → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have hne := ((Set.DefinableFun.proj LRV (i := (Sum.inr 0 : Z))).ofPred_eq hzero).compl
  have hBad := (hsort.inter (hne.inter hHit.compl)).exists_of_finite
  convert (vfRawUniverse_definable S n).inter hBad.compl using 1
  ext a
  change (a ∈ vfRawUniverse n ∧ ∀ r : M, iVF r → r ≠ iVFZero → ∃ x ∈ A, x ∈ uniformBall a r) ↔
    a ∈ vfRawUniverse n ∧ ¬ ∃ t : Fin 1 → M, iVF (t 0) ∧ t 0 ≠ iVFZero ∧
      ¬ ∃ x ∈ A, x ∈ uniformBall a (t 0)
  refine and_congr_right (fun _ => ⟨?_, ?_⟩)
  · rintro h ⟨t, ht, ht₀, hno⟩
    exact hno (h (t 0) ht ht₀)
  · intro h r hr hr₀
    by_contra hno
    exact h ⟨![r], hr, hr₀, hno⟩

variable [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem mem_vfRawClosure_iff
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (Fin n → M)) (a : Fin n → VFType (M := M)) :
    vfValues a ∈ vfRawClosure A ↔ a ∈ closure {x | vfValues x ∈ A} := by
  rw [mem_closure_iff_nhds]
  constructor
  · intro ha U hU
    obtain ⟨r, hr, hsub⟩ := exists_uniformBall_subset_of_mem_nhds hv a hU
    obtain ⟨z, hz, hzB⟩ := ha.2 r.val r.property (fun h => hr (Subtype.ext h))
    let x : Fin n → VFType (M := M) := fun i => ⟨z i, (hzB i).2.1⟩
    exact ⟨x, hsub hzB, hz⟩
  · intro ha
    refine ⟨fun i => (a i).property, fun r hr hr₀ => ?_⟩
    let s : VFType (M := M) := ⟨r, hr⟩
    have hs : s ≠ 0 := fun h => hr₀ (congrArg Subtype.val h)
    obtain ⟨x, hxB, hx⟩ := ha _ (uniformBall_mem_nhds hv a s hs)
    exact ⟨vfValues x, hx, hxB⟩

noncomputable def vfObjectOfRaw {S : Set M} {A : Set (Fin n → M)}
    (hA : S.Definable LRV A) : DefSet (rawMixedSpace (M := M) n 0) S where
  carrier := {p | vfValues p.1 ∈ A}
  definable := by
    let P := rawMixedSpace (M := M) n 0
    have h := (P.definable_domain S).inter (hA.preimage_comp (Sum.inl : Fin n → Fin n ⊕ Fin 0))
    change S.Definable LRV (P.preimage {p | vfValues p.1 ∈ A})
    convert h using 1
    ext z
    have he (hz : z ∈ P.domain) : vfValues (P.decode ⟨z, hz⟩).1 = z ∘ Sum.inl :=
      funext (fun i => congrFun (mixedValues_decode ⟨z, hz⟩) (.inl i))
    exact ⟨fun ⟨hz, hmem⟩ => ⟨hz, Eq.mp (congrArg (· ∈ A) (he hz)) hmem⟩,
      fun ⟨hz, hmem⟩ => ⟨hz, Eq.mpr (congrArg (· ∈ A) (he hz)) hmem⟩⟩

private theorem defSet_eq_of_carrier_eq {P : Space LRV M} {S : Set M}
    {A B : DefSet P S} (h : A.carrier = B.carrier) : A = B := by
  cases A
  cases B
  cases h
  rfl

theorem vfDim_lt_of_no_independent (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : Space LRV M) (hΔ : Δ.RVCoded) (hn : 0 < n) {A : Set (Fin n → M)}
    (hA : S.Definable LRV A)
    (hno : ∀ a : Fin n → VFType (M := M), vfValues a ∈ A → ¬ AlgebraicIndependent (vfParameterField S) a) :
    vfDim Δ (vfObjectOfRaw hA) < n := by
  let B := vfObjectOfRaw hA
  by_cases hne : B.carrier.Nonempty
  · apply lt_of_le_of_ne (vfDim_le_arity Δ B)
    intro he
    obtain ⟨a, ha⟩ := exists_independent_of_full_dimension hc hs hsmall Δ hΔ B hne he
    exact hno a.val.1 a.property ha
  · have he : B.carrier = (DefSet.empty (rawMixedSpace (M := M) n 0) S).carrier :=
      Set.not_nonempty_iff_eq_empty.mp hne
    have hb : B = DefSet.empty (rawMixedSpace (M := M) n 0) S := by
      exact defSet_eq_of_carrier_eq he
    change vfDim Δ B < n
    rw [hb]
    have hz : vfDim Δ (DefSet.empty (rawMixedSpace (M := M) n 0) S) = 0 :=
      Dimension.dim_empty rawVFSpace (AuxiliaryCoordinates.space Δ) (.rv 0)
    rw [hz]
    exact hn

theorem vfRawClosure_dim_lt_arity (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (Δ : Space LRV M) (hΔ : Δ.RVCoded) (hn : 0 < n)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : Set (Fin n → M)} (hA : S.Definable LRV A)
    (hdim : vfDim Δ (vfObjectOfRaw hA) < n) :
    vfDim Δ (vfObjectOfRaw (vfRawClosure_definable hA)) < n := by
  apply vfDim_lt_of_no_independent hc hs hsmall Δ hΔ hn
  intro a ha hInd
  have haA : vfValues a ∉ A := by
    intro h
    let x : vfObjectOfRaw hA := ⟨(a, Fin.elim0), h⟩
    have he : vfTupleTrdeg S a = n :=
      (tupleField_trdeg_eq_arity_iff (vfParameterField S) a).mpr hInd
    have hle := vfTupleTrdeg_le_vfDim hc Δ hΔ (vfObjectOfRaw hA) x
    change vfTupleTrdeg S a ≤ (vfDim Δ (vfObjectOfRaw hA) : Cardinal) at hle
    rw [he] at hle
    exact (not_le_of_gt hdim) (by exact_mod_cast hle)
  let C := vfRawUniverse n \ A
  have hCd := raw_definableOver_sorted hc S (fun _ => .vf) C
    ((vfRawUniverse_definable S n).inter hA.compl) (fun _ hx => hx.1)
  have hNear := independent_definable_mem_nhds hv S C hCd a hInd ⟨fun i => (a i).property, haA⟩
  have hcl := (mem_vfRawClosure_iff hv A a).mp ha
  obtain ⟨x, hx, hxA⟩ := mem_closure_iff_nhds.mp hcl _ hNear
  exact hx.2 hxA

end SpecialTransformations.Section8
