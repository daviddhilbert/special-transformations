module

public import Section9.PartialDerivativeFormula
public import Section9.GenericDifferentiation

@[expose] public section

/-! Lemma 9.8 and Corollary 9.9 for a definable VF function. The
derivative graph is definable over the original parameters. Its
undefined locus is small, and generic continuity applies to the
derivative extended by zero off that graph. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}
local notation "VF" => VFType (M := M)

/-- The same-base partial derivative graph, in input and slope
coordinates. -/
def partialDerivativeGraph (f : (Fin n → VF) → Fin m → VF) (j : Fin n) (i : Fin m) :
    Set (Fin n ⊕ Fin 1 → M) :=
  {z | ∃ (a : Fin n → VF) (d : VF), HasVFPartialAt f a j i d ∧
    Sum.elim (vfValues a) ![d.val] = z}

theorem partialDerivativeGraph_definable {S : Set M}
    (f : (Fin n → VF) → Fin m → VF) (hf : S.Definable LRV (vfGraph f))
    (j : Fin n) (i : Fin m) : S.Definable LRV (partialDerivativeGraph f j i) := by
  let p : Fin n ⊕ Fin 1 → (Fin n ⊕ Fin m) ⊕ Fin 1 :=
    Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  convert (partialDerivativeCodes_definable hf j i).image_comp p using 1
  ext z
  constructor
  · rintro ⟨a, d, h, rfl⟩
    exact ⟨derivativeCode a (f a) d, (partialDerivativeCodes_iff f j i a d).mpr h, by
      funext k
      cases k <;> rfl⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨a, ha⟩ := hq.1
    let d : VF := ⟨q (.inr 0), hq.2.1⟩
    have he : derivativeCode a (f a) d = q := by
      funext k
      rcases k with k | k
      · exact congrFun ha k
      · fin_cases k
        rfl
    have h := (partialDerivativeCodes_iff f j i a d).mp (he.symm ▸ hq)
    exact ⟨a, d, h, by rw [← he]; funext k; cases k <;> rfl⟩

def partialDerivativeDomain (f : (Fin n → VF) → Fin m → VF) (j : Fin n) (i : Fin m) :
    Set (Fin n → M) :=
  (fun z : Fin n ⊕ Fin 1 → M => z ∘ Sum.inl) '' partialDerivativeGraph f j i

theorem partialDerivativeDomain_definable {S : Set M}
    (f : (Fin n → VF) → Fin m → VF) (hf : S.Definable LRV (vfGraph f))
    (j : Fin n) (i : Fin m) : S.Definable LRV (partialDerivativeDomain f j i) :=
  (partialDerivativeGraph_definable f hf j i).image_comp Sum.inl

theorem mem_partialDerivativeDomain_iff
    (f : (Fin n → VF) → Fin m → VF) (j : Fin n) (i : Fin m) (a : Fin n → VF) :
    vfValues a ∈ partialDerivativeDomain f j i ↔ ∃ d, HasVFPartialAt f a j i d := by
  constructor
  · rintro ⟨_, ⟨b, d, hd, rfl⟩, hba⟩
    exact ⟨d, vfValues_injective hba ▸ hd⟩
  · rintro ⟨d, hd⟩
    exact ⟨_, ⟨a, d, hd, rfl⟩, rfl⟩

private noncomputable def totalPartial (f : (Fin n → VF) → Fin m → VF)
    (j : Fin n) (i : Fin m) (a : Fin n → VF) : Fin 1 → VF := fun _ => by
  classical
  exact if h : ∃ d, HasVFPartialAt f a j i d then h.choose else 0

private theorem totalPartial_hasPartial (f : (Fin n → VF) → Fin m → VF)
    (j : Fin n) (i : Fin m) (a : Fin n → VF) (h : ∃ d, HasVFPartialAt f a j i d) :
    HasVFPartialAt f a j i (totalPartial f j i a 0) := by
  classical
  simpa only [totalPartial, dif_pos h] using h.choose_spec

private theorem totalPartialGraph_definable {S : Set M}
    (f : (Fin n → VF) → Fin m → VF) (hf : S.Definable LRV (vfGraph f))
    (j : Fin n) (i : Fin m) : S.Definable LRV (vfGraph (totalPartial f j i)) := by
  classical
  let Z := {z : Fin n ⊕ Fin 1 → M | z ∘ Sum.inl ∈ vfRawUniverse n ∧
    z ∘ Sum.inl ∉ partialDerivativeDomain f j i ∧ z (.inr 0) = iVFZero}
  have hZ : S.Definable LRV Z := by
    have hzero : S.DefinableFun LRV (fun _ : Fin n ⊕ Fin 1 → M => iVFZero) :=
      DefinableConstants.constant (DefinableConstants.function_symbol (L := LRV)
        Fn.vfZero Fin.elim0 (fun k => k.elim0))
    exact ((vfRawUniverse_definable S n).preimage_comp Sum.inl).inter
      (((partialDerivativeDomain_definable f hf j i).compl.preimage_comp Sum.inl).inter
        ((Set.DefinableFun.proj LRV (i := Sum.inr 0)).ofPred_eq hzero))
  convert (partialDerivativeGraph_definable f hf j i).union hZ using 1
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    by_cases h : ∃ d, HasVFPartialAt f a j i d
    · exact Or.inl ⟨a, totalPartial f j i a 0, totalPartial_hasPartial f j i a h,
        by
          funext k
          rcases k with k | k
          · rfl
          · fin_cases k
            rfl⟩
    · exact Or.inr ⟨fun k => (a k).property, (mem_partialDerivativeDomain_iff f j i a).not.mpr h,
        by simp only [Sum.elim_inr, vfValues, totalPartial, dif_neg h]; rfl⟩
  · rintro (⟨a, d, hd, rfl⟩ | ⟨hVF, hD, hz⟩)
    · have h := (totalPartial_hasPartial f j i a ⟨d, hd⟩).unique hd
      refine ⟨a, ?_⟩
      funext k
      rcases k with k | k
      · rfl
      · fin_cases k
        exact congrArg Subtype.val h
    · let a : Fin n → VF := fun k => ⟨z (.inl k), hVF k⟩
      have h := (mem_partialDerivativeDomain_iff f j i a).not.mp hD
      refine ⟨a, ?_⟩
      funext k
      rcases k with k | k
      · rfl
      · have hk : k = 0 := Subsingleton.elim _ _
        subst k
        change (totalPartial f j i a 0).val = z (.inr 0)
        rw [show totalPartial f j i a 0 = 0 from dif_neg h]
        exact hz.symm

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VFType (M := M)) G]

/-- The derivative exists and is continuous off a same-base definable
subset of smaller VF dimension. This gives Lemma 9.8 and Corollary 9.9
for each partial derivative. -/
theorem corollary_9_9 [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : (Fin n → VF) → Fin m → VF) (hf : S.Definable LRV (vfGraph f))
    (j : Fin n) (i : Fin m) :
    ∃ B : Set (Fin n → M), ∃ hB : S.Definable LRV B,
      vfDim (rawRVSpace (M := M) 1) (vfObjectOfRaw hB) < n ∧
      ∃ d : (Fin n → VF) → VF,
        (∀ a, vfValues a ∉ B → HasVFPartialAt f a j i (d a)) ∧
        ContinuousOn d {a | vfValues a ∉ B} := by
  let D := partialDerivativeDomain f j i
  let F := totalPartial f j i
  have hF := totalPartialGraph_definable f hf j i
  let C := continuityExceptionRaw (vfGraph F)
  let B := vfRawUniverse n \ D ∪ C
  have hB : S.Definable LRV B :=
    ((vfRawUniverse_definable S n).inter (partialDerivativeDomain_definable f hf j i).compl).union
      (continuityExceptionRaw_definable hF)
  refine ⟨B, hB, ?_, fun a => F a 0, ?_, ?_⟩
  · apply vfDim_lt_of_no_independent hc hs hsmall _ (rawRVSpace_rvCoded 1)
      (Nat.zero_lt_of_lt j.isLt) hB
    intro a ha hi
    obtain ⟨L, hL⟩ := differentiableAt_of_independent hc hκ hs hsmall hv f hf a hi
    rcases ha with hD | hC
    · exact hD.2 ((mem_partialDerivativeDomain_iff f j i a).mpr ⟨_, hL.hasPartialAt j i⟩)
    · have hFn := continuousAt_of_independent hc hκ hs hsmall hv F hF a hi
      let X := vfRawUniverse n \ continuousInputs (vfGraph F)
      have hX : S.Definable LRV X :=
        (vfRawUniverse_definable S n).inter (continuousInputs_definable hF).compl
      have hne : vfValues a ∉ X := fun h => h.2 ((mem_continuousInputs_iff hv F a).mpr hFn)
      let Y := vfRawUniverse n \ X
      have hY := raw_definableOver_sorted hc S (fun _ => .vf) Y
        ((vfRawUniverse_definable S n).inter hX.compl) (fun _ h => h.1)
      have hnear := independent_definable_mem_nhds hv S Y hY a hi ⟨fun k => (a k).property, hne⟩
      have hcl := (mem_vfRawClosure_iff hv X a).mp hC
      obtain ⟨b, hb, hbx⟩ := mem_closure_iff_nhds.mp hcl _ hnear
      exact hb.2 hbx
  · intro a ha
    exact totalPartial_hasPartial f j i a ((mem_partialDerivativeDomain_iff f j i a).mp (by
      by_contra h
      exact ha (Or.inl ⟨fun k => (a k).property, h⟩)))
  · intro a ha
    have hC : vfValues a ∉ C := fun h => ha (Or.inr h)
    have hCont : ContinuousAt F a := by
      apply (mem_continuousInputs_iff hv F a).mp
      by_contra h
      exact hC ((mem_vfRawClosure_iff hv _ a).mpr (subset_closure ⟨fun k => (a k).property, h⟩))
    exact ((continuous_apply 0).continuousAt.comp hCont).continuousWithinAt

/-- Every partial derivative of a definable VF function exists outside
a same-base definable set of smaller VF dimension. -/
theorem lemma_9_8 [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : (Fin n → VF) → Fin m → VF) (hf : S.Definable LRV (vfGraph f))
    (j : Fin n) (i : Fin m) :
    ∃ B : Set (Fin n → M), ∃ hB : S.Definable LRV B,
      vfDim (rawRVSpace (M := M) 1) (vfObjectOfRaw hB) < n ∧
      ∀ a, vfValues a ∉ B → ∃ d, HasVFPartialAt f a j i d := by
  obtain ⟨B, hB, hdim, d, hd, _⟩ := corollary_9_9 hc hκ hs hsmall hv f hf j i
  exact ⟨B, hB, hdim, fun a ha => ⟨d a, hd a ha⟩⟩

/-- A single same-base exception suffices for all partial derivatives.
In input arity zero there are no partial derivatives to check. -/
theorem continuouslyPartiallyDifferentiable_ae [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : (Fin n → VF) → Fin m → VF) (hf : S.Definable LRV (vfGraph f)) :
    ∃ B : Set (Fin n → M), ∃ hB : S.Definable LRV B,
      vfDim (rawRVSpace (M := M) 1) (vfObjectOfRaw hB) < n ∧
      ∀ (j : Fin n) (i : Fin m), ∃ d : (Fin n → VF) → VF,
        (∀ a, vfValues a ∉ B → HasVFPartialAt f a j i (d a)) ∧
        ContinuousOn d {a | vfValues a ∉ B} := by
  classical
  choose B hB hdim d hd hcont using
    fun p : Fin n × Fin m => corollary_9_9 hc hκ hs hsmall hv f hf p.1 p.2
  let C := ⋃ p : Fin n × Fin m, B p
  have hC : S.Definable LRV C := Set.definable_iUnion_of_finite hB
  refine ⟨C, hC, ?_, fun j i => ?_⟩
  · apply vfDim_lt_of_no_independent hc hs hsmall _ (rawRVSpace_rvCoded 1) hn hC
    intro a ha hi
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp ha
    let b : vfObjectOfRaw (hB p) := ⟨(a, Fin.elim0), hp⟩
    have he : vfTupleTrdeg S a = (n : Cardinal) :=
      (tupleField_trdeg_eq_arity_iff (vfParameterField S) a).mpr hi
    have hle := vfTupleTrdeg_le_vfDim hc _ (rawRVSpace_rvCoded 1) (vfObjectOfRaw (hB p)) b
    change vfTupleTrdeg S a ≤ _ at hle
    rw [he] at hle
    exact (not_le_of_gt (hdim p)) (by exact_mod_cast hle)
  · have hsub : {a : Fin n → VF | vfValues a ∉ C} ⊆ {a | vfValues a ∉ B (j, i)} :=
      fun _ ha hb => ha (Set.mem_iUnion.mpr ⟨(j, i), hb⟩)
    exact ⟨d (j, i), fun a ha => hd (j, i) a (hsub ha), (hcont (j, i)).mono hsub⟩

end SpecialTransformations.Section9
