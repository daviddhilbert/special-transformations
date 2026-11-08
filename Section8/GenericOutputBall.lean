import Section8.GenericContinuity
import Section3.SmallFiniteParameters
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-! Choose a generic centre inside a prescribed output ball.
Naming the new centre and an RV radius preserves independence of the
input. The resulting definable neighbourhood proves continuity there. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

private theorem independent_of_subfield_le {K : Type} [Field K] {ι : Type} {a : ι → K}
    {E F : Subfield K} (h : E ≤ F) (ha : AlgebraicIndependent F a) :
    AlgebraicIndependent E a := by
  letI := (Subfield.inclusion h).toAlgebra
  letI : IsScalarTower E F K := .of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap E F) :=
    fun _ _ he => Subtype.ext (congrArg (fun x : F => x.val) he)
  exact ha.restrictScalars hinj

theorem independent_over_tupleField_swap {K : Type} [Field K] (E : Subfield K)
    (a : Fin n → K) (b : Fin m → K)
    (ha : AlgebraicIndependent E a) (hb : AlgebraicIndependent (tupleField E a) b) :
    AlgebraicIndependent (tupleField E b) a := by
  rw [tupleField_eq_adjoin E a] at hb
  have hab := ha.sumElim_of_tower (S := IntermediateField.adjoin E (Set.range a))
    (by rintro _ ⟨i, rfl⟩; exact ⟨⟨a i, IntermediateField.subset_adjoin E _ (Set.mem_range_self i)⟩, rfl⟩)
    hb
  have hba : AlgebraicIndependent E (Sum.elim a b) := by
    convert hab.comp (Equiv.sumComm (Fin n) (Fin m)) (Equiv.sumComm _ _).injective using 1
    funext i
    cases i <;> rfl
  have h := (AlgebraicIndependent.sumElim_iff.mp hba).2.extendScalars
    (IntermediateField.adjoin E (Set.range b))
  rw [tupleField_eq_adjoin E b]
  exact h

theorem independent_snoc_slices {K : Type} [Field K] (E : Subfield K)
    (a : Fin n → K) (b : K) (h : AlgebraicIndependent E (Fin.snoc a b)) :
    AlgebraicIndependent (tupleField E (![b] : Fin 1 → K)) a ∧
      AlgebraicIndependent (tupleField E a) (![b] : Fin 1 → K) := by
  have hs : AlgebraicIndependent E (Sum.elim (![b] : Fin 1 → K) a) := by
    let e := (Equiv.sumComm (Fin 1) (Fin n)).trans
      (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
    convert h.comp e e.injective using 1
    funext i
    rcases i with i | i
    · fin_cases i
      have he : e (.inl 0) = Fin.last n := Fin.ext (by simp [e, finSumFinEquiv_apply_right])
      change b = Fin.snoc (α := fun _ => K) a b (e (.inl 0))
      rw [he, Fin.snoc_last]
    · have he : e (.inr i) = i.castSucc := rfl
      simp only [Function.comp_apply, he, Fin.snoc_castSucc, Sum.elim_inr]
  obtain ⟨ha, hb⟩ := AlgebraicIndependent.sumElim_iff.mp hs
  have hb' : AlgebraicIndependent (tupleField E a) (![b] : Fin 1 → K) := by
    rw [tupleField_eq_adjoin E a]
    exact hb.extendScalars (IntermediateField.adjoin E (Set.range a))
  exact ⟨independent_over_tupleField_swap E a ![b] ha hb', hb'⟩

theorem continuousAt_of_independent (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (hf : S.Definable LRV (vfGraph f)) (a : Fin n → VFType (M := M))
    (ha : AlgebraicIndependent (vfParameterField S) a) : ContinuousAt f a := by
  intro U hU
  obtain ⟨r, hr, hUr⟩ := exists_uniformBall_subset_of_mem_nhds hv (f a) hU
  let S₁ := S ∪ Set.range (vfValues a)
  let T := (S₁ ∪ Set.range (vfValues (f a))) ∪ {r.val}
  have hsmallT : Cardinal.mk T < κ :=
    small_union_finite hκ _ (small_union_range hκ _ (small_union_range hκ S hsmall _) _)
      _ (Set.finite_singleton _)
  let D : ValuedPolydisc (Valued.v : Valuation (VFType (M := M)) Γ) m :=
    ⟨f a, fun _ => r, fun _ => hr⟩
  have hD : T.Definable LRV (uniformBall (vfValues (f a)) r.val) := by
    change T.Definable LRV {z : Fin m → M | ∀ i, z i ∈ rawOpenBall (vfValues (f a) i) r.val}
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun i => (rawOpenBall_definable (S := T)
      (Or.inl (Or.inr (Set.mem_range_self i))) (Or.inr rfl)).preimage_comp (fun _ : Fin 1 => i))
  let A := vfObjectOfRaw hD
  let t : Fin 0 → CanonicalRV.RVSort M := Fin.elim0
  obtain ⟨b', hb'⟩ := exists_independent_of_contains_box hs hsmallT A D.side
    (D.side_infinite (model_valuation_nontrivial hv)) t (by
      intro b hb
      exact (mem_uniformBall_iff Valued.v hv (f a) b r hr).mpr (fun i => hb i (Set.mem_univ i)))
  let b := b'.val.1
  have hb : vfValues b ∈ uniformBall (vfValues (f a)) r.val := b'.property
  have hST : vfParameterField S₁ ≤ vfParameterField T := Subfield.closure_mono (by
    intro x hx
    exact Or.inl (Or.inl hx))
  have hind := independent_of_subfield_le hST hb'
  change AlgebraicIndependent (vfParameterField (S ∪ Set.range (vfValues a))) b at hind
  rw [vfParameterField_union_tuple] at hind
  let B := (S ∪ Set.range (vfValues b)) ∪ {iRv r.val}
  have hB : AlgebraicIndependent (vfParameterField B) a := by
    change AlgebraicIndependent (vfParameterField ((S ∪ Set.range (vfValues b)) ∪ {iRv r.val})) a
    rw [vfParameterField_union_rv _ _ (by rintro z rfl; exact (CanonicalRV.encodedRv r).property),
      vfParameterField_union_tuple]
    exact independent_over_tupleField_swap _ a b ha hind
  let Y := rvUniformBall (vfValues b) (iRv r.val)
  have hY : B.Definable LRV Y := by
    let g (x : Fin m → M) := Sum.elim (Sum.elim (vfValues b) x) (fun _ : Fin 1 => iRv r.val)
    have hg : B.DefinableMap LRV g := by
      rintro ((i | i) | i)
      · exact LRV.definableFun_const _ (Or.inl (Or.inr (Set.mem_range_self i)))
      · exact Set.DefinableFun.proj LRV
      · exact LRV.definableFun_const _ (Or.inr rfl)
    exact (rvUniformBallRelation_definable B m).preimage_map hg
  have hYSem (x : Fin m → VFType (M := M)) :
      vfValues x ∈ Y ↔ vfValues x ∈ uniformBall (vfValues b) r.val := by
    constructor
    · rintro ⟨ht, s, hs, he, hx⟩
      let s' : VFType (M := M) := ⟨s, hs⟩
      have hs₀ : s' ≠ 0 := fun hz => ht.2 (he.symm.trans ((CanonicalRV.encodedRv_zero_iff s').mpr hz))
      have hsame : Valued.v s' = Valued.v r :=
        (Values.vf_value_eq_iff Valued.v hv s' r).mp (congrArg Values.vrv (Subtype.ext he))
      exact (mem_uniformBall_iff Valued.v hv b x r hr).mpr (fun i => hsame ▸
        (mem_uniformBall_iff Valued.v hv b x s' hs₀).mp hx i)
    · intro hx
      exact ⟨⟨(CanonicalRV.encodedRv r).property, fun hz => hr ((CanonicalRV.encodedRv_zero_iff r).mp hz)⟩,
        r.val, r.property, rfl, hx⟩
  let X := (fun z : Fin n ⊕ Fin m → M => z ∘ Sum.inl) ''
    (vfGraph f ∩ (fun z => z ∘ Sum.inr) ⁻¹' Y)
  have hX : B.Definable LRV X :=
    ((hf.mono (Set.subset_union_left.trans Set.subset_union_left)).inter
      (hY.preimage_comp (Sum.inr : Fin m → Fin n ⊕ Fin m))).image_comp Sum.inl
  have hXsort : DefinableOver B (fun _ => .vf) X := by
    apply raw_definableOver_sorted hc B (fun _ => .vf) X hX
    rintro _ ⟨z, ⟨⟨x, rfl⟩, _⟩, rfl⟩ i
    exact (x i).property
  have haf : vfValues (f a) ∈ uniformBall (vfValues b) r.val := fun i =>
    rawOpenBall_recentre Valued.v hv (hb i)
      (rawOpenBall_self Valued.v hv (f a i).property r.property (fun h => hr (Subtype.ext h)))
  have haX : vfValues a ∈ X :=
    ⟨Sum.elim (vfValues a) (vfValues (f a)), ⟨⟨a, rfl⟩, (hYSem (f a)).mpr haf⟩, rfl⟩
  change f ⁻¹' U ∈ 𝓝 a
  apply Filter.mem_of_superset (independent_definable_mem_nhds hv B X hXsort a hB haX)
  rintro x ⟨_, ⟨⟨x', rfl⟩, hx'⟩, he⟩
  have hxx : x' = x := vfValues_injective he
  subst x'
  have hx := (hYSem (f x)).mp hx'
  exact hUr (fun i => rawOpenBall_recentre Valued.v hv (haf i) (hx i))

theorem lemma_8_7_canonical (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (hf : S.Definable LRV (vfGraph f)) :
    ∃ B : Set (Fin n → M), ∃ hB : S.Definable LRV B,
      B ⊆ vfRawUniverse n ∧ IsClosed {a | vfValues a ∈ B} ∧
      vfDim (rawRVSpace (M := M) 1) (vfObjectOfRaw hB) < n ∧
      ContinuousOn f {a | vfValues a ∉ B} :=
  closed_exception_of_generic_continuity hc hs hsmall _ (rawRVSpace_rvCoded 1) hn hv f hf
    (continuousAt_of_independent hc hκ hs hsmall hv f hf)

end SpecialTransformations.Section8
