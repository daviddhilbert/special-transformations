import Section3.FiniteFibreMeans
import Section3.FiniteGluing
import Section3.ParameterBridge
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Barycentre
open RawClosure.Tuple
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

/-- Means of a uniformly bounded definable family of finite VF sets form a
definable function over its original base. Empty fibres have mean zero. -/
theorem mean_definable (h00 : M ⊨ Axioms.ACVF00) (S : Set M)
    (F : (Fin n → M) → Finset (VFType (M := M)))
    (hF : RelationDefinable S (finiteFibreRelation F))
    (N : ℕ) (hbound : ∀ t, (F t).card ≤ N) :
    S.DefinableFun LRV (fun t => (mean (F t)).val) := by
  let R := finiteFibreRelation F
  let E (k : ℕ) : Set (Option (Fin n) → M) :=
    {w | ∃ c : Fin k → M, Enumerates R k (w ∘ some) c ∧
      iVF (w none) ∧ (linearTerm k).realize (Sum.elim (fun _ => w none) c) = iVFZero}
  have hE (k : ℕ) : S.Definable LRV (E k) := by
    let ι := Option (Fin n) ⊕ Fin k
    have he := (enumeration_definable S R hF k).preimage_comp
      (Sum.map some id : Fin n ⊕ Fin k → ι)
    have hv := (definableAt_sort S .vf).raw_definable.preimage_comp
      (fun _ : Fin 1 => (.inl none : ι))
    have ht := (linearTerm_zero_definable S k).preimage_comp
      (Sum.elim (fun _ : Fin 1 => (.inl none : ι)) Sum.inr)
    have h := ((he.inter hv).inter ht).exists_of_finite
    convert h using 1
    ext w
    simp only [E, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff,
      Function.comp_def, Sum.elim_inl, Sum.elim_inr, Sum.map_inl, Sum.map_inr]
    apply exists_congr
    intro c
    have hmap : (fun x : Fin 1 ⊕ Fin k =>
        Sum.elim w c (Sum.elim (fun _ : Fin 1 => (Sum.inl none : ι)) Sum.inr x)) =
        Sum.elim (fun _ : Fin 1 => w none) c := by
      funext x
      cases x <;> rfl
    rw [hmap]
    exact and_assoc.symm
  let Z : Set (Option (Fin n) → M) :=
    {w | (F (w ∘ some)) = ∅ ∧ w none = iVFZero}
  have hZ : S.Definable LRV Z := by
    have hd := (domain_definable S R hF).compl.preimage_comp
      (some : Fin n → Option (Fin n))
    have hzero : S.DefinableFun LRV (fun _ : Option (Fin n) → M => iVFZero) :=
      DefinableConstants.constant
        (DefinableConstants.function_symbol (L := LRV) Fn.vfZero Fin.elim0
          (fun i => i.elim0))
    have heq := (Set.DefinableFun.proj (L := LRV) (A := S) (i := none)).ofPred_eq hzero
    convert hd.inter heq using 1
    ext w
    change ((F (w ∘ some)) = ∅ ∧ w none = iVFZero) ↔
      (¬ ∃ b, (w ∘ some, b) ∈ R) ∧ w none = iVFZero
    refine and_congr ?_ Iff.rfl
    simp only [R, finiteFibreRelation, Set.mem_ofPred_eq]
    constructor
    · rintro hf ⟨b, x, hx, _⟩
      rw [hf] at hx
      exact Finset.notMem_empty x hx
    · intro h
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h ⟨x.val, x, hx, rfl⟩
  let U := Z ∪ ⋃ k : Fin (N + 1), if k.val = 0 then ∅ else E k.val
  have hU : S.Definable LRV U := by
    apply hZ.union
    apply Set.definable_iUnion_of_finite
    intro k
    split_ifs
    · exact Set.definable_empty
    · exact hE k.val
  change S.Definable LRV (Function.tupleGraph (fun t => (mean (F t)).val))
  convert hU using 1
  ext w
  change (mean (F (w ∘ some))).val = w none ↔ w ∈ U
  constructor
  · intro hw
    by_cases hempty : F (w ∘ some) = ∅
    · left
      refine ⟨hempty, ?_⟩
      rw [← hw, hempty]
      simp only [mean, Finset.sum_empty, Finset.card_empty, Nat.cast_zero, div_zero]
      rfl
    · right
      let k : Fin (N + 1) := ⟨(F (w ∘ some)).card, by have := hbound (w ∘ some); omega⟩
      have hk : k.val ≠ 0 := fun h => hempty (Finset.card_eq_zero.mp h)
      apply Set.mem_iUnion.mpr
      refine ⟨k, ?_⟩
      rw [if_neg hk]
      obtain ⟨c, hc⟩ := finiteFibre_enumeration_exists F (w ∘ some)
      refine ⟨c, hc, hw ▸ (mean (F (w ∘ some))).property, ?_⟩
      rw [← hw]
      exact (enumerated_mean_equation h00 F _ hk c hc _).mpr rfl
  · intro hw
    rcases hw with hw | hw
    · rcases hw with ⟨hempty, hz⟩
      rw [hempty, hz]
      simp only [mean, Finset.sum_empty, Finset.card_empty, Nat.cast_zero, div_zero]
      rfl
    · obtain ⟨k, hkE⟩ := Set.mem_iUnion.mp hw
      by_cases hk : k.val = 0
      · rw [if_pos hk] at hkE
        exact hkE.elim
      · rw [if_neg hk] at hkE
        obtain ⟨c, hc, hz, heq⟩ := hkE
        let z : VFType (M := M) := ⟨w none, hz⟩
        have hm : z = mean (F (w ∘ some)) :=
          (enumerated_mean_equation h00 F _ hk c hc z).mp heq
        exact (congrArg Subtype.val hm).symm

end SpecialTransformations.Section3.Barycentre
