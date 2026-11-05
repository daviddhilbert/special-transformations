import Section3.RootFreeConstancy
import Section3.ClosedBallRoots
import Section3.MinimalBallFamilies
import Section3.MeanInBalls
import Section3.DefinableMeans
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.BallFamilies
open RawClosure.Tuple Barycentre ClosedBallRoots
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv

/-- A finite definable family of closed balls has a finite definable set
meeting every member. Only the family, rather than any list of its members
or any chosen centers, is definable over S. -/
theorem finite_definable_hitting_set (hc : CanonicalStructure.IsCanonical (M := M))
    (hnt : ∃ x : VFType (M := M), x ≠ 0 ∧ v x < 1)
    (S : Set M) (C : Set (Fin n → M)) (hC : S.Definable LRV C)
    (D : (Fin n → M) → Set (VFType (M := M)))
    (hD : RelationDefinable S (relation D)) (hfin : (D '' C).Finite)
    (hclosed : ∀ t ∈ C, IsClosedBall v (D t)) :
    ∃ R : Finset (VFType (M := M)),
      DefinableAt S .vf (Subtype.val '' (R : Set (VFType (M := M)))) ∧
        ∀ t ∈ C, ∃ x ∈ R, x ∈ D t := by
  let F : Set (Set (VFType (M := M))) := D '' minimalDomain C D
  have hFC : F ⊆ D '' C := Set.image_mono (fun _ ht => ht.1)
  have hfF : F.Finite := hfin.subset hFC
  let U : Set M := Subtype.val '' (⋃ t ∈ minimalDomain C D, D t)
  have hU : DefinableAt S .vf U := raw_definable_sorted hc S U .vf
    (minimal_union_definable S C hC D hD) (by rintro z ⟨x, _, rfl⟩; exact x.property)
  obtain ⟨R, hR, hRdef, hconst⟩ := finite_definable_obstacles v hv S U hU
  have hball (B) (hB : B ∈ F) : IsClosedBall v B := by
    obtain ⟨t, ht, rfl⟩ := hB
    exact hclosed t ht.1
  have hdisj (B) (hB : B ∈ F) (B') (hB' : B' ∈ F) (hne : B ≠ B') : Disjoint B B' := by
    by_contra hnot
    obtain ⟨t, ht, rfl⟩ := hB
    obtain ⟨u, hu, rfl⟩ := hB'
    have hmeet : (D t ∩ D u).Nonempty := Set.not_disjoint_iff.mp hnot
    rcases ValOneEC.Johnson.isValBall_subset_or_subset v
      (IsClosedBall.isValBall v (hclosed t ht.1))
      (IsClosedBall.isValBall v (hclosed u hu.1)) hmeet with htu | hut
    · exact hne (Set.Subset.antisymm htu (hu.2 t ht.1 htu))
    · exact hne (Set.Subset.antisymm (ht.2 u hu.1 hut) hut)
  have hUmem (x : VFType (M := M)) : x.val ∈ U ↔ x ∈ ⋃ B ∈ hfF.toFinset, B := by
    change (∃ y, y ∈ ⋃ t ∈ minimalDomain C D, D t ∧ y.val = x.val) ↔ _
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨y, ⟨t, ht, hy⟩, he⟩
      have hyx : y = x := Subtype.ext he
      exact ⟨D t, ⟨t, ht, rfl⟩, hyx ▸ hy⟩
    · rintro ⟨B, ⟨t, ht, rfl⟩, hx⟩
      exact ⟨x, ⟨t, ht, hx⟩, rfl⟩
  have hconst' (a b : VFType (M := M))
      (havoid : ∀ c ∈ R, c ∉ ValOneEC.openBall v a (v b))
      (x : VFType (M := M)) (hx : x ∈ ValOneEC.openBall v a (v b))
      (y : VFType (M := M)) (hy : y ∈ ValOneEC.openBall v a (v b)) :
      (x ∈ ⋃ B ∈ hfF.toFinset, B ↔ y ∈ ⋃ B ∈ hfF.toFinset, B) := by
    have hb : v b ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le hx)
    have heq : Balls.openDisc v a (↑(OrderDual.toDual (v b))) = ValOneEC.openBall v a (v b) := by
      simp only [Balls.openDisc, OrderDual.ofDual_toDual, if_neg hb]
      rfl
    exact (hUmem x).symm.trans ((hconst a _ (heq.symm ▸ havoid) x
      (heq.symm ▸ hx) y (heq.symm ▸ hy)).trans (hUmem y))
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  have hhit := ClosedBallRoots.meets_each v hnt hfF.toFinset id
    (fun B hB => hball B (hfF.mem_toFinset.mp hB))
    (fun B hB B' hB' hne => hdisj B (hfF.mem_toFinset.mp hB) B' (hfF.mem_toFinset.mp hB') hne)
    R hR hconst'
  refine ⟨R, hRdef, ?_⟩
  intro t ht
  obtain ⟨u, hu, hut⟩ := exists_minimal_below C D hfin t ht
  obtain ⟨x, hxR, hxDu⟩ := hhit (D u) (hfF.mem_toFinset.mpr ⟨u, hu, rfl⟩)
  exact ⟨x, hxR, hut hxDu⟩

/-- Uniform centers over the original base, constant on codes of the same
ball. Finiteness is a condition on distinct ball values; real codes may be
infinite. The canonical premise is removed by the sorted-code wrapper. -/
theorem closed_family_centres (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00)
    (hnt : ∃ x : VFType (M := M), x ≠ 0 ∧ v x < 1)
    (S : Set M) (C : Set (Fin n → M)) (hC : S.Definable LRV C)
    (D : (Fin n → M) → Set (VFType (M := M)))
    (hD : RelationDefinable S (relation D)) (hfin : (D '' C).Finite)
    (hclosed : ∀ t ∈ C, IsClosedBall v (D t)) :
    ∃ f : (Fin n → M) → VFType (M := M),
      S.DefinableFun LRV (fun t => (f t).val) ∧
      (∀ t ∈ C, f t ∈ D t) ∧
      ∀ t u, D t = D u → f t = f u := by
  obtain ⟨R, hRdef, hhit⟩ := finite_definable_hitting_set v hv hc hnt S C hC D hD hfin hclosed
  let F (t : Fin n → M) : Finset (VFType (M := M)) := R.filter (fun x => x ∈ D t)
  have hF : RelationDefinable S (finiteFibreRelation F) := by
    have hR := hRdef.raw_definable.preimage_comp
      (Sum.inr : Fin 1 → Fin n ⊕ Fin 1)
    change S.Definable LRV {z : Fin n ⊕ Fin 1 → M | (z ∘ Sum.inl, z (.inr 0)) ∈ finiteFibreRelation F}
    convert hD.inter hR using 1
    ext z
    change (∃ x ∈ F (z ∘ Sum.inl), x.val = z (.inr 0)) ↔
      (∃ x ∈ D (z ∘ Sum.inl), x.val = z (.inr 0)) ∧
        z (.inr 0) ∈ Subtype.val '' (R : Set (VFType (M := M)))
    constructor
    · rintro ⟨x, hx, he⟩
      obtain ⟨hxR, hxD⟩ := Finset.mem_filter.mp hx
      exact ⟨⟨x, hxD, he⟩, x, hxR, he⟩
    · rintro ⟨⟨x, hxD, he⟩, ⟨y, hyR, hy⟩⟩
      have hxy : y = x := Subtype.ext (hy.trans he.symm)
      exact ⟨x, Finset.mem_filter.mpr ⟨hxy ▸ hyR, hxD⟩, he⟩
  refine ⟨fun t => mean (F t), mean_definable h00 S F hF R.card
    (fun t => Finset.card_filter_le _ _), ?_, ?_⟩
  · intro t ht
    have hne : (F t).Nonempty := by
      obtain ⟨x, hxR, hxD⟩ := hhit t ht
      exact ⟨x, Finset.mem_filter.mpr ⟨hxR, hxD⟩⟩
    rcases hclosed t ht with he | ⟨a, b, he⟩
    · rw [he]; trivial
    · rw [he]
      exact mean_mem_closedDisc v hv h00 (F t) hne a (↑(OrderDual.toDual (v b)))
        (by
          intro x hx
          have hh : x ∈ ValOneEC.closedBall v a (v b) := he ▸ (Finset.mem_filter.mp hx).2
          exact hh)
  · intro t u he
    have hFtu : F t = F u := by simp only [F, he]
    exact congrArg mean hFtu

end SpecialTransformations.Section3.BallFamilies
