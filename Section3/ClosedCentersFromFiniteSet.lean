module

public import Section3.ClosedBallCentres

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.BallFamilies
open RawClosure.Tuple Barycentre ClosedBallRoots
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

/-- Extracted from closed_family_centres: once a finite original-base
hitting set is given, neither finiteness nor real-base definability of the
family is needed to define the invariant center function on real codes. -/
theorem centers_of_finite_hitting_set {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (h00 : M ⊨ Axioms.ACVF00) (S : Set M) (C : Set (Fin n → M))
    (D : (Fin n → M) → Set (VFType (M := M)))
    (hD : RelationDefinable S (relation D))
    (R : Finset (VFType (M := M)))
    (hRdef : DefinableAt S .vf (Subtype.val '' (R : Set (VFType (M := M)))))
    (hhit : ∀ t ∈ C, ∃ x ∈ R, x ∈ D t)
    (hclosed : ∀ t ∈ C, IsClosedBall v (D t)) :
    ∃ f : (Fin n → M) → VFType (M := M),
      S.DefinableFun LRV (fun t => (f t).val) ∧ (∀ t ∈ C, f t ∈ D t) ∧
      ∀ t u, D t = D u → f t = f u := by
  let F (t : Fin n → M) : Finset (VFType (M := M)) := R.filter (fun x => x ∈ D t)
  have hF : RelationDefinable S (finiteFibreRelation F) := by
    have hR := hRdef.raw_definable.preimage_comp
      (Sum.inr : Fin 1 → Fin n ⊕ Fin 1)
    change S.Definable LRV {z : Fin n ⊕ Fin 1 → M |
      (z ∘ Sum.inl,z (.inr 0)) ∈ finiteFibreRelation F}
    convert hD.inter hR using 1
    ext z
    change (∃ x ∈ F (z ∘ Sum.inl), x.val = z (.inr 0)) ↔
      (∃ x ∈ D (z ∘ Sum.inl), x.val = z (.inr 0)) ∧
      z (.inr 0) ∈ Subtype.val '' (R : Set (VFType (M := M)))
    constructor
    · rintro ⟨x,hx,he⟩
      obtain ⟨hxR,hxD⟩ := Finset.mem_filter.mp hx
      exact ⟨⟨x,hxD,he⟩,x,hxR,he⟩
    · rintro ⟨⟨x,hxD,he⟩,y,hyR,hy⟩
      have hxy : y = x := Subtype.ext (hy.trans he.symm)
      exact ⟨x,Finset.mem_filter.mpr ⟨hxy ▸ hyR,hxD⟩,he⟩
  refine ⟨fun t => mean (F t),mean_definable h00 S F hF R.card
    (fun t => Finset.card_filter_le _ _),?_,?_⟩
  · intro t ht
    have hne : (F t).Nonempty := by
      obtain ⟨x,hxR,hxD⟩ := hhit t ht
      exact ⟨x,Finset.mem_filter.mpr ⟨hxR,hxD⟩⟩
    rcases hclosed t ht with he | ⟨a,b,he⟩
    · rw [he]; trivial
    · rw [he]
      exact mean_mem_closedDisc v hv h00 (F t) hne a (↑(OrderDual.toDual (v b)))
        (fun x hx => by
          have hxD := (Finset.mem_filter.mp hx).2
          rw [he] at hxD
          exact hxD)
  · intro t u he
    have hFtu : F t = F u := by simp only [F,he]
    exact congrArg mean hFtu

end SpecialTransformations.Section3.BallFamilies
