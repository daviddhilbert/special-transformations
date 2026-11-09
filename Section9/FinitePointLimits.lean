import Section9.LimitGeometry

/-! Lemmas 9.2 and 9.3 for finite VF limit points. This is the scope
explicitly stated in 9.2. The auxiliary infinity remains available in
`Limits` and `LimitGeometry`; no finite-point argument is applied to it.
The proofs adapt the finite-point argument in the historical
`Sec9Limits.lean` to the released model and its actual Gamma quotient. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

def IsVFLimitSet (A : Set (Fin n → VFType (M := M)))
    (a : Fin n → VFType (M := M))
    (f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M)))
    (L : Set (Fin m → VFType (M := M))) : Prop :=
  IsLimitSet A a f (finiteLimitPoint '' L)

theorem isVFLimitSet_iff (A : Set (Fin n → VFType (M := M)))
    (a : Fin n → VFType (M := M))
    (f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M)))
    (L : Set (Fin m → VFType (M := M))) :
    IsVFLimitSet A a f L ↔ ∀ ε, ∃ δ, ∀ x ∈ A \ {a}, x ∈ vfBall a δ →
      ∀ y ∈ f x, ∃ b ∈ L, y ∈ vfBall b ε := by
  simp only [IsVFLimitSet, isLimitSet_iff, Set.mem_image, exists_exists_and_eq_and,
    limitBall_finite]

def IsMinimalVFLimitSet (A : Set (Fin n → VFType (M := M)))
    (a : Fin n → VFType (M := M))
    (f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M)))
    (L : Set (Fin m → VFType (M := M))) : Prop :=
  IsVFLimitSet A a f L ∧ ∀ L' ⊂ L, ¬ IsVFLimitSet A a f L'

/-- Closure characterized by the actual Gamma polydiscs. -/
def vfClosure (L : Set (Fin m → VFType (M := M))) : Set (Fin m → VFType (M := M)) :=
  {b | ∀ ε : Values.Gamma (M := M), ∃ c ∈ L, c ∈ vfBall b ε}

def IsVFClosed (L : Set (Fin m → VFType (M := M))) : Prop := vfClosure L ⊆ L

def IsVFLimit (A : Set (Fin n → VFType (M := M)))
    (a : Fin n → VFType (M := M))
    (f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M)))
    (L : Set (Fin m → VFType (M := M))) : Prop :=
  IsMinimalVFLimitSet A a f L ∧ IsVFClosed L

theorem subset_vfClosure {L : Set (Fin m → VFType (M := M))} : L ⊆ vfClosure L :=
  fun b hb ε => ⟨b, hb, mem_vfBall_self b ε⟩

theorem vfClosure_mono {L K : Set (Fin m → VFType (M := M))} (h : L ⊆ K) :
    vfClosure L ⊆ vfClosure K := by
  intro b hb ε
  obtain ⟨c, hc, hnear⟩ := hb ε
  exact ⟨c, h hc, hnear⟩

theorem vfClosure_idem (L : Set (Fin m → VFType (M := M))) :
    vfClosure (vfClosure L) = vfClosure L := by
  apply Set.Subset.antisymm
  · intro b hb ε
    obtain ⟨c, hc, hcb⟩ := hb ε
    obtain ⟨d, hd, hdc⟩ := hc ε
    have hcd : c ∈ vfBall d ε := vfBall_symm hdc
    exact ⟨d, hd, mem_vfBall_of_common (a := b) (b := d) (x := c) hcb hcd⟩
  · exact subset_vfClosure

theorem IsVFLimitSet.mono {A : Set (Fin n → VFType (M := M))}
    {a : Fin n → VFType (M := M)}
    {f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
    {L K : Set (Fin m → VFType (M := M))}
    (h : IsVFLimitSet A a f L) (hLK : L ⊆ K) : IsVFLimitSet A a f K :=
  IsLimitSet.mono h (Set.image_mono hLK)

private theorem erase_ssubset {α : Type*} {L : Set α} {b : α} (hb : b ∈ L) :
    L \ {b} ⊂ L := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.sdiff_subset, ?_⟩
  intro he
  have h : b ∈ L \ {b} := he.symm ▸ hb
  exact h.2 rfl

/-- A second limit set separated from b makes b redundant in the first. -/
theorem IsVFLimitSet.erase_of_separated
    {A : Set (Fin n → VFType (M := M))} {a : Fin n → VFType (M := M)}
    {f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
    {L K : Set (Fin m → VFType (M := M))}
    (hL : IsVFLimitSet A a f L) (hK : IsVFLimitSet A a f K)
    (b : Fin m → VFType (M := M)) (ε₀ : Values.Gamma (M := M))
    (hsep : ∀ c ∈ K, c ∉ vfBall b ε₀) : IsVFLimitSet A a f (L \ {b}) := by
  rw [isVFLimitSet_iff] at hL hK ⊢
  intro ε
  obtain ⟨δ₁, hδ₁⟩ := hL (max ε ε₀)
  obtain ⟨δ₂, hδ₂⟩ := hK ε₀
  refine ⟨max δ₁ δ₂, ?_⟩
  intro x hx hnear y hy
  obtain ⟨d, hd, hyd⟩ := hδ₁ x hx (vfBall_anti (le_max_left _ _) hnear) y hy
  obtain ⟨c, hc, hyc⟩ := hδ₂ x hx (vfBall_anti (le_max_right _ _) hnear) y hy
  refine ⟨d, ⟨hd, ?_⟩, vfBall_anti (le_max_left _ _) hyd⟩
  intro hdb
  have hdb' : d = b := hdb
  subst d
  exact hsep c hc (mem_vfBall_of_common (vfBall_anti (le_max_right _ _) hyd) hyc)

theorem IsMinimalVFLimitSet.subset_closure
    {A : Set (Fin n → VFType (M := M))} {a : Fin n → VFType (M := M)}
    {f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
    {L K : Set (Fin m → VFType (M := M))}
    (hL : IsMinimalVFLimitSet A a f L) (hK : IsVFLimitSet A a f K) : L ⊆ vfClosure K := by
  classical
  intro b hb
  by_contra hn
  obtain ⟨ε, hε⟩ := not_forall.mp hn
  have hsep : ∀ c ∈ K, c ∉ vfBall b ε := by
    intro c hc hnear
    exact hε ⟨c, hc, hnear⟩
  exact hL.2 _ (erase_ssubset hb) (hL.1.erase_of_separated hK b ε hsep)

/-- Lemma 9.2. Minimal limit sets in VF^m have equal closures. -/
theorem lemma_9_2
    {A : Set (Fin n → VFType (M := M))} {a : Fin n → VFType (M := M)}
    {f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
    {L₁ L₂ : Set (Fin m → VFType (M := M))}
    (h₁ : IsMinimalVFLimitSet A a f L₁) (h₂ : IsMinimalVFLimitSet A a f L₂) :
    vfClosure L₁ = vfClosure L₂ := by
  apply Set.Subset.antisymm
  · simpa only [vfClosure_idem] using vfClosure_mono (h₁.subset_closure h₂.1)
  · simpa only [vfClosure_idem] using vfClosure_mono (h₂.subset_closure h₁.1)

theorem IsMinimalVFLimitSet.isolated
    {A : Set (Fin n → VFType (M := M))} {a : Fin n → VFType (M := M)}
    {f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
    {L : Set (Fin m → VFType (M := M))} (h : IsMinimalVFLimitSet A a f L)
    {b : Fin m → VFType (M := M)} (hb : b ∈ L) :
    ∃ ε : Values.Gamma (M := M), ∀ c ∈ L \ {b}, c ∉ vfBall b ε := by
  classical
  by_contra hn
  push Not at hn
  apply h.2 _ (erase_ssubset hb)
  rw [isVFLimitSet_iff]
  intro ε
  obtain ⟨δ, hδ⟩ := (isVFLimitSet_iff _ _ _ _).mp h.1 ε
  obtain ⟨c, hc, hcb⟩ := hn ε
  refine ⟨δ, ?_⟩
  intro x hx hnear y hy
  obtain ⟨d, hd, hyd⟩ := hδ x hx hnear y hy
  by_cases he : d = b
  · subst d
    exact ⟨c, hc, mem_vfBall_of_common_center hcb hyd⟩
  · exact ⟨d, ⟨hd, he⟩, hyd⟩

theorem IsVFLimitSet.union
    {A : Set (Fin n → VFType (M := M))} {a : Fin n → VFType (M := M)}
    {f₁ f₂ : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
    {L₁ L₂ : Set (Fin m → VFType (M := M))}
    (h₁ : IsVFLimitSet A a f₁ L₁) (h₂ : IsVFLimitSet A a f₂ L₂) :
    IsVFLimitSet A a (fun x => f₁ x ∪ f₂ x) (L₁ ∪ L₂) := by
  rw [isVFLimitSet_iff] at h₁ h₂ ⊢
  intro ε
  obtain ⟨δ₁, hδ₁⟩ := h₁ ε
  obtain ⟨δ₂, hδ₂⟩ := h₂ ε
  refine ⟨max δ₁ δ₂, ?_⟩
  intro x hx hnear y hy
  rcases hy with hy | hy
  · obtain ⟨b, hb, hyb⟩ := hδ₁ x hx (vfBall_anti (le_max_left _ _) hnear) y hy
    exact ⟨b, Or.inl hb, hyb⟩
  · obtain ⟨b, hb, hyb⟩ := hδ₂ x hx (vfBall_anti (le_max_right _ _) hnear) y hy
    exact ⟨b, Or.inr hb, hyb⟩

theorem IsVFClosed.union {L₁ L₂ : Set (Fin m → VFType (M := M))}
    (h₁ : IsVFClosed L₁) (h₂ : IsVFClosed L₂) : IsVFClosed (L₁ ∪ L₂) := by
  classical
  intro b hb
  by_cases h : b ∈ vfClosure L₁
  · exact Or.inl (h₁ h)
  · obtain ⟨ε₀, hε₀⟩ := not_forall.mp h
    right
    apply h₂
    intro ε
    obtain ⟨c, hc, hcb⟩ := hb (max ε ε₀)
    refine ⟨c, ?_, vfBall_anti (le_max_left _ _) hcb⟩
    rcases hc with hc | hc
    · exact (hε₀ ⟨c, hc, vfBall_anti (le_max_right _ _) hcb⟩).elim
    · exact hc

theorem IsVFLimit.isolated_or_separated
    {A : Set (Fin n → VFType (M := M))} {a : Fin n → VFType (M := M)}
    {f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
    {L : Set (Fin m → VFType (M := M))} (h : IsVFLimit A a f L)
    (b : Fin m → VFType (M := M)) :
    ∃ ε : Values.Gamma (M := M), ∀ c ∈ L \ {b}, c ∉ vfBall b ε := by
  classical
  by_cases hb : b ∈ L
  · exact h.1.isolated hb
  · have hn : b ∉ vfClosure L := fun hcl => hb (h.2 hcl)
    obtain ⟨ε, hε⟩ := not_forall.mp hn
    exact ⟨ε, fun c hc hcb => hε ⟨c, hc.1, hcb⟩⟩

/-- Lemma 9.3 on the finite-point scope of Lemma 9.2. -/
theorem lemma_9_3
    {A : Set (Fin n → VFType (M := M))} {a : Fin n → VFType (M := M)}
    {f₁ f₂ : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
    {L₁ L₂ : Set (Fin m → VFType (M := M))}
    (h₁ : IsVFLimit A a f₁ L₁) (h₂ : IsVFLimit A a f₂ L₂) :
    IsVFLimit A a (fun x => f₁ x ∪ f₂ x) (L₁ ∪ L₂) := by
  classical
  refine ⟨⟨h₁.1.1.union h₂.1.1, ?_⟩, h₁.2.union h₂.2⟩
  intro K hK hlim
  obtain ⟨b, hb, hbK⟩ := Set.exists_of_ssubset hK
  obtain ⟨ε₁, hε₁⟩ := h₁.isolated_or_separated b
  obtain ⟨ε₂, hε₂⟩ := h₂.isolated_or_separated b
  have hsep : ∀ c ∈ K, c ∉ vfBall b (max ε₁ ε₂) := by
    intro c hc hcb
    have hne : c ∉ ({b} : Set _) := fun he => hbK (he ▸ hc)
    rcases hK.subset hc with hc₁ | hc₂
    · exact hε₁ c ⟨hc₁, hne⟩ (vfBall_anti (le_max_left _ _) hcb)
    · exact hε₂ c ⟨hc₂, hne⟩ (vfBall_anti (le_max_right _ _) hcb)
  have hrestrict {f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
      (hf : ∀ x, f x ⊆ f₁ x ∪ f₂ x) : IsVFLimitSet A a f K := by
    rw [isVFLimitSet_iff] at hlim ⊢
    intro ε
    obtain ⟨δ, hδ⟩ := hlim ε
    exact ⟨δ, fun x hx hnear y hy => hδ x hx hnear y (hf x hy)⟩
  rcases hb with hb | hb
  · exact h₁.1.2 _ (erase_ssubset hb)
      (h₁.1.1.erase_of_separated (hrestrict (fun _ => Set.subset_union_left)) b _ hsep)
  · exact h₂.1.2 _ (erase_ssubset hb)
      (h₂.1.1.erase_of_separated (hrestrict (fun _ => Set.subset_union_right)) b _ hsep)

end SpecialTransformations.Section9
