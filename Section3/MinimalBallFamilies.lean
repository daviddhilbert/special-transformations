import Section3.FiniteGluing
import VFField
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.BallFamilies
open RawClosure.Tuple
variable {M : Type} [LRV.Structure M] {n : ℕ}

/-- The complete membership graph of a VF-set family on real tuple codes. -/
def relation (D : (Fin n → M) → Set (VFType (M := M))) : Set ((Fin n → M) × M) :=
  {p | ∃ x ∈ D p.1, x.val = p.2}

theorem mem_relation_iff (D : (Fin n → M) → Set (VFType (M := M)))
    (t : Fin n → M) (x : VFType (M := M)) : (t, x.val) ∈ relation D ↔ x ∈ D t := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact (Subtype.ext he : y = x) ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

def minimalDomain (C : Set (Fin n → M)) (D : (Fin n → M) → Set (VFType (M := M))) :
    Set (Fin n → M) := {t | t ∈ C ∧ ∀ u ∈ C, D u ⊆ D t → D t ⊆ D u}

theorem subset_codes_definable (S : Set M) (D : (Fin n → M) → Set (VFType (M := M)))
    (hD : RelationDefinable S (relation D)) :
    S.Definable LRV {z : (Fin n ⊕ Fin n) → M | D (z ∘ Sum.inr) ⊆ D (z ∘ Sum.inl)} := by
  let ι := (Fin n ⊕ Fin n) ⊕ Fin 1
  have hr := hD.preimage_comp (Sum.map Sum.inr id : Fin n ⊕ Fin 1 → ι)
  have hl := hD.preimage_comp (Sum.map Sum.inl id : Fin n ⊕ Fin 1 → ι)
  have h := (hr.himp hl).forall_of_finite
  convert h using 1
  ext z
  change (D (z ∘ Sum.inr) ⊆ D (z ∘ Sum.inl)) ↔
    ∀ b : Fin 1 → M, (z ∘ Sum.inr, b 0) ∈ relation D → (z ∘ Sum.inl, b 0) ∈ relation D
  constructor
  · intro h b hb
    obtain ⟨x, hx, he⟩ := hb
    exact ⟨x, h hx, he⟩
  · intro h x hx
    exact (mem_relation_iff D _ x).mp
      (h ![x.val] ((mem_relation_iff D _ x).mpr hx))

theorem minimalDomain_definable (S : Set M) (C : Set (Fin n → M))
    (hC : S.Definable LRV C) (D : (Fin n → M) → Set (VFType (M := M)))
    (hD : RelationDefinable S (relation D)) : S.Definable LRV (minimalDomain C D) := by
  have hs := subset_codes_definable S D hD
  have ht := hs.preimage_comp (Sum.swap : Fin n ⊕ Fin n → Fin n ⊕ Fin n)
  have hc := hC.preimage_comp (Sum.inr : Fin n → Fin n ⊕ Fin n)
  have hall := ((hc.inter hs).himp ht).forall_of_finite
  convert hC.inter hall using 1
  ext z
  change (z ∈ C ∧ ∀ u ∈ C, D u ⊆ D z → D z ⊆ D u) ↔
    (z ∈ C ∧ ∀ u : Fin n → M, u ∈ C ∧ D u ⊆ D z → D z ⊆ D u)
  exact and_congr_right (fun _ => by simp only [and_imp])

theorem minimal_union_definable (S : Set M) (C : Set (Fin n → M))
    (hC : S.Definable LRV C) (D : (Fin n → M) → Set (VFType (M := M)))
    (hD : RelationDefinable S (relation D)) :
    S.Definable₁ LRV (Subtype.val '' (⋃ t ∈ minimalDomain C D, D t)) := by
  have hm := (minimalDomain_definable S C hC D hD).preimage_comp
    (Sum.inl : Fin n → Fin n ⊕ Fin 1)
  have h := (hD.inter hm).preimage_comp (Sum.swap : Fin n ⊕ Fin 1 → Fin 1 ⊕ Fin n)
  change S.Definable LRV _
  convert h.exists_of_finite using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_iUnion,
    Set.mem_inter_iff, Set.mem_preimage, Function.comp_def, Sum.swap_inl,
    Sum.swap_inr, Sum.elim_inl, Sum.elim_inr, relation]
  constructor
  · rintro ⟨x, ⟨t, ht, hxt⟩, he⟩
    exact ⟨t, ⟨x, hxt, he⟩, ht⟩
  · rintro ⟨t, ⟨x, hx, he⟩, ht⟩
    exact ⟨x, ⟨t, ht, hx⟩, he⟩

/-- Every member of a finite family contains a minimal member. The family
of codes may be infinite; only its set of distinct values is assumed finite. -/
theorem exists_minimal_below (C : Set (Fin n → M))
    (D : (Fin n → M) → Set (VFType (M := M))) (hfin : (D '' C).Finite)
    (t : Fin n → M) (ht : t ∈ C) :
    ∃ u ∈ minimalDomain C D, D u ⊆ D t := by
  obtain ⟨B, hBt, hB, hmin⟩ := hfin.exists_le_minimal (Set.mem_image_of_mem D ht)
  obtain ⟨u, hu, rfl⟩ := hB
  refine ⟨u, ⟨hu, ?_⟩, hBt⟩
  intro w hw hwu
  exact hmin (Set.mem_image_of_mem D hw) hwu

end SpecialTransformations.Section3.BallFamilies
