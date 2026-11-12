module

public import Section5.GammaDimension
public import Section5.GammaDimensionalPresentation

@[expose] public section

/-! Actual finite-map dimension and the pointwise VF rank criterion. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m k l : ℕ}

theorem GammaIso.refl {A : Set (Point (M := M) n m)} (hA : GammaSetDefinable B A) :
    Nonempty (GammaIso B A A) := by
  refine ⟨⟨Equiv.refl _, ?_⟩⟩
  let L := gammaLogicInput B
  let W := PresentedSet.univ (pointSpace (M := M) n m) B.real
  apply GammaGraphDefinable.congr (L.restrict_graph hA (L.real_map_graph (Map.id W)))
  intro p q
  constructor
  · rintro ⟨hp, a, ha, hq⟩
    exact ⟨⟨p, hp⟩, rfl, ha.symm.trans hq⟩
  · rintro ⟨a, rfl, hq⟩
    exact ⟨a.property, ⟨a.val, Set.mem_univ _⟩, rfl, hq⟩

theorem GammaIso.dimension_le {A : Set (Point (M := M) n m)} {D : Set (Point (M := M) k l)}
    (e : GammaIso B A D) : GammaHasVFDimLE B A k := by
  let f : A → Point (M := M) k l × (Fin 0 → Values.Gamma (M := M)) :=
    fun a => ((e.equiv a).val, Fin.elim0)
  refine ⟨k, le_rfl, l, 0, f, ?_, ?_⟩
  · intro y
    by_cases hy : ∃ a, f a = y
    · obtain ⟨a, rfl⟩ := hy
      apply (Set.finite_singleton a).subset
      intro b hb
      exact e.equiv.injective (Subtype.ext (congrArg Prod.fst hb))
    · exact Set.finite_empty.subset (fun a ha => (hy ⟨a, ha⟩).elim)
  · apply GammaGraphDefinable.congr e.graph
    intro p q
    have hap (z : Fin l → RV (M := M)) (t : Fin 0 → RV (M := M)) :
        Fin.append z t = z := by
      funext i
      exact Fin.append_left z t i
    constructor
    · rintro ⟨a, ha, he⟩
      exact ⟨a, ha, Fin.elim0, Subsingleton.elim _ _, by
        rw [hap]
        exact he.symm⟩
    · rintro ⟨a, ha, t, _, he⟩
      rw [hap] at he
      exact ⟨a, ha, he.symm⟩

theorem gamma_dim_le_iff_rank {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    {A : Set (Point (M := M) n m)} (hA : GammaSetDefinable B A) :
    GammaHasVFDimLE B A k ↔
      ∀ p ∈ A, @vfTupleTrdeg M (CanonicalStructure.normalize (M := M))
        (@CanonicalStructure.normalized_model M sM hM) B.real n p.1 ≤ (k : Cardinal) := by
  refine ⟨gamma_rank_of_dimension, fun h => ?_⟩
  obtain ⟨l, D, ⟨e⟩⟩ := gammaDimensionalPresentation_of_rank hκ hs h00 B hsmall A hA h
  exact e.dimension_le

end SpecialTransformations.Section5
