module

public import Section4.RVCoproduct
public import Section4.RVEmptyIso
public import Section4.RVScissorPresentation

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

/-- Addition in the actual positive scissor quotient is represented by
the concrete definable coproduct, before group completion. -/
theorem rvClass_coprod (U V : RVObject (M := M) S k) :
    rvClass (rvCoprodObject U V) = rvClass U + rvClass V := by
  let W := rvCoprodObject U V
  let A := (rvLeftTagMap U.domain V.arity).image
  let B := (rvRightTagMap V.domain U.arity).image
  have hA : A.carrier ⊆ W.domain.carrier := fun _ h => Or.inl h
  have hB : B.carrier ⊆ W.domain.carrier := fun _ h => Or.inr h
  have eA : U ≅ W.restrict A hA :=
    rvIsoOfVolumePreservingBijection (rvLeftTagMap U.domain V.arity).toImage
      (rvLeftTagMap_toImage_bijective U.domain V.arity) (rvCoprod_value_left U V)
  have eB : V ≅ W.restrict B hB :=
    rvIsoOfVolumePreservingBijection (rvRightTagMap V.domain U.arity).toImage
      (rvRightTagMap_toImage_bijective V.domain U.arity) (rvCoprod_value_right U V)
  have eUnion : W.restrict (A.union B)
      (fun _ h => h.elim (fun ha => hA ha) (fun hb => hB hb)) ≅ W :=
    rvSelfRestrictionIso W
  have he : (A.inter B).carrier = ∅ := by
    apply Set.Subset.antisymm
    · rintro x ⟨ha, hb⟩
      exact False.elim (Set.disjoint_left.mp (rvTaggedImages_disjoint U.domain V.domain) ha hb)
    · exact Set.empty_subset _
  have eInter : W.restrict (A.inter B) (fun _ h => hA h.1) ≅ RVObject.empty S k :=
    rvEmptyIso _ he
  have hs := rvClass_scissor (S := S) (k := k)
    ⟨W, A, B, hA, hB, rfl, rfl, rfl, rfl⟩
  calc
    rvClass W = rvClass (W.restrict (A.union B) _) + rvClass (W.restrict (A.inter B) _) := by
      rw [rvClass_iso eUnion, rvClass_iso eInter, rvClass_empty, add_zero]
    _ = rvClass (W.restrict A hA) + rvClass (W.restrict B hB) := hs.symm
    _ = rvClass U + rvClass V := by rw [← rvClass_iso eA, ← rvClass_iso eB]

end SpecialTransformations.Section4

end
