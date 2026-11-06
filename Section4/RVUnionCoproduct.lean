import Section4.RVCoproduct

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

def rvUnionSubset (U : RVObject (M := M) S k)
    (A B : DefSet (rawRVSpace (M := M) U.arity) S)
    (hA : A.carrier ⊆ U.domain.carrier) (hB : B.carrier ⊆ U.domain.carrier) :
    (A.union B).carrier ⊆ U.domain.carrier :=
  fun _ h => h.elim (fun ha => hA ha) (fun hb => hB hb)

def rvUnionInl (U : RVObject (M := M) S k)
    (A B : DefSet (rawRVSpace (M := M) U.arity) S)
    (hA : A.carrier ⊆ U.domain.carrier) (hB : B.carrier ⊆ U.domain.carrier) :
    U.restrict A hA ⟶ U.restrict (A.union B) (rvUnionSubset U A B hA hB) :=
  rvHomOfVolumePreserving (Map.inclusion (fun _ h => Or.inl h)) (fun _ => rfl)

def rvUnionInr (U : RVObject (M := M) S k)
    (A B : DefSet (rawRVSpace (M := M) U.arity) S)
    (hA : A.carrier ⊆ U.domain.carrier) (hB : B.carrier ⊆ U.domain.carrier) :
    U.restrict B hB ⟶ U.restrict (A.union B) (rvUnionSubset U A B hA hB) :=
  rvHomOfVolumePreserving (Map.inclusion (fun _ h => Or.inr h)) (fun _ => rfl)

def rvUnionDesc (U : RVObject (M := M) S k)
    (A B : DefSet (rawRVSpace (M := M) U.arity) S)
    (hA : A.carrier ⊆ U.domain.carrier) (hB : B.carrier ⊆ U.domain.carrier)
    {W : RVObject (M := M) S k} (f : U.restrict A hA ⟶ W)
    (g : U.restrict B hB ⟶ W) :
    U.restrict (A.union B) (rvUnionSubset U A B hA hB) ⟶ W where
  map := f.map.union g.map
  volumetric a := by
    change rvWeight (U.value ⟨a.val, rvUnionSubset U A B hA hB a.property⟩) ≤
      rvWeight (W.value ((f.map.union g.map) a))
    by_cases ha : a.val ∈ A.carrier
    · have he : (f.map.union g.map) a = f.map ⟨a.val, ha⟩ := by
        simp [Map.union, RVObject.restrict, ha]
      rw [he]
      exact f.volumetric ⟨a.val, ha⟩
    · have he : (f.map.union g.map) a = g.map ⟨a.val, a.property.resolve_left ha⟩ := by
        simp [Map.union, RVObject.restrict, ha]
      rw [he]
      exact g.volumetric ⟨a.val, a.property.resolve_left ha⟩
  finite_volume_images t := by
    apply ((f.finite_volume_images t).union (g.finite_volume_images t)).subset
    rintro s ⟨a, ha, hs⟩
    by_cases hleft : a.val ∈ A.carrier
    · exact Or.inl ⟨⟨a.val, hleft⟩, ha, by simpa [Map.union, RVObject.restrict, hleft] using hs⟩
    · exact Or.inr ⟨⟨a.val, a.property.resolve_left hleft⟩, ha,
        by simpa [Map.union, RVObject.restrict, hleft] using hs⟩

theorem rvUnion_inl_desc (U : RVObject (M := M) S k)
    (A B : DefSet (rawRVSpace (M := M) U.arity) S)
    (hA : A.carrier ⊆ U.domain.carrier) (hB : B.carrier ⊆ U.domain.carrier)
    {W : RVObject (M := M) S k} (f : U.restrict A hA ⟶ W)
    (g : U.restrict B hB ⟶ W) :
    rvUnionInl U A B hA hB ≫ rvUnionDesc U A B hA hB f g = f := by
  apply RVHom.ext
  apply Map.ext
  intro a
  exact Map.union_on_left f.map g.map a

theorem rvUnion_inr_desc (U : RVObject (M := M) S k)
    (A B : DefSet (rawRVSpace (M := M) U.arity) S)
    (hA : A.carrier ⊆ U.domain.carrier) (hB : B.carrier ⊆ U.domain.carrier)
    (hd : Disjoint A.carrier B.carrier)
    {W : RVObject (M := M) S k} (f : U.restrict A hA ⟶ W)
    (g : U.restrict B hB ⟶ W) :
    rvUnionInr U A B hA hB ≫ rvUnionDesc U A B hA hB f g = g := by
  apply RVHom.ext
  apply Map.ext
  intro b
  exact Map.union_on_right f.map g.map hd b

theorem rvUnion_hom_ext (U : RVObject (M := M) S k)
    (A B : DefSet (rawRVSpace (M := M) U.arity) S)
    (hA : A.carrier ⊆ U.domain.carrier) (hB : B.carrier ⊆ U.domain.carrier)
    {W : RVObject (M := M) S k}
    {f g : U.restrict (A.union B) (rvUnionSubset U A B hA hB) ⟶ W}
    (hl : rvUnionInl U A B hA hB ≫ f = rvUnionInl U A B hA hB ≫ g)
    (hr : rvUnionInr U A B hA hB ≫ f = rvUnionInr U A B hA hB ≫ g) : f = g := by
  apply RVHom.ext
  apply Map.ext
  intro a
  rcases a.property with ha | ha
  · have h := congrArg (fun h : RVHom (U.restrict A hA) W => h.map ⟨a.val, ha⟩) hl
    exact h
  · have h := congrArg (fun h : RVHom (U.restrict B hB) W => h.map ⟨a.val, ha⟩) hr
    exact h

/-- A disjoint definable partition, with inherited labels, is also a
categorical coproduct. All glued maps satisfy both RV morphism conditions. -/
def rvUnionIsColimit (U : RVObject (M := M) S k)
    (A B : DefSet (rawRVSpace (M := M) U.arity) S)
    (hA : A.carrier ⊆ U.domain.carrier) (hB : B.carrier ⊆ U.domain.carrier)
    (hd : Disjoint A.carrier B.carrier) :
    IsColimit (BinaryCofan.mk (rvUnionInl U A B hA hB) (rvUnionInr U A B hA hB)) :=
  BinaryCofan.IsColimit.mk _ (fun f g => rvUnionDesc U A B hA hB f g)
    (rvUnion_inl_desc U A B hA hB) (rvUnion_inr_desc U A B hA hB hd)
    (fun f g m hl hr => rvUnion_hom_ext U A B hA hB
      (hl.trans (rvUnion_inl_desc U A B hA hB f g).symm)
      (hr.trans (rvUnion_inr_desc U A B hA hB hd f g).symm))

variable [hM : M ⊨ Axioms.ACVF]

def rvCoprodUnionIso (U : RVObject (M := M) S k)
    (A B : DefSet (rawRVSpace (M := M) U.arity) S)
    (hA : A.carrier ⊆ U.domain.carrier) (hB : B.carrier ⊆ U.domain.carrier)
    (hd : Disjoint A.carrier B.carrier) :
    rvCoprodObject (U.restrict A hA) (U.restrict B hB) ≅
      U.restrict (A.union B) (rvUnionSubset U A B hA hB) :=
  (rvCoprodIsColimit (U.restrict A hA) (U.restrict B hB)).coconePointUniqueUpToIso
    (rvUnionIsColimit U A B hA hB hd)

end SpecialTransformations.Section4

end
