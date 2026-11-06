import Section4.RVAppend

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {n m k l : ℕ}

def rvPack (A : DefSet (rawRVSpace (M := M) n) S)
    (B : DefSet (rawRVSpace (M := M) m) S) :
    Map (A.prod B) (DefSet.univ (rawRVSpace (n + m)) S) :=
  (rvAppendMap S n m).restrict (Set.subset_univ _)

theorem rvPack_injective (A : DefSet (rawRVSpace (M := M) n) S)
    (B : DefSet (rawRVSpace (M := M) m) S) : Function.Injective (rvPack A B) := by
  intro a b he
  exact Subtype.ext (rvAppend_injective (congrArg Subtype.val he))

def rvProductDomain (A : DefSet (rawRVSpace (M := M) n) S)
    (B : DefSet (rawRVSpace (M := M) m) S) : DefSet (rawRVSpace (M := M) (n + m)) S :=
  (rvPack A B).image

theorem rvPackToImage_bijective (A : DefSet (rawRVSpace (M := M) n) S)
    (B : DefSet (rawRVSpace (M := M) m) S) :
    Function.Bijective (rvPack A B).toImage := by
  constructor
  · intro a b he
    apply rvPack_injective A B
    exact Subtype.ext (congrArg (fun x : rvProductDomain A B => x.val) he)
  · rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩

def rvUnpack (A : DefSet (rawRVSpace (M := M) n) S)
    (B : DefSet (rawRVSpace (M := M) m) S) : Map (rvProductDomain A B) (A.prod B) :=
  (rvPack A B).toImage.inverse (rvPackToImage_bijective A B)

@[simp] theorem rvUnpack_pack (A : DefSet (rawRVSpace (M := M) n) S)
    (B : DefSet (rawRVSpace (M := M) m) S) (a : A.prod B) :
    rvUnpack A B ((rvPack A B).toImage a) = a :=
  Map.inverse_apply _ _ _

@[simp] theorem rvPack_unpack (A : DefSet (rawRVSpace (M := M) n) S)
    (B : DefSet (rawRVSpace (M := M) m) S) (a : rvProductDomain A B) :
    (rvPack A B).toImage (rvUnpack A B a) = a :=
  Map.apply_inverse _ _ _

/-- The genuine cartesian product has concatenated domain and label tuples.
In degree zero the label is exactly the other factor's label (up to the
canonical empty-tuple coordinate identification), as required in 4.21. -/
def rvProductObject (U : RVObject (M := M) S k) (V : RVObject (M := M) S l) :
    RVObject (M := M) S (k + l) where
  arity := U.arity + V.arity
  domain := rvProductDomain U.domain V.domain
  volume := (rvAppendMap S k l).comp
    ((Map.prodMap U.volume V.volume).toUniv.comp (rvUnpack U.domain V.domain))

theorem rvProductObject_value (U : RVObject (M := M) S k)
    (V : RVObject (M := M) S l) (a : (rvProductObject U V).domain) :
    (rvProductObject U V).value a =
      rvAppend (U.value ⟨(rvUnpack U.domain V.domain a).val.1,
        (rvUnpack U.domain V.domain a).property.1⟩)
        (V.value ⟨(rvUnpack U.domain V.domain a).val.2,
        (rvUnpack U.domain V.domain a).property.2⟩) := rfl

theorem rvProductObject_weight (U : RVObject (M := M) S k)
    (V : RVObject (M := M) S l) (a : (rvProductObject U V).domain) :
    rvWeight ((rvProductObject U V).value a) =
      rvWeight (U.value ⟨(rvUnpack U.domain V.domain a).val.1,
        (rvUnpack U.domain V.domain a).property.1⟩) +
      rvWeight (V.value ⟨(rvUnpack U.domain V.domain a).val.2,
        (rvUnpack U.domain V.domain a).property.2⟩) :=
  rvWeight_append _ _

theorem rvProductObject_finite_volume (U : RVObject (M := M) S k)
    (V : RVObject (M := M) S l) (hU : U.volume.FiniteFibres)
    (hV : V.volume.FiniteFibres) : (rvProductObject U V).volume.FiniteFibres := by
  have hp := hU.prodMap hV
  have hpt : (Map.prodMap U.volume V.volume).toUniv.FiniteFibres := by
    intro z
    apply (hp ⟨z.val, Set.mem_univ _, Set.mem_univ _⟩).subset
    intro a ha
    exact Subtype.ext (congrArg
      (fun x : DefSet.univ ((rawRVSpace (M := M) k).prod (rawRVSpace l)) S => x.val) ha)
  apply (Map.finiteFibres_of_injective (rvAppendMap_bijective S k l).1).comp
  apply hpt.comp
  apply Map.finiteFibres_of_injective
  intro a b he
  have he' := congrArg (rvPack U.domain V.domain).toImage he
  simpa only [rvPack_unpack] using he'

end SpecialTransformations.Section4

end
