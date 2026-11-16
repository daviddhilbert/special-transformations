module

public import Section4.VFAppend
public import Section4.RVAppend
public import Section4.VFCategories

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {n r m s : ℕ}

/-- Concatenate VF coordinates and RV coordinates separately, retaining
their actual sorts and the released language. -/
def mixedAppendMap (S : Set M) (n r m s : ℕ) :
    Map (DefSet.univ ((rawMixedSpace (M := M) n r).prod (rawMixedSpace m s)) S)
      (DefSet.univ (rawMixedSpace (n + m) (r + s)) S) :=
  (Map.prodUnivMap (vfAppendMap S n m) (rvAppendMap S r s)).comp
    (Map.shuffle (rawVFSpace n) (rawRVSpace r) (rawVFSpace m) (rawRVSpace s) S)

theorem mixedAppendMap_bijective (S : Set M) (n r m s : ℕ) :
    Function.Bijective (mixedAppendMap (M := M) S n r m s) :=
  (Map.prodUnivMap_bijective _ _ (vfAppendMap_bijective S n m)
    (rvAppendMap_bijective S r s)).comp (Map.shuffle_bijective _ _ _ _ _)

def mixedPack (A : DefSet (rawMixedSpace (M := M) n r) S)
    (B : DefSet (rawMixedSpace (M := M) m s) S) :
    Map (A.prod B) (DefSet.univ (rawMixedSpace (n + m) (r + s)) S) :=
  (mixedAppendMap S n r m s).restrict (Set.subset_univ _)

theorem mixedPack_injective (A : DefSet (rawMixedSpace (M := M) n r) S)
    (B : DefSet (rawMixedSpace (M := M) m s) S) : Function.Injective (mixedPack A B) := by
  intro a b he
  have he' := (mixedAppendMap_bijective S n r m s).1
    (show mixedAppendMap S n r m s ⟨a.val, Set.mem_univ _⟩ =
      mixedAppendMap S n r m s ⟨b.val, Set.mem_univ _⟩ from he)
  exact Subtype.ext (congrArg
    (fun z : DefSet.univ ((rawMixedSpace (M := M) n r).prod (rawMixedSpace m s)) S => z.val) he')

def mixedProductDomain (A : DefSet (rawMixedSpace (M := M) n r) S)
    (B : DefSet (rawMixedSpace (M := M) m s) S) :
    DefSet (rawMixedSpace (M := M) (n + m) (r + s)) S := (mixedPack A B).image

theorem mem_mixedProductDomain (A : DefSet (rawMixedSpace (M := M) n r) S)
    (B : DefSet (rawMixedSpace (M := M) m s) S)
    (p : (rawMixedSpace (M := M) (n + m) (r + s)).Carrier) :
    p ∈ (mixedProductDomain A B).carrier ↔
      (p.1 ∘ Fin.castAdd m, p.2 ∘ Fin.castAdd s) ∈ A.carrier ∧
      (p.1 ∘ Fin.natAdd n, p.2 ∘ Fin.natAdd r) ∈ B.carrier := by
  constructor
  · rintro ⟨a, ha⟩
    change (vfAppend a.val.1.1 a.val.2.1, rvAppend a.val.1.2 a.val.2.2) = p at ha
    rw [← ha]
    have hA : (a.val.1.1, a.val.1.2) ∈ A.carrier ∧
        (a.val.2.1, a.val.2.2) ∈ B.carrier := a.property
    simpa only [vfAppend, rvAppend, Function.comp_def, Fin.append_left, Fin.append_right]
      using hA
  · rintro ⟨ha, hb⟩
    refine ⟨⟨((p.1 ∘ Fin.castAdd m, p.2 ∘ Fin.castAdd s),
      (p.1 ∘ Fin.natAdd n, p.2 ∘ Fin.natAdd r)), ha, hb⟩, ?_⟩
    exact Prod.ext Fin.append_castAdd_natAdd Fin.append_castAdd_natAdd

theorem mixedPackToImage_bijective (A : DefSet (rawMixedSpace (M := M) n r) S)
    (B : DefSet (rawMixedSpace (M := M) m s) S) :
    Function.Bijective (mixedPack A B).toImage := by
  constructor
  · intro a b he
    apply mixedPack_injective A B
    exact Subtype.ext (congrArg (fun z : mixedProductDomain A B => z.val) he)
  · rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩

def mixedUnpack (A : DefSet (rawMixedSpace (M := M) n r) S)
    (B : DefSet (rawMixedSpace (M := M) m s) S) :
    Map (mixedProductDomain A B) (A.prod B) :=
  (mixedPack A B).toImage.inverse (mixedPackToImage_bijective A B)

@[simp] theorem mixedUnpack_pack (A : DefSet (rawMixedSpace (M := M) n r) S)
    (B : DefSet (rawMixedSpace (M := M) m s) S) (a : A.prod B) :
    mixedUnpack A B ((mixedPack A B).toImage a) = a := Map.inverse_apply _ _ _

@[simp] theorem mixedPack_unpack (A : DefSet (rawMixedSpace (M := M) n r) S)
    (B : DefSet (rawMixedSpace (M := M) m s) S) (a : mixedProductDomain A B) :
    (mixedPack A B).toImage (mixedUnpack A B a) = a := Map.apply_inverse _ _ _

def vfAllProductObject (U V : VFAllObject (M := M) S) : VFAllObject (M := M) S :=
  ⟨(U.index.1 + V.index.1, U.index.2 + V.index.2), mixedProductDomain U.set V.set⟩

def vfAllProductHom {U U' V V' : VFAllObject (M := M) S} (f : U ⟶ U') (g : V ⟶ V') :
    vfAllProductObject U V ⟶ vfAllProductObject U' V' :=
  (mixedPack U'.set V'.set).toImage.comp
    ((Map.prodMap f g).comp (mixedUnpack U.set V.set))

theorem vfAllProductHom_id (U V : VFAllObject (M := M) S) :
    vfAllProductHom (𝟙 U) (𝟙 V) = 𝟙 (vfAllProductObject U V) := by
  apply Map.ext
  intro a
  change (mixedPack U.set V.set).toImage
    (Map.prodMap (Map.id U.set) (Map.id V.set) (mixedUnpack U.set V.set a)) = a
  have he : Map.prodMap (Map.id U.set) (Map.id V.set)
      (mixedUnpack U.set V.set a) = mixedUnpack U.set V.set a := Subtype.ext rfl
  rw [he, mixedPack_unpack]

theorem vfAllProductHom_comp {U U' U'' V V' V'' : VFAllObject (M := M) S}
    (f : U ⟶ U') (f' : U' ⟶ U'') (g : V ⟶ V') (g' : V' ⟶ V'') :
    vfAllProductHom (f ≫ f') (g ≫ g') = vfAllProductHom f g ≫ vfAllProductHom f' g' := by
  apply Map.ext
  intro a
  change (mixedPack U''.set V''.set).toImage
      (Map.prodMap (f'.comp f) (g'.comp g) (mixedUnpack U.set V.set a)) =
    (mixedPack U''.set V''.set).toImage
      (Map.prodMap f' g'
        (mixedUnpack U'.set V'.set ((mixedPack U'.set V'.set).toImage
          (Map.prodMap f g (mixedUnpack U.set V.set a)))))
  rw [mixedUnpack_pack]
  apply congrArg (mixedPack U''.set V''.set).toImage
  exact Subtype.ext rfl

end SpecialTransformations.Section4

end
