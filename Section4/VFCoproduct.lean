module

public import Section4.MixedTagging
public import Section4.VFCategories
public import Section4.UnionMapLaws
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

theorem mixedLeftTagMap_toImage_bijective {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) (m s : ℕ) :
    Function.Bijective (mixedLeftTagMap A m s).toImage := by
  constructor
  · intro a b he
    exact Subtype.ext (mixedLeftTag_injective m s (congrArg Subtype.val he))
  · rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩

theorem mixedRightTagMap_toImage_bijective {m s : ℕ}
    (B : DefSet (rawMixedSpace (M := M) m s) S) (n r : ℕ) :
    Function.Bijective (mixedRightTagMap B n r).toImage := by
  constructor
  · intro a b he
    exact Subtype.ext (mixedRightTag_injective n r (congrArg Subtype.val he))
  · rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩

def mixedUntagLeft {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S) (m s : ℕ) :
    Map (mixedLeftTagMap A m s).image A :=
  (mixedLeftTagMap A m s).toImage.inverse (mixedLeftTagMap_toImage_bijective A m s)

def mixedUntagRight {m s : ℕ} (B : DefSet (rawMixedSpace (M := M) m s) S) (n r : ℕ) :
    Map (mixedRightTagMap B n r).image B :=
  (mixedRightTagMap B n r).toImage.inverse (mixedRightTagMap_toImage_bijective B n r)

theorem mixedTaggedImages_disjoint {n r m s : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (B : DefSet (rawMixedSpace (M := M) m s) S) :
    Disjoint (mixedLeftTagMap A m s).image.carrier (mixedRightTagMap B n r).image.carrier := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ha⟩ ⟨b, hb⟩
  exact mixedTag_disjoint a.val b.val (ha.trans hb.symm)

def vfAllCoprodObject (U V : VFAllObject (M := M) S) : VFAllObject (M := M) S :=
  ⟨(U.index.1 + V.index.1, 1 + (U.index.2 + V.index.2)),
    (mixedLeftTagMap U.set V.index.1 V.index.2).image.union
      (mixedRightTagMap V.set U.index.1 U.index.2).image⟩

def vfAllCoprodInl (U V : VFAllObject (M := M) S) : U ⟶ vfAllCoprodObject U V :=
  (Map.inclusion (show (mixedLeftTagMap U.set V.index.1 V.index.2).image.carrier ⊆
    (vfAllCoprodObject U V).set.carrier from fun _ h => Or.inl h)).comp
      (mixedLeftTagMap U.set V.index.1 V.index.2).toImage

def vfAllCoprodInr (U V : VFAllObject (M := M) S) : V ⟶ vfAllCoprodObject U V :=
  (Map.inclusion (show (mixedRightTagMap V.set U.index.1 U.index.2).image.carrier ⊆
    (vfAllCoprodObject U V).set.carrier from fun _ h => Or.inr h)).comp
      (mixedRightTagMap V.set U.index.1 U.index.2).toImage

def vfAllCoprodDesc {U V W : VFAllObject (M := M) S} (f : U ⟶ W) (g : V ⟶ W) :
    vfAllCoprodObject U V ⟶ W :=
  (f.comp (mixedUntagLeft U.set V.index.1 V.index.2)).union
    (g.comp (mixedUntagRight V.set U.index.1 U.index.2))

theorem vfAllCoprodInl_desc {U V W : VFAllObject (M := M) S} (f : U ⟶ W) (g : V ⟶ W) :
    vfAllCoprodInl U V ≫ vfAllCoprodDesc f g = f := by
  apply Map.ext
  intro a
  change ((f.comp (mixedUntagLeft U.set V.index.1 V.index.2)).union
    (g.comp (mixedUntagRight V.set U.index.1 U.index.2)))
      ⟨((mixedLeftTagMap U.set V.index.1 V.index.2).toImage a).val,
        Or.inl ((mixedLeftTagMap U.set V.index.1 V.index.2).toImage a).property⟩ =
      DefinableSetCat.homFunction f a
  rw [Map.union_on_left]
  exact congrArg (DefinableSetCat.homFunction f) (Map.inverse_apply _ _ a)

theorem vfAllCoprodInr_desc {U V W : VFAllObject (M := M) S} (f : U ⟶ W) (g : V ⟶ W) :
    vfAllCoprodInr U V ≫ vfAllCoprodDesc f g = g := by
  apply Map.ext
  intro b
  change ((f.comp (mixedUntagLeft U.set V.index.1 V.index.2)).union
    (g.comp (mixedUntagRight V.set U.index.1 U.index.2)))
      ⟨((mixedRightTagMap V.set U.index.1 U.index.2).toImage b).val,
        Or.inr ((mixedRightTagMap V.set U.index.1 U.index.2).toImage b).property⟩ =
      DefinableSetCat.homFunction g b
  rw [Map.union_on_right _ _ (mixedTaggedImages_disjoint U.set V.set)]
  exact congrArg (DefinableSetCat.homFunction g) (Map.inverse_apply _ _ b)

theorem vfAllCoprod_hom_ext {U V W : VFAllObject (M := M) S}
    {f g : vfAllCoprodObject U V ⟶ W}
    (hl : vfAllCoprodInl U V ≫ f = vfAllCoprodInl U V ≫ g)
    (hr : vfAllCoprodInr U V ≫ f = vfAllCoprodInr U V ≫ g) : f = g := by
  apply Map.ext
  intro a
  rcases a.property with ha | hb
  · let u := mixedUntagLeft U.set V.index.1 V.index.2 ⟨a.val, ha⟩
    have he : DefinableSetCat.homFunction (vfAllCoprodInl U V) u = a := Subtype.ext
      (congrArg (fun z : (mixedLeftTagMap U.set V.index.1 V.index.2).image => z.val)
        (Map.apply_inverse (mixedLeftTagMap U.set V.index.1 V.index.2).toImage
          (mixedLeftTagMap_toImage_bijective U.set V.index.1 V.index.2) ⟨a.val, ha⟩))
    have hh := congrArg (fun h : U ⟶ W => DefinableSetCat.homFunction h u) hl
    change DefinableSetCat.homFunction f
      (DefinableSetCat.homFunction (vfAllCoprodInl U V) u) =
      DefinableSetCat.homFunction g (DefinableSetCat.homFunction (vfAllCoprodInl U V) u) at hh
    rwa [he] at hh
  · let v := mixedUntagRight V.set U.index.1 U.index.2 ⟨a.val, hb⟩
    have he : DefinableSetCat.homFunction (vfAllCoprodInr U V) v = a := Subtype.ext
      (congrArg (fun z : (mixedRightTagMap V.set U.index.1 U.index.2).image => z.val)
        (Map.apply_inverse (mixedRightTagMap V.set U.index.1 U.index.2).toImage
          (mixedRightTagMap_toImage_bijective V.set U.index.1 U.index.2) ⟨a.val, hb⟩))
    have hh := congrArg (fun h : V ⟶ W => DefinableSetCat.homFunction h v) hr
    change DefinableSetCat.homFunction f
      (DefinableSetCat.homFunction (vfAllCoprodInr U V) v) =
      DefinableSetCat.homFunction g (DefinableSetCat.homFunction (vfAllCoprodInr U V) v) at hh
    rwa [he] at hh

def vfAllCoprodIsColimit (U V : VFAllObject (M := M) S) :
    IsColimit (BinaryCofan.mk (vfAllCoprodInl U V) (vfAllCoprodInr U V)) :=
  BinaryCofan.IsColimit.mk _ (fun f g => vfAllCoprodDesc f g)
    vfAllCoprodInl_desc vfAllCoprodInr_desc (fun f g m hl hr =>
      vfAllCoprod_hom_ext (hl.trans (vfAllCoprodInl_desc f g).symm)
        (hr.trans (vfAllCoprodInr_desc f g).symm))

def vfAllEmptyObject (S : Set M) : VFAllObject (M := M) S :=
  ⟨(0, 0), DefSet.empty (rawMixedSpace 0 0) S⟩

def vfAllEmptyIsInitial : IsInitial (vfAllEmptyObject (M := M) S) :=
  IsInitial.ofUniqueHom (fun U => Map.emptyTo U.set) (fun U f => by
    apply Map.ext
    intro a
    exact False.elim a.property)

end SpecialTransformations.Section4

end
