import Section4.RVTagging
import Section4.RVIsoTools
import Section4.UnionMapLaws
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k n m : ℕ}

theorem rvLeftTagMap_toImage_bijective (A : DefSet (rawRVSpace (M := M) n) S) (m : ℕ) :
    Function.Bijective (rvLeftTagMap A m).toImage := by
  constructor
  · intro a b he
    exact Subtype.ext (rvLeftTag_injective m (congrArg Subtype.val he))
  · rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩

theorem rvRightTagMap_toImage_bijective (B : DefSet (rawRVSpace (M := M) m) S) (n : ℕ) :
    Function.Bijective (rvRightTagMap B n).toImage := by
  constructor
  · intro a b he
    exact Subtype.ext (rvRightTag_injective n (congrArg Subtype.val he))
  · rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩

def rvUntagLeft (A : DefSet (rawRVSpace (M := M) n) S) (m : ℕ) :
    Map (rvLeftTagMap A m).image A :=
  (rvLeftTagMap A m).toImage.inverse (rvLeftTagMap_toImage_bijective A m)

def rvUntagRight (B : DefSet (rawRVSpace (M := M) m) S) (n : ℕ) :
    Map (rvRightTagMap B n).image B :=
  (rvRightTagMap B n).toImage.inverse (rvRightTagMap_toImage_bijective B n)

theorem rvTaggedImages_disjoint (A : DefSet (rawRVSpace (M := M) n) S)
    (B : DefSet (rawRVSpace (M := M) m) S) :
    Disjoint (rvLeftTagMap A m).image.carrier (rvRightTagMap B n).image.carrier := by
  apply Set.disjoint_left.mpr
  rintro x ⟨a, ha⟩ ⟨b, hb⟩
  exact rvTag_disjoint a.val b.val (ha.trans hb.symm)

/-- A disjoint union of actual definable RV sets, with two definable tags.
Its label is the original label on each summand. The tags use the existing
RV zero and RV one, without any additional absorbing point. -/
def rvCoprodObject (U V : RVObject (M := M) S k) : RVObject (M := M) S k where
  arity := 1 + (U.arity + V.arity)
  domain := (rvLeftTagMap U.domain V.arity).image.union (rvRightTagMap V.domain U.arity).image
  volume := (U.volume.comp (rvUntagLeft U.domain V.arity)).union
    (V.volume.comp (rvUntagRight V.domain U.arity))

theorem rvCoprod_nonempty_iff (U V : RVObject (M := M) S k) :
    (rvCoprodObject U V).domain.carrier.Nonempty ↔
      U.domain.carrier.Nonempty ∨ V.domain.carrier.Nonempty := by
  constructor
  · rintro ⟨x, hx | hx⟩
    · obtain ⟨a, _⟩ := hx
      exact Or.inl ⟨a.val, a.property⟩
    · obtain ⟨b, _⟩ := hx
      exact Or.inr ⟨b.val, b.property⟩
  · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · exact ⟨rvLeftTag V.arity a, Or.inl ⟨⟨a, ha⟩, rfl⟩⟩
    · exact ⟨rvRightTag U.arity b, Or.inr ⟨⟨b, hb⟩, rfl⟩⟩

theorem rvCoprod_finite_volume (U V : RVObject (M := M) S k)
    (hU : U.volume.FiniteFibres) (hV : V.volume.FiniteFibres) :
    (rvCoprodObject U V).volume.FiniteFibres :=
  (hU.comp (Map.finiteFibres_of_injective
    (Map.inverse_injective _ (rvLeftTagMap_toImage_bijective U.domain V.arity)))).union
  (hV.comp (Map.finiteFibres_of_injective
    (Map.inverse_injective _ (rvRightTagMap_toImage_bijective V.domain U.arity))))

def rvFiniteCoprodObject (U V : RVFiniteObject (M := M) S k) : RVFiniteObject (M := M) S k :=
  ⟨rvCoprodObject U.obj V.obj, rvCoprod_finite_volume U.obj V.obj U.property V.property⟩

def rvCoprodLeftMap (U V : RVObject (M := M) S k) : Map U.domain (rvCoprodObject U V).domain :=
  (Map.inclusion (show (rvLeftTagMap U.domain V.arity).image.carrier ⊆
    (rvCoprodObject U V).domain.carrier from fun _ h => Or.inl h)).comp
    (rvLeftTagMap U.domain V.arity).toImage

def rvCoprodRightMap (U V : RVObject (M := M) S k) : Map V.domain (rvCoprodObject U V).domain :=
  (Map.inclusion (show (rvRightTagMap V.domain U.arity).image.carrier ⊆
    (rvCoprodObject U V).domain.carrier from fun _ h => Or.inr h)).comp
    (rvRightTagMap V.domain U.arity).toImage

theorem rvCoprod_value_left (U V : RVObject (M := M) S k) (a : U.domain) :
    (rvCoprodObject U V).value (rvCoprodLeftMap U V a) = U.value a := by
  change (((U.volume.comp (rvUntagLeft U.domain V.arity)).union
    (V.volume.comp (rvUntagRight V.domain U.arity)))
      ⟨((rvLeftTagMap U.domain V.arity).toImage a).val,
        Or.inl ((rvLeftTagMap U.domain V.arity).toImage a).property⟩).val = U.value a
  rw [Map.union_on_left]
  exact congrArg (fun u : U.domain => U.value u) (Map.inverse_apply _ _ a)

theorem rvCoprod_value_right (U V : RVObject (M := M) S k) (b : V.domain) :
    (rvCoprodObject U V).value (rvCoprodRightMap U V b) = V.value b := by
  change (((U.volume.comp (rvUntagLeft U.domain V.arity)).union
    (V.volume.comp (rvUntagRight V.domain U.arity)))
      ⟨((rvRightTagMap V.domain U.arity).toImage b).val,
        Or.inr ((rvRightTagMap V.domain U.arity).toImage b).property⟩).val = V.value b
  rw [Map.union_on_right _ _ (rvTaggedImages_disjoint U.domain V.domain)]
  exact congrArg (fun v : V.domain => V.value v) (Map.inverse_apply _ _ b)

def rvCoprodInl (U V : RVObject (M := M) S k) : U ⟶ rvCoprodObject U V :=
  rvHomOfVolumePreserving (rvCoprodLeftMap U V) (rvCoprod_value_left U V)

def rvCoprodInr (U V : RVObject (M := M) S k) : V ⟶ rvCoprodObject U V :=
  rvHomOfVolumePreserving (rvCoprodRightMap U V) (rvCoprod_value_right U V)

def rvCoprodDesc {U V W : RVObject (M := M) S k} (f : U ⟶ W) (g : V ⟶ W) :
    rvCoprodObject U V ⟶ W where
  map := (f.map.comp (rvUntagLeft U.domain V.arity)).union
    (g.map.comp (rvUntagRight V.domain U.arity))
  volumetric a := by
    by_cases ha : a.val ∈ (rvLeftTagMap U.domain V.arity).image.carrier
    · simpa only [RVObject.value, rvCoprodObject, Map.union, Map.comp, dif_pos ha] using
        f.volumetric (rvUntagLeft U.domain V.arity ⟨a.val, ha⟩)
    · simpa only [RVObject.value, rvCoprodObject, Map.union, Map.comp, dif_neg ha] using
        g.volumetric (rvUntagRight V.domain U.arity ⟨a.val, a.property.resolve_left ha⟩)
  finite_volume_images t := by
    apply ((f.finite_volume_images t).union (g.finite_volume_images t)).subset
    rintro s ⟨a, ha, hs⟩
    by_cases hleft : a.val ∈ (rvLeftTagMap U.domain V.arity).image.carrier
    · left
      refine ⟨rvUntagLeft U.domain V.arity ⟨a.val, hleft⟩, ?_, ?_⟩
      · simpa only [RVObject.value, rvCoprodObject, Map.union, Map.comp, dif_pos hleft] using ha
      · simpa only [Map.union, Map.comp, dif_pos hleft] using hs
    · right
      refine ⟨rvUntagRight V.domain U.arity ⟨a.val, a.property.resolve_left hleft⟩, ?_, ?_⟩
      · simpa only [RVObject.value, rvCoprodObject, Map.union, Map.comp, dif_neg hleft] using ha
      · simpa only [Map.union, Map.comp, dif_neg hleft] using hs

theorem rvCoprodInl_desc {U V W : RVObject (M := M) S k} (f : U ⟶ W) (g : V ⟶ W) :
    rvCoprodInl U V ≫ rvCoprodDesc f g = f := by
  apply RVHom.ext
  apply Map.ext
  intro a
  change ((f.map.comp (rvUntagLeft U.domain V.arity)).union
    (g.map.comp (rvUntagRight V.domain U.arity)))
      ⟨((rvLeftTagMap U.domain V.arity).toImage a).val,
        Or.inl ((rvLeftTagMap U.domain V.arity).toImage a).property⟩ = f.map a
  rw [Map.union_on_left]
  exact congrArg f.map (Map.inverse_apply _ _ a)

theorem rvCoprodInr_desc {U V W : RVObject (M := M) S k} (f : U ⟶ W) (g : V ⟶ W) :
    rvCoprodInr U V ≫ rvCoprodDesc f g = g := by
  apply RVHom.ext
  apply Map.ext
  intro b
  change ((f.map.comp (rvUntagLeft U.domain V.arity)).union
    (g.map.comp (rvUntagRight V.domain U.arity)))
      ⟨((rvRightTagMap V.domain U.arity).toImage b).val,
        Or.inr ((rvRightTagMap V.domain U.arity).toImage b).property⟩ = g.map b
  rw [Map.union_on_right _ _ (rvTaggedImages_disjoint U.domain V.domain)]
  exact congrArg g.map (Map.inverse_apply _ _ b)

theorem rvCoprod_hom_ext {U V W : RVObject (M := M) S k}
    {f g : rvCoprodObject U V ⟶ W}
    (hl : rvCoprodInl U V ≫ f = rvCoprodInl U V ≫ g)
    (hr : rvCoprodInr U V ≫ f = rvCoprodInr U V ≫ g) : f = g := by
  apply RVHom.ext
  apply Map.ext
  intro a
  rcases a.property with ha | ha
  · let u := rvUntagLeft U.domain V.arity ⟨a.val, ha⟩
    have he : rvCoprodLeftMap U V u = a :=
      Subtype.ext (congrArg (fun x : (rvLeftTagMap U.domain V.arity).image => x.val) (Map.apply_inverse
        (rvLeftTagMap U.domain V.arity).toImage (rvLeftTagMap_toImage_bijective U.domain V.arity)
        ⟨a.val, ha⟩))
    have h := congrArg (fun h : RVHom U W => h.map u) hl
    change f.map (rvCoprodLeftMap U V u) = g.map (rvCoprodLeftMap U V u) at h
    rwa [he] at h
  · let v := rvUntagRight V.domain U.arity ⟨a.val, ha⟩
    have he : rvCoprodRightMap U V v = a :=
      Subtype.ext (congrArg (fun x : (rvRightTagMap V.domain U.arity).image => x.val) (Map.apply_inverse
        (rvRightTagMap V.domain U.arity).toImage (rvRightTagMap_toImage_bijective V.domain U.arity)
        ⟨a.val, ha⟩))
    have h := congrArg (fun h : RVHom V W => h.map v) hr
    change f.map (rvCoprodRightMap U V v) = g.map (rvCoprodRightMap U V v) at h
    rwa [he] at h

def rvCoprodIsColimit (U V : RVObject (M := M) S k) :
    IsColimit (BinaryCofan.mk (rvCoprodInl U V) (rvCoprodInr U V)) :=
  BinaryCofan.IsColimit.mk _ (fun f g => rvCoprodDesc f g)
    rvCoprodInl_desc rvCoprodInr_desc (fun f g m hl hr =>
      rvCoprod_hom_ext (hl.trans (rvCoprodInl_desc f g).symm)
        (hr.trans (rvCoprodInr_desc f g).symm))

def rvEmptyHom (U : RVObject (M := M) S k) : RVHom (RVObject.empty S k) U where
  map := Map.emptyTo U.domain
  volumetric a := False.elim a.property
  finite_volume_images t := by
    apply Set.finite_empty.subset
    rintro s ⟨a, _, _⟩
    exact False.elim a.property

def rvEmptyIsInitial : IsInitial (RVObject.empty (M := M) S k) :=
  IsInitial.ofUniqueHom rvEmptyHom (fun U f => by
    apply RVHom.ext
    apply Map.ext
    intro a
    exact False.elim a.property)

end SpecialTransformations.Section4

end
