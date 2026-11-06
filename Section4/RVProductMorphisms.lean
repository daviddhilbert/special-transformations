import Section4.RVProduct

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {k l : ℕ}
variable {U U' U'' : RVObject (M := M) S k} {V V' V'' : RVObject (M := M) S l}

def rvProductMap (f : Map U.domain U'.domain) (g : Map V.domain V'.domain) :
    Map (rvProductObject U V).domain (rvProductObject U' V').domain :=
  (rvPack U'.domain V'.domain).toImage.comp
    ((Map.prodMap f g).comp (rvUnpack U.domain V.domain))

@[simp] theorem rvProductMap_unpack (f : Map U.domain U'.domain)
    (g : Map V.domain V'.domain) (a : (rvProductObject U V).domain) :
    rvUnpack U'.domain V'.domain (rvProductMap f g a) =
      Map.prodMap f g (rvUnpack U.domain V.domain a) := by
  exact rvUnpack_pack _ _ _

theorem rvProductMap_value (f : Map U.domain U'.domain)
    (g : Map V.domain V'.domain) (a : (rvProductObject U V).domain) :
    (rvProductObject U' V').value (rvProductMap f g a) =
      rvAppend
        (U'.value (f ⟨(rvUnpack U.domain V.domain a).val.1,
          (rvUnpack U.domain V.domain a).property.1⟩))
        (V'.value (g ⟨(rvUnpack U.domain V.domain a).val.2,
          (rvUnpack U.domain V.domain a).property.2⟩)) := by
  rw [rvProductObject_value, rvProductMap_unpack]
  rfl

/-- Cartesian products preserve the weight inequality and the finite
image of each volume fibre. The target degree is the sum of the degrees. -/
def rvProductHom (f : U ⟶ U') (g : V ⟶ V') :
    rvProductObject U V ⟶ rvProductObject U' V' where
  map := rvProductMap f.map g.map
  volumetric a := by
    rw [rvProductObject_weight, rvProductMap_value, rvWeight_append]
    exact Nat.add_le_add (f.volumetric _) (g.volumetric _)
  finite_volume_images t := by
    let tU := t ∘ Fin.castAdd l
    let tV := t ∘ Fin.natAdd k
    apply (((f.finite_volume_images tU).prod (g.finite_volume_images tV)).image
      (fun ab => rvAppend ab.1 ab.2)).subset
    rintro s ⟨a, ha, hs⟩
    let ab := rvUnpack U.domain V.domain a
    let u : U.domain := ⟨ab.val.1, ab.property.1⟩
    let v : V.domain := ⟨ab.val.2, ab.property.2⟩
    have hau : U.value u = tU := by
      funext i
      have h := congrFun ha (Fin.castAdd l i)
      simpa only [rvProductObject_value, rvAppend, Fin.append_left,
        u, ab, tU, Function.comp_apply] using h
    have hav : V.value v = tV := by
      funext i
      have h := congrFun ha (Fin.natAdd k i)
      simpa only [rvProductObject_value, rvAppend, Fin.append_right,
        v, ab, tV, Function.comp_apply] using h
    exact ⟨(U'.value (f.map u), V'.value (g.map v)),
      ⟨⟨u, hau, rfl⟩, ⟨v, hav, rfl⟩⟩,
      (rvProductMap_value f.map g.map a).symm.trans hs⟩

theorem rvProductHom_id (U : RVObject (M := M) S k) (V : RVObject (M := M) S l) :
    rvProductHom (𝟙 U) (𝟙 V) = 𝟙 (rvProductObject U V) := by
  apply RVHom.ext
  apply Map.ext
  intro a
  change (rvPack U.domain V.domain).toImage
    (Map.prodMap (Map.id U.domain) (Map.id V.domain) (rvUnpack U.domain V.domain a)) = a
  have he : Map.prodMap (Map.id U.domain) (Map.id V.domain)
      (rvUnpack U.domain V.domain a) = rvUnpack U.domain V.domain a := Subtype.ext rfl
  rw [he, rvPack_unpack]

theorem rvProductHom_comp (f : U ⟶ U') (f' : U' ⟶ U'')
    (g : V ⟶ V') (g' : V' ⟶ V'') :
    rvProductHom (f ≫ f') (g ≫ g') = rvProductHom f g ≫ rvProductHom f' g' := by
  apply RVHom.ext
  apply Map.ext
  intro a
  change (rvPack U''.domain V''.domain).toImage
      (Map.prodMap (f'.map.comp f.map) (g'.map.comp g.map)
        (rvUnpack U.domain V.domain a)) =
    (rvPack U''.domain V''.domain).toImage
      (Map.prodMap f'.map g'.map
        (rvUnpack U'.domain V'.domain (rvProductMap f.map g.map a)))
  rw [rvProductMap_unpack]
  apply congrArg (rvPack U''.domain V''.domain).toImage
  exact Subtype.ext rfl

def rvProductIso (e : U ≅ U') (d : V ≅ V') :
    rvProductObject U V ≅ rvProductObject U' V' where
  hom := rvProductHom e.hom d.hom
  inv := rvProductHom e.inv d.inv
  hom_inv_id := by rw [← rvProductHom_comp, e.hom_inv_id, d.hom_inv_id, rvProductHom_id]
  inv_hom_id := by rw [← rvProductHom_comp, e.inv_hom_id, d.inv_hom_id, rvProductHom_id]

end SpecialTransformations.Section4

end
