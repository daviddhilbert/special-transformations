module

public import Section4.MixedProducts
public import Section4.UnionMapLaws
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

def vfAllProductFst (U V : VFAllObject (M := M) S) : vfAllProductObject U V ⟶ U :=
  (Map.prodFst U.set V.set).comp (mixedUnpack U.set V.set)

def vfAllProductSnd (U V : VFAllObject (M := M) S) : vfAllProductObject U V ⟶ V :=
  (Map.prodSnd U.set V.set).comp (mixedUnpack U.set V.set)

def vfAllProductLift {U V W : VFAllObject (M := M) S} (f : W ⟶ U) (g : W ⟶ V) :
    W ⟶ vfAllProductObject U V := (mixedPack U.set V.set).toImage.comp (f.pair g)

theorem vfAllProductLift_fst {U V W : VFAllObject (M := M) S} (f : W ⟶ U) (g : W ⟶ V) :
    vfAllProductLift f g ≫ vfAllProductFst U V = f := by
  apply Map.ext
  intro a
  change Map.prodFst U.set V.set
    (mixedUnpack U.set V.set ((mixedPack U.set V.set).toImage (Map.pair f g a))) =
      DefinableSetCat.homFunction f a
  rw [mixedUnpack_pack]
  rfl

theorem vfAllProductLift_snd {U V W : VFAllObject (M := M) S} (f : W ⟶ U) (g : W ⟶ V) :
    vfAllProductLift f g ≫ vfAllProductSnd U V = g := by
  apply Map.ext
  intro a
  change Map.prodSnd U.set V.set
    (mixedUnpack U.set V.set ((mixedPack U.set V.set).toImage (Map.pair f g a))) =
      DefinableSetCat.homFunction g a
  rw [mixedUnpack_pack]
  rfl

theorem vfAllProduct_hom_ext {U V W : VFAllObject (M := M) S}
    {f g : W ⟶ vfAllProductObject U V}
    (hl : f ≫ vfAllProductFst U V = g ≫ vfAllProductFst U V)
    (hr : f ≫ vfAllProductSnd U V = g ≫ vfAllProductSnd U V) : f = g := by
  apply Map.ext
  intro a
  apply Map.inverse_injective (mixedPack U.set V.set).toImage (mixedPackToImage_bijective U.set V.set)
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Subtype.val
      (congrArg (fun h : W ⟶ U => DefinableSetCat.homFunction h a) hl)
  · exact congrArg Subtype.val
      (congrArg (fun h : W ⟶ V => DefinableSetCat.homFunction h a) hr)

def vfAllProductIsLimit (U V : VFAllObject (M := M) S) :
    IsLimit (BinaryFan.mk (vfAllProductFst U V) (vfAllProductSnd U V)) :=
  BinaryFan.IsLimit.mk _ (fun f g => vfAllProductLift f g) vfAllProductLift_fst
    vfAllProductLift_snd (fun f g m hl hr => vfAllProduct_hom_ext
      (hl.trans (vfAllProductLift_fst f g).symm) (hr.trans (vfAllProductLift_snd f g).symm))

instance vfAllHasLimitPair (U V : VFAllObject (M := M) S) : HasLimit (pair U V) :=
  HasLimit.mk ⟨_, vfAllProductIsLimit U V⟩

instance vfAllHasBinaryProducts : HasBinaryProducts (VFAllObject (M := M) S) :=
  hasBinaryProducts_of_hasLimit_pair (VFAllObject (M := M) S)

def vfAllProductComparisonIso (U V : VFAllObject (M := M) S) : vfAllProductObject U V ≅ U ⨯ V :=
  (limit.isoLimitCone
    { cone := BinaryFan.mk (vfAllProductFst U V) (vfAllProductSnd U V)
      isLimit := vfAllProductIsLimit U V }).symm

def vfAllProductIso {U U' V V' : VFAllObject (M := M) S} (e : U ≅ U') (d : V ≅ V') :
    vfAllProductObject U V ≅ vfAllProductObject U' V' where
  hom := vfAllProductHom e.hom d.hom
  inv := vfAllProductHom e.inv d.inv
  hom_inv_id := by rw [← vfAllProductHom_comp, e.hom_inv_id, d.hom_inv_id, vfAllProductHom_id]
  inv_hom_id := by rw [← vfAllProductHom_comp, e.inv_hom_id, d.inv_hom_id, vfAllProductHom_id]

def vfAllProductCommIso (U V : VFAllObject (M := M) S) :
    vfAllProductObject U V ≅ vfAllProductObject V U :=
  (vfAllProductComparisonIso U V) ≪≫ prod.braiding U V ≪≫ (vfAllProductComparisonIso V U).symm

def vfAllProductAssocIso (U V W : VFAllObject (M := M) S) :
    vfAllProductObject (vfAllProductObject U V) W ≅ vfAllProductObject U (vfAllProductObject V W) :=
  (vfAllProductComparisonIso _ _) ≪≫ prod.mapIso (vfAllProductComparisonIso U V) (Iso.refl W) ≪≫
    prod.associator U V W ≪≫ (prod.mapIso (Iso.refl U) (vfAllProductComparisonIso V W)).symm ≪≫
    (vfAllProductComparisonIso _ _).symm

def vfAllUnitObject (S : Set M) : VFAllObject (M := M) S :=
  ⟨(0, 0), DefSet.univ (rawMixedSpace 0 0) S⟩

def vfAllUnitIsTerminal : IsTerminal (vfAllUnitObject (M := M) S) :=
  by
    letI : Nonempty (rawMixedSpace (M := M) 0 0).Carrier := ⟨(Fin.elim0, Fin.elim0)⟩
    letI : Subsingleton (rawMixedSpace (M := M) 0 0).Carrier := by
      change Subsingleton ((Fin 0 → SpecialTransformations.Milestone0.Transfer.VFType (M := M)) ×
        (Fin 0 → CanonicalRV.RVSort M))
      infer_instance
    apply IsTerminal.ofUniqueHom (fun U => Map.toSubsingleton U.set (rawMixedSpace 0 0))
    intro U f
    apply Map.ext
    intro a
    apply Subtype.ext
    exact @Subsingleton.elim (rawMixedSpace (M := M) 0 0).Carrier inferInstance _ _

instance vfAllHasTerminal : HasTerminal (VFAllObject (M := M) S) := vfAllUnitIsTerminal.hasTerminal

def vfAllProductRightUnitIso (U : VFAllObject (M := M) S) :
    vfAllProductObject U (vfAllUnitObject S) ≅ U :=
  vfAllProductComparisonIso _ _ ≪≫
    prod.mapIso (Iso.refl U) (vfAllUnitIsTerminal.uniqueUpToIso terminalIsTerminal) ≪≫
    prod.rightUnitor U

def vfAllProductLeftUnitIso (U : VFAllObject (M := M) S) :
    vfAllProductObject (vfAllUnitObject S) U ≅ U :=
  vfAllProductCommIso _ _ ≪≫ vfAllProductRightUnitIso U

end SpecialTransformations.Section4

end
