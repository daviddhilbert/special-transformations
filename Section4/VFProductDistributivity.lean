module

public import Section4.VFAllScissors
public import Section4.VFProductUniversal

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

def vfAllCoprodComparisonIso (U V : VFAllObject (M := M) S) : vfAllCoprodObject U V ≅ U ⨿ V :=
  (colimit.isoColimitCocone
    { cocone := BinaryCofan.mk (vfAllCoprodInl U V) (vfAllCoprodInr U V)
      isColimit := vfAllCoprodIsColimit U V }).symm

def vfAllCoprodIso {U U' V V' : VFAllObject (M := M) S} (e : U ≅ U') (d : V ≅ V') :
    vfAllCoprodObject U V ≅ vfAllCoprodObject U' V' :=
  vfAllCoprodComparisonIso _ _ ≪≫ coprod.mapIso e d ≪≫ (vfAllCoprodComparisonIso _ _).symm

theorem mixedProductDomain_union {n r m s : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) (B C : DefSet (rawMixedSpace (M := M) m s) S) :
    mixedProductDomain A (B.union C) = (mixedProductDomain A B).union (mixedProductDomain A C) := by
  apply DefSet.eq_of_carrier_eq
  ext p
  simp only [mem_mixedProductDomain, DefSet.union, Set.mem_union]
  tauto

theorem mixedProductDomain_disjoint {n r m s : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) (B C : DefSet (rawMixedSpace (M := M) m s) S)
    (hd : Disjoint B.carrier C.carrier) :
    Disjoint (mixedProductDomain A B).carrier (mixedProductDomain A C).carrier := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  exact Set.disjoint_left.mp hd ((mem_mixedProductDomain A B p).mp hp).2
    ((mem_mixedProductDomain A C p).mp hq).2

/-- Distributivity is an actual definable isomorphism: split the second
factor by its two tagged definable pieces, distribute the cartesian set
product over that disjoint union, and remove the tags. -/
def vfAllRightDistribIso (U V W : VFAllObject (M := M) S) :
    vfAllProductObject U (vfAllCoprodObject V W) ≅
      vfAllCoprodObject (vfAllProductObject U V) (vfAllProductObject U W) := by
  let T := vfAllCoprodObject V W
  let B := (mixedLeftTagMap V.set W.index.1 W.index.2).image
  let C := (mixedRightTagMap W.set V.index.1 V.index.2).image
  let I := (U.index.1 + T.index.1, U.index.2 + T.index.2)
  have eV : V ≅ DefinableSetCat.objOfSet T.index B :=
    DefinableSetCat.isoOfBijective (A := V) (B := DefinableSetCat.objOfSet T.index B)
      (mixedLeftTagMap V.set W.index.1 W.index.2).toImage
      (mixedLeftTagMap_toImage_bijective V.set W.index.1 W.index.2)
  have eW : W ≅ DefinableSetCat.objOfSet T.index C :=
    DefinableSetCat.isoOfBijective (A := W) (B := DefinableSetCat.objOfSet T.index C)
      (mixedRightTagMap W.set V.index.1 V.index.2).toImage
      (mixedRightTagMap_toImage_bijective W.set V.index.1 V.index.2)
  have he : vfAllProductObject U T = DefinableSetCat.objOfSet I
      ((mixedProductDomain U.set B).union (mixedProductDomain U.set C)) := by
    change (DefinableSetCat.mk (F := mixedFamily (M := M)) (S := S) I
      (mixedProductDomain U.set (B.union C))) =
      DefinableSetCat.mk (F := mixedFamily (M := M)) (S := S) I
        ((mixedProductDomain U.set B).union (mixedProductDomain U.set C))
    rw [mixedProductDomain_union]
  exact eqToIso he ≪≫
    (vfAllCoprodUnionIso I (mixedProductDomain U.set B) (mixedProductDomain U.set C)
      (mixedProductDomain_disjoint U.set B C (mixedTaggedImages_disjoint V.set W.set))).symm ≪≫
    vfAllCoprodIso (vfAllProductIso (Iso.refl U) eV).symm (vfAllProductIso (Iso.refl U) eW).symm

def vfAllLeftDistribIso (U V W : VFAllObject (M := M) S) :
    vfAllProductObject (vfAllCoprodObject U V) W ≅
      vfAllCoprodObject (vfAllProductObject U W) (vfAllProductObject V W) :=
  vfAllProductCommIso _ _ ≪≫ vfAllRightDistribIso W U V ≪≫
    vfAllCoprodIso (vfAllProductCommIso W U) (vfAllProductCommIso W V)

def vfAllProductEmptyIso (U : VFAllObject (M := M) S) :
    vfAllProductObject U (vfAllEmptyObject S) ≅ vfAllEmptyObject S := by
  apply vfAllEmptyIso
  apply Set.Subset.antisymm
  · intro p hp
    exact ((mem_mixedProductDomain U.set (vfAllEmptyObject S).set p).mp hp).2
  · exact Set.empty_subset _

end SpecialTransformations.Section4

end
