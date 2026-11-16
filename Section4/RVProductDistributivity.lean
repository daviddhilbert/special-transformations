module

public import Section4.RVProductRestrictions
public import Section4.RVProductMorphisms
public import Section4.RVUnionCoproduct
public import Section4.RVIsomorphismClasses
public import Section4.RVEmptyIso

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k l : ℕ}

def rvCoprodComparisonIso (U V : RVObject (M := M) S k) : rvCoprodObject U V ≅ U ⨿ V :=
  (colimit.isoColimitCocone
    { cocone := BinaryCofan.mk (rvCoprodInl U V) (rvCoprodInr U V)
      isColimit := rvCoprodIsColimit U V }).symm

def rvCoprodIso {U U' V V' : RVObject (M := M) S k} (e : U ≅ U') (d : V ≅ V') :
    rvCoprodObject U V ≅ rvCoprodObject U' V' :=
  rvCoprodComparisonIso _ _ ≪≫ coprod.mapIso e d ≪≫ (rvCoprodComparisonIso _ _).symm

def rvCoprodLeftRestrictionIso (U V : RVObject (M := M) S k) :
    U ≅ (rvCoprodObject U V).restrict (rvLeftTagMap U.domain V.arity).image
      (fun _ h => Or.inl h) :=
  rvIsoOfVolumePreservingBijection (rvLeftTagMap U.domain V.arity).toImage
    (rvLeftTagMap_toImage_bijective U.domain V.arity) (rvCoprod_value_left U V)

def rvCoprodRightRestrictionIso (U V : RVObject (M := M) S k) :
    V ≅ (rvCoprodObject U V).restrict (rvRightTagMap V.domain U.arity).image
      (fun _ h => Or.inr h) :=
  rvIsoOfVolumePreservingBijection (rvRightTagMap V.domain U.arity).toImage
    (rvRightTagMap_toImage_bijective V.domain U.arity) (rvCoprod_value_right U V)

/-- Cartesian product distributes over the genuine RV coproduct. The
proof splits the tagged union into its actual definable pieces, uses the
set product's disjoint union, and removes the tags by RV isomorphisms. -/
def rvProductRightDistribIso (U : RVObject (M := M) S k)
    (V W : RVObject (M := M) S l) :
    rvProductObject U (rvCoprodObject V W) ≅
      rvCoprodObject (rvProductObject U V) (rvProductObject U W) := by
  let T := rvCoprodObject V W
  let B := (rvLeftTagMap V.domain W.arity).image
  let C := (rvRightTagMap W.domain V.arity).image
  have hB : B.carrier ⊆ T.domain.carrier := fun _ h => Or.inl h
  have hC : C.carrier ⊆ T.domain.carrier := fun _ h => Or.inr h
  let X := rvProductObject U T
  let PB := rvProductDomain U.domain B
  let PC := rvProductDomain U.domain C
  have hPB : PB.carrier ⊆ X.domain.carrier := rvProductRestrictionSubset U T B hB
  have hPC : PC.carrier ⊆ X.domain.carrier := rvProductRestrictionSubset U T C hC
  have hdomain : (PB.union PC).carrier = X.domain.carrier := by
    exact congrArg DefSet.carrier (rvProductDomain_union U.domain B C).symm
  have hself : X.restrict (PB.union PC) (rvUnionSubset X PB PC hPB hPC) ≅ X :=
    eqToIso (X.restrict_eq_of_carrier_eq _ X.domain _ (Set.Subset.refl _) hdomain) ≪≫
      rvSelfRestrictionIso X
  have eB : X.restrict PB hPB ≅ rvProductObject U V :=
    (rvProductRestrictionIso U T B hB).symm ≪≫
      (rvProductIso (Iso.refl U) (rvCoprodLeftRestrictionIso V W)).symm
  have eC : X.restrict PC hPC ≅ rvProductObject U W :=
    (rvProductRestrictionIso U T C hC).symm ≪≫
      (rvProductIso (Iso.refl U) (rvCoprodRightRestrictionIso V W)).symm
  exact hself.symm ≪≫
    (rvCoprodUnionIso X PB PC hPB hPC
      (rvProductDomain_disjoint U.domain B C (rvTaggedImages_disjoint V.domain W.domain))).symm ≪≫
    rvCoprodIso eB eC

end SpecialTransformations.Section4

end
