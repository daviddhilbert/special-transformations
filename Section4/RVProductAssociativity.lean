module

public import Section4.RVProductSymmetry

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {n m k l j : ℕ}

def rvPackPair (A : DefSet (rawRVSpace (M := M) n) S)
    (B : DefSet (rawRVSpace (M := M) m) S) (a : A) (b : B) : rvProductDomain A B :=
  (rvPack A B).toImage ⟨(a.val, b.val), a.property, b.property⟩

@[simp] theorem rvUnpack_pair (A : DefSet (rawRVSpace (M := M) n) S)
    (B : DefSet (rawRVSpace (M := M) m) S) (a : A) (b : B) :
    rvUnpack A B (rvPackPair A B a b) = ⟨(a.val, b.val), a.property, b.property⟩ :=
  rvUnpack_pack A B _

theorem exists_rvPackPair (A : DefSet (rawRVSpace (M := M) n) S)
    (B : DefSet (rawRVSpace (M := M) m) S) (c : rvProductDomain A B) :
    ∃ a : A, ∃ b : B, rvPackPair A B a b = c := by
  let p := rvUnpack A B c
  exact ⟨⟨p.val.1, p.property.1⟩, ⟨p.val.2, p.property.2⟩, rvPack_unpack A B c⟩

theorem rvProductObject_value_pair (U : RVObject (M := M) S k)
    (V : RVObject (M := M) S l) (a : U.domain) (b : V.domain) :
    (rvProductObject U V).value (rvPackPair U.domain V.domain a b) =
      rvAppend (U.value a) (V.value b) := by
  rw [rvProductObject_value, rvUnpack_pair]

def rvProductAssocMap (U : RVObject (M := M) S k) (V : RVObject (M := M) S l)
    (W : RVObject (M := M) S j) :
    Map (rvProductObject (rvProductObject U V) W).domain
      (rvProductObject U (rvProductObject V W)).domain :=
  (rvPack U.domain (rvProductObject V W).domain).toImage.comp
    ((Map.prodMap (Map.id U.domain) (rvPack V.domain W.domain).toImage).comp
      ((Map.prodAssoc U.domain V.domain W.domain).comp
        ((Map.prodMap (rvUnpack U.domain V.domain) (Map.id W.domain)).comp
          (rvUnpack (rvProductObject U V).domain W.domain))))

theorem rvProductAssocMap_bijective (U : RVObject (M := M) S k) (V : RVObject (M := M) S l)
    (W : RVObject (M := M) S j) : Function.Bijective (rvProductAssocMap U V W) :=
  (rvPackToImage_bijective U.domain (rvProductObject V W).domain).comp
    ((Map.prodMap_bijective _ _ Function.bijective_id (rvPackToImage_bijective V.domain W.domain)).comp
      ((Map.prodAssoc_bijective U.domain V.domain W.domain).comp
        ((Map.prodMap_bijective _ _ (rvUnpack_bijective U.domain V.domain) Function.bijective_id).comp
          (rvUnpack_bijective (rvProductObject U V).domain W.domain))))

theorem rvProductAssocMap_pair (U : RVObject (M := M) S k) (V : RVObject (M := M) S l)
    (W : RVObject (M := M) S j) (a : U.domain) (b : V.domain) (c : W.domain) :
    rvProductAssocMap U V W
      (rvPackPair (rvProductObject U V).domain W.domain (rvPackPair U.domain V.domain a b) c) =
      rvPackPair U.domain (rvProductObject V W).domain a (rvPackPair V.domain W.domain b c) := by
  simp only [rvProductAssocMap, Map.comp_apply, rvPackPair, rvUnpack_pack,
    Map.prodMap_mk, Map.prodAssoc_mk, Map.id_apply]
  rfl

def rvProductAssocReindexedIso (U : RVObject (M := M) S k) (V : RVObject (M := M) S l)
    (W : RVObject (M := M) S j) :
    rvProductObject (rvProductObject U V) W ≅
      (rvProductObject U (rvProductObject V W)).reindexVolume
        (finCongr (Nat.add_assoc k l j)) := by
  apply rvIsoOfVolumePreservingBijection (rvProductAssocMap U V W)
    (rvProductAssocMap_bijective U V W)
  intro p
  obtain ⟨ab, c, rfl⟩ := exists_rvPackPair (rvProductObject U V).domain W.domain p
  obtain ⟨a, b, rfl⟩ := exists_rvPackPair U.domain V.domain ab
  change (rvProductObject U (rvProductObject V W)).value
      (rvProductAssocMap U V W
        (rvPackPair (rvProductObject U V).domain W.domain (rvPackPair U.domain V.domain a b) c)) ∘
      (finCongr (Nat.add_assoc k l j)) = _
  rw [rvProductAssocMap_pair, rvProductObject_value_pair, rvProductObject_value_pair,
    rvProductObject_value_pair, rvProductObject_value_pair]
  exact (Fin.append_assoc (U.value a) (V.value b) (W.value c)).symm

end SpecialTransformations.Section4

end
