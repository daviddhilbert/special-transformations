module

public import Section4.MixedProducts

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {P Q : DefinableGeometry.Space LRV M}

/-- Combine two actual dimension witnesses by concatenating VF
coordinates and retaining the product of their RV/Gamma auxiliaries. -/
theorem HasVFDimLE.prod (Γ : DefinableGeometry.Space LRV M)
    {A : DefSet P S} {B : DefSet Q S} {k l : ℕ}
    (hA : HasVFDimLE Γ A k) (hB : HasVFDimLE Γ B l) :
    HasVFDimLE Γ (A.prod B) (k + l) := by
  obtain ⟨a, ha, i, f, hf⟩ := hA
  obtain ⟨b, hb, j, g, hg⟩ := hB
  let I := i.space Γ
  let J := j.space Γ
  let shuffle := Map.shuffle (rawVFSpace (M := M) a) I (rawVFSpace b) J S
  let concat := Map.prodUnivMap (vfAppendMap (M := M) S a b)
    (Map.id (DefSet.univ (I.prod J) S))
  let F := concat.comp (shuffle.comp (Map.prodMap f g).toUniv)
  refine ⟨a + b, Nat.add_le_add ha hb, .prod i j, F, ?_⟩
  have hfg : (Map.prodMap f g).toUniv.FiniteFibres := by
    intro z
    apply ((hf.prodMap hg)
      ⟨z.val, Set.mem_univ _, Set.mem_univ _⟩).subset
    intro x hx
    exact Subtype.ext (congrArg
      (fun z : DefSet.univ (((rawVFSpace a).prod I).prod ((rawVFSpace b).prod J)) S =>
        z.val) hx)
  exact (Map.finiteFibres_of_injective (Map.prodUnivMap_bijective _ _
    (vfAppendMap_bijective S a b) Function.bijective_id).1).comp
      ((Map.finiteFibres_of_injective (Map.shuffle_bijective _ _ _ _ _).1).comp hfg)

theorem vfDim_mixed_product_le (Γ : DefinableGeometry.Space LRV M)
    {n r m s : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S)
    (B : DefSet (rawMixedSpace (M := M) m s) S) :
    vfDim Γ (mixedProductDomain A B) ≤ vfDim Γ A + vfDim Γ B := by
  have hA := (vfDim_le_iff Γ A (vfDim Γ A)).mp le_rfl
  have hB := (vfDim_le_iff Γ B (vfDim Γ B)).mp le_rfl
  apply (vfDim_le_iff Γ (mixedProductDomain A B) _).mpr
  apply Dimension.HasDim.of_finiteFibres rawVFSpace (AuxiliaryCoordinates.space Γ)
    (mixedUnpack A B)
  · apply Map.finiteFibres_of_injective
    intro a b he
    have he' := congrArg (mixedPack A B).toImage he
    simpa only [mixedPack_unpack] using he'
  · exact hA.prod Γ hB

def vfProductObject (Γ : DefinableGeometry.Space LRV M) {k l : ℕ}
    (U : VFObject Γ (M := M) S k) (V : VFObject Γ (M := M) S l) :
    VFObject Γ (M := M) S (k + l) :=
  ⟨vfAllProductObject U.obj V.obj,
    (vfDim_mixed_product_le Γ U.obj.set V.obj.set).trans
      (Nat.add_le_add U.property V.property)⟩

def vfProductHom (Γ : DefinableGeometry.Space LRV M) {k l : ℕ}
    {U U' : VFObject Γ (M := M) S k} {V V' : VFObject Γ (M := M) S l}
    (f : U ⟶ U') (g : V ⟶ V') : vfProductObject Γ U V ⟶ vfProductObject Γ U' V' :=
  ObjectProperty.homMk (vfAllProductHom f.hom g.hom)

theorem finiteRVFibres_product {U V : VFAllObject (M := M) S}
    (hU : finiteRVFibres U) (hV : finiteRVFibres V) :
    finiteRVFibres (vfAllProductObject U V) := by
  intro a
  let au := a ∘ Fin.castAdd V.index.1
  let av := a ∘ Fin.natAdd U.index.1
  apply (((hU au).prod (hV av)).image (fun ts => rvAppend ts.1 ts.2)).subset
  intro t ht
  have hab := (mem_mixedProductDomain U.set V.set (a, t)).mp ht
  exact ⟨(t ∘ Fin.castAdd V.index.2, t ∘ Fin.natAdd U.index.2),
    hab, Fin.append_castAdd_natAdd⟩

def vfFiniteAllProductObject (U V : VFFiniteAllObject (M := M) S) :
    VFFiniteAllObject (M := M) S :=
  ⟨vfAllProductObject U.obj V.obj, finiteRVFibres_product U.property V.property⟩

def vfFiniteProductObject (Γ : DefinableGeometry.Space LRV M) {k l : ℕ}
    (U : VFFiniteObject Γ (M := M) S k) (V : VFFiniteObject Γ (M := M) S l) :
    VFFiniteObject Γ (M := M) S (k + l) :=
  ⟨vfProductObject Γ U.obj V.obj, finiteRVFibres_product U.property V.property⟩

end SpecialTransformations.Section4

end
