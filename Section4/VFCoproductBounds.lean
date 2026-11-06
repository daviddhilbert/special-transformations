import Section4.VFCoproduct
import Section4.VFUnions

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

theorem vfDim_coprod (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded)
    (U V : VFAllObject (M := M) S) :
    vfDim Γ (vfAllCoprodObject U V).set = max (vfDim Γ U.set) (vfDim Γ V.set) := by
  change vfDim Γ ((mixedLeftTagMap U.set V.index.1 V.index.2).image.union
    (mixedRightTagMap V.set U.index.1 U.index.2).image) = _
  rw [vfDim_union hcan hs hsmall Γ hΓ]
  rw [← vfDim_eq_of_bijective Γ (mixedLeftTagMap U.set V.index.1 V.index.2).toImage
    (mixedLeftTagMap_toImage_bijective U.set V.index.1 V.index.2)]
  rw [← vfDim_eq_of_bijective Γ (mixedRightTagMap V.set U.index.1 U.index.2).toImage
    (mixedRightTagMap_toImage_bijective V.set U.index.1 U.index.2)]

theorem finiteRVFibres_leftTag {n r : ℕ}
    (A : DefSet (rawMixedSpace (M := M) n r) S) (m s : ℕ)
    (hA : ∀ a, {t | (a, t) ∈ A.carrier}.Finite) :
    ∀ a, {t | (a, t) ∈ (mixedLeftTagMap A m s).image.carrier}.Finite := by
  intro a
  apply ((hA (a ∘ Fin.castAdd m)).image (rvLeftTag s)).subset
  rintro t ⟨u, hu⟩
  change mixedLeftTag m s u.val = (a, t) at hu
  have hx : u.val.1 = a ∘ Fin.castAdd m := by
    funext i
    simpa only [mixedLeftTag, vfAppend, Fin.append_left, Function.comp_apply] using
      congrFun (congrArg Prod.fst hu) (Fin.castAdd m i)
  refine ⟨u.val.2, ?_, congrArg Prod.snd hu⟩
  change (a ∘ Fin.castAdd m, u.val.2) ∈ A.carrier
  rw [← hx]
  exact u.property

theorem finiteRVFibres_rightTag {m s : ℕ}
    (B : DefSet (rawMixedSpace (M := M) m s) S) (n r : ℕ)
    (hB : ∀ b, {t | (b, t) ∈ B.carrier}.Finite) :
    ∀ b, {t | (b, t) ∈ (mixedRightTagMap B n r).image.carrier}.Finite := by
  intro b
  apply ((hB (b ∘ Fin.natAdd n)).image (rvRightTag r)).subset
  rintro t ⟨u, hu⟩
  change mixedRightTag n r u.val = (b, t) at hu
  have hx : u.val.1 = b ∘ Fin.natAdd n := by
    funext i
    simpa only [mixedRightTag, vfAppend, Fin.append_right, Function.comp_apply] using
      congrFun (congrArg Prod.fst hu) (Fin.natAdd n i)
  refine ⟨u.val.2, ?_, congrArg Prod.snd hu⟩
  change (b ∘ Fin.natAdd n, u.val.2) ∈ B.carrier
  rw [← hx]
  exact u.property

theorem finiteRVFibres_coprod {U V : VFAllObject (M := M) S}
    (hU : finiteRVFibres U) (hV : finiteRVFibres V) :
    finiteRVFibres (vfAllCoprodObject U V) := by
  intro a
  exact (finiteRVFibres_leftTag U.set V.index.1 V.index.2 hU a).union
    (finiteRVFibres_rightTag V.set U.index.1 U.index.2 hV a)

def vfCoprodObject (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded) {k : ℕ}
    (U V : VFObject Γ (M := M) S k) : VFObject Γ (M := M) S k :=
  ⟨vfAllCoprodObject U.obj V.obj, by
    change vfDim Γ (vfAllCoprodObject U.obj V.obj).set ≤ k
    rw [vfDim_coprod hcan hs hsmall Γ hΓ]
    exact max_le U.property V.property⟩

def vfFiniteAllCoprodObject (U V : VFFiniteAllObject (M := M) S) :
    VFFiniteAllObject (M := M) S :=
  ⟨vfAllCoprodObject U.obj V.obj, finiteRVFibres_coprod U.property V.property⟩

def vfFiniteCoprodObject (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded) {k : ℕ}
    (U V : VFFiniteObject Γ (M := M) S k) : VFFiniteObject Γ (M := M) S k :=
  ⟨vfCoprodObject hcan hs hsmall Γ hΓ U.obj V.obj,
    finiteRVFibres_coprod U.property V.property⟩

end SpecialTransformations.Section4

end
