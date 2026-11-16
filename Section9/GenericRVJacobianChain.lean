module

public import Section9.GenericRVJacobian
public import Section9.GenericVolumeChain
public import Section9.ZeroArityVolumeJacobian

@[expose] public section

/-! The same-base exceptional sets for the three Jacobians and the
failure set of their product have RV dimension less than the arity. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section7 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "RV" => CanonicalRV.RVSort M

theorem rvJacobian_chain_ae_finite_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : BaseContext M) (hn : 0 < n)
    {U V W : RVFiniteObject (M := M) (B.base : Set M) n} (f : U ≅ V) (g : V ≅ W)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (hW : ∀ u : W.obj.domain, ∀ i, (W.obj.value u i).val ≠ iRVZero) :
    let F := (finiteVolumeProperty (B.base : Set M) n).ι.mapIso f
    let G := (finiteVolumeProperty (B.base : Set M) n).ι.mapIso g
    ∃ Z : DefSet (rawRVSpace (M := M) U.obj.arity) (B.base : Set M),
      ∃ hZ : Z.carrier ⊆ U.obj.domain.carrier,
        rvDim Z < n ∧ rvDim (U.obj.volume.restrict hZ).image < n ∧
        ∀ u : U.obj.domain, u.val ∉ Z.carrier → ∃ ω η : RV,
          IsRVJacobianAt (volumeCorrespondence F.hom.map).carrier (U.obj.value u) (V.obj.value (F.hom.map u)) ω ∧
          IsRVJacobianAt (volumeCorrespondence G.hom.map).carrier (V.obj.value (F.hom.map u))
            (W.obj.value (G.hom.map (F.hom.map u))) η ∧
          IsRVJacobianAt (volumeCorrespondence (F.trans G).hom.map).carrier (U.obj.value u)
            (W.obj.value (G.hom.map (F.hom.map u))) (η * ω) := by
  let S := (B.base : Set M)
  let F := (finiteVolumeProperty S n).ι.mapIso f
  let G := (finiteVolumeProperty S n).ι.mapIso g
  let A := rawRVSpace (M := M) U.obj.arity
  let Q := rawRVSpace (M := M) 1
  obtain ⟨ω, X, hX, hdX, hω⟩ := exists_definable_generic_RVJacobian hc B hn f hU hV
  obtain ⟨η, Y, _, hdY, hη⟩ := exists_definable_generic_RVJacobian hc B hn g hV hW
  obtain ⟨θ, T, hT, hdT, hθ⟩ := exists_definable_generic_RVJacobian hc B hn (f.trans g) hU hW
  let Y' : DefSet A S := ⟨{x | ∃ u : U.obj.domain, u.val = x ∧ (F.hom.map u).val ∈ Y.carrier},
    F.hom.map.definable_preimage Y.definable⟩
  have hY' : Y'.carrier ⊆ U.obj.domain.carrier := by
    rintro _ ⟨u, rfl, _⟩
    exact u.property
  let m := (F.hom.map.restrict hY').corestrict (show ∀ y : Y',
      (F.hom.map.restrict hY' y).val ∈ Y.carrier from by
    intro y
    obtain ⟨u, he, hu⟩ := y.property
    have h : (⟨y.val, hY' y.property⟩ : U.obj.domain) = u := Subtype.ext he.symm
    change (F.hom.map (⟨y.val, hY' y.property⟩ : U.obj.domain)).val ∈ Y.carrier
    rwa [h])
  have hm : Function.Injective m := by
    intro a b hab
    let u : U.obj.domain := ⟨a.val, hY' a.property⟩
    let v : U.obj.domain := ⟨b.val, hY' b.property⟩
    have he : F.hom.map u = F.hom.map v := Subtype.ext (congrArg (fun p : Y => p.val) hab)
    have h := (show Function.LeftInverse F.inv.map F.hom.map from Section7.rvIso_inv_apply F).injective he
    exact Subtype.ext (congrArg (fun p : U.obj.domain => p.val) h)
  have hdY' := (rvDim_le_of_finite_map m (Map.finiteFibres_of_injective hm)).trans_lt hdY
  let P := (rvCoordinateProductMap (M := M) (n := 1) S).comp (((η.comp F.hom.map).pair ω).toUniv)
  let Good : DefSet A S := ⟨{x | ∃ y, P.graph x y ∧ θ.graph x y},
    ((P.graph_definable.inter A Q θ.graph_definable).exists_right A Q)⟩
  have hGood (u : U.obj.domain) : u.val ∈ Good.carrier ↔ (P u).val 0 = (θ u).val 0 := by
    constructor
    · rintro ⟨y, hy, hz⟩
      exact congrFun (((P.graph_apply u y).mp hy).trans (((θ.graph_apply u y).mp hz).symm)) 0
    · intro he
      have h : (P u).val = (θ u).val := by
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        simpa only [hi] using he
      exact ⟨(θ u).val, (P.graph_apply u _).mpr h, (θ.graph_apply u _).mpr rfl⟩
  let Bad := X.union (Y'.union T)
  let D := (U.obj.domain.sdiff Bad).sdiff Good
  have hD : D.carrier ⊆ U.obj.domain.carrier := Set.diff_subset.trans Set.diff_subset
  have hBad : Bad.carrier ⊆ U.obj.domain.carrier := Set.union_subset hX (Set.union_subset hY' hT)
  have hNotBad (u : U.obj.domain) (hu : u.val ∉ Bad.carrier) :
      u.val ∉ X.carrier ∧ (F.hom.map u).val ∉ Y.carrier ∧ u.val ∉ T.carrier :=
    ⟨fun h => hu (Or.inl h), fun h => hu (Or.inr (Or.inl ⟨u, rfl, h⟩)), fun h => hu (Or.inr (Or.inr h))⟩
  have hP (u : U.obj.domain) : (P u).val 0 = (η (F.hom.map u)).val 0 * (ω u).val 0 := rfl
  have hdD : rvDim D < n := by
    by_contra hnD
    have hle := (rvDim_le_of_finite_map (U.obj.volume.restrict hD) (U.property.restrict hD)).trans (rvDim_le_arity _)
    have he : rvDim D = n := hle.antisymm (Nat.le_of_not_gt hnD)
    obtain ⟨u, hu, α, β, hα, hβ, hαβ⟩ := exists_rvJacobian_chain_on_full_label_subset hc B hn F G U.property
      (fun u i h => hU u i ((congrArg Subtype.val h).trans RVOperations.zero_val))
      (fun u i h => hV u i ((congrArg Subtype.val h).trans RVOperations.zero_val))
      (fun u i h => hW u i ((congrArg Subtype.val h).trans RVOperations.zero_val)) D hD he
    obtain ⟨hxu, hyu, htu⟩ := hNotBad u hu.1.2
    apply hu.2 ((hGood u).mpr ?_)
    rw [hP, (hη _ hyu).unique hβ, (hω u hxu).unique hα]
    exact hαβ.unique (hθ u htu)
  let Z := Bad.union D
  have hZ : Z.carrier ⊆ U.obj.domain.carrier := Set.union_subset hBad hD
  let hex := rvExchangeInput_of_earlier B.uncountable.le B.saturated B.model00
  have hDim (A' B' : DefSet (rawRVSpace (M := M) U.obj.arity) S) :
      rvDim (A'.union B') ≤ max (rvDim A') (rvDim B') :=
    rvDim_union_le_max hc hex B.saturated B.small A' B'
  have hdBad : rvDim Bad < n := (hDim X (Y'.union T)).trans_lt
    (max_lt hdX ((hDim Y' T).trans_lt (max_lt hdY' hdT)))
  have hdZ : rvDim Z < n := (hDim Bad D).trans_lt (max_lt hdBad hdD)
  refine ⟨Z, hZ, hdZ, ?_, fun u hu => ?_⟩
  · rw [rvDim_mapImage_eq_of_finiteFibres hc hex B.saturated B.small _ (U.property.restrict hZ)]
    exact hdZ
  · have hub : u.val ∉ Bad.carrier := fun h => hu (Or.inl h)
    obtain ⟨hx, hy, ht⟩ := hNotBad u hub
    have hg : u.val ∈ Good.carrier := by
      by_contra h
      exact hu (Or.inr ⟨⟨u.property, hub⟩, h⟩)
    have he := (hGood u).mp hg
    rw [hP] at he
    exact ⟨_, _, hω u hx, hη _ hy, he.symm ▸ hθ u ht⟩

theorem rvJacobian_chain_zero_arity {S : Set M}
    {U V W : RVFiniteObject (M := M) S 0} (f : U ≅ V) (g : V ≅ W) (u : U.obj.domain) :
    let F := (finiteVolumeProperty S 0).ι.mapIso f
    let G := (finiteVolumeProperty S 0).ι.mapIso g
    IsRVJacobianAt (volumeCorrespondence F.hom.map).carrier (U.obj.value u) (V.obj.value (F.hom.map u)) 1 ∧
    IsRVJacobianAt (volumeCorrespondence G.hom.map).carrier (V.obj.value (F.hom.map u))
      (W.obj.value (G.hom.map (F.hom.map u))) 1 ∧
    IsRVJacobianAt (volumeCorrespondence (F.trans G).hom.map).carrier (U.obj.value u)
      (W.obj.value (G.hom.map (F.hom.map u))) (1 * 1) := by
  dsimp only
  rw [one_mul]
  exact ⟨isRVJacobianAt_zero_arity _ _ _ ⟨u, rfl⟩,
    isRVJacobianAt_zero_arity _ _ _ ⟨_, rfl⟩,
    isRVJacobianAt_zero_arity _ _ _ ⟨u, rfl⟩⟩

end SpecialTransformations.Section9
