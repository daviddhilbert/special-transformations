module

public import Section4.RVFiniteScissors
public import Section4.RVWeightRestriction
public import Section4.RVDimensionRank
public import Section4.CoordinateMaps
public import Section4.CanonicalLift

@[expose] public section

/-! Coordinate head maps for the lower-RV-dimensional step of Theorem
9.16. A head is taken from actual volume coordinates and keeps the original
RV label on the domain. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] {S : Set M} {n k : ℕ}

/-- The same-base coordinate projection on an arbitrary definable RV set. -/
def rvHeadSelect (v : Fin k → Fin n) (A : DefSet (rawRVSpace (M := M) n) S) :
    Map A (DefSet.univ (rawRVSpace (M := M) k) S) := by
  let P := rawRVSpace (M := M) n
  let Q := rawRVSpace (M := M) k
  let F (z : Fin n → M) := z ∘ v
  have hcode (c : P.domain) : rvValues (P.decode c ∘ v) = F c.val := by
    funext i
    exact congrFun (rvValues_decode c) (v i)
  have hdom (c : P.domain) : F c.val ∈ Q.domain := ⟨P.decode c ∘ v, hcode c⟩
  refine Map.ofCodes A (fun t => t ∘ v) F (fun _ => Set.DefinableFun.proj LRV) hdom ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode ⟨F c.val, hdom c⟩).trans (hcode c).symm

@[simp] theorem rvHeadSelect_apply (v : Fin k → Fin n)
    (A : DefSet (rawRVSpace (M := M) n) S) (a : A) :
    (rvHeadSelect v A a).val = a.val ∘ v := rfl

def rvHeadVolume (U : RVObject (M := M) S n) (v : Fin k → Fin n) :
    Map U.domain (DefSet.univ (rawRVSpace (M := M) k) S) :=
  (rvHeadSelect v U.volume.image).comp U.volume.toImage

@[simp] theorem rvHeadVolume_apply (U : RVObject (M := M) S n)
    (v : Fin k → Fin n) (u : U.domain) :
    (rvHeadVolume U v u).val = U.value u ∘ v := rfl

theorem rvHeadVolume_finite (U : RVFiniteObject (M := M) S n)
    (v : Fin k → Fin n) (hv : (rvHeadSelect v U.obj.volume.image).FiniteFibres) :
    (rvHeadVolume U.obj v).FiniteFibres := by
  apply hv.comp
  intro t
  apply (U.property ⟨t.val, Set.mem_univ _⟩).subset
  intro a ha
  change U.obj.volume.toImage a = t at ha
  apply Subtype.ext
  exact congrArg (fun x : U.obj.volume.image => x.val) ha

def rvFiniteHead (U : RVFiniteObject (M := M) S n)
    (v : Fin k → Fin n) (hv : (rvHeadVolume U.obj v).FiniteFibres) :
    RVFiniteObject (M := M) S k :=
  ⟨⟨U.obj.arity, U.obj.domain, rvHeadVolume U.obj v⟩, hv⟩

variable [M ⊨ Axioms.ACVF] in
def rvLiftHeadSelect (U : RVFiniteObject (M := M) S n) (v : Fin k → Fin n)
    (hv : (rvHeadVolume U.obj v).FiniteFibres) :
    Map (rvLift U.obj) (rvLift (rvFiniteHead U v hv).obj) :=
  (vfSelect v (rvLift U.obj)).corestrict (fun p => by
    obtain ⟨u, hu, ht⟩ := p.property
    exact ⟨u, hu, congrArg (fun t => t ∘ v) ht⟩)

variable [M ⊨ Axioms.ACVF] in
@[simp] theorem rvLiftHeadSelect_apply (U : RVFiniteObject (M := M) S n) (v : Fin k → Fin n)
    (hv : (rvHeadVolume U.obj v).FiniteFibres) (p : rvLift U.obj) :
    (rvLiftHeadSelect U v hv p).val = (p.val.1 ∘ v, p.val.2) := rfl

private def rvHom_of_finite_source {U V : RVObject (M := M) S k}
    (hU : U.volume.FiniteFibres) (F : Map U.domain V.domain)
    (hV : ∀ v : V.domain, ∀ i, (V.value v i).val ≠ iRVZero) : RVHom U V where
  map := F
  volumetric u := by
    have hw : rvWeight (V.value (F u)) = k := by simp [rvWeight, hV]
    change rvWeight (U.value u) ≤ rvWeight (V.value (F u))
    rw [hw]
    exact rvWeight_le_arity _
  finite_volume_images t := by
    apply ((hU ⟨t, Set.mem_univ _⟩).image (fun u => V.value (F u))).subset
    rintro s ⟨u, hu, hs⟩
    exact ⟨u, Subtype.ext hu, hs⟩

/-- Finite head volume maps on both sides turn the unchanged label
bijection into an isomorphism of the projected finite-volume objects. -/
def rvFiniteHeadIso {U V : RVFiniteObject (M := M) S n} (e : U ≅ V)
    (v w : Fin k → Fin n)
    (hv : (rvHeadVolume U.obj v).FiniteFibres) (hw : (rvHeadVolume V.obj w).FiniteFibres)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero) :
    rvFiniteHead U v hv ≅ rvFiniteHead V w hw := by
  let E : U.obj ≅ V.obj := (finiteVolumeProperty S n).ι.mapIso e
  apply rvFiniteIsoOfAmbient
  refine {
    hom := rvHom_of_finite_source hv E.hom.map (fun a i => hV a (w i))
    inv := rvHom_of_finite_source hw E.inv.map (fun a i => hU a (v i))
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · apply RVHom.ext
    apply Map.ext
    intro a
    exact rvIso_inv_apply E a
  · apply RVHom.ext
    apply Map.ext
    intro b
    exact rvIso_inv_apply E.symm b

def rvHeadPreimage (U : RVObject (M := M) S n) (v : Fin k → Fin n)
    (Z : DefSet (rawRVSpace (M := M) k) S) :
    DefSet (rawRVSpace (M := M) U.arity) S where
  carrier := {x | ∃ u : U.domain, u.val = x ∧ U.value u ∘ v ∈ Z.carrier}
  definable := (rvHeadVolume U v).definable_preimage Z.definable

theorem rvHeadPreimage_subset (U : RVObject (M := M) S n) (v : Fin k → Fin n)
    (Z : DefSet (rawRVSpace (M := M) k) S) :
    (rvHeadPreimage U v Z).carrier ⊆ U.domain.carrier := by
  rintro _ ⟨u, rfl, _⟩
  exact u.property

/-- Pulling an exceptional set back along a finite head does not raise
RV dimension. This is the drop needed for the recursion in 9.16. -/
theorem rvHeadPreimage_rvDim_le (U : RVObject (M := M) S n) (v : Fin k → Fin n)
    (hv : (rvHeadVolume U v).FiniteFibres) (Z : DefSet (rawRVSpace (M := M) k) S) :
    rvDim (rvHeadPreimage U v Z) ≤ rvDim Z := by
  let f := (rvHeadVolume U v).restrict (rvHeadPreimage_subset U v Z)
  have hZ (a : rvHeadPreimage U v Z) : (f a).val ∈ Z.carrier := by
    obtain ⟨u, hu, hz⟩ := a.property
    have he : (⟨a.val, rvHeadPreimage_subset U v Z a.property⟩ : U.domain) = u :=
      Subtype.ext hu.symm
    change U.value ⟨a.val, rvHeadPreimage_subset U v Z a.property⟩ ∘ v ∈ Z.carrier
    rwa [he]
  apply rvDim_le_of_finite_map (f.corestrict hZ)
  intro b
  apply ((hv.restrict (rvHeadPreimage_subset U v Z)) ⟨b.val, Set.mem_univ _⟩).subset
  intro a ha
  change (f.corestrict hZ) a = b at ha
  apply Subtype.ext
  exact congrArg (fun x : Z => x.val) ha

end SpecialTransformations.Section9

end
