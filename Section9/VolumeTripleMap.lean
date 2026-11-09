import Section9.VolumePairMap

/-! The two composable volume correspondences must be evaluated at
the same label. The joint volume map records this compatibility. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {U V W : RVObject (M := M) S n}

noncomputable def volumeTripleMap (f : Map U.domain V.domain) (g : Map V.domain W.domain) :
    Map U.domain (DefSet.univ (rawRVSpace (M := M) (n + (n + n))) S) :=
  (rvAppendMap S n (n + n)).comp (U.volume.pair ((volumePairMap g).toUniv.comp f)).toUniv

@[simp] theorem volumeTripleMap_left (f : Map U.domain V.domain) (g : Map V.domain W.domain)
    (u : U.domain) (i : Fin n) :
    (volumeTripleMap f g u).val (productLeft n (n + n) i) = U.value u i :=
  Fin.append_left _ _ i

@[simp] theorem volumeTripleMap_right (f : Map U.domain V.domain) (g : Map V.domain W.domain)
    (u : U.domain) (i : Fin (n + n)) :
    (volumeTripleMap f g u).val (productRight n (n + n) i) =
      productTuple (V.value (f u)) (W.value (g (f u))) i := by
  change Fin.append (U.value u) ((volumePairMap g (f u)).val) (productRight n (n + n) i) = _
  rw [show productRight n (n + n) i = Fin.natAdd n i from rfl, Fin.append_right,
    volumePairMap_apply]

theorem volumeTripleMap_finite (f : Map U.domain V.domain) (g : Map V.domain W.domain)
    (hU : U.volume.FiniteFibres) : (volumeTripleMap f g).FiniteFibres := by
  intro p
  let x : DefSet.univ (rawRVSpace (M := M) n) S :=
    ⟨p.val ∘ productLeft n (n + n), Set.mem_univ _⟩
  apply (hU x).subset
  intro u hu
  apply Subtype.ext
  funext i
  have hi := congrArg (fun z : DefSet.univ (rawRVSpace (M := M) (n + (n + n))) S =>
    z.val (productLeft n (n + n) i)) hu
  change U.value u i = p.val (productLeft n (n + n) i)
  simpa only [volumeTripleMap_left] using hi

theorem volumeTriple_leftProjection_finite (f : Map U.domain V.domain) (g : Map V.domain W.domain)
    (hU : U.volume.FiniteFibres) :
    (rvHeadSelect (productLeft n (n + n)) (volumeTripleMap f g).image).FiniteFibres := by
  let T := volumeTripleMap f g
  let proj (p : U.domain) : T.image := ⟨(T p).val, Set.mem_range_self p⟩
  intro x
  apply ((hU x).image proj).subset
  intro t ht
  obtain ⟨u, hu⟩ := t.property
  have htu : proj u = t := Subtype.ext hu
  refine ⟨u, Subtype.ext (funext fun i => ?_), htu⟩
  have hxi := congrArg (fun p : DefSet.univ (rawRVSpace (M := M) n) S => p.val i) ht
  rw [← htu, rvHeadSelect_apply] at hxi
  exact (volumeTripleMap_left f g u i).symm.trans hxi

end SpecialTransformations.Section9
