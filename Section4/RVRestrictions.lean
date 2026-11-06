import Section4.RVPadding
import Section4.MapCorestrict
import Section4.VFFibreFiniteness

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.DefinableGeometry

variable {L : Language} {M : Type} [L.Structure M] {P : Space L M} {S : Set M}

def DefSet.inter (A B : DefSet P S) : DefSet P S :=
  ⟨A.carrier ∩ B.carrier, A.definable.inter P B.definable⟩

def DefSet.sdiff (A B : DefSet P S) : DefSet P S :=
  ⟨A.carrier \ B.carrier, A.definable.inter P (B.definable.compl P)⟩

end SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

def RVObject.restrict (U : RVObject (M := M) S k)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier) :
    RVObject (M := M) S k where
  arity := U.arity
  domain := A
  volume := U.volume.restrict hA

@[simp] theorem RVObject.restrict_value (U : RVObject (M := M) S k)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier) (a : A) :
    (U.restrict A hA).value a = U.value ⟨a.val, hA a.property⟩ := rfl

def RVObject.empty (S : Set M) (k : ℕ) : RVObject (M := M) S k where
  arity := 0
  domain := DefSet.empty (rawRVSpace 0) S
  volume := Map.empty (rawRVSpace 0) (rawRVSpace k) S

def RVObject.restrictInclusion (U : RVObject (M := M) S k)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier) :
    RVHom (U.restrict A hA) U where
  map := Map.inclusion hA
  volumetric _ := le_rfl
  finite_volume_images t := by
    apply (Set.finite_singleton t).subset
    rintro s ⟨a, ha, he⟩
    exact Set.mem_singleton_iff.mpr (he.symm.trans ha)

theorem RVObject.restrict_finite_volume (U : RVObject (M := M) S k)
    (hU : U.volume.FiniteFibres) (A : DefSet (rawRVSpace (M := M) U.arity) S)
    (hA : A.carrier ⊆ U.domain.carrier) : (U.restrict A hA).volume.FiniteFibres :=
  hU.restrict hA

def RVHom.restrict {U V : RVObject (M := M) S k} (f : RVHom U V)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier)
    (B : DefSet (rawRVSpace (M := M) V.arity) S) (hB : B.carrier ⊆ V.domain.carrier)
    (hmap : ∀ a : A, (f.map ⟨a.val, hA a.property⟩).val ∈ B.carrier) :
    RVHom (U.restrict A hA) (V.restrict B hB) where
  map := (f.map.restrict hA).corestrict hmap
  volumetric a := f.volumetric ⟨a.val, hA a.property⟩
  finite_volume_images t := by
    apply (f.finite_volume_images t).subset
    rintro s ⟨a, ha, he⟩
    exact ⟨⟨a.val, hA a.property⟩, ha, he⟩

variable [hM : M ⊨ Axioms.ACVF]

theorem rvPadObject_restrict (U : RVObject (M := M) S k)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier) :
    rvPadObject (U.restrict A hA) = (rvPadObject U).restrict A hA := rfl

end SpecialTransformations.Section4

end
