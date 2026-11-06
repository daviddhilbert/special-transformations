import Section4.DefinableCategory
import Section4.RealPresentations
import Section4.FiniteMaps
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option backward.isDefEq.respectTransparency false

/-!
# RV categories

Definitions 4.15--4.16 use genuine definable maps over the fixed base.
Morphisms satisfy both the weight inequality and the finite-volume-image
condition. The latter is preserved by composition using a finite union of
finite images. The single absorbing element is iRVZero.
-/

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open scoped BigOperators

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M]

/-- Definition 4.15: the number of coordinates distinct from the absorbing
RV element, expressed as a sum of indicator functions. -/
noncomputable def rvWeight {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) : ℕ := by
  classical
  exact ∑ i, if (t i).val ≠ iRVZero then 1 else 0

theorem rvWeight_eq_card {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) :
    rvWeight t = (Finset.univ.filter (fun i => (t i).val ≠ iRVZero)).card := by
  classical
  simpa only [rvWeight] using
    (Finset.card_filter (fun i => (t i).val ≠ iRVZero) Finset.univ).symm

structure RVObject (S : Set M) (k : ℕ) where
  arity : ℕ
  domain : DefSet (rawRVSpace (M := M) arity) S
  volume : Map domain (DefSet.univ (rawRVSpace k) S)

namespace RVObject

variable {S : Set M} {k : ℕ}

def value (U : RVObject (M := M) S k) (a : U.domain) : Fin k → CanonicalRV.RVSort M :=
  (U.volume a).val

def volumeFibreImage (U V : RVObject (M := M) S k) (F : Map U.domain V.domain)
    (t : Fin k → CanonicalRV.RVSort M) : Set (Fin k → CanonicalRV.RVSort M) :=
  {s | ∃ a : U.domain, U.value a = t ∧ V.value (F a) = s}

def companion (U : RVObject (M := M) S k) :
    DefSet ((rawRVSpace k).prod (rawRVSpace U.arity)) S :=
  (U.volume.pair (Map.id U.domain)).image

def toCompanion (U : RVObject (M := M) S k) : Map U.domain U.companion :=
  (U.volume.pair (Map.id U.domain)).toImage

theorem toCompanion_bijective (U : RVObject (M := M) S k) :
    Function.Bijective U.toCompanion := by
  constructor
  · intro a b he
    apply Subtype.ext
    exact congrArg (fun z : U.companion => z.val.2) he
  · rintro ⟨p, a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

end RVObject

structure RVHom {S : Set M} {k : ℕ} (U V : RVObject (M := M) S k) where
  map : Map U.domain V.domain
  volumetric : ∀ a, rvWeight (U.value a) ≤ rvWeight (V.value (map a))
  finite_volume_images : ∀ t, (U.volumeFibreImage V map t).Finite

namespace RVHom

variable {S : Set M} {k : ℕ} {U V W : RVObject (M := M) S k}

@[ext] theorem ext {f g : RVHom U V} (he : f.map = g.map) : f = g := by
  cases f
  cases g
  cases he
  rfl

def id (U : RVObject (M := M) S k) : RVHom U U where
  map := Map.id U.domain
  volumetric _ := le_rfl
  finite_volume_images t := by
    apply (Set.finite_singleton t).subset
    rintro s ⟨a, ha, he⟩
    exact Set.mem_singleton_iff.mpr (he.symm.trans ha)

def comp (g : RVHom V W) (f : RVHom U V) : RVHom U W where
  map := g.map.comp f.map
  volumetric a := (f.volumetric a).trans (g.volumetric (f.map a))
  finite_volume_images t := by
    have hf := (f.finite_volume_images t).biUnion
      (fun s _ => g.finite_volume_images s)
    apply hf.subset
    rintro s ⟨a, ha, he⟩
    exact Set.mem_iUnion.mpr ⟨V.value (f.map a), Set.mem_iUnion.mpr
      ⟨⟨a, ha, rfl⟩, ⟨f.map a, rfl, he⟩⟩⟩

end RVHom

instance (S : Set M) (k : ℕ) : Category (RVObject (M := M) S k) where
  Hom U V := RVHom U V
  id := RVHom.id
  comp f g := g.comp f
  id_comp f := by apply RVHom.ext; apply Map.ext; intro a; rfl
  comp_id f := by apply RVHom.ext; apply Map.ext; intro a; rfl
  assoc f g h := by apply RVHom.ext; apply Map.ext; intro a; rfl

/-- RV[k] is the full subcategory with finite-to-one volume maps. -/
def finiteVolumeProperty (S : Set M) (k : ℕ) : ObjectProperty (RVObject (M := M) S k) :=
  fun U => U.volume.FiniteFibres

abbrev RVFiniteObject (S : Set M) (k : ℕ) :=
  (finiteVolumeProperty (M := M) S k).FullSubcategory

/-- Forgetting the volume data preserves the complete definable map. -/
def rvForget (S : Set M) (k : ℕ) :
    RVObject (M := M) S k ⥤ DefinableSetCat (rawRVSpace (M := M)) S where
  obj U := ⟨U.arity, U.domain⟩
  map f := f.map

instance (S : Set M) (k : ℕ) : (rvForget (M := M) S k).Faithful where
  map_injective h := RVHom.ext h

end SpecialTransformations.Section4

end
