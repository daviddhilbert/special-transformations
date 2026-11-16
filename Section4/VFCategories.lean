module

public import Section4.VFDimension
public import Section4.DefinableCategory
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (Γ : DefinableGeometry.Space LRV M) {S : Set M}

theorem vfDim_le_of_finite_map {n r n' r' : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n' r') S}
    (f : Map A B) (hf : f.FiniteFibres) : vfDim Γ A ≤ vfDim Γ B :=
  Dimension.dim_le_of_finiteFibres rawVFSpace (AuxiliaryCoordinates.space Γ)
    f hf ⟨n', mixed_has_dimension_bound Γ B⟩

theorem vfDim_eq_of_bijective {n r n' r' : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n' r') S}
    (f : Map A B) (hf : Function.Bijective f) : vfDim Γ A = vfDim Γ B := by
  have hinv : Function.Injective (f.inverse hf) := by
    intro a b he
    have h := congrArg f he
    simpa only [Map.apply_inverse] using h
  exact (vfDim_le_of_finite_map Γ f (Map.finiteFibres_of_injective hf.1)).antisymm
    (vfDim_le_of_finite_map Γ (f.inverse hf) (Map.finiteFibres_of_injective hinv))

def mixedFamily (p : ℕ × ℕ) : DefinableGeometry.Space LRV M :=
  rawMixedSpace p.1 p.2

/-- All mixed real definable sets, with genuine definable functions. -/
abbrev VFAllObject (S : Set M) := DefinableSetCat (mixedFamily (M := M)) S

def vfDimensionProperty (S : Set M) (k : ℕ) : ObjectProperty (VFAllObject (M := M) S) :=
  fun U => vfDim Γ U.set ≤ k

/-- Definition 4.14: VF[k,·]. -/
abbrev VFObject (S : Set M) (k : ℕ) := (vfDimensionProperty Γ S k).FullSubcategory

/-- Every RV fibre is finite; no alternative finite-map characterization
is assumed as part of this definition. -/
def finiteRVFibres (U : VFAllObject (M := M) S) : Prop :=
  ∀ a : (rawVFSpace (M := M) U.index.1).Carrier,
    {t : (rawRVSpace (M := M) U.index.2).Carrier | (a, t) ∈ U.set.carrier}.Finite

def vfFiniteProperty (S : Set M) : ObjectProperty (VFAllObject (M := M) S) :=
  finiteRVFibres

abbrev VFFiniteAllObject (S : Set M) := (vfFiniteProperty (M := M) S).FullSubcategory

def vfBoundedFiniteProperty (S : Set M) (k : ℕ) : ObjectProperty (VFObject Γ S k) :=
  fun U => finiteRVFibres U.obj

/-- Definition 4.14: VF[k]. -/
abbrev VFFiniteObject (S : Set M) (k : ℕ) := (vfBoundedFiniteProperty Γ S k).FullSubcategory

/-- The union of the dimension bounds covers the ambient VF category. -/
theorem vfAllObject_has_bound (U : VFAllObject (M := M) S) :
    ∃ k : ℕ, vfDimensionProperty Γ S k U :=
  ⟨U.index.1, vfDim_le_arity Γ U.set⟩

end SpecialTransformations.Section4

end
