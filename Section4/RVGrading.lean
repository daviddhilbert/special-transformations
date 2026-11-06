import Section4.RVRestrictions
import Mathlib.CategoryTheory.Pi.Basic

/-!
# Finite graded RV families

The dependent product category supplies all componentwise morphisms. We
restrict its objects to families with only finitely many nonempty degrees.
Thus a morphism can act on the whole definable set in each degree; it does
not have to send a chosen smaller summand into a single target summand.
Empty degrees are retained, so adding empty trailing degrees changes no
isomorphism class. This gives the finite-family categories of 4.16.
-/

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M}

abbrev RVFamily (S : Set M) := ∀ k : ℕ, RVObject (M := M) S k

def rvFamilySupport (U : RVFamily (M := M) S) : Set ℕ :=
  {k | (U k).domain.carrier.Nonempty}

def rvFiniteSupportProperty (S : Set M) : ObjectProperty (RVFamily (M := M) S) :=
  fun U => (rvFamilySupport U).Finite

/-- RV[*,·]: finitely supported, genuinely degree-preserving families. -/
abbrev RVGradedObject (S : Set M) :=
  (rvFiniteSupportProperty (M := M) S).FullSubcategory

def rvGradedEvaluation (S : Set M) (k : ℕ) :
    RVGradedObject (M := M) S ⥤ RVObject (M := M) S k :=
  (rvFiniteSupportProperty S).ι ⋙ Pi.eval (fun k => RVObject (M := M) S k) k

theorem rvGradedObject_has_bound (U : RVGradedObject (M := M) S) :
    ∃ b : ℕ, ∀ k, b < k → (U.obj k).domain.carrier = ∅ := by
  let F := U.property.toFinset
  refine ⟨F.sup id, ?_⟩
  intro k hk
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hne
  have hmem : k ∈ F := U.property.mem_toFinset.mpr hne
  exact (not_le_of_gt hk) (Finset.le_sup (f := id) hmem)

def rvBoundedGradingProperty (S : Set M) (b : ℕ) :
    ObjectProperty (RVGradedObject (M := M) S) :=
  fun U => ∀ k, b < k → (U.obj k).domain.carrier = ∅

/-- RV[≤b,·]. All morphisms are still the componentwise RV morphisms. -/
abbrev RVBoundedGradedObject (S : Set M) (b : ℕ) :=
  (rvBoundedGradingProperty (M := M) S b).FullSubcategory

def rvGradedFiniteVolumeProperty (S : Set M) :
    ObjectProperty (RVGradedObject (M := M) S) :=
  fun U => ∀ k, (U.obj k).volume.FiniteFibres

/-- RV[*], the full subcategory with finite-to-one volume in every degree. -/
abbrev RVFiniteGradedObject (S : Set M) :=
  (rvGradedFiniteVolumeProperty (M := M) S).FullSubcategory

def rvBoundedFiniteGradingProperty (S : Set M) (b : ℕ) :
    ObjectProperty (RVFiniteGradedObject (M := M) S) :=
  fun U => ∀ k, b < k → (U.obj.obj k).domain.carrier = ∅

/-- RV[≤b]. -/
abbrev RVFiniteBoundedGradedObject (S : Set M) (b : ℕ) :=
  (rvBoundedFiniteGradingProperty (M := M) S b).FullSubcategory

def rvSingleFamily (k : ℕ) (U : RVObject (M := M) S k) : RVFamily (M := M) S :=
  fun j => if h : j = k then h.symm ▸ U else RVObject.empty S j

@[simp] theorem rvSingleFamily_self (k : ℕ) (U : RVObject (M := M) S k) :
    rvSingleFamily k U k = U := by
  simp [rvSingleFamily]

theorem rvSingleFamily_support_subset (k : ℕ) (U : RVObject (M := M) S k) :
    rvFamilySupport (rvSingleFamily k U) ⊆ {k} := by
  intro j hj
  by_contra hne
  have hjk : j ≠ k := fun h => hne (Set.mem_singleton_iff.mpr h)
  have he : rvSingleFamily k U j = RVObject.empty S j := dif_neg hjk
  change (rvSingleFamily k U j).domain.carrier.Nonempty at hj
  rw [he] at hj
  exact Set.not_nonempty_empty hj

def rvSingleGradedObject (k : ℕ) (U : RVObject (M := M) S k) : RVGradedObject (M := M) S :=
  ⟨rvSingleFamily k U, (Set.finite_singleton k).subset (rvSingleFamily_support_subset k U)⟩

theorem rvGradedIso_iff (U V : RVGradedObject (M := M) S) :
    Nonempty (U ≅ V) ↔ ∀ k, Nonempty (U.obj k ≅ V.obj k) := by
  constructor
  · rintro ⟨e⟩ k
    exact ⟨(rvGradedEvaluation S k).mapIso e⟩
  · intro h
    let e := fun k => Classical.choice (h k)
    refine ⟨{
      hom := ObjectProperty.homMk (fun k => (e k).hom)
      inv := ObjectProperty.homMk (fun k => (e k).inv)
      hom_inv_id := ?_
      inv_hom_id := ?_ }⟩
    · apply ObjectProperty.hom_ext
      funext k
      exact (e k).hom_inv_id
    · apply ObjectProperty.hom_ext
      funext k
      exact (e k).inv_hom_id

end SpecialTransformations.Section4

end
