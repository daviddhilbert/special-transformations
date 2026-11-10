import Section10.MeasuredVFCategory
import Section10.MeasuredRVCategory
import Section4.VFCategories
import Mathlib.CategoryTheory.Sigma.Basic

/-! The categories across degrees in Definitions 10.1 and 10.3.
Take the index type to be `ℕ` for all degrees or `Fin (bound + 1)`
for a bounded coproduct. Morphisms stay in their own degree. -/

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section

namespace SpecialTransformations.Section10

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [CommMonoidWithZero G]
local notation "VF" => VFType (M := M)

abbrev VFInDegree (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (d : VolumeScale M G) : ℕ → Type
  | 0 => VFFiniteObject (volumeGammaSpace hc) (C.base : Set M) 0
  | k + 1 => MeasuredVF C hc d k

instance vfInDegreeCategory [CharZero VF] (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (d : VolumeScale M G) : ∀ n, Category (VFInDegree hc C d n)
  | 0 => inferInstanceAs (Category (VFFiniteObject (volumeGammaSpace hc) (C.base : Set M) 0))
  | k + 1 => inferInstanceAs (Category (MeasuredVF C hc d k))

abbrev RVInDegree (S : Set M) (positive : ℕ → Type) : ℕ → Type
  | 0 => RVFiniteObject S 0
  | k + 1 => positive k

@[instance_reducible] def rvInDegreeCategory (S : Set M) (positive : ℕ → Type)
    (cat : ∀ k, Category (positive k)) : ∀ n, Category (RVInDegree S positive n)
  | 0 => inferInstanceAs (Category (RVFiniteObject S 0))
  | k + 1 => cat k

abbrev VFDegreeCoproduct {I : Type} (degree : I → ℕ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (d : VolumeScale M G) :=
  Σ i : I, VFInDegree hc C d (degree i)

instance vfDegreeCoproductCategory [CharZero VF] {I : Type} (degree : I → ℕ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (d : VolumeScale M G) :
    Category (VFDegreeCoproduct degree hc C d) := CategoryTheory.Sigma.sigma

abbrev RVDegreeCoproduct {I : Type} (degree : I → ℕ) (S : Set M) (positive : ℕ → Type) :=
  Σ i : I, RVInDegree S positive (degree i)

@[instance_reducible] def rvDegreeCoproductCategory {I : Type} (degree : I → ℕ) (S : Set M) (positive : ℕ → Type)
    (cat : ∀ k, Category (positive k)) : Category (RVDegreeCoproduct degree S positive) :=
  letI : ∀ i, Category (RVInDegree S positive (degree i)) := fun i => rvInDegreeCategory S positive cat (degree i)
  CategoryTheory.Sigma.sigma

@[instance_reducible] def rvVolumeDegreeCoproductCategory {I : Type} (degree : I → ℕ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    Category (RVDegreeCoproduct degree (C.base : Set M) (RVVolumeObject (C.base : Set M))) :=
  rvDegreeCoproductCategory degree (C.base : Set M) _ (fun _ => (rvVolumeGroupoid hc C).toCategory)

@[instance_reducible] def gammaVolumeDegreeCoproductCategory {I : Type} (degree : I → ℕ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    Category (RVDegreeCoproduct degree S (GammaVolumeObject hc S)) :=
  rvDegreeCoproductCategory degree S _ (fun _ => (gammaVolumeGroupoid hc).toCategory)

def rvUnitVolumeProperty (S : Set M) (k : ℕ) [Category (RVVolumeObject S k)] :
    ObjectProperty (RVVolumeObject S k) :=
  fun U => ∀ u, U.form.value u = 1

def gammaUnitVolumeProperty (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ)
    [Category (GammaVolumeObject hc S k)] : ObjectProperty (GammaVolumeObject hc S k) :=
  fun U => ∀ u, gammaFormValue U.form u = 1

abbrev RVUnitVolumeObject (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ) :=
  letI := (rvVolumeGroupoid (k := k) hc C).toCategory
  (rvUnitVolumeProperty (C.base : Set M) k).FullSubcategory

abbrev GammaUnitVolumeObject (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  letI := (gammaVolumeGroupoid (k := k) (S := S) hc).toCategory
  (gammaUnitVolumeProperty hc S k).FullSubcategory

@[instance_reducible] def rvUnitVolumeDegreeCoproductCategory {I : Type} (degree : I → ℕ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    Category (RVDegreeCoproduct degree (C.base : Set M) (RVUnitVolumeObject hc C)) :=
  rvDegreeCoproductCategory degree (C.base : Set M) _ (fun k => by
    letI := (rvVolumeGroupoid (k := k) hc C).toCategory
    infer_instance)

@[instance_reducible] def gammaUnitVolumeDegreeCoproductCategory {I : Type} (degree : I → ℕ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    Category (RVDegreeCoproduct degree S (GammaUnitVolumeObject hc S)) :=
  rvDegreeCoproductCategory degree S _ (fun k => by
    letI := (gammaVolumeGroupoid (k := k) (S := S) hc).toCategory
    infer_instance)

end SpecialTransformations.Section10
