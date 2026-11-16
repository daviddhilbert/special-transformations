module

public import Section5.PullbackLift

@[expose] public section

/-!
# Surjectivity of lifting on isomorphism classes

The dimensional presentation and finite-RV-fibre invariance interfaces are
explicit earlier-section inputs. The actual lift object and bijection are
constructed here from the special-bijection existence theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

theorem lift_representation_of_reduction (h00 : M ⊨ Axioms.ACVF00)
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v S N)
    {P : PresentedSpace (M := M)} (A : PresentedSet P S)
    (hreduce : ∃ m : ℕ, ∃ D : DefSet (M := M) S k m,
      ∃ f : Map A D, Function.Bijective f) :
    ∃ U : @Section4.RVObject M (CanonicalStructure.normalize (M := M)) S k,
      ∃ g : Map A (rawLift U), Function.Bijective g := by
  obtain ⟨m, D, f, hf⟩ := hreduce
  obtain ⟨U, g, hg⟩ := deformed_pullback_is_lift h00 v hv hObstacles D
  exact ⟨U, Map.comp g f, hg.comp hf⟩

theorem finite_lift_representation_of_reduction (h00 : M ⊨ Axioms.ACVF00)
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v S N)
    {P : PresentedSpace (M := M)} (A : PresentedSet P S)
    (hreduce : ∃ m : ℕ, ∃ D : DefSet (M := M) S k m,
      ∃ f : Map A D, Function.Bijective f)
    (hfinite : ∀ {m : ℕ} (D : DefSet (M := M) S k m) (f : Map A D),
      Function.Bijective f → ∀ x : Fin k → VF (M := M),
        {t : Fin m → RV (M := M) | (x, t) ∈ carrier D}.Finite) :
    ∃ U : @Section4.RVFiniteObject M (CanonicalStructure.normalize (M := M)) S k,
      ∃ g : Map A (rawLift (rvFiniteObject U)), Function.Bijective g := by
  obtain ⟨m, D, f, hf⟩ := hreduce
  obtain ⟨r, B, ⟨T⟩, hB⟩ := corollary_5_6 h00 v hv hObstacles D
  let q := Map.comp T.toMap f
  have hq : Function.Bijective q := T.bijective.comp hf
  have hfin := pullbackObject_finiteVolume B hB (hfinite B q hq)
  let obj := pullbackObject B
  let U : @Section4.RVFiniteObject M (CanonicalStructure.normalize (M := M)) S k := by
    letI := @CanonicalStructure.normalize M sM
    exact ⟨obj, hfin⟩
  exact ⟨U, Map.comp (pullbackLiftMap B) q, (pullbackLiftMap_bijective B hB).comp hq⟩

abbrev normalizedVFObject (Δ : PresentedSpace (M := M)) (S : Set M) (k : ℕ) :=
  @Section4.VFObject M (CanonicalStructure.normalize (M := M)) Δ S k

abbrev normalizedVFFiniteObject (Δ : PresentedSpace (M := M)) (S : Set M) (k : ℕ) :=
  @Section4.VFFiniteObject M (CanonicalStructure.normalize (M := M)) Δ S k

def normalizedVFData (Δ : PresentedSpace (M := M)) (S : Set M) (k : ℕ)
    (A : normalizedVFObject Δ S k) :
    Σ i : ℕ × ℕ, PresentedSet (rawPointSpace (M := M) i.1 i.2) S := by
  letI := @CanonicalStructure.normalize M sM
  exact ⟨A.obj.index, A.obj.set⟩

def normalizedFiniteParent (Δ : PresentedSpace (M := M)) (S : Set M) (k : ℕ)
    (A : normalizedVFFiniteObject Δ S k) : normalizedVFObject Δ S k := by
  letI := @CanonicalStructure.normalize M sM
  exact A.obj

abbrev normalizedLiftObject (Δ : PresentedSpace (M := M))
    (U : @Section4.RVObject M (CanonicalStructure.normalize (M := M)) S k) :=
  @Section4.rvLiftObject M (CanonicalStructure.normalize (M := M))
    (CanonicalStructure.normalized_model hM) S k Δ U

abbrev normalizedLiftFiniteObject (Δ : PresentedSpace (M := M))
    (U : @Section4.RVFiniteObject M (CanonicalStructure.normalize (M := M)) S k) :=
  @Section4.rvLiftFiniteObject M (CanonicalStructure.normalize (M := M))
    (CanonicalStructure.normalized_model hM) S k Δ U

/-- Corollary 5.7 for VF[k,·]. The given reduction is the real-sort
presentation consequence of Section 4.2, retaining the same base. -/
theorem corollary_5_7 (h00 : M ⊨ Axioms.ACVF00)
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v S N)
    (Δ : PresentedSpace (M := M)) (k : ℕ)
    (hreduce : ∀ A : normalizedVFObject Δ S k,
      ∃ m : ℕ, ∃ D : DefSet (M := M) S k m,
        ∃ f : Map (normalizedVFData Δ S k A).2 D, Function.Bijective f)
    (A : normalizedVFObject Δ S k) :
    ∃ U : @Section4.RVObject M (CanonicalStructure.normalize (M := M)) S k,
      Nonempty (A ≅ normalizedLiftObject Δ U) := by
  obtain ⟨U, f, hf⟩ := lift_representation_of_reduction h00 v hv hObstacles
    (normalizedVFData Δ S k A).2 (hreduce A)
  refine ⟨U, ⟨?_⟩⟩
  apply CategoryTheory.ObjectProperty.isoMk
  exact @DefinableGeometry.DefinableSetCat.isoOfBijective LRV M
    (CanonicalStructure.normalize (M := M)) _ _ S _ _ f hf

/-- Corollary 5.7 for VF[k]. The extra given input is precisely finite-RV-
fibre invariance under definable bijections, the zero-dimensional case
of the Section 4.13 invariant. -/
theorem corollary_5_7_finite (h00 : M ⊨ Axioms.ACVF00)
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v S N)
    (Δ : PresentedSpace (M := M)) (k : ℕ)
    (hreduce : ∀ A : normalizedVFObject Δ S k,
      ∃ m : ℕ, ∃ D : DefSet (M := M) S k m,
        ∃ f : Map (normalizedVFData Δ S k A).2 D, Function.Bijective f)
    (hfinite : ∀ A : normalizedVFFiniteObject Δ S k,
      ∀ {m : ℕ} (D : DefSet (M := M) S k m)
        (f : Map (normalizedVFData Δ S k (normalizedFiniteParent Δ S k A)).2 D),
        Function.Bijective f → ∀ x : Fin k → VF (M := M),
          {t : Fin m → RV (M := M) | (x, t) ∈ carrier D}.Finite)
    (A : normalizedVFFiniteObject Δ S k) :
    ∃ U : @Section4.RVFiniteObject M (CanonicalStructure.normalize (M := M)) S k,
      Nonempty (A ≅ normalizedLiftFiniteObject Δ U) := by
  obtain ⟨U, f, hf⟩ := finite_lift_representation_of_reduction h00 v hv hObstacles
    (normalizedVFData Δ S k (normalizedFiniteParent Δ S k A)).2
    (hreduce (normalizedFiniteParent Δ S k A)) (hfinite A)
  refine ⟨U, ⟨?_⟩⟩
  apply CategoryTheory.ObjectProperty.isoMk
  apply CategoryTheory.ObjectProperty.isoMk
  exact @DefinableGeometry.DefinableSetCat.isoOfBijective LRV M
    (CanonicalStructure.normalize (M := M)) _ _ S _ _ f hf

end SpecialTransformations.Section5
