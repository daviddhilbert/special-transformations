module

public import Section5.GeneralAssembly

@[expose] public section

/-!
# Definable-map preparation in every finite mixed arity

All hypotheses below are visible: the uniform finite root-free obstacle
interface is earlier-section input. The existence of special bijections is
proved by the preceding dimensional construction, rather than assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m u w : ℕ}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

theorem map_preparation_at_boundary (h00 : M ⊨ Axioms.ACVF00)
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v S N)
    {A : DefSet (M := M) S n m} {D : DefSet (M := M) S u w}
    (previous : Option Bool) (hTags : previous = some false → AllTagged A) (f : Map A D) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S n r, ∃ V : SpecialBijection A B,
      V.chain.Alternating previous ∧ IsRVPullback (carrier B) ∧
        Contractible (Map.comp f V.inverseMap) := by
  let g := Map.comp (flattenKeyMap (PresentedSet.univ (keySpace u w) S)) (Map.comp (keyMap D) f)
  obtain ⟨r, B, V, hVa, hB, hg⟩ := rvPreparation_all h00 v hv hObstacles n A previous hTags g
  refine ⟨r, B, V, hVa, hB, ?_⟩
  intro b c he
  change SameRV (f (V.inverseMap b)).val (f (V.inverseMap c)).val
  have hh := ((sameRV_iff _ _).mp (hg b c he)).2
  change Fin.append (key (f (V.inverseMap b)).val).1 (key (f (V.inverseMap b)).val).2 =
    Fin.append (key (f (V.inverseMap c)).val).1 (key (f (V.inverseMap c)).val).2 at hh
  apply Prod.ext
  · funext i
    simpa only [Fin.append_left] using congrFun hh (Fin.castAdd w i)
  · funext i
    simpa only [Fin.append_right] using congrFun hh (Fin.natAdd u i)

/-- An arbitrary initial special bijection is retained with genuine
alternation at its concatenation boundary. -/
theorem map_preparation (h00 : M ⊨ Axioms.ACVF00)
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v S N)
    {a : ℕ} {A₀ : DefSet (M := M) S n a} {A : DefSet (M := M) S n m}
    {D : DefSet (M := M) S u w} (τ : SpecialBijection A₀ A) (f : Map A D) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S n r, ∃ V : SpecialBijection A B,
      (τ.chain.append V.chain).Alternating none ∧ IsRVPullback (carrier B) ∧
        Contractible (Map.comp f V.inverseMap) := by
  obtain ⟨r, B, V, hVa, hB, hf⟩ := map_preparation_at_boundary h00 v hv hObstacles
    (τ.chain.lastKind none)
    (fun h => τ.chain.lastKind_allTagged none (by intro he; cases he) h) f
  exact ⟨r, B, V, τ.chain.append_alternating V.chain none τ.alternating hVa, hB, hf⟩

theorem corollary_5_6 (h00 : M ⊨ Axioms.ACVF00)
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v S N)
    (A : DefSet (M := M) S n m) : IsDeformedRVPullback A := by
  obtain ⟨r, B, V, _, hB, _⟩ := map_preparation_at_boundary h00 v hv hObstacles none
    (by intro h; cases h) (Map.id A)
  exact ⟨r, B, ⟨V⟩, hB⟩

end SpecialTransformations.Section5
