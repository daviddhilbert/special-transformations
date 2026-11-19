import Section5.GammaInvariantLogic
import Section5.VerticalConstruction

/-! Real global maps on point spaces and their Gamma graphs: coordinate
selections and the RV reduction of one VF coordinate. These are real maps over
`B.real`, so their graphs are Gamma-definable over every Gamma base `B`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5

namespace SpecialTransformations.Section9.GammaLift

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n m u w : ℕ}

/-- Simultaneous selection of VF and RV coordinates, as a real map of point spaces. -/
def pointCoordinateMap (σ : Fin u → Fin n) (τ : Fin w → Fin m) (S : Set M) :
    Map (PresentedSet.univ (pointSpace (M := M) n m) S)
      (PresentedSet.univ (pointSpace (M := M) u w) S) :=
  Map.ofCodes _ (fun p => (p.1 ∘ σ, p.2 ∘ τ))
    (fun z => Sum.elim (fun i => z (.inl (σ i))) (fun i => z (.inr (τ i))))
    (by intro i; cases i with
        | inl i => exact rawProj S (.inl (σ i) : Fin n ⊕ Fin m)
        | inr i => exact rawProj S (.inr (τ i) : Fin n ⊕ Fin m))
    (by intro c; exact ⟨fun i => c.property.1 (σ i), fun i => c.property.2 (τ i)⟩)
    (by intro c; exact Prod.ext rfl rfl)

theorem pointCoordinateMap_value (σ : Fin u → Fin n) (τ : Fin w → Fin m) (S : Set M)
    (x : PresentedSet.univ (pointSpace (M := M) n m) S) :
    (pointCoordinateMap σ τ S x).val = (x.val.1 ∘ σ, x.val.2 ∘ τ) := rfl

theorem gamma_global_map_graph {B : Base (M := M)}
    (f : Map (PresentedSet.univ (pointSpace (M := M) n m) B.real)
      (PresentedSet.univ (pointSpace (M := M) u w) B.real)) :
    GammaGraphDefinable B (fun p q => (f ⟨p, Set.mem_univ _⟩).val = q) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput B).real_map_graph f)
  intro p q
  constructor
  · rintro ⟨x, hx, hq⟩
    have he : x = ⟨p, Set.mem_univ _⟩ := Subtype.ext hx
    exact he ▸ hq
  · exact fun h => ⟨⟨p, Set.mem_univ _⟩, rfl, h⟩

/-- Coordinate selection has a Gamma graph. -/
theorem gamma_coordinate_graph {B : Base (M := M)} (σ : Fin u → Fin n) (τ : Fin w → Fin m) :
    GammaGraphDefinable B (fun (p : Point (M := M) n m) (q : Point (M := M) u w) =>
      q = (p.1 ∘ σ, p.2 ∘ τ)) :=
  GammaGraphDefinable.congr (gamma_global_map_graph (pointCoordinateMap σ τ B.real))
    (fun _ _ => eq_comm)

/-- The RV label of a mixed point, as a Gamma graph. -/
theorem gamma_label_graph {B : Base (M := M)} :
    GammaGraphDefinable B (fun (p : Point (M := M) n m) (q : Point (M := M) 0 m) =>
      q = (Fin.elim0, p.2)) := by
  apply GammaGraphDefinable.congr (gamma_coordinate_graph (B := B) (Fin.elim0 : Fin 0 → Fin n) id)
  intro p q
  constructor
  · intro h
    rw [h]
    exact Prod.ext (funext (fun i => Fin.elim0 i)) rfl
  · intro h
    rw [h]
    exact Prod.ext (funext (fun i => Fin.elim0 i)) rfl

/-- The RV reduction `Point 1 0 → Point 0 1` as a Gamma graph. -/
theorem gamma_scalar_rv_graph {B : Base (M := M)} :
    GammaGraphDefinable B (fun (z : Point (M := M) 1 0) (y : Point (M := M) 0 1) =>
      y = (Fin.elim0, fun _ => rv (z.1 0))) := by
  apply GammaGraphDefinable.congr
    ((gammaLogicInput B).real_map_graph
      (headKeyMap (PresentedSet.univ (pointSpace (M := M) (0+1) 0) B.real)))
  intro z y
  constructor
  · rintro ⟨x, hx, hy⟩
    rw [← hy, headKeyMap_apply, hx]
    refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
    funext i
    fin_cases i
    rfl
  · intro hy
    refine ⟨⟨z, Set.mem_univ _⟩, rfl, ?_⟩
    rw [headKeyMap_apply, hy]
    refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
    funext i
    fin_cases i
    rfl

end SpecialTransformations.Section9.GammaLift
