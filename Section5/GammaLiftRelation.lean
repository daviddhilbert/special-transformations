import Section5.GammaInvariantLogic
import Section5.GammaLift

/-! Definable graphs and actual RV pullbacks over the original Gamma base. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters

noncomputable section

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m u w : ℕ}

private theorem pointCode_injective :
    Function.Injective (gammaPointCode (M := M) (n := n) (m := m)) := by
  intro p q h
  apply Prod.ext
  · funext i
    apply Subtype.ext
    simpa only [gammaPointCode, vfAt, Fin.append_left] using congrFun h (Fin.castAdd m i)
  · funext i
    apply Subtype.ext
    simpa only [gammaPointCode, Fin.append_right] using congrFun h (Fin.natAdd n i)

theorem GammaGraphDefinable.inter
    {r t : Point (M := M) n m → Point (M := M) u w → Prop}
    (hr : GammaGraphDefinable B r) (ht : GammaGraphDefinable B t) :
    GammaGraphDefinable B (fun x y => r x y ∧ t x y) := by
  unfold GammaGraphDefinable at *
  convert hr.inter ht using 1
  ext z
  constructor
  · rintro ⟨p, q, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨⟨p, q, h₁, rfl⟩, ⟨p, q, h₂, rfl⟩⟩
  · rintro ⟨⟨p, q, h₁, h₁z⟩, ⟨x, y, h₂, h₂z⟩⟩
    have he := h₁z.trans h₂z.symm
    have hp : p = x := pointCode_injective (funext fun i => by
      simpa only [Fin.append_left] using congrFun he (Fin.castAdd (u + w) i))
    have hq : q = y := pointCode_injective (funext fun i => by
      simpa only [Fin.append_right] using congrFun he (Fin.natAdd (n + m) i))
    exact ⟨p, q, ⟨h₁, hp.symm ▸ hq.symm ▸ h₂⟩, h₁z⟩

theorem GammaGraphDefinable.preimage_maps {a b c d : ℕ}
    {r : Point (M := M) n m → Point (M := M) u w → Prop}
    (hr : GammaGraphDefinable B r)
    (f : Map (PresentedSet.univ (pointSpace a b) B.real)
      (PresentedSet.univ (pointSpace n m) B.real))
    (g : Map (PresentedSet.univ (pointSpace c d) B.real)
      (PresentedSet.univ (pointSpace u w) B.real)) :
    GammaGraphDefinable B (fun p q =>
      r (f ⟨p, Set.mem_univ _⟩).val (g ⟨q, Set.mem_univ _⟩).val) := by
  let L := gammaLogicInput B
  apply GammaGraphDefinable.congr
    (L.comp_graph (L.comp_graph (L.real_map_graph f) hr) (L.swap_graph (L.real_map_graph g)))
  intro p q
  constructor
  · rintro ⟨t, ⟨s, ⟨x, hx, hs⟩, hst⟩, y, hy, ht⟩
    have hx' : x = ⟨p, Set.mem_univ _⟩ := Subtype.ext hx
    have hy' : y = ⟨q, Set.mem_univ _⟩ := Subtype.ext hy
    rw [hx'] at hs
    rw [hy'] at ht
    simpa only [hs, ht] using hst
  · intro h
    exact ⟨_, ⟨_, ⟨⟨p, Set.mem_univ _⟩, rfl, rfl⟩, h⟩,
      ⟨q, Set.mem_univ _⟩, rfl, rfl⟩

theorem GammaGraphDefinable.diagonal
    {r : Point (M := M) n m → Point (M := M) n m → Prop}
    (hr : GammaGraphDefinable B r) :
    GammaSetDefinable B {p | r p p} := by
  let W := PresentedSet.univ (pointSpace (M := M) n m) B.real
  let L := gammaLogicInput B
  have he := L.real_map_graph (Map.id W)
  have h := L.image_graph (hr.inter he)
  convert h using 1
  ext y
  constructor
  · intro hy
    exact ⟨y, hy, ⟨y, Set.mem_univ _⟩, rfl, rfl⟩
  · rintro ⟨x, hxy, a, hx, hy⟩
    change a.val = y at hy
    exact (hx.symm.trans hy) ▸ hxy

private def keyPointMap (S : Set M) (n m : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) n m) S)
      (PresentedSet.univ (pointSpace 0 (n + m)) S) :=
  Map.comp (flattenKeyMap (PresentedSet.univ (keySpace n m) S))
    (keyMap (PresentedSet.univ (pointSpace n m) S))

def pointLabels (S : Set M) (n m : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) n m) S)
      (PresentedSet.univ (pointSpace 0 m) S) :=
  Map.comp (rvCoordinatePointMap (Fin.natAdd n) S) (keyPointMap S n m)

def pointVolumes (S : Set M) (n m : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) n m) S)
      (PresentedSet.univ (pointSpace 0 n) S) :=
  Map.comp (rvCoordinatePointMap (fun i => Fin.castAdd m i) S) (keyPointMap S n m)

theorem pointLabels_snd (S : Set M) (n m : ℕ)
    (p : PresentedSet.univ (pointSpace (M := M) n m) S) :
    (pointLabels S n m p).val.2 = p.val.2 := by
  funext i
  change Fin.append (fun j => rv (p.val.1 j)) p.val.2 (Fin.natAdd n i) = p.val.2 i
  exact Fin.append_right _ _ _

theorem pointVolumes_snd (S : Set M) (n m : ℕ)
    (p : PresentedSet.univ (pointSpace (M := M) n m) S) :
    (pointVolumes S n m p).val.2 = fun i => rv (p.val.1 i) := by
  funext i
  change Fin.append (fun j => rv (p.val.1 j)) p.val.2 (Fin.castAdd m i) = rv (p.val.1 i)
  exact Fin.append_left _ _ _

theorem GammaRVObject.lift_definable {k : ℕ} (U : GammaRVObject B k) :
    GammaSetDefinable B U.lift := by
  let m := rvObjectArity U.object
  have h := (U.volume_graph.preimage_maps (pointLabels B.real k m) (pointVolumes B.real k m)).diagonal
  convert h using 1
  ext p
  let a : PresentedSet.univ (pointSpace (M := M) k m) B.real := ⟨p, Set.mem_univ _⟩
  change (∃ u : rvObjectDomain U.object, u.val = p.2 ∧
    (rvObjectVolume U.object u).val = _) ↔
    ∃ u : rvObjectDomain U.object, u.val = (pointLabels B.real k m a).val.2 ∧
      (rvObjectVolume U.object u).val = (pointVolumes B.real k m a).val.2
  rw [pointLabels_snd, pointVolumes_snd]
  apply exists_congr
  intro u
  exact and_congr Iff.rfl
    (Iff.of_eq (congrArg (fun t => (rvObjectVolume U.object u).val = t)
      (@normalized_tupleRV M sM hM k p.1)))

end SpecialTransformations.Section5
