import Section5.GammaGraphs
import Section5.UnaryMaps

/-!
# Given invariant-Gamma logic and its geometric consequences

The input fields are ordinary real-parameter embedding, Boolean closure,
relational composition and definable image rules for the genuine invariant
preimages of Section3.GammaParameters. They are earlier-section interfaces,
not saturation and not special-bijection existence assumptions. The RV-hull
consequence is derived below using the actual mixed-key map.
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

def pointMapGraph {S : Set M} {n m u w : ℕ}
    {A : DefSet (M := M) S n m} {D : DefSet (M := M) S u w} (f : Map A D)
    (p : Point (M := M) n m) (q : Point (M := M) u w) : Prop :=
  ∃ a : A, a.val = p ∧ (f a).val = q

def GammaScalarGraphDefinable (B : Section3.GammaParameters.Base (M := M)) {n m : ℕ}
    (r : Point (M := M) n m → VF (M := M) → Prop) : Prop :=
  GammaGraphDefinable B (fun (p : Point (M := M) n m) (z : Point (M := M) 1 0) => r p (vfAt z 0))

theorem GammaGraphDefinable.congr {B : Section3.GammaParameters.Base (M := M)} {n m u w : ℕ}
    {r t : Point (M := M) n m → Point (M := M) u w → Prop}
    (hr : GammaGraphDefinable B r) (h : ∀ p q, r p q ↔ t p q) : GammaGraphDefinable B t := by
  have he : r = t := funext (fun p => funext (fun q => propext (h p q)))
  exact he ▸ hr

theorem GammaScalarGraphDefinable.congr {B : Section3.GammaParameters.Base (M := M)} {n m : ℕ}
    {r t : Point (M := M) n m → VF (M := M) → Prop}
    (hr : GammaScalarGraphDefinable B r) (h : ∀ p x, r p x ↔ t p x) :
    GammaScalarGraphDefinable B t :=
  GammaGraphDefinable.congr hr (fun p z => h p (vfAt z 0))

structure GammaLogicInput (B : Section3.GammaParameters.Base (M := M)) where
  real_set : ∀ {n m : ℕ} (A : Set (Point (M := M) n m)),
    SetDefinable (pointSpace n m) B.real A → GammaSetDefinable B A
  real_map_graph : ∀ {n m u w : ℕ} {A : DefSet (M := M) B.real n m}
    {D : DefSet (M := M) B.real u w} (f : Map A D), GammaGraphDefinable B (pointMapGraph f)
  real_scalar_graph : ∀ {n m : ℕ} {A : DefSet (M := M) B.real n m}
    (f : Map A (PresentedSet.univ (Section4.vfSpace 1) B.real)),
    GammaScalarGraphDefinable B (fun p x => ∃ a : A, a.val = p ∧ (f a).val 0 = x)
  inter : ∀ {n m : ℕ} {A C : Set (Point (M := M) n m)},
    GammaSetDefinable B A → GammaSetDefinable B C → GammaSetDefinable B (A ∩ C)
  union : ∀ {n m : ℕ} {A C : Set (Point (M := M) n m)},
    GammaSetDefinable B A → GammaSetDefinable B C → GammaSetDefinable B (A ∪ C)
  sdiff : ∀ {n m : ℕ} {A C : Set (Point (M := M) n m)},
    GammaSetDefinable B A → GammaSetDefinable B C → GammaSetDefinable B (A \ C)
  restrict_graph : ∀ {n m u w : ℕ} {A : Set (Point (M := M) n m)}
    {r : Point (M := M) n m → Point (M := M) u w → Prop},
    GammaSetDefinable B A → GammaGraphDefinable B r →
      GammaGraphDefinable B (fun p q => p ∈ A ∧ r p q)
  union_graph : ∀ {n m u w : ℕ} {r t : Point (M := M) n m → Point (M := M) u w → Prop},
    GammaGraphDefinable B r → GammaGraphDefinable B t →
      GammaGraphDefinable B (fun p q => r p q ∨ t p q)
  comp_graph : ∀ {n m u w a b : ℕ}
    {r : Point (M := M) n m → Point (M := M) u w → Prop}
    {t : Point (M := M) u w → Point (M := M) a b → Prop},
    GammaGraphDefinable B r → GammaGraphDefinable B t →
      GammaGraphDefinable B (fun p q => ∃ z, r p z ∧ t z q)
  swap_graph : ∀ {n m u w : ℕ} {r : Point (M := M) n m → Point (M := M) u w → Prop},
    GammaGraphDefinable B r → GammaGraphDefinable B (fun q p => r p q)
  image_graph : ∀ {n m u w : ℕ} {r : Point (M := M) n m → Point (M := M) u w → Prop},
    GammaGraphDefinable B r → GammaSetDefinable B {q | ∃ p, r p q}
  scalar_image_graph : ∀ {n m a b u w : ℕ}
    {r : Point (M := M) n m → VF (M := M) → Prop},
    GammaScalarGraphDefinable B r →
    ∀ f : Map (PresentedSet.univ (spaceProd (pointSpace n m) (Section4.vfSpace 1)) B.real)
      (PresentedSet.univ (spaceProd (pointSpace a b) (pointSpace u w)) B.real),
    GammaGraphDefinable B (fun p q => ∃ z x,
      r z x ∧ (f ⟨(z, ![x]), Set.mem_univ _⟩).val = (p, q))

namespace GammaLogicInput

variable {B : Section3.GammaParameters.Base (M := M)} (hΓ : GammaLogicInput B)

include hΓ

theorem image_real {n m u w : ℕ} {A : DefSet (M := M) B.real n m}
    {D : DefSet (M := M) B.real u w} (f : Map A D)
    {C : Set (Point (M := M) n m)} (hC : GammaSetDefinable B C) :
    GammaSetDefinable B {q | ∃ a : A, a.val ∈ C ∧ (f a).val = q} := by
  have hh := hΓ.image_graph (hΓ.restrict_graph hC (hΓ.real_map_graph f))
  convert hh using 1
  ext q
  constructor
  · rintro ⟨a, ha, he⟩
    exact ⟨a.val, ha, a, rfl, he⟩
  · rintro ⟨p, hp, a, rfl, he⟩
    exact ⟨a, hp, he⟩

theorem preimage_real {n m u w : ℕ} {A : DefSet (M := M) B.real n m}
    {D : DefSet (M := M) B.real u w} (f : Map A D)
    {C : Set (Point (M := M) u w)} (hC : GammaSetDefinable B C) :
    GammaSetDefinable B {p | ∃ a : A, a.val = p ∧ (f a).val ∈ C} := by
  have hh := hΓ.image_graph (hΓ.restrict_graph hC (hΓ.swap_graph (hΓ.real_map_graph f)))
  convert hh using 1
  ext p
  constructor
  · rintro ⟨a, rfl, ha⟩
    exact ⟨(f a).val, ha, a, rfl, rfl⟩
  · rintro ⟨q, hq, a, rfl, he⟩
    exact ⟨a, rfl, he.symm ▸ hq⟩

theorem hull {n m : ℕ} {C : Set (Point (M := M) n m)} (hC : GammaSetDefinable B C) :
    GammaSetDefinable B (hull C) := by
  let A := PresentedSet.univ (pointSpace (M := M) n m) B.real
  let f := Map.comp (flattenKeyMap (PresentedSet.univ (keySpace n m) B.real)) (keyMap A)
  have hflat (p q : Point (M := M) n m) :
      (f ⟨p, Set.mem_univ _⟩).val = (f ⟨q, Set.mem_univ _⟩).val ↔ SameRV p q := by
    constructor
    · intro he
      have ht := congrArg Prod.snd he
      change Fin.append (key p).1 (key p).2 = Fin.append (key q).1 (key q).2 at ht
      apply Prod.ext
      · funext i
        simpa only [Fin.append_left] using congrFun ht (Fin.castAdd m i)
      · funext i
        simpa only [Fin.append_right] using congrFun ht (Fin.natAdd n i)
    · intro he
      refine Prod.ext (Subsingleton.elim _ _) ?_
      exact congrArg (fun z => Fin.append z.1 z.2) he
  have hi := hΓ.image_real f hC
  have hp := hΓ.preimage_real f hi
  convert hp using 1
  ext p
  constructor
  · rintro ⟨q, hq, he⟩
    exact ⟨⟨p, Set.mem_univ _⟩, rfl, ⟨⟨q, Set.mem_univ _⟩, hq, (hflat q p).mpr he⟩⟩
  · rintro ⟨a, rfl, b, hb, he⟩
    exact ⟨b.val, hb, (hflat b.val a.val).mp he⟩

end GammaLogicInput
end SpecialTransformations.Section5
