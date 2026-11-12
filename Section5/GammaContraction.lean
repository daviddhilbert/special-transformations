module

public import Section5.GammaExistence

@[expose] public section

/-! The contraction paragraph over the original named-Gamma base. -/

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
variable {B : Section3.GammaParameters.Base (M := M)} {S : Set M} {n m u w : ℕ}

def flatKey (p : Point (M := M) n m) : Point (M := M) 0 (n + m) :=
  (Fin.elim0, Fin.append (key p).1 (key p).2)

theorem flatKey_eq_iff (p q : Point (M := M) n m) : flatKey p = flatKey q ↔ SameRV p q := by
  constructor
  · intro h
    have ht := congrArg Prod.snd h
    change Fin.append (key p).1 (key p).2 = Fin.append (key q).1 (key q).2 at ht
    apply Prod.ext
    · funext i
      simpa only [Fin.append_left] using congrFun ht (Fin.castAdd m i)
    · funext i
      simpa only [Fin.append_right] using congrFun ht (Fin.natAdd n i)
  · intro h
    refine Prod.ext (Subsingleton.elim _ _) ?_
    change Fin.append (key p).1 (key p).2 = Fin.append (key q).1 (key q).2
    exact congrArg (fun z : (Fin n → RV (M := M)) × (Fin m → RV (M := M)) =>
      Fin.append z.1 z.2) h

def contractionRelation {A : DefSet (M := M) S n m} {D : DefSet (M := M) S u w}
    (f : Map A D) (t : Point (M := M) 0 (n + m)) (z : Point (M := M) 0 (u + w)) : Prop :=
  ∃ a : A, flatKey a.val = t ∧ flatKey (f a).val = z

theorem gamma_contraction_graph (hΓ : GammaLogicInput B)
    {A : DefSet (M := M) S n m} {D : DefSet (M := M) S u w}
    (f : Map A D) (hf : GammaGraphDefinable B (pointMapGraph f)) (hBS : B.real ⊆ S) :
    GammaGraphDefinable B (contractionRelation f) := by
  let g := Map.comp (flattenKeyMap (PresentedSet.univ (keySpace u w) B.real))
    (keyMap (PresentedSet.univ (pointSpace u w) B.real))
  let k := Map.comp (flattenKeyMap (PresentedSet.univ (keySpace n m) B.real))
    (keyMap (PresentedSet.univ (pointSpace n m) B.real))
  have hh := hΓ.comp_graph (hΓ.swap_graph (hΓ.real_map_graph k))
    (gamma_postcompose_real hΓ f hf g hBS)
  apply GammaGraphDefinable.congr hh
  intro t z
  constructor
  · rintro ⟨p, ⟨x, hx, ht⟩, ⟨a, ha, hz⟩⟩
    refine ⟨a, ?_, hz⟩
    have he : x.val = a.val := hx.trans ha.symm
    exact (congrArg flatKey he).symm.trans ht
  · rintro ⟨a, ht, hz⟩
    exact ⟨a.val, ⟨⟨a.val, Set.mem_univ _⟩, rfl, ht⟩, ⟨a, rfl, hz⟩⟩

theorem contractionRelation_unique {A : DefSet (M := M) S n m} {D : DefSet (M := M) S u w}
    (f : Map A D) (hc : Contractible f) (t : Point (M := M) 0 (n + m))
    (ht : ∃ a : A, flatKey a.val = t) : ∃! z, contractionRelation f t z := by
  obtain ⟨a, ha⟩ := ht
  refine ⟨flatKey (f a).val, ⟨a, ha, rfl⟩, ?_⟩
  rintro z ⟨b, hb, hz⟩
  have he := hc a b ((flatKey_eq_iff a.val b.val).mp (ha.trans hb.symm))
  exact hz.symm.trans ((flatKey_eq_iff (f a).val (f b).val).mpr he).symm

def keyContraction {A : DefSet (M := M) S n m} {D : DefSet (M := M) S u w}
    (f : Map A D) : (flatKey '' carrier A) → (flatKey '' carrier D) := fun t => by
  let a : A := ⟨t.property.choose, t.property.choose_spec.1⟩
  exact ⟨flatKey (f a).val, (f a).val, (f a).property, rfl⟩

theorem keyContraction_graph {A : DefSet (M := M) S n m} {D : DefSet (M := M) S u w}
    (f : Map A D) (hc : Contractible f) (t : Point (M := M) 0 (n + m))
    (z : Point (M := M) 0 (u + w)) :
    (∃ x : flatKey '' carrier A, x.val = t ∧ (keyContraction f x).val = z) ↔
      contractionRelation f t z := by
  constructor
  · rintro ⟨x, rfl, hz⟩
    exact ⟨⟨x.property.choose, x.property.choose_spec.1⟩, x.property.choose_spec.2, hz⟩
  · rintro ⟨a, ha, hz⟩
    let t' : flatKey '' carrier A := ⟨t, a.val, a.property, ha⟩
    obtain ⟨v, hv, hu⟩ := contractionRelation_unique f hc t ⟨a, ha⟩
    have hk : contractionRelation f t (keyContraction f t').val :=
      ⟨⟨t'.property.choose, t'.property.choose_spec.1⟩, t'.property.choose_spec.2, rfl⟩
    exact ⟨t', rfl, (hu _ hk).trans (hu _ ⟨a, ha, hz⟩).symm⟩

theorem gamma_keyContraction_graph (hΓ : GammaLogicInput B)
    {A : DefSet (M := M) S n m} {D : DefSet (M := M) S u w}
    (f : Map A D) (hc : Contractible f) (hf : GammaGraphDefinable B (pointMapGraph f))
    (hBS : B.real ⊆ S) : GammaGraphDefinable B
      (fun t z => ∃ x : flatKey '' carrier A, x.val = t ∧ (keyContraction f x).val = z) :=
  GammaGraphDefinable.congr (gamma_contraction_graph hΓ f hf hBS)
    (fun t z => (keyContraction_graph f hc t z).symm)

theorem keyContraction_spec {A : DefSet (M := M) S n m} {D : DefSet (M := M) S u w}
    (f : Map A D) (hc : Contractible f) (a : A) :
    (keyContraction f ⟨flatKey a.val, a.val, a.property, rfl⟩).val = flatKey (f a).val := by
  let t : flatKey '' carrier A := ⟨flatKey a.val, a.val, a.property, rfl⟩
  have hk := (keyContraction_graph f hc t.val (keyContraction f t).val).mp ⟨t, rfl, rfl⟩
  obtain ⟨v, _, hu⟩ := contractionRelation_unique f hc t.val ⟨a, rfl⟩
  exact (hu _ hk).trans (hu _ ⟨a, rfl, rfl⟩).symm

theorem exists_unique_gamma_contraction (hΓ : GammaLogicInput B)
    {A : DefSet (M := M) S n m} {D : DefSet (M := M) S u w}
    (f : Map A D) (hc : Contractible f) (hf : GammaGraphDefinable B (pointMapGraph f))
    (hBS : B.real ⊆ S) :
    ∃! g : (flatKey '' carrier A) → (flatKey '' carrier D),
      (∀ a : A, (g ⟨flatKey a.val, a.val, a.property, rfl⟩).val = flatKey (f a).val) ∧
      GammaGraphDefinable B (fun t z => ∃ x : flatKey '' carrier A, x.val = t ∧ (g x).val = z) := by
  refine ⟨keyContraction f, ⟨keyContraction_spec f hc, gamma_keyContraction_graph hΓ f hc hf hBS⟩, ?_⟩
  intro g hg
  funext t
  obtain ⟨p, hp, he⟩ := t.property
  let a : A := ⟨p, hp⟩
  have ht : t = (⟨flatKey a.val, a.val, a.property, rfl⟩ : flatKey '' carrier A) :=
    Subtype.ext he.symm
  rw [ht]
  exact Subtype.ext ((hg.1 a).trans (keyContraction_spec f hc a).symm)

end SpecialTransformations.Section5
