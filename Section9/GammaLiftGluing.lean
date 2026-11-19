import Section9.GlueLabelLifts
import Section9.RestrictActualLift
import Section9.GammaLiftObjects

/-! Gamma counterparts of restricting a lift to a label cut and of gluing
lifts along a finite label partition. The raw constructions determine the
resulting graphs (restriction of the given graph, union of the given graphs),
so Gamma graphs are inherited without new choices. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)

namespace SpecialTransformations.Section9.GammaLift

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {B : Base (M := M)} {n : ℕ}

theorem gamma_label_preimage {k a : ℕ} {A : DefSet (rawRVSpace (M := M) a) S} (hA : RVSetGamma A B) :
    GammaSetDefinable B {p : Point (M := M) k a | p.2 ∈ A.carrier} := by
  have L := gammaLogicInput B
  have h := L.image_graph (L.restrict_graph hA (L.swap_graph (gamma_label_graph (B := B) (n := k) (m := a))))
  convert h using 1
  ext p
  constructor
  · intro hp
    exact ⟨(Fin.elim0, p.2), hp, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

theorem gamma_univ_set {a b : ℕ} : GammaSetDefinable B (Set.univ : Set (Point (M := M) a b)) := by
  have h := (gammaLogicInput B).image_graph (gamma_coordinate_graph (B := B) (n := a) (m := b) id id)
  convert h using 1
  ext q
  exact ⟨fun _ => ⟨q, rfl⟩, fun _ => Set.mem_univ _⟩

theorem gamma_true_graph {a b c d : ℕ} :
    GammaGraphDefinable B (fun (_ : Point (M := M) a b) (_ : Point (M := M) c d) => True) := by
  have L := gammaLogicInput B
  have h := L.comp_graph (gamma_coordinate_graph (B := B) (n := a) (m := b) (u := 0) (w := 0)
    Fin.elim0 Fin.elim0) (L.swap_graph (gamma_coordinate_graph (B := B) (n := c) (m := d) (u := 0) (w := 0)
    Fin.elim0 Fin.elim0))
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr h
  intro p q
  refine ⟨fun _ => trivial, fun _ => ⟨(Fin.elim0, Fin.elim0), ?_, ?_⟩⟩
  · exact Prod.ext (funext (fun i => Fin.elim0 i)) (funext (fun i => Fin.elim0 i))
  · exact Prod.ext (funext (fun i => Fin.elim0 i)) (funext (fun i => Fin.elim0 i))

theorem gamma_empty_graph {a b c d : ℕ} :
    GammaGraphDefinable B (fun (_ : Point (M := M) a b) (_ : Point (M := M) c d) => False) := by
  have L := gammaLogicInput B
  have h := L.restrict_graph (L.sdiff (gamma_univ_set (B := B) (a := a) (b := b)) gamma_univ_set)
    (gamma_true_graph (B := B) (c := c) (d := d))
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr h
  intro p q
  exact ⟨fun h => h.1.2 h.1.1, fun h => h.elim⟩

/-- Finite unions of Gamma graphs. -/
theorem gamma_iUnion_graph {I : Type} [Finite I] {a b c d : ℕ}
    {r : I → Point (M := M) a b → Point (M := M) c d → Prop}
    (h : ∀ i, GammaGraphDefinable B (r i)) :
    GammaGraphDefinable B (fun p q => ∃ i, r i p q) := by
  classical
  letI := Fintype.ofFinite I
  have L := gammaLogicInput B
  have hs : ∀ s : Finset I, GammaGraphDefinable B (fun p q => ∃ i ∈ s, r i p q) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      apply SpecialTransformations.Section5.GammaGraphDefinable.congr gamma_empty_graph
      intro p q
      simp
    | insert j s hj ih =>
      apply SpecialTransformations.Section5.GammaGraphDefinable.congr (L.union_graph (h j) ih)
      intro p q
      simp only [Finset.mem_insert, exists_eq_or_imp]
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (hs Finset.univ)
  intro p q
  simp

variable {U V : RVObject (M := M) S n}

theorem gamma_restricted_actual_lift
    (e : U ≅ V) (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier)
    (hAΓ : RVSetGamma A B)
    (f : Map (rvLift U) (rvLift V)) (hf : Function.Bijective f) (hfΓ : MixedMapGamma f B)
    (hlabel : ∀ p : rvLift U, e.hom.map.graph p.val.2 (f p).val.2) :
    let B' := (e.hom.map.restrict hA).image
    let hB' := rvLabelImage_subset e A hA
    ∃ g : Map (rvLift (U.restrict A hA)) (rvLift (V.restrict B' hB')), Function.Bijective g ∧
      MixedMapGamma g B ∧
      ∀ (p : rvLift (U.restrict A hA)) (q : rvLift U), p.val = q.val → (g p).val = (f q).val := by
  obtain ⟨g, hg, hgf⟩ := exists_restricted_actual_lift e A hA f hf hlabel
  refine ⟨g, hg, ?_, hgf⟩
  have L := gammaLogicInput B
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    (L.restrict_graph (gamma_label_preimage (k := n) hAΓ) hfΓ)
  intro p q
  constructor
  · rintro ⟨hpA, y, rfl, rfl⟩
    let x : rvLift (U.restrict A hA) := ⟨y.val, (rvLift_restrict_mem_iff U A hA _).mpr ⟨y.property, hpA⟩⟩
    exact ⟨x, rfl, hgf x y rfl⟩
  · rintro ⟨x, rfl, rfl⟩
    have hx := (rvLift_restrict_mem_iff U A hA _).mp x.property
    exact ⟨hx.2, ⟨x.val, hx.1⟩, rfl, (hgf x ⟨x.val, hx.1⟩ rfl).symm⟩

theorem gamma_glued_label_lift {I : Type} [Finite I]
    (e : U ≅ V) (P : I → DefSet (rawRVSpace (M := M) U.arity) S)
    (hP : ∀ i, (P i).carrier ⊆ U.domain.carrier)
    (hcover : ∀ u : U.domain, ∃ i, u.val ∈ (P i).carrier)
    (hdisj : ∀ i j z, z ∈ (P i).carrier → z ∈ (P j).carrier → i = j)
    (F : ∀ i, Map (rvLift (U.restrict (P i) (hP i)))
      (rvLift (V.restrict (e.hom.map.restrict (hP i)).image
        (rvLabelImage_subset e (P i) (hP i)))))
    (hF : ∀ i, Function.Bijective (F i)) (hFΓ : ∀ i, MixedMapGamma (F i) B)
    (hlabel : ∀ i (p : rvLift (U.restrict (P i) (hP i))),
      e.hom.map.graph p.val.2 (F i p).val.2) :
    ∃ G : Map (rvLift U) (rvLift V), Function.Bijective G ∧ MixedMapGamma G B ∧
      (∀ p : rvLift U, e.hom.map.graph p.val.2 (G p).val.2) ∧
      ∀ i (p : rvLift (U.restrict (P i) (hP i))) (q : rvLift U), p.val = q.val →
        (F i p).val = (G q).val := by
  obtain ⟨G, hG, hGlab, hGloc⟩ := exists_glued_label_lift e P hP hcover hdisj F hF hlabel
  refine ⟨G, hG, ?_, hGlab, hGloc⟩
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (gamma_iUnion_graph hFΓ)
  intro p q
  constructor
  · rintro ⟨i, y, rfl, rfl⟩
    let x : rvLift U := ⟨y.val, ((rvLift_restrict_mem_iff U (P i) (hP i) _).mp y.property).1⟩
    exact ⟨x, rfl, (hGloc i y x rfl).symm⟩
  · rintro ⟨x, rfl, rfl⟩
    obtain ⟨i, hi⟩ := hcover (liftLabelMap U x)
    let y : rvLift (U.restrict (P i) (hP i)) :=
      ⟨x.val, (rvLift_restrict_mem_iff U (P i) (hP i) _).mpr ⟨x.property, hi⟩⟩
    exact ⟨i, y, rfl, hGloc i y x rfl⟩

end SpecialTransformations.Section9.GammaLift
