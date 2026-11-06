import Section4.RVSequenceIndependence
import Section4.AlgebraicAutomorphisms
import Section4.HomogeneousAvoidance

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem RVSequenceIndependent.map_automorphism
    (hcan : CanonicalStructure.IsCanonical (M := M)) (e : M ≃[LRV] M) {S : Set M}
    (hfix : ∀ s ∈ S, e s = s) {n : ℕ} {t : Fin n → CanonicalRV.RVSort M}
    (h : RVSequenceIndependent S t) :
    RVSequenceIndependent S (rvAutomorphism e ∘ t) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    change RVSequenceIndependent S (Fin.init (rvAutomorphism e ∘ t)) ∧
      ¬ AlgebraicAt (S ∪ Set.range (rvValues (Fin.init (rvAutomorphism e ∘ t))))
        .rv (rvAutomorphism e (t (Fin.last n))).val
    have hinit : Fin.init (rvAutomorphism e ∘ t) = rvAutomorphism e ∘ Fin.init t := rfl
    rw [hinit]
    refine ⟨ih h.1, ?_⟩
    exact fun hlast => h.2 ((rvAutomorphism_algebraic_tuple_iff hcan e hfix
      (Fin.init t) (t (Fin.last n))).mp hlast)

/-- Move a finite independent RV sequence away from a larger small base.
At each stage the new automorphism fixes every previously chosen coordinate.
The argument uses actual saturation and strong homogeneity. -/
theorem exists_automorphism_rv_sequence_independent
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hh : StronglyHomogeneous M κ) {S T : Set M} (hST : S ⊆ T)
    (hS : Cardinal.mk S < κ) (hT : Cardinal.mk T < κ)
    {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) (ht : RVSequenceIndependent S t) :
    ∃ e : M ≃[LRV] M, (∀ x ∈ S, e x = x) ∧
      RVSequenceIndependent T (rvAutomorphism e ∘ t) := by
  induction n with
  | zero => exact ⟨FirstOrder.Language.Equiv.refl LRV M, fun _ _ => rfl, trivial⟩
  | succ n ih =>
    obtain ⟨e, hefix, heind⟩ := ih (Fin.init t) ht.1
    let b := rvAutomorphism e ∘ t
    have heind' : RVSequenceIndependent T (Fin.init b) := heind
    have hb := ht.map_automorphism hcan e hefix
    let P := S ∪ Set.range (rvValues (Fin.init b))
    let Q := T ∪ Set.range (rvValues (Fin.init b))
    have hPQ : P ⊆ Q := by
      rintro x (hx | hx)
      · exact Or.inl (hST hx)
      · exact Or.inr hx
    have hP : Cardinal.mk P < κ := small_union_range hκ S hS (rvValues (Fin.init b))
    have hQ : Cardinal.mk Q < κ := small_union_range hκ T hT (rvValues (Fin.init b))
    have hnot : ¬ RawClosure.AlgebraicOver P (b (Fin.last n)).val := by
      intro hraw
      exact hb.2 ((algebraicAt_iff_raw hcan P .rv _).mpr
        ⟨hraw, (b (Fin.last n)).property⟩)
    obtain ⟨f, hffix, hfnot⟩ := exists_automorphism_avoiding_algebraic_closure
      hκ hs hh hPQ hP hQ (b (Fin.last n)).val hnot
    let g := f.comp e
    have hinit : Fin.init (rvAutomorphism g ∘ t) = Fin.init b := by
      funext i
      apply Subtype.ext
      change f (e (t i.castSucc).val) = e (t i.castSucc).val
      exact hffix _ (Or.inr ⟨i, rfl⟩)
    refine ⟨g, ?_, ?_⟩
    · intro x hx
      change f (e x) = x
      rw [hefix x hx]
      exact hffix x (Or.inl hx)
    · change RVSequenceIndependent T (Fin.init (rvAutomorphism g ∘ t)) ∧
        ¬ AlgebraicAt (T ∪ Set.range (rvValues (Fin.init (rvAutomorphism g ∘ t))))
          .rv (rvAutomorphism g (t (Fin.last n))).val
      rw [hinit]
      refine ⟨heind', ?_⟩
      intro halg
      exact hfnot halg.raw_finite_witness

end SpecialTransformations.Section4

end
