module

public import Section4.GammaPredicates
public import Section4.OrderControllerTuples
public import Section4.GammaOrderControllers

@[expose] public section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

theorem gamma_tupleControls_definable (A : Set (Values.Gamma (M := M)))
    (hA : Values.GammaDefinable S A) (n : ℕ) :
    GammaSyntax.Definable S (fun c : Fin n → Values.Gamma (M := M) =>
      FiniteOrder.TupleControls c A) := by
  have hpat : GammaSyntax.Definable S
      (fun z : Fin n ⊕ Fin 2 → Values.Gamma (M := M) =>
        ∀ i, (z (.inr 0) < z (.inl i) ↔ z (.inr 1) < z (.inl i)) ∧
          (z (.inl i) < z (.inr 0) ↔ z (.inl i) < z (.inr 1))) :=
    GammaSyntax.Definable.forall_finite (fun i =>
      ((GammaSyntax.lt_definable S (Sum.inr 0) (Sum.inl i)).iff
        (GammaSyntax.lt_definable S (Sum.inr 1) (Sum.inl i))).and
      ((GammaSyntax.lt_definable S (Sum.inl i) (Sum.inr 0)).iff
        (GammaSyntax.lt_definable S (Sum.inl i) (Sum.inr 1))))
  have hm := (GammaSyntax.unary_at hA (Sum.inr (0 : Fin 2) : Fin n ⊕ Fin 2)).iff
    (GammaSyntax.unary_at hA (Sum.inr (1 : Fin 2) : Fin n ⊕ Fin 2))
  have h := (hpat.imp hm).forall_block
  exact h.congr (fun c => by
    constructor
    · intro hc x y hp
      exact hc ![x,y] hp
    · intro hc p
      exact hc (p 0) (p 1))

/-- The original-base formula quantifies over controlling tuples of the
least possible length. Uniqueness shows its union is exactly the finite
intrinsic endpoint set; no chosen endpoint is added to the parameters. -/
theorem minimal_gamma_controller_definable
    (A : Set (Values.Gamma (M := M))) (hA : Values.GammaDefinable S A)
    (F : Finset (Values.Gamma (M := M))) (hF : FiniteOrder.Controls F A)
    (hmin : ∀ H, FiniteOrder.Controls H A → F.card ≤ H.card) :
    Values.GammaDefinable S (F : Set (Values.Gamma (M := M))) := by
  let ι := Fin 1 ⊕ Fin F.card
  have hc := (gamma_tupleControls_definable A hA F.card).reindex
    (Sum.inr : Fin F.card → ι)
  have hi : GammaSyntax.Definable S
      (fun z : ι → Values.Gamma (M := M) =>
        ∃ i : Fin F.card, z (.inr i) = z (.inl 0)) := by
    have h := (GammaSyntax.Definable.forall_finite (fun i : Fin F.card =>
      (GammaSyntax.eq_definable (M := M) S (Sum.inr i : ι) (Sum.inl 0)).not)).not
    exact h.congr (fun z => by simp only [not_forall, not_not])
  have he := (hc.and hi).exists_block
  apply (GammaSyntax.scalar_definable_iff (F : Set (Values.Gamma (M := M)))).mp
  exact he.congr (fun z =>
    (FiniteOrder.minimal_controller_mem_iff_tuple hF hmin (z 0)).symm)

theorem exists_definable_minimal_gamma_controller (h00 : M ⊨ Axioms.ACVF00)
    (A : Set (Values.Gamma (M := M))) (hA : Values.GammaDefinable S A) :
    ∃ F : Finset (Values.Gamma (M := M)), FiniteOrder.Controls F A ∧
      Values.GammaDefinable S (F : Set (Values.Gamma (M := M))) ∧
      ∀ H, FiniteOrder.Controls H A → F.card ≤ H.card := by
  have hb := GammaParameters.real_definableAtBase
    (⟨S, ∅⟩ : GammaParameters.Base (M := M)) .rv (Values.gammaPullback A) hA
  obtain ⟨F, ⟨hF, hmin⟩, _⟩ := exists_unique_gamma_order_controller h00 ⟨S, ∅⟩ A hb
  exact ⟨F, hF, minimal_gamma_controller_definable A hA F hF hmin, hmin⟩

end SpecialTransformations.Section4

end
