import Section6.AlignedComparison
import Section6.ExpandedImages

/-! Transfer the constructed common-envelope comparison back to the
original expanded henselian structures. Their arbitrary RV operations
are transported by a proved isomorphism, rather than by an elementary
RV embedding into the algebraically closed field. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace SpecialTransformations.Section6.NativeImageComparison
open RVTermSupport RVAbstraction RVGraphLanguage AlignedComparison

variable {E : _root_.FirstOrder.Language.{0, 0}} {M N C : Type}
variable [(Expanded E).Structure M] [(Expanded E).Structure N]
variable [LRV.Structure M] [LRV.Structure N] [LRV.Structure C] [C ⊨ Axioms.ACVF]
variable [(LHom.sumInl : LRV →ᴸ Expanded E).IsExpansionOn M]
variable [(LHom.sumInl : LRV →ᴸ Expanded E).IsExpansionOn N]

theorem existential_type_invariant {r m n : ℕ}
    (hM : M ⊨ HenselianTheory.expanded E) (hN : N ⊨ HenselianTheory.expanded E)
    (hcan : CanonicalStructure.IsCanonical (M := C)) (h00 : C ⊨ Axioms.ACVF00)
    (f : M ↪[LRV] C) (g : N ↪[LRV] C)
    (hX : HenselianInputs (ExpandedImages.Image f))
    (hY : HenselianInputs (ExpandedImages.Image g))
    (a : Context r m → M) (b : Context r m → N)
    (halign : f ∘ a = g ∘ b)
    (ha : ∀ i, sortEval (sorts i) (f (a i)))
    (hdefs : RVQFDefinitions (Substructure.closure LRV (Set.range (f ∘ a))))
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF (M := C)) Γ)
    (hv : ∀ x y, VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ k, UniformVerticalObstacles v
      ((Substructure.closure LRV (Set.range (f ∘ a))) : Set C) k)
    (φ : (Expanded E).Formula ((Fin r ⊕ Fin n) ⊕ (Fin m ⊕ Empty))) (hφ : Fragment φ)
    (htype : ∀ χ : (Expanded E).Formula (Context r m),
      ExpandedLogic.IsVFQF χ → ExpandedLogic.WellSorted sorts (fun _ => .rv) χ →
      (χ.Realize a ↔ χ.Realize b)) :
    (NormalizedQuery.formula φ).Realize a ↔ (NormalizedQuery.formula φ).Realize b := by
  let X := ExpandedImages.Image f
  let Y := ExpandedImages.Image g
  let lawsM := ExtraSortSemantics.laws_of_henselian_model hM
  let lawsN := ExtraSortSemantics.laws_of_henselian_model hN
  letI := ExpandedImages.extraStructure f lawsM
  letI := ExpandedImages.extraStructure g lawsN
  letI : (Expanded E).Structure X := CommonEnvelopeComparison.expandedStructure (E := E) X
  letI : (Expanded E).Structure Y := CommonEnvelopeComparison.expandedStructure (E := E) Y
  let eM := ExpandedImages.expandedEquiv f lawsM
  let eN := ExpandedImages.expandedEquiv g lawsN
  have hBX : Substructure.closure LRV (Set.range (f ∘ a)) ≤ X := by
    apply Substructure.closure_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨a i, rfl⟩
  have hBY : Substructure.closure LRV (Set.range (f ∘ a)) ≤ Y := by
    rw [halign]
    apply Substructure.closure_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, rfl⟩
  have heM : tuple (f ∘ a) X hBX = eM ∘ a := by
    funext i
    apply Subtype.ext
    rfl
  have heN : tuple (f ∘ a) Y hBY = eN ∘ b := by
    funext i
    apply Subtype.ext
    exact congrFun halign i
  have ht : ∀ χ : (Expanded E).Formula (Context r m),
      ExpandedLogic.IsVFQF χ → ExpandedLogic.WellSorted sorts (fun _ => .rv) χ →
      (χ.Realize (tuple (f ∘ a) X hBX) ↔ χ.Realize (tuple (f ∘ a) Y hBY)) := by
    intro χ hχ hsχ
    rw [heM, heN]
    exact (eM.toElementaryEmbedding.map_formula χ a).trans
      ((htype χ hχ hsχ).trans (eN.toElementaryEmbedding.map_formula χ b).symm)
  have h := AlignedComparison.existential_type_invariant hcan (f ∘ a) ha hdefs
    h00 v hv hObstacles φ hφ X Y hBX hBY hX hY ht
  rw [heM, heN] at h
  exact (eM.toElementaryEmbedding.map_formula (NormalizedQuery.formula φ) a).symm.trans
    (h.trans (eN.toElementaryEmbedding.map_formula (NormalizedQuery.formula φ) b))

end SpecialTransformations.Section6.NativeImageComparison
