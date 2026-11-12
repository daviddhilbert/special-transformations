module

public import Section6.CommonEnvelopeComparison
public import Section6.NormalizedQuery
public import Section6.SentenceDenaming

@[expose] public section

/-! Compare a normalized existential formula on two henselian images
after all of its original parameters have been aligned. The auxiliary
sentence is denamed into exactly the original free context. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace SpecialTransformations.Section6.AlignedComparison
open RVTermSupport RVAbstraction RVGraphLanguage RVGraphExpansion NamedLanguage

abbrev Context (r m : ℕ) := Fin r ⊕ (Fin m ⊕ Empty)

def sorts {r m : ℕ} : Context r m → SortTag :=
  Sum.elim (fun _ => .vf) (fun _ => .rv)

variable {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF]
variable {E : _root_.FirstOrder.Language.{0, 0}} {r m n : ℕ}

def tuple (z : Context r m → C) (X : LRV.Substructure C)
    (hBX : Substructure.closure LRV (Set.range z) ≤ X) : Context r m → X :=
  fun i => ⟨z i, hBX (Substructure.subset_closure (Set.mem_range_self i))⟩

theorem existential_type_invariant
    (hcan : CanonicalStructure.IsCanonical (M := C))
    (z : Context r m → C) (hz : ∀ i, sortEval (sorts i) (z i))
    (hdefs : RVQFDefinitions (Substructure.closure LRV (Set.range z)))
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : C ⊨ Axioms.ACVF00) (v : Valuation (VF (M := C)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (hObstacles : ∀ N, UniformVerticalObstacles v
      ((Substructure.closure LRV (Set.range z)) : Set C) N)
    (φ : (Expanded E).Formula ((Fin r ⊕ Fin n) ⊕ (Fin m ⊕ Empty))) (hφ : Fragment φ)
    (X Y : LRV.Substructure C)
    (hBX : Substructure.closure LRV (Set.range z) ≤ X)
    (hBY : Substructure.closure LRV (Set.range z) ≤ Y)
    [E.Structure (SubRV (X : Set C))] [E.Structure (SubRV (Y : Set C))]
    (hX : HenselianInputs X) (hY : HenselianInputs Y)
    (htype : ∀ χ : (Expanded E).Formula (Context r m),
      ExpandedLogic.IsVFQF χ → ExpandedLogic.WellSorted sorts (fun _ => .rv) χ →
      (@Formula.Realize _ _ (CommonEnvelopeComparison.expandedStructure (E := E) X) _
        χ (tuple z X hBX) ↔
       @Formula.Realize _ _ (CommonEnvelopeComparison.expandedStructure (E := E) Y) _
        χ (tuple z Y hBY))) :
    (@Formula.Realize _ _ (CommonEnvelopeComparison.expandedStructure (E := E) X) _
      (NormalizedQuery.formula φ) (tuple z X hBX) ↔
     @Formula.Realize _ _ (CommonEnvelopeComparison.expandedStructure (E := E) Y) _
      (NormalizedQuery.formula φ) (tuple z Y hBY)) := by
  let B := Substructure.closure LRV (Set.range z)
  let c : Fin r → VF (M := C) := fun i => ⟨z (.inl i), hz (.inl i)⟩
  have hc : ∀ i, (c i).val ∈ B :=
    fun i => Substructure.subset_closure (Set.mem_range_self (f := z) (Sum.inl i))
  let d : Fin m → SubRV (B : Set C) := fun i =>
    ⟨⟨z (.inr (.inl i)), hz (.inr (.inl i))⟩,
      Substructure.subset_closure (Set.mem_range_self (f := z) (Sum.inr (Sum.inl i)))⟩
  obtain ⟨ψ, ⟨θ, rfl⟩, he⟩ := native_formula_elimination B hdefs h00 v hv hObstacles
    c hc d φ hφ
  obtain ⟨χ, hχ, hsχ, hχsem⟩ := SentenceDenaming.dename hcan sorts z hz θ
  have local_equivalence (Z : LRV.Substructure C) (hBZ : B ≤ Z)
      [E.Structure (SubRV (Z : Set C))] (hZ : HenselianInputs Z) :
      @Formula.Realize _ _ (CommonEnvelopeComparison.expandedStructure (E := E) Z) _
        (NormalizedQuery.formula φ) (tuple z Z hBZ) ↔
      @Formula.Realize _ _ (CommonEnvelopeComparison.expandedStructure (E := E) Z) _
        χ (tuple z Z hBZ) := by
    letI := RVSubstructure.extraStructure (E := E) Z
    let b : Empty → SubRV (Z : Set C) := default
    have hq := NormalizedQuery.named_realize B Z hBZ c hc d φ b
    have hassign :
        Sum.elim (fun i => (⟨(c i).val, hBZ (hc i)⟩ : Z))
          (RVSubstructure.inclusion Z ∘ Sum.elim (FiniteNamedSyntax.rvTuple B Z hBZ d) b) =
        tuple z Z hBZ := by
      funext i
      rcases i with i | (i | i)
      · rfl
      · rfl
      · exact i.elim
    rw [hassign] at hq
    have hd := fromAuxiliary_realize B Z hBZ θ b
    have hn := hχsem Z hBZ
    exact hq.trans ((he Z hBZ hZ b).trans (hd.symm.trans hn.symm))
  exact (local_equivalence X hBX hX).trans
    ((htype χ hχ hsχ).trans (local_equivalence Y hBY hY).symm)

end SpecialTransformations.Section6.AlignedComparison
