import Section6.SyntacticDescent
import Section3.QuantifierFree

/-! Quantifier-free full contraction graphs over the original base. The
earlier sorted definability bridge and released ACVF QE are used as given.
The domain is retained even for an empty tuple of occurring polynomials.
The chosen formula is independent of a later henselian substructure. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section5

namespace SpecialTransformations.Section6

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n l k : ℕ}

def contractionGraphIndex (n l k : ℕ) :
    (Fin n ⊕ Fin l) ⊕ (Fin 0 ⊕ Fin k) → Fin (n + l + k) :=
  Sum.elim
    (Sum.elim (fun i => Fin.castAdd k (Fin.castAdd l i))
      (fun i => Fin.castAdd k (Fin.natAdd n i)))
    (Sum.elim Fin.elim0 (Fin.natAdd (n + l)))

def contractionGraphCodes {A : PresentedSet (keySpace (M := M) n l) S}
    {D : PresentedSet (keySpace (M := M) 0 k) S} (g : Map A D) :
    Set (Fin (n + l + k) → M) :=
  {z | z ∘ contractionGraphIndex n l k ∈
    @DefinableGeometry.Space.relation LRV M (CanonicalStructure.normalize (M := M))
      (keySpace n l) (keySpace 0 k)
      (fun u w => ∃ a : A, a.val = u ∧ (g a).val = w)}

theorem contractionGraphCodes_definable
    {A : PresentedSet (keySpace (M := M) n l) S}
    {D : PresentedSet (keySpace (M := M) 0 k) S} (g : Map A D) :
    Section4.RawDefinable S (contractionGraphCodes g) :=
  @Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
    ((Fin n ⊕ Fin l) ⊕ (Fin 0 ⊕ Fin k)) (Fin (n + l + k))
    (contractionGraphIndex n l k) _ (Map.graph_definable g)

theorem contractionGraphCodes_sorted
    {A : PresentedSet (keySpace (M := M) n l) S}
    {D : PresentedSet (keySpace (M := M) 0 k) S} (g : Map A D)
    {z : Fin (n + l + k) → M} (hz : z ∈ contractionGraphCodes g) :
    ∀ i, iRV (z i) := by
  obtain ⟨hu, hw, _⟩ := hz
  intro i
  cases i using Fin.addCases with
  | left i =>
    cases i using Fin.addCases with
    | left i => exact hu.1 i
    | right i => exact hu.2 i
  | right i => exact hw.2 i

/-- QE for the whole graph, not merely a conjunction of coordinate
equations on an unstated domain. All parameters remain in S. -/
theorem exists_qf_contraction_graph
    {A : PresentedSet (keySpace (M := M) n l) S}
    {D : PresentedSet (keySpace (M := M) 0 k) S} (g : Map A D) :
    ∃ p : Parameters S, ∃ ψ : LRV.BoundedFormula (Fin p.length) (n + l + k),
      ψ.IsQF ∧ WellSorted p.sorts (fun _ => .rv) ψ ∧
      ∀ z : Fin (n + l + k) → M,
        z ∈ contractionGraphCodes g ↔
          (∀ i, iRV (z i)) ∧ ψ.Realize p.values z := by
  have hd : DefinableOver S (fun _ => .rv) (contractionGraphCodes g) :=
    (definableOver_iff_normalized_raw S (fun _ => .rv) _).mpr
      ⟨contractionGraphCodes_definable g, fun _ hz => contractionGraphCodes_sorted g hz⟩
  obtain ⟨p, ψ, hq, hs, he⟩ := hd.quantifier_free hM
  exact ⟨p, ψ, hq, hs, fun z => Set.ext_iff.mp he z⟩

end SpecialTransformations.Section6
