import Section3.GammaSpecialization
import Section3.SortedFiniteImage
import Section3.SmallFiniteParameters
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Corollary3.5 with full finite tuple arities and genuine Gamma-named
bases. A formula uses finitely many Gamma names; representative parameters
remain explicit only in the intermediate application of the real theorem. -/
theorem corollary_3_5_gamma_base {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {m n : ℕ} (A : Set (Fin m → M)) (f : A → Fin n → M)
    (hA : ∀ t ∈ A, ∀ j, iRV (t j)) (hf : ∀ t j, iVF (f t j))
    (hgraph : DefinableOverBase B (rvvfSort (m := m) (n := n)) (rvvfGraph A f)) :
    (Set.range f).Finite := by
  obtain ⟨k,t,hG⟩ := hgraph.specialize
  exact corollary_3_5_sorted hs (B.real ∪ Set.range (rawTuple t))
    (small_union_range hκ B.real hsmall (rawTuple t)) A f hA hf hG

end SpecialTransformations.Section3.GammaParameters
namespace SpecialTransformations.Section3
export GammaParameters (corollary_3_5_gamma_base)
end SpecialTransformations.Section3
