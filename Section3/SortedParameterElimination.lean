import Section3.CanonicalParameters
import Section3.DefinableConstants
import Section3.ClosureBridge
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Eliminate parameters already in sorted definable closure. This form
requires no convention for wrong-sort applications in the original model. -/
theorem DefinableAt.eliminate_sorted_definable_params {S B s : Set M} {σ : SortTag}
    (hs : DefinableAt B σ s)
    (hB : ∀ b ∈ B, ∃ τ, DefinableClosureAt S τ b) : DefinableAt S σ s := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have hcan : @CanonicalStructure.IsCanonical M N := CanonicalStructure.normalize_isCanonical
  have hBn (b : M) (hb : b ∈ B) : @Set.Definable₁ M S LRV N {b} := by
    obtain ⟨τ, hb'⟩ := hB b hb
    have hn : @DefinableClosureAt M N S τ b :=
      (definableClosureAt_normalize_iff S τ b).mpr hb'
    exact @DefinableAt.raw_definable M N S τ {b} hn
  have hsn : @DefinableAt M N B σ s := (definableAt_normalize_iff B σ s).mpr hs
  have hraw : @Set.Definable₁ M S LRV N s :=
    @DefinableConstants.eliminate_parameters M LRV N S B 1
      {z : Fin 1 → M | z 0 ∈ s} hBn (@DefinableAt.raw_definable M N B σ s hsn)
  have hout : @DefinableAt M N S σ s :=
    @raw_definable_sorted M N hN hcan S s σ hraw hsn.2
  exact (definableAt_normalize_iff S σ s).mp hout

theorem AlgebraicAt.eliminate_sorted_definable_params {S B : Set M} {σ : SortTag} {x : M}
    (hx : AlgebraicAt B σ x)
    (hB : ∀ b ∈ B, ∃ τ, DefinableClosureAt S τ b) : AlgebraicAt S σ x := by
  obtain ⟨s, hs, hf, hxs⟩ := hx
  exact ⟨s, hs.eliminate_sorted_definable_params hB, hf, hxs⟩

end SpecialTransformations.Section3
