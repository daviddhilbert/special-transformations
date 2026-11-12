module

public import Section3.CanonicalParameters
public import Section3.DefinableConstants
public import Section3.GammaParameterBridge

@[expose] public section

/- Component: GammaRealBaseElimination -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Eliminate real definable names and imaginary names whose full value
fibres are already definable. Every Gamma representative is quantified. -/
theorem DefinableOverBase.eliminate_to_real_base {B : Base (M := M)} {S : Set M}
    {n : ℕ} {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : DefinableOverBase B sn A)
    (hreal : ∀ b ∈ B.real, ∃ σ, DefinableClosureAt S σ b)
    (hgamma : ∀ γ ∈ B.gamma, DefinableAt S .rv (Values.gammaPullback {γ})) :
    SpecialTransformations.Section3.DefinableOver S sn A := by
  obtain ⟨k,γ,hγ,R,rfl⟩ := hA
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hrealN (b : M) (hb : b ∈ B.real) : @Set.Definable₁ M S LRV N {b} := by
    obtain ⟨σ,hb⟩ := hreal b hb
    exact ((definableAt_iff_normalized_raw S σ {b}).mp hb).1
  let e : Fin k ⊕ Fin n ≃ Fin (k+n) := finSumFinEquiv
  have hR0 := @Set.Definable.preimage_comp M B.real LRV N
    (Fin k ⊕ Fin n) (Fin (k+n)) e _ R.definable
  have hR1 := @DefinableConstants.eliminate_parameters M LRV N S B.real (k+n) _ hrealN hR0
  have hR2 := @Set.Definable.preimage_comp M S LRV N
    (Fin (k+n)) (Fin k ⊕ Fin n) e.symm _ hR1
  have hR : @Set.Definable M S LRV N (Fin k ⊕ Fin n)
      {z | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ R.carrier} := by
    convert hR2 using 1
    ext z
    simp only [Set.mem_preimage,Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id]
  have hG (i : Fin k) :=
    ((definableAt_iff_normalized_raw S .rv (Values.gammaPullback {γ i})).mp
      (hgamma (γ i) (hγ i))).1
  have hs := R.fibre_proper γ
  apply (definableOver_iff_normalized_raw S sn (R.fibre γ)).mpr
  refine ⟨?_,hs⟩
  letI := N
  have hGs := Set.definable_iInter_of_finite (fun i : Fin k =>
    (hG i).preimage_comp (fun _ : Fin 1 => (Sum.inl i : Fin k ⊕ Fin n)))
  have hp := (hR.inter hGs).image_comp (Sum.inr : Fin n → Fin k ⊕ Fin n)
  letI := sM
  convert hp using 1
  ext z
  change z ∈ R.fibre γ ↔ ∃ w,
    ((w ∘ Sum.inl,w ∘ Sum.inr) ∈ R.carrier ∧
      (w ∈ ⋂ i : Fin k, {w : Fin k ⊕ Fin n → M | w (Sum.inl i) ∈ Values.gammaPullback {γ i}})) ∧
      w ∘ Sum.inr = z
  constructor
  · intro hz
    refine ⟨Sum.elim (rawTuple (representatives γ)) z,⟨hz,?_⟩,rfl⟩
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    intro i
    exact ⟨raw_rv (representative (γ i)),raw_ne_zero (representative (γ i)),
      representative_value (γ i)⟩
  · rintro ⟨w,⟨hw,hG⟩,he⟩
    have hwP := (R.proper _ hw).1
    let t := ofRaw (w ∘ Sum.inl) hwP
    have ht : values t = γ := by
      funext i
      obtain ⟨hi,h0,hval⟩ := Set.mem_iInter.mp hG i
      exact hval
    have hm := (R.mem_fibre_iff t γ ht (w ∘ Sum.inr)).mpr hw
    rwa [he] at hm

end SpecialTransformations.Section3.GammaParameters
