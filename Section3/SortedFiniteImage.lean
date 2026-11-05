import Section3.FiniteImage
import Section3.NormalizationSaturation
import Section3.CanonicalParameters
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The sort profile of an RV-input, VF-output graph. -/
def rvvfSort {m n : ℕ} : Fin (m + n) → SortTag :=
  Sum.elim (fun _ : Fin m => .rv) (fun _ : Fin n => .vf) ∘ finSumFinEquiv.symm

/-- A partial function graph, with the input and output coordinates concatenated. -/
def rvvfGraph {m n : ℕ} (A : Set (Fin m → M)) (f : A → Fin n → M) :
    Set (Fin (m + n) → M) :=
  {z | ∃ t : A, t.val = z ∘ finSumFinEquiv ∘ Sum.inl ∧
    f t = z ∘ finSumFinEquiv ∘ Sum.inr}

/-- Corollary 3.5 for the paper's sorted definability, over any original small
base, in every ACVF model. No off-sort totalization is prescribed. -/
theorem corollary_3_5_sorted {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) {m n : ℕ}
    (A : Set (Fin m → M)) (f : A → Fin n → M)
    (hA : ∀ t ∈ A, ∀ j, iRV (t j)) (hf : ∀ t j, iVF (f t j))
    (hgraph : DefinableOver S (rvvfSort (m := m) (n := n)) (rvvfGraph A f)) :
    (Set.range f).Finite := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have hcan : @CanonicalStructure.IsCanonical M N := CanonicalStructure.normalize_isCanonical
  have hsat : @Saturated M N κ := hs.normalize
  have hGN : @DefinableOver M N S (m + n) rvvfSort (rvvfGraph A f) :=
    (definableOver_normalize_iff S _ _).mpr hgraph
  have hraw := @DefinableOver.raw_definable M N S (m + n) rvvfSort (rvvfGraph A f) hGN
  have hG : @Set.Definable M S LRV N (Fin m ⊕ Fin n)
      {z | ∃ t : A, t.val = z ∘ Sum.inl ∧ f t = z ∘ Sum.inr} := by
    letI := N
    convert hraw.preimage_comp (finSumFinEquiv.symm : Fin (m + n) → Fin m ⊕ Fin n) using 1
    ext z
    simp only [rvvfGraph, Set.mem_preimage, Set.mem_ofPred_eq, Function.comp_def,
      Equiv.symm_apply_apply]
  have hAN (t : Fin m → M) (ht : t ∈ A) (j : Fin m) : @iRV M N (t j) := hA t ht j
  have hfN (t : A) (j : Fin n) : @iVF M N (f t j) := hf t j
  exact @corollary_3_5 M N hN hcan κ hsat S hsmall m n A f hAN hfN hG

end SpecialTransformations.Section3
