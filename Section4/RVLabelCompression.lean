import Section4.RVZeroDeletion
import Section4.RVCoordinates
import Section4.FiniteGluingRelation

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M]

theorem rvZero_coordinate_definable (S : Set M) {ι : Type} (i : ι) :
    S.Definable LRV {z : ι → M | z i = iRVZero} := by
  have hc : S.DefinableFun LRV (fun _ : ι → M => iRVZero) :=
    (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvZero)).comp
      (show S.DefinableMap LRV (fun _ : ι → M => Fin.elim0) from fun j => j.elim0)
  exact (Set.DefinableFun.proj LRV).ofPred_eq hc

def rvDefSetOfCode (S : Set M) {n : ℕ} (C : Set (Fin n → M)) (hC : S.Definable LRV C) :
    DefSet (rawRVSpace (M := M) n) S where
  carrier := {t | rvValues t ∈ C}
  definable := by
    change S.Definable LRV _
    convert ((rawRVSpace (M := M) n).domain_definable.mono (Set.empty_subset S)).inter hC using 1
    ext z
    constructor
    · rintro ⟨hz, hmem⟩
      refine ⟨hz, ?_⟩
      change rvValues ((rawRVSpace n).decode ⟨z, hz⟩) ∈ C at hmem
      rwa [rvValues_decode] at hmem
    · rintro ⟨hz, hmem⟩
      refine ⟨hz, ?_⟩
      change rvValues ((rawRVSpace n).decode ⟨z, hz⟩) ∈ C
      rwa [rvValues_decode]

def zeroLabelsAt (S : Set M) {k : ℕ} (i : Fin (k + 1)) :
    DefSet (rawRVSpace (M := M) (k + 1)) S :=
  rvDefSetOfCode S {z | z i = iRVZero} (rvZero_coordinate_definable S i)

def lowZeroLabels (S : Set M) (k : ℕ) : DefSet (rawRVSpace (M := M) (k + 1)) S :=
  rvDefSetOfCode S {z | ∃ i, z i = iRVZero} (by
    convert Set.definable_iUnion_of_finite (fun i : Fin (k + 1) => rvZero_coordinate_definable S i) using 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion])

def zeroDeleteAt (S : Set M) {k : ℕ} (i : Fin (k + 1)) :
    Map (zeroLabelsAt (M := M) S i) (DefSet.univ (rawRVSpace k) S) := by
  let F (z : Fin (k + 1) → M) := z ∘ i.succAbove
  have hcode (c : (rawRVSpace (M := M) (k + 1)).domain) :
      rvValues ((rawRVSpace (k + 1)).decode c ∘ i.succAbove) = F c.val := by
    funext j
    exact congrFun (rvValues_decode c) (i.succAbove j)
  refine Map.ofCodes _ (fun t => t ∘ i.succAbove) F
    (fun _ => Set.DefinableFun.proj LRV)
    (fun c => ⟨(rawRVSpace (k + 1)).decode c ∘ i.succAbove, hcode c⟩) ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode _).trans (hcode c).symm

theorem zeroDeleteAt_injective (S : Set M) {k : ℕ} (i : Fin (k + 1)) :
    Function.Injective (zeroDeleteAt (M := M) S i) := by
  intro a b he
  apply Subtype.ext
  have heval : Fin.removeNth i a.val = Fin.removeNth i b.val := congrArg Subtype.val he
  have hzero : a.val i = b.val i := Subtype.ext (a.property.trans b.property.symm)
  calc
    a.val = Fin.insertNth i (a.val i) (Fin.removeNth i a.val) := (Fin.insertNth_self_removeNth i a.val).symm
    _ = Fin.insertNth i (b.val i) (Fin.removeNth i b.val) := by rw [hzero, heval]
    _ = b.val := Fin.insertNth_self_removeNth i b.val

theorem exists_zero_label_compression (k : ℕ) :
    ∃ f : Map (lowZeroLabels (M := M) ∅ k) (DefSet.univ (rawRVSpace k) ∅),
      f.FiniteFibres ∧ ∀ a, RVZeroDeletion a.val (f a).val := by
  apply finite_cover_finite_map_respecting _ _ (fun i : Fin (k + 1) => zeroLabelsAt ∅ i)
    (fun i => zeroDeleteAt ∅ i)
    (fun i => Map.finiteFibres_of_injective (zeroDeleteAt_injective ∅ i))
  · intro i a
    exact ⟨i, a.property, rfl⟩
  · intro a
    obtain ⟨i, hi⟩ := a.property
    exact ⟨i, hi⟩

/-- One globally fixed definable compression over the empty base. It is
obtained by finite definable gluing of coordinate deletions, rather than
pointwise choice of RV values. -/
def labelCompression (k : ℕ) :
    Map (lowZeroLabels (M := M) ∅ k) (DefSet.univ (rawRVSpace k) ∅) :=
  Classical.choose (exists_zero_label_compression (M := M) k)

theorem labelCompression_finite (k : ℕ) : (labelCompression (M := M) k).FiniteFibres :=
  (Classical.choose_spec (exists_zero_label_compression (M := M) k)).1

theorem labelCompression_deletes_zero {k : ℕ} (a : lowZeroLabels (M := M) ∅ k) :
    RVZeroDeletion a.val (labelCompression k a).val :=
  (Classical.choose_spec (exists_zero_label_compression (M := M) k)).2 a

theorem labelCompression_weight {k : ℕ} (a : lowZeroLabels (M := M) ∅ k) :
    rvWeight (labelCompression k a).val = rvWeight a.val :=
  (labelCompression_deletes_zero a).weight

end SpecialTransformations.Section4

end
