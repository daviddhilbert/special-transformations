import Section8.IsolationDimension

/-! The isolation construction works in a definable family. The same
parameters are held fixed at both graph points. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] {ι : Type} {n m : ℕ}

def graphIsolationFamily (G : Set ((ι ⊕ (Fin n ⊕ Fin m)) → M)) :
    Set ((ι ⊕ ((Fin n ⊕ Fin m) ⊕ Fin 2)) → M) :=
  {z | z ∘ Sum.inr ∈ graphIsolation {w | Sum.elim (z ∘ Sum.inl) w ∈ G}}

theorem graphIsolationFamily_definable {S : Set M} {G : Set ((ι ⊕ (Fin n ⊕ Fin m)) → M)}
    (hG : S.Definable LRV G) : S.Definable LRV (graphIsolationFamily G) := by
  let X := Fin n ⊕ Fin m
  let Z := ι ⊕ (X ⊕ Fin 2)
  let codeA : (Fin n ⊕ Fin n) ⊕ Fin 1 → Z ⊕ X := Sum.elim
    (Sum.elim (fun i => .inl (.inr (.inl (.inl i)))) (fun i => .inr (.inl i)))
    (fun _ => .inl (.inr (.inr 0)))
  let codeB : (Fin m ⊕ Fin m) ⊕ Fin 1 → Z ⊕ X := Sum.elim
    (Sum.elim (fun i => .inl (.inr (.inl (.inr i)))) (fun i => .inr (.inr i)))
    (fun _ => .inl (.inr (.inr 1)))
  let centre : ι ⊕ X → Z := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
  let competitor : ι ⊕ X → Z ⊕ X := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  have hA := (rvUniformBallRelation_definable S n).preimage_comp codeA
  have hB := (rvUniformBallRelation_definable S m).preimage_comp codeB
  have hEq : S.Definable LRV {z : Z ⊕ X → M | ∀ i : Fin n,
      z (.inr (.inl i)) = z (.inl (.inr (.inl (.inl i))))} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun i =>
      (Set.DefinableFun.proj LRV (i := Sum.inr (Sum.inl i))).ofPred_eq
        (Set.DefinableFun.proj LRV (i := Sum.inl (Sum.inr (Sum.inl (Sum.inl i))))))
  have hBad := ((hG.preimage_comp competitor).inter
    (hA.inter (hB.inter hEq.compl))).exists_of_finite
  have hRadii : S.Definable LRV {z : Z → M | ∀ j : Fin 2,
      GammaParameters.NonzeroRV (z (.inr (.inr j)))} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun j => (GammaParameters.nonzero_rv_definable S).preimage_comp
      (fun _ : Fin 1 => (Sum.inr (Sum.inr j) : Z)))
  convert (hG.preimage_comp centre).inter (hRadii.inter hBad.compl) using 1
  ext z
  have hcentre : Sum.elim (z ∘ Sum.inl) ((z ∘ Sum.inr) ∘ Sum.inl) = z ∘ centre := by
    funext i
    cases i <;> rfl
  have hcompetitor (w : X → M) :
      Sum.elim (z ∘ Sum.inl) w = Sum.elim z w ∘ competitor := by
    funext i
    cases i <;> rfl
  simp only [graphIsolationFamily, graphIsolation, Set.mem_ofPred_eq, Set.mem_setOf_eq,
    Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, hcentre, hcompetitor,
    Function.comp_apply, codeA, codeB, Sum.elim_inl, Sum.elim_inr] <;> rfl

def isolatedInputsFamily (G : Set ((ι ⊕ (Fin n ⊕ Fin m)) → M)) :
    Set ((ι ⊕ Fin n) → M) :=
  {z | z ∘ Sum.inr ∈ isolatedInputs {w | Sum.elim (z ∘ Sum.inl) w ∈ G}}

theorem isolatedInputsFamily_definable [Finite ι] {S : Set M}
    {G : Set ((ι ⊕ (Fin n ⊕ Fin m)) → M)} (hG : S.Definable LRV G) :
    S.Definable LRV (isolatedInputsFamily G) := by
  let project : ι ⊕ Fin n → ι ⊕ ((Fin n ⊕ Fin m) ⊕ Fin 2) :=
    Sum.elim Sum.inl (fun i => .inr (.inl (.inl i)))
  convert (graphIsolationFamily_definable hG).image_comp project using 1
  ext z
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨y, hy⟩ := (mem_inputIsolation_iff (z ∘ Sum.inr) t).mp ht
    refine ⟨Sum.elim (z ∘ Sum.inl) (Sum.elim (Sum.elim (z ∘ Sum.inr) y) t), hy, ?_⟩
    funext i
    cases i <;> rfl
  · rintro ⟨w, hw, rfl⟩
    let t : Fin 2 → M := fun j => w (.inr (.inr j))
    let y : Fin m → M := fun j => w (.inr (.inl (.inr j)))
    refine ⟨t, (mem_inputIsolation_iff ((w ∘ project) ∘ Sum.inr) t).mpr ⟨y, ?_⟩⟩
    have he : Sum.elim (Sum.elim ((w ∘ project) ∘ Sum.inr) y) t = w ∘ Sum.inr := by
      funext i
      rcases i with (i | j) | k <;> rfl
    rw [he]
    exact hw

end SpecialTransformations.Section8
