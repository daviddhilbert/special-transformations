module

public import Section8.ContinuityFormula

@[expose] public section

/-! The topology formulas work in families with an unchanged parameter
prefix. This lets continuity and topological closure descend from the
full relations of Gamma representatives. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] {ι : Type} {n m : ℕ}

private def stayInBallFamily (G : Set (ι ⊕ (Fin n ⊕ Fin m) → M)) :
    Set ((((ι ⊕ (Fin n ⊕ Fin m)) ⊕ Fin 1) ⊕ Fin 1) → M) :=
  {z | ¬ ∃ w : Fin n ⊕ Fin m → M, Sum.elim (fun i => z (.inl (.inl (.inl i)))) w ∈ G ∧
    w ∘ Sum.inl ∈ uniformBall (fun i => z (.inl (.inl (.inr (.inl i))))) (z (.inr 0)) ∧
    w ∘ Sum.inr ∉ uniformBall (fun i => z (.inl (.inl (.inr (.inr i))))) (z (.inl (.inr 0)))}

private theorem stayInBallFamily_definable {S : Set M} {G : Set (ι ⊕ (Fin n ⊕ Fin m) → M)}
    (hG : S.Definable LRV G) : S.Definable LRV (stayInBallFamily G) := by
  let X := Fin n ⊕ Fin m
  let Z := ((ι ⊕ X) ⊕ Fin 1) ⊕ Fin 1
  let W := Z ⊕ X
  let A : (Fin n ⊕ Fin n) ⊕ Fin 1 → W := Sum.elim
    (Sum.elim (fun i => .inl (.inl (.inl (.inr (.inl i))))) (fun i => .inr (.inl i)))
    (fun i => .inl (.inr i))
  let B : (Fin m ⊕ Fin m) ⊕ Fin 1 → W := Sum.elim
    (Sum.elim (fun i => .inl (.inl (.inl (.inr (.inr i))))) (fun i => .inr (.inr i)))
    (fun i => .inl (.inl (.inr i)))
  let e : ι ⊕ X → W := Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr
  convert ((hG.preimage_comp e).inter
    (((uniformBallRelation_definable S n).preimage_comp A).inter
      ((uniformBallRelation_definable S m).preimage_comp B).compl)).exists_of_finite.compl using 1
  ext z
  have he (w : X → M) :
      Sum.elim z w ∘ e = Sum.elim (fun i => z (.inl (.inl (.inl i)))) w := by
    funext i
    cases i <;> rfl
  change (¬ ∃ w : X → M, Sum.elim (fun i => z (.inl (.inl (.inl i)))) w ∈ G ∧
      w ∘ Sum.inl ∈ uniformBall (fun i => z (.inl (.inl (.inr (.inl i))))) (z (.inr 0)) ∧
      w ∘ Sum.inr ∉ uniformBall (fun i => z (.inl (.inl (.inr (.inr i))))) (z (.inl (.inr 0)))) ↔
    ¬ ∃ w : X → M, Sum.elim z w ∘ e ∈ G ∧
      (Sum.elim z w ∘ A) ∈ uniformBallRelation n ∧
      (Sum.elim z w ∘ B) ∉ uniformBallRelation m
  simp only [he, A, B, uniformBallRelation, Function.comp_apply, Sum.elim_inl, Sum.elim_inr] <;> rfl

private def continuousGraphFamily (G : Set (ι ⊕ (Fin n ⊕ Fin m) → M)) :
    Set (ι ⊕ (Fin n ⊕ Fin m) → M) :=
  {z | z ∈ G ∧ ∀ s : M, iVF s → s ≠ iVFZero →
    ∃ r : M, iVF r ∧ r ≠ iVFZero ∧ Sum.elim (Sum.elim z ![s]) ![r] ∈ stayInBallFamily G}

private theorem continuousGraphFamily_definable {S : Set M} {G : Set (ι ⊕ (Fin n ⊕ Fin m) → M)}
    (hG : S.Definable LRV G) : S.Definable LRV (continuousGraphFamily G) := by
  let X := ι ⊕ (Fin n ⊕ Fin m)
  let W := (X ⊕ Fin 1) ⊕ Fin 1
  have hGood := ((properRadiusAt_definable S (.inr 0 : W)).inter
    (stayInBallFamily_definable hG)).exists_of_finite
  have hBad := ((properRadiusAt_definable S (.inr 0 : X ⊕ Fin 1)).inter hGood.compl).exists_of_finite
  convert hG.inter hBad.compl using 1
  ext z
  change (z ∈ G ∧ ∀ s : M, iVF s → s ≠ iVFZero → ∃ r : M, iVF r ∧ r ≠ iVFZero ∧
    Sum.elim (Sum.elim z ![s]) ![r] ∈ stayInBallFamily G) ↔
    z ∈ G ∧ ¬ ∃ s : Fin 1 → M, (iVF (s 0) ∧ s 0 ≠ iVFZero) ∧
      ¬ ∃ r : Fin 1 → M, (iVF (r 0) ∧ r 0 ≠ iVFZero) ∧
        Sum.elim (Sum.elim z s) r ∈ stayInBallFamily G
  have he (u : Fin 1 → M) : ![u 0] = u := by funext i; fin_cases i; rfl
  refine and_congr_right (fun _ => ⟨?_, ?_⟩)
  · rintro h ⟨s, hs, hn⟩
    obtain ⟨r, hr, hr₀, h⟩ := h (s 0) hs.1 hs.2
    exact hn ⟨![r], ⟨hr, hr₀⟩, he s ▸ h⟩
  · intro h s hs hs₀
    by_contra hn
    apply h ⟨![s], ⟨hs, hs₀⟩, ?_⟩
    rintro ⟨r, hr, h⟩
    exact hn ⟨r 0, hr.1, hr.2, (he r).symm ▸ h⟩

def continuousInputsFamily (G : Set (ι ⊕ (Fin n ⊕ Fin m) → M)) : Set (ι ⊕ Fin n → M) :=
  {z | z ∘ Sum.inr ∈ continuousInputs {w | Sum.elim (z ∘ Sum.inl) w ∈ G}}

theorem continuousInputsFamily_definable [Finite ι] {S : Set M} {G : Set (ι ⊕ (Fin n ⊕ Fin m) → M)}
    (hG : S.Definable LRV G) : S.Definable LRV (continuousInputsFamily G) := by
  let i : ι ⊕ Fin n → ι ⊕ (Fin n ⊕ Fin m) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
  convert (continuousGraphFamily_definable hG).image_comp i using 1
  ext z
  have hgraph (w : Fin n ⊕ Fin m → M) :
      w ∈ continuousGraph {w | Sum.elim (z ∘ Sum.inl) w ∈ G} ↔
        Sum.elim (z ∘ Sum.inl) w ∈ continuousGraphFamily G := by
    change (_ ∧ _) ↔ (_ ∧ _)
    apply and_congr_right
    intro _
    refine forall_congr' (fun s => imp_congr Iff.rfl (imp_congr Iff.rfl (exists_congr (fun r => ?_))))
    refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
    simp only [stayInBall, stayInBallFamily, Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨w, hw, he⟩
    refine ⟨Sum.elim (z ∘ Sum.inl) w, (hgraph w).mp hw, ?_⟩
    funext j
    cases j with
    | inl j => rfl
    | inr j => exact congrFun he j
  · rintro ⟨w, hw, rfl⟩
    have he : Sum.elim ((w ∘ i) ∘ Sum.inl) (w ∘ Sum.inr) = w := by funext j; cases j <;> rfl
    exact ⟨w ∘ Sum.inr, (hgraph (w ∘ Sum.inr)).mpr (he.symm ▸ hw), rfl⟩

def vfRawClosureFamily (A : Set (ι ⊕ Fin n → M)) : Set (ι ⊕ Fin n → M) :=
  {z | z ∘ Sum.inr ∈ vfRawClosure {w | Sum.elim (z ∘ Sum.inl) w ∈ A}}

theorem vfRawClosureFamily_definable {S : Set M} {A : Set (ι ⊕ Fin n → M)}
    (hA : S.Definable LRV A) : S.Definable LRV (vfRawClosureFamily A) := by
  let Z := (ι ⊕ Fin n) ⊕ Fin 1
  let W := Z ⊕ Fin n
  let box : (Fin n ⊕ Fin n) ⊕ Fin 1 → W :=
    Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inr) Sum.inr) (Sum.inl ∘ Sum.inr)
  let e : ι ⊕ Fin n → W := Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr
  have hHit := ((hA.preimage_comp e).inter ((uniformBallRelation_definable S n).preimage_comp box)).exists_of_finite
  have hMiss := ((properRadiusAt_definable S (.inr 0 : Z)).inter hHit.compl).exists_of_finite
  convert ((vfRawUniverse_definable S n).preimage_comp (Sum.inr : Fin n → ι ⊕ Fin n)).inter
    hMiss.compl using 1
  ext z
  have he (r : Fin 1 → M) (w : Fin n → M) :
      Sum.elim (Sum.elim z r) w ∘ e = Sum.elim (z ∘ Sum.inl) w := by
    funext i
    cases i <;> rfl
  change (z ∘ Sum.inr ∈ vfRawUniverse n ∧
    ∀ r : M, iVF r → r ≠ iVFZero →
      ∃ w : Fin n → M, Sum.elim (z ∘ Sum.inl) w ∈ A ∧ w ∈ uniformBall (z ∘ Sum.inr) r) ↔
    z ∘ Sum.inr ∈ vfRawUniverse n ∧ ¬ ∃ r : Fin 1 → M, (iVF (r 0) ∧ r 0 ≠ iVFZero) ∧
      ¬ ∃ w : Fin n → M, Sum.elim (Sum.elim z r) w ∘ e ∈ A ∧ w ∈ uniformBall (z ∘ Sum.inr) (r 0)
  simp only [he]
  refine and_congr_right (fun _ => ⟨?_, ?_⟩)
  · rintro h ⟨r, hr, hn⟩
    exact hn (h (r 0) hr.1 hr.2)
  · intro h r hr hr₀
    by_contra hn
    exact h ⟨![r], ⟨hr, hr₀⟩, hn⟩

theorem continuityExceptionFamily_definable [Finite ι] {S : Set M} {G : Set (ι ⊕ (Fin n ⊕ Fin m) → M)}
    (hG : S.Definable LRV G) :
    S.Definable LRV {z | z ∘ Sum.inr ∈ continuityExceptionRaw {w | Sum.elim (z ∘ Sum.inl) w ∈ G}} := by
  let A := {z : ι ⊕ Fin n → M | z ∘ Sum.inr ∈ vfRawUniverse n} \ continuousInputsFamily G
  have hA : S.Definable LRV A :=
    ((vfRawUniverse_definable S n).preimage_comp (Sum.inr : Fin n → ι ⊕ Fin n)).inter
      (continuousInputsFamily_definable hG).compl
  convert vfRawClosureFamily_definable hA using 1
  ext z
  have he : {w | Sum.elim (z ∘ Sum.inl) w ∈ A} =
      vfRawUniverse n \ continuousInputs {w | Sum.elim (z ∘ Sum.inl) w ∈ G} := by
    ext w
    simp only [A, continuousInputsFamily, Set.mem_ofPred_eq, Set.mem_diff, Sum.elim_comp_inr,
      Sum.elim_comp_inl]
  change z ∘ Sum.inr ∈ continuityExceptionRaw _ ↔ z ∘ Sum.inr ∈ vfRawClosure _
  rw [he]
  rfl

end SpecialTransformations.Section8
