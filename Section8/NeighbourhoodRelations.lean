import Section8.UniformBalls

/-! The uniform ball membership relation needed for Lemma 8.2. Here both
tuples and the radius representative are variables in a single formula. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M]

/-- Code order: centre tuple, member tuple, radius representative. -/
def uniformBallRelation (n : ℕ) : Set (((Fin n ⊕ Fin n) ⊕ Fin 1) → M) :=
  {z | (fun i => z (.inl (.inr i))) ∈
    uniformBall (fun i => z (.inl (.inl i))) (z (.inr 0))}

theorem uniformBallRelation_definable (S : Set M) (n : ℕ) :
    S.Definable LRV (uniformBallRelation n) := by
  let index (i : Fin n) : Fin 3 → (Fin n ⊕ Fin n) ⊕ Fin 1 :=
    ![.inl (.inl i), .inr 0, .inl (.inr i)]
  have h (i : Fin n) := (OpenBallCodes.membership_raw_definable S).preimage_comp (index i)
  convert Set.definable_iInter_of_finite h using 1
  ext z
  simp only [uniformBallRelation, uniformBall, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  apply forall_congr'
  intro i
  have hinit : Fin.init (z ∘ index i) = ![z (.inl (.inl i)), z (.inr 0)] := by
    funext j
    fin_cases j <;> rfl
  rw [hinit]
  rfl

variable [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv

theorem disjoint_uniformBall_iff {n : ℕ} {a b : Fin n → M} {r : M}
    (ha : ∀ i, iVF (a i)) (hb : ∀ i, iVF (b i)) (hr : iVF r) (hr0 : r ≠ iVFZero) :
    Disjoint (uniformBall a r) (uniformBall b r) ↔ b ∉ uniformBall a r := by
  constructor
  · intro hd hab
    exact Set.disjoint_left.mp hd hab (fun i => rawOpenBall_self v hv (hb i) hr hr0)
  · intro hab
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    apply hab
    intro i
    have ha' := rawOpenBall_recentre v hv (hxa i) (rawOpenBall_self v hv (ha i) hr hr0)
    have hb' := rawOpenBall_recentre v hv (hxb i) (rawOpenBall_self v hv (hb i) hr hr0)
    exact rawOpenBall_recentre v hv ha' hb'

end SpecialTransformations.Section8
