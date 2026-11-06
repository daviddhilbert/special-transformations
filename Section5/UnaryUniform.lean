import Section5.UnarySets

/-!
# Simultaneous unary contraction

Finite polynomial families are treated over the same original base. Each
refinement preserves all previously obtained contractions because the
inverse of a special bijection preserves RV equivalence.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

namespace SpecialBijection

variable {S : Set M} {n a b c : ℕ}
variable {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
variable {C : DefSet (M := M) S n c}

theorem comp_toMap (T : SpecialBijection A B) (U : SpecialBijection B C)
    (h : (T.chain.append U.chain).Alternating none) :
    (T.comp U h).toMap = Map.comp U.toMap T.toMap := T.chain.append_toMap U.chain

theorem comp_inverseMap (T : SpecialBijection A B) (U : SpecialBijection B C)
    (h : (T.chain.append U.chain).Alternating none) (c : C) :
    (T.comp U h).inverseMap c = T.inverseMap (U.inverseMap c) := by
  apply (T.comp U h).bijective.1
  rw [SpecialBijection.apply_inverse, comp_toMap]
  change c = U.toMap (T.toMap (T.inverseMap (U.inverseMap c)))
  rw [T.apply_inverse, U.apply_inverse]

end SpecialBijection

variable {S : Set M} {a b : ℕ} {A : DefSet (M := M) S 1 a}
variable {B : DefSet (M := M) S 1 b}

theorem ScalarContractible.refine {f : A → VF (M := M)} (hf : ScalarContractible f)
    (T : SpecialBijection A B) : ScalarContractible (fun b : B => f (T.inverseMap b)) := by
  intro b c he
  exact hf _ _ (T.inverse_contractible b c he)

/-- Simultaneous unary Theorem 5.5, retaining the initial chain and its
alternation. The polynomial family may be empty. -/
theorem theorem_5_5_unary_finite (h00 : M ⊨ Axioms.ACVF00)
    (P : Finset (Polynomial (VF (M := M))))
    (hc : ∀ p ∈ P, ∀ i : ℕ, (p.coeff i).val ∈ S) :
    ∀ {m : ℕ} {A₀ : DefSet (M := M) S 1 0} {A : DefSet (M := M) S 1 m}
      (τ : SpecialBijection A₀ A),
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ T : SpecialBijection A B,
      (τ.chain.append T.chain).Alternating none ∧ IsRVPullback (carrier B) ∧
        ∀ p ∈ P, ScalarContractible
          (fun b : B => p.eval (vfAt (τ.inverseMap (T.inverseMap b)).val 0)) := by
  induction P using Finset.induction_on with
  | empty =>
    intro m A₀ A τ
    obtain ⟨r, B, T, hT, hB⟩ := lemma_5_2_after h00 τ
    exact ⟨r, B, T, hT, hB, by simp⟩
  | @insert p P hp ih =>
    intro m A₀ A τ
    obtain ⟨l, C, V, hV, hC, hP⟩ := ih (fun q hq => hc q (Finset.mem_insert_of_mem hq)) τ
    let U₀ := τ.comp V hV
    obtain ⟨r, B, W, hW, hB, hpol⟩ := theorem_5_5_unary h00 U₀ p (hc p (Finset.mem_insert_self _ _))
    have halt : (τ.chain.append (V.chain.append W.chain)).Alternating none := by
      rw [← Chain.append_assoc]
      exact hW
    let T := V.comp W (τ.chain.append_suffix_alternating _ none halt)
    refine ⟨r, B, T, halt, hB, ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · intro b c he
      simpa only [U₀, SpecialBijection.comp_inverseMap, T] using hpol b c he
    · have hh := (hP q hq).refine W
      intro b c he
      simpa only [T, SpecialBijection.comp_inverseMap] using hh b c he

end SpecialTransformations.Section5
