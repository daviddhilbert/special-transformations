import Section4.RealPresentations

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k l : ℕ}

def padVF (hkl : k ≤ l) (x : Fin k → VFType (M := M)) : Fin l → VFType (M := M) :=
  fun i => if hi : i.val < k then x ⟨i.val, hi⟩ else 0

theorem padVF_injective (hkl : k ≤ l) : Function.Injective (padVF (M := M) hkl) := by
  intro x y he
  funext i
  have hi : (Fin.castLE hkl i).val < k := i.isLt
  have h := congrFun he (Fin.castLE hkl i)
  simpa [padVF, Fin.castLE, hi] using h

noncomputable def vfPadding (hkl : k ≤ l) (Q : DefinableGeometry.Space LRV M) (S : Set M) :
    Map (DefSet.univ ((rawVFSpace k).prod Q) S)
      (DefSet.univ ((rawVFSpace l).prod Q) S) := by
  let F (z : Fin k ⊕ Q.Index → M) : Fin l ⊕ Q.Index → M :=
    Sum.elim (fun i => if hi : i.val < k then z (.inl ⟨i.val, hi⟩) else iVFZero)
      (z ∘ Sum.inr)
  have hF : S.DefinableMap LRV F := by
    intro u
    cases u with
    | inl i =>
      dsimp only [F, Sum.elim_inl]
      split_ifs
      · exact Set.DefinableFun.proj LRV
      · exact (Set.DefinableFun.of_empty
          (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfZero)).comp
          (show S.DefinableMap LRV (fun _ : Fin k ⊕ Q.Index → M => Fin.elim0) from
            fun j => j.elim0)
    | inr i => exact Set.DefinableFun.proj LRV
  have hcode (c : ((rawVFSpace (M := M) k).prod Q).domain) :
      vfValues (padVF hkl ((rawVFSpace (M := M) k).decode
        ⟨c.val ∘ Sum.inl, c.property.1⟩)) = F c.val ∘ Sum.inl := by
    have hv := Space.ofEmbedding_decode vfValues vfValues_injective
      (rawVFSpace (M := M) k).domain_definable ⟨c.val ∘ Sum.inl, c.property.1⟩
    funext i
    dsimp only [vfValues, padVF, F, Sum.elim_inl, Function.comp_apply]
    split_ifs with hi
    · exact congrFun hv ⟨i.val, hi⟩
    · rfl
  refine Map.ofCodes _ (fun x => (padVF hkl x.1, x.2)) F hF
    (fun c => ⟨⟨padVF hkl ((rawVFSpace (M := M) k).decode
      ⟨c.val ∘ Sum.inl, c.property.1⟩), hcode c⟩, c.property.2⟩) ?_
  intro c
  apply Prod.ext
  · apply vfValues_injective
    exact (Space.ofEmbedding_decode _ _ _ _).trans (hcode c).symm
  · rfl

theorem vfPadding_injective (hkl : k ≤ l) (Q : DefinableGeometry.Space LRV M) (S : Set M) :
    Function.Injective (vfPadding (M := M) hkl Q S) := by
  intro a b he
  apply Subtype.ext
  apply Prod.ext
  · apply padVF_injective hkl
    exact congrArg (fun z : DefSet.univ ((rawVFSpace l).prod Q) S => z.val.1) he
  · exact congrArg (fun z : DefSet.univ ((rawVFSpace l).prod Q) S => z.val.2) he

end SpecialTransformations.Section4
